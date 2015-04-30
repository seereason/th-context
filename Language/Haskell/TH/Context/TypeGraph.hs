{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wall #-}
module Language.Haskell.TH.Context.TypeGraph
    ( VertexStatus(..)
    , TypeGraphNode(..)
    , typeGraphNode
    , TypeGraphEdges
    , typeGraphEdges
    , typeGraphVertices
    , typeGraph
    ) where

#if __GLASGOW_HASKELL__ < 709
import Control.Applicative
import Data.Monoid (mempty)
#endif
import Control.Monad.State (execStateT, modify, MonadState(get), StateT)
import Control.Monad.Trans (lift)
import Data.Default (Default(def))
import Data.Graph (Graph, Vertex, graphFromEdges)
import Data.Map as Map (Map, keys, lookup, toList, update, alter)
import Data.Set as Set (insert, Set, empty, fromList, toList)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH -- (Con, Dec, nameBase, Type)
import Language.Haskell.TH.Context.Expand (E, expandType, runExpanded)
import Language.Haskell.TH.Desugar as DS (DsMonad)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.Syntax (Quasi(..))

-- | For simple type graphs always set _field and _alias to Nothing.
data TypeGraphNode
    = TypeGraphNode
      { _field :: Maybe (Name, Name, Either Int Name) -- ^ The record filed which contains this type
      , _alias :: [Name] -- ^ The series of type synonyms we expanded to arrive at this type
      , _etype :: Type -- ^ The fully expanded type
      } deriving (Eq, Ord, Show)

-- | Build a TypeGraphNode from an unexpanded type.  This records the
-- type synonyms we expand to reach the "real" type.  Arguments
-- supply the optional field and alias list values.
typeGraphNode :: forall m. DsMonad m => Maybe (Name, Name, Either Int Name) -> [Name] -> Type -> m TypeGraphNode
typeGraphNode field alias typ =
    case typ of
      (ConT name) -> doName name -- special case to catch top level type synonyms.  Others are removed by expandType below.
      _ -> doType typ
    where
      doType :: Type -> m TypeGraphNode
      -- What happens to ForallT types here?
      doType typ' = expandType typ' >>= \(etype :: E Type) -> return $ TypeGraphNode {_field = field, _alias = alias, _etype = runExpanded etype}
      doName :: Name -> m TypeGraphNode
      doName name = runQ (reify name) >>= doInfo name
      doInfo :: Name -> Info -> m TypeGraphNode
      doInfo name (TyConI dec) = doDec name dec
      doInfo name _ = doType (ConT name)
      doDec :: Name -> Dec -> m TypeGraphNode
      doDec _ (TySynD name _ typ') = doType typ' >>= \node -> return $ node {_alias = name : _alias node}
      doDec name _dec = doType (ConT name)

type TypeGraphEdges = Map TypeGraphNode (Set TypeGraphNode)

-- | When a VertexStatus value is associated with a Type it describes
-- alterations in the type graph from the usual default.
data VertexStatus
    = Vertex      -- ^ normal case
    | NoVertex    -- ^ exclude this type from the graph
    | Sink        -- ^ out degree zero - don't create any outgoing edges
    | Divert Type -- ^ replace all outgoing edges with an edge to an alternate type
    | Extra Type  -- ^ add an extra outgoing edge to the given type
    deriving Show

instance Default VertexStatus where
    def = Vertex

-- | Return the set of types embedded in the given type.  This is just
-- the nodes of the type graph.  The type aliases are expanded by the
-- th-desugar package to make them suitable for use as map keys.
typeGraphVertices :: forall m. DsMonad m =>
                     (TypeGraphNode -> m VertexStatus)
                  -> [Type]
                  -> m (Set TypeGraphNode)
typeGraphVertices augment types =
    (Set.fromList . Map.keys) <$> (typeGraphEdges augment types :: m TypeGraphEdges)

typeGraphEdges
    :: forall m. DsMonad m =>
       (TypeGraphNode -> m VertexStatus)
           -- ^ This function is used to obtain hints about the graph
           -- structure around a given node.  If it returns NoVertex,
           -- no vertices or edges are added to the graph.  If it
           -- returns Sink no outgoing edges are added.  The current
           -- use case Substitute is to see if there is an instance of
           -- class @View a b@ where @a@ is the type passed to
           -- @doType@, and replace it with @b@, and use the lens
           -- returned by @View's@ method to convert between @a@ and
           -- @b@ (i.e. to implement the edge in the type graph.)
    -> [Type]
    -> m TypeGraphEdges
typeGraphEdges augment types = do
  execStateT (mapM_ (\ typ -> typeGraphNode Nothing [] typ >>= doNode) types) mempty
    where
      doNode :: TypeGraphNode -> StateT TypeGraphEdges m ()
      doNode node = do
        (mp :: TypeGraphEdges) <- get
        status <- lift (augment node)
        case Map.lookup node mp of
          Just _ -> return ()
          Nothing ->
            case status of
              NoVertex -> return ()
              Sink -> addNode
              (Divert typ') -> typeGraphNode Nothing [] typ' >>= \node' -> addNode >> addEdge node' >> doNode node' -- field or Nothing?  Are we still in the same field after Divert (or Extra)?)
              (Extra typ') -> typeGraphNode Nothing [] typ' >>= \node' -> addNode >> doEdges node >> addEdge node' >> doNode node'
              Vertex -> addNode >> doEdges node
        where
          addNode :: StateT TypeGraphEdges m ()
          -- addNode a = expandType a >>= \ a' -> modify $ Map.insertWith (flip const) a' Set.empty
          addNode = modify $ Map.alter (maybe (Just Set.empty) Just) node
          addEdge :: TypeGraphNode -> StateT TypeGraphEdges m ()
          addEdge node' = modify $ Map.update (Just . Set.insert node') node

          -- Find and add the out edges from a node.
          doEdges :: TypeGraphNode -> StateT TypeGraphEdges m ()
          -- Do we treat this as a distinct type?
          doEdges (TypeGraphNode {_etype = (ForallT _ _ typ')}) = typeGraphNode (_field node) (_alias node) typ' >>= \node' -> addEdge node' >> doNode node'
          doEdges (TypeGraphNode {_etype = (AppT container element)}) = do
            cnode <- typeGraphNode Nothing [] container
            enode <- typeGraphNode Nothing [] element
            addEdge cnode
            addEdge enode
            doNode cnode
            doNode enode
          doEdges (TypeGraphNode {_etype = (ConT name)}) = do
            info <- qReify name
            case info of
              TyConI dec -> doDec dec
              _ -> return ()
              where
                doDec :: Dec -> StateT TypeGraphEdges m ()
                doDec dec@(NewtypeD _ tname _ con _) = doCon tname dec con
                doDec dec@(DataD _ tname _ cons _) = mapM_ (doCon tname dec) cons
                doDec (TySynD _tname _tvars typ') = typeGraphNode Nothing [] typ' >>= \node' -> doNode node'
                doDec _ = return ()

                doCon :: Name -> Dec -> Con -> StateT TypeGraphEdges m ()
                doCon tname dec (ForallC _ _ con) = doCon tname dec con
                doCon tname dec (NormalC cname fields) = mapM_ (doField tname dec cname) (zip (map Left ([1..] :: [Int])) (map snd fields))
                doCon tname dec (RecC cname fields) = mapM_ (doField tname dec cname) (map (\ (fname, _, typ') -> (Right fname, typ')) fields)
                doCon tname dec (InfixC (_, lhs) cname (_, rhs)) = mapM_ (doField tname dec cname) [(Left 1, lhs), (Left 2, rhs)]

                doField :: Name -> Dec -> Name -> (Either Int Name, Type) -> StateT TypeGraphEdges m ()
                doField tname _dec cname (field, ftype) = typeGraphNode (Just (tname, cname, field)) [] ftype >>= \node' -> addEdge node' >> doNode node'

          doEdges _ = return ({-trace ("Unrecognized type: " ++ pprint' typ)-} ())

-- | Build a graph from the result of typeGraphEdges, each edge goes
-- from a type to one of the types it contains.  Thus, each edge
-- represents a primitive lens, and each path in the graph is a
-- composition of lenses.
typeGraph :: forall m node key. (DsMonad m, node ~ TypeGraphNode, key ~ TypeGraphNode) =>
                (TypeGraphNode -> m VertexStatus) -> [Type] -> m (Graph, Vertex -> (node, key, [key]), key -> Maybe Vertex)
typeGraph augment types = do
  typeGraphEdges augment types >>= return . graphFromEdges . triples
    where
      triples :: Map TypeGraphNode (Set TypeGraphNode) -> [(TypeGraphNode, TypeGraphNode, [TypeGraphNode])]
      triples mp = map (\ (k, ks) -> (k, k, Set.toList ks)) $ Map.toList mp
