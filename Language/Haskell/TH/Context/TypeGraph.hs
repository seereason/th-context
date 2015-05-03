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
    ( VertexHint(..)
    , TypeGraphVertex(..)
    , typeVertex
    , fieldVertex
    , TypeGraphEdges
    , typeGraphEdges
    , typeGraphVertices
    , typeGraph
    , simpleVertex
    , simpleEdges
    , typeSynonymMap
    , typeSynonymMapSimple
    ) where

#if __GLASGOW_HASKELL__ < 709
import Control.Applicative
import Data.Monoid (mempty)
#endif
import Control.Monad.State (execStateT, modify, MonadState(get), StateT)
import Control.Monad.Trans (lift)
import Data.Default (Default(def))
import Data.Generics (Data, everywhere, mkT)
import Data.Graph (Graph, Vertex, graphFromEdges)
import Data.List as List (concatMap, intersperse, map)
import Data.Map as Map (Map, filter, fromList, fromListWith, keys, lookup, map, mapKeys, toList, update, alter)
import Data.Set as Set (empty, fromList, insert, map, member, null, Set, toList, union)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH -- (Con, Dec, nameBase, Type)
import Language.Haskell.TH.Context.Expand (E, expandType, markExpanded, runExpanded)
import Language.Haskell.TH.Desugar as DS (DsMonad)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.PprLib (hcat, ptext)
import Language.Haskell.TH.Syntax (Quasi(..))

import Debug.Trace

-- | For simple type graphs always set _field and _synonyms to Nothing.
data TypeGraphVertex
    = TypeGraphVertex
      { _field :: Maybe (Name, Name, Either Int Name) -- ^ The record filed which contains this type
      , _synonyms :: [Name] -- ^ The series of type synonyms we expanded to arrive at this type
      , _etype :: Type -- ^ The fully expanded type
      } deriving (Eq, Ord, Show)

instance Ppr TypeGraphVertex where
    ppr (TypeGraphVertex {_field = fld, _synonyms = ns, _etype = typ}) =
        hcat (ppr (unReify typ) :
              case (fld, ns) of
                 (Nothing, []) -> []
                 _ ->   [ptext " ("] ++
                        intersperse (ptext ", ")
                          (List.concatMap (\ n -> [ptext ("aka " ++ show (unReifyName n))]) ns ++
                           maybe [] (\ f -> [ptext (printField f)]) fld) ++
                        [ptext ")"])
        where
          printField :: (Name, Name, Either Int Name) -> String
          printField (tname, cname, field) =
              "field " ++
              show (unReifyName tname) ++ "." ++
              either (\ n -> show (unReifyName cname) ++ "[" ++ show n ++ "]") (\ f -> show (unReifyName f)) field

          unReify :: Data a => a -> a
          unReify = everywhere (mkT unReifyName)

          unReifyName :: Name -> Name
          unReifyName = mkName . nameBase

-- | Build a TypeGraphVertex from an unexpanded type.  This records the
-- type synonyms we expand to reach the "real" type.
typeVertex :: DsMonad m => Type -> m TypeGraphVertex
typeVertex typ =
    case typ of
      (ConT name) -> doName name -- special case to catch top level type synonyms.  Others are removed by expandType below.
      _ -> doType typ
    where
      -- What happens to ForallT types here?
      doType typ' = expandType typ' >>= \(etype :: E Type) -> return $ TypeGraphVertex {_field = Nothing, _synonyms = [], _etype = runExpanded etype}
      doName name = runQ (reify name) >>= doInfo name
      doInfo name (TyConI dec) = doDec name dec
      doInfo name _ = doType (ConT name)
      doDec _ (TySynD name _ typ') = doType typ' >>= \node -> return $ node {_synonyms = name : _synonyms node}
      doDec name _dec = doType (ConT name)

-- | Build a TypeGraphVertex for a field of a record.  This calls
-- 'typeVertex' and then sets the _field value.
fieldVertex :: forall m. DsMonad m => Type -> (Name, Name, Either Int Name) -> m TypeGraphVertex
fieldVertex typ field = typeVertex typ >>= \node -> return $ node {_field = Just field}

type TypeGraphEdges = Map TypeGraphVertex (Set TypeGraphVertex)

-- | When a VertexHint value is associated with a Type it describes
-- alterations in the type graph from the usual default.
data VertexHint
    = Normal      -- ^ normal case
    | Hidden      -- ^ don't create this vertex, no in or out edges
    | Sink        -- ^ out degree zero - don't create any out edges
    | Divert Type -- ^ replace all out edges with an edge to an alternate type
    | Extra Type  -- ^ add an extra out edge to the given type
    deriving (Eq, Ord, Show)

instance Default VertexHint where
    def = Normal

-- | Return the set of types embedded in the given type.  This is just
-- the nodes of the type graph.  The type synonymes are expanded by the
-- th-desugar package to make them suitable for use as map keys.
typeGraphVertices :: forall m. DsMonad m =>
                     (TypeGraphVertex -> m VertexHint)
                  -> [Type]
                  -> m (Set TypeGraphVertex)
typeGraphVertices augment types =
    (Set.fromList . Map.keys) <$> (typeGraphEdges augment types :: m TypeGraphEdges)

typeGraphEdges
    :: forall m. DsMonad m =>
       (TypeGraphVertex -> m VertexHint)
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
  execStateT (mapM_ (\ typ -> typeVertex typ >>= doVertex Set.empty) types) mempty
    where
      doVertex :: Set (TypeGraphVertex, VertexHint) -> TypeGraphVertex -> StateT TypeGraphEdges m ()
      doVertex used node = do
        (mp :: TypeGraphEdges) <- get
        status <- lift (augment node)
        case Map.lookup node mp of
          Just _ -> return ()
          Nothing ->
            case status of
              _ | Set.member (node, status) used -> addVertex >> doEdges node
              Normal -> addVertex >> doEdges node
              Hidden -> return ()
              Sink -> addVertex
              hint@(Divert typ') -> typeVertex typ' >>= \node' -> addVertex >> addEdge node' >> doVertex (Set.insert (node, hint) used) node'
              (Extra typ') -> typeVertex typ' >>= \node' -> addVertex >> doEdges node >> addEdge node' >> doVertex (Set.insert (node, status) used) node'
        where
          addVertex :: StateT TypeGraphEdges m ()
          -- addVertex a = expandType a >>= \ a' -> modify $ Map.insertWith (flip const) a' Set.empty
          addVertex = modify $ Map.alter (maybe (Just Set.empty) Just) node
          addEdge :: TypeGraphVertex -> StateT TypeGraphEdges m ()
          addEdge node' = modify $ Map.update (Just . Set.insert node') node

          -- Find and add the out edges from a node.
          doEdges :: TypeGraphVertex -> StateT TypeGraphEdges m ()
          -- Do we treat this as a distinct type?
          doEdges (TypeGraphVertex {_etype = (ForallT _ _ typ')}) =
              -- typeGraphVertex (_field node) (_synonyms node) typ' >>= \node' -> addEdge node' >> doVertex node'
              doEdges (node {_etype = typ'})
          doEdges (TypeGraphVertex {_etype = (AppT container element)}) = do
            cnode <- typeVertex container
            enode <- typeVertex element
            addEdge cnode
            addEdge enode
            doVertex used cnode
            doVertex used enode
          doEdges (TypeGraphVertex {_etype = (ConT name)}) = do
            info <- qReify name
            case info of
              TyConI dec -> doDec dec
              _ -> return ()
              where
                doDec :: Dec -> StateT TypeGraphEdges m ()
                doDec dec@(NewtypeD _ tname _ con _) = doCon tname dec con
                doDec dec@(DataD _ tname _ cons _) = mapM_ (doCon tname dec) cons
                doDec (TySynD _tname _tvars typ') = trace "unexpected synonym" (return ()) >> typeVertex typ' >>= \node' -> doVertex used node'
                doDec _ = return ()

                doCon :: Name -> Dec -> Con -> StateT TypeGraphEdges m ()
                doCon tname dec (ForallC _ _ con) = doCon tname dec con
                doCon tname dec (NormalC cname fields) = mapM_ (doField tname dec cname) (zip (List.map Left ([1..] :: [Int])) (List.map snd fields))
                doCon tname dec (RecC cname fields) = mapM_ (doField tname dec cname) (List.map (\ (fname, _, typ') -> (Right fname, typ')) fields)
                doCon tname dec (InfixC (_, lhs) cname (_, rhs)) = mapM_ (doField tname dec cname) [(Left 1, lhs), (Left 2, rhs)]

                doField :: Name -> Dec -> Name -> (Either Int Name, Type) -> StateT TypeGraphEdges m ()
                doField tname _dec cname (field, ftype) = fieldVertex ftype (tname, cname, field) >>= \node' -> addEdge node' >> doVertex used node'

          doEdges _ = return ({-trace ("Unrecognized type: " ++ pprint' typ)-} ())

-- | Build a graph from the result of typeGraphEdges, each edge goes
-- from a type to one of the types it contains.  Thus, each edge
-- represents a primitive lens, and each path in the graph is a
-- composition of lenses.
typeGraph :: forall m node key. (DsMonad m, node ~ TypeGraphVertex, key ~ TypeGraphVertex) =>
                (TypeGraphVertex -> m VertexHint) -> [Type] -> m (Graph, Vertex -> (node, key, [key]), key -> Maybe Vertex)
typeGraph augment types = do
  typeGraphEdges augment types >>= return . graphFromEdges . triples
    where
      triples :: Map TypeGraphVertex (Set TypeGraphVertex) -> [(TypeGraphVertex, TypeGraphVertex, [TypeGraphVertex])]
      triples mp = List.map (\ (k, ks) -> (k, k, Set.toList ks)) $ Map.toList mp

-- | Simplify a graph by throwing away the field and type synonym
-- information in each node.  This means the nodes only contain the
-- fully expanded Type value.
simpleEdges :: TypeGraphEdges -> TypeGraphEdges
simpleEdges = Map.mapKeys simpleVertex . Map.map (Set.map simpleVertex)

simpleVertex :: TypeGraphVertex -> TypeGraphVertex
simpleVertex node = node {_synonyms = [], _field = Nothing}

-- | Find all the reachable type synonyms and return then in a Map.
typeSynonymMap :: forall m. DsMonad m => (TypeGraphVertex -> m VertexHint) -> [Type] -> m (Map TypeGraphVertex (Set Name))
typeSynonymMap augment types =
     (Map.filter (not . Set.null) .
      Map.fromList .
      List.map (\node -> (node, Set.fromList (_synonyms node))) .
      Map.keys) <$> typeGraphEdges augment types

typeSynonymMapSimple :: forall m. DsMonad m => (TypeGraphVertex -> m VertexHint) -> [Type] -> m (Map (E Type) (Set Name))
typeSynonymMapSimple augment types =
    simplify <$> typeSynonymMap augment types
    where
      simplify :: Map TypeGraphVertex (Set Name) -> Map (E Type) (Set Name)
      simplify mp = Map.fromListWith Set.union (List.map (\ (k, a) -> (markExpanded (_etype k), a)) (Map.toList mp))
