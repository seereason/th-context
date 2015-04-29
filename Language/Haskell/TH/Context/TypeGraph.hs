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
import Language.Haskell.TH.Context.Expand (Expanded, expandType, markExpanded, runExpanded)
import Language.Haskell.TH.Desugar as DS (DsMonad)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.Syntax (Quasi(..))

type TypeGraphEdges typ = Map typ (Set typ)

-- | When a VertexStatus value is associated with a Type it describes
-- alterations in the type graph from the usual default.
data VertexStatus typ
    = Vertex      -- ^ normal case
    | NoVertex    -- ^ exclude this type from the graph
    | Sink        -- ^ out degree zero - don't create any outgoing edges
    | Divert typ  -- ^ replace all outgoing edges with an edge to an alternate type
    | Extra typ   -- ^ add an extra outgoing edge to the given type
    deriving Show

instance Default (VertexStatus typ) where
    def = Vertex

-- | Return the set of types embedded in the given type.  This is just
-- the nodes of the type graph.  The type aliases are expanded by the
-- th-desugar package to make them suitable for use as map keys.
typeGraphVertices :: (DsMonad m, Expanded Type etype, Ord etype) =>
                     (etype -> m (VertexStatus etype))
                  -> [etype]
                  -> m (Set etype)
typeGraphVertices augment types =
    (Set.fromList . Map.keys) <$> typeGraphEdges augment types

typeGraphEdges
    :: forall m etype. (DsMonad m, Expanded Type etype, Ord etype) =>
       (etype -> m (VertexStatus etype))
           -- ^ This function is applied to every expanded type before
           -- use, and the result is used instead.  If it returns
           -- NoVertex, no vertices or edges are added to the graph.
           -- If it returns Sink no outgoing edges are added.  The
           -- current use case Substitute is to see if there is an
           -- instance of class @View a b@ where @a@ is the type
           -- passed to @doType@, and replace it with @b@, and use the
           -- lens returned by @View's@ method to convert between @a@
           -- and @b@ (i.e. to implement the edge in the type graph.)
    -> [etype]
    -> m (TypeGraphEdges etype)

typeGraphEdges augment types = do
  execStateT (mapM_ doNode types) mempty
    where
      doNode :: etype -> StateT (TypeGraphEdges etype) m ()
      doNode typ = do
        (mp :: TypeGraphEdges etype) <- get
        status <- lift (augment typ)
        case Map.lookup typ mp of
          Just _ -> return ()
          Nothing ->
            case status of
              NoVertex -> return ()
              Sink -> addNode typ
              (Divert typ') -> addNode typ >> addEdge typ typ' >> doNode typ'
              (Extra typ') -> addNode typ >> doEdges (runExpanded typ) >> addEdge typ typ' >> doNode typ'
              Vertex -> addNode typ >> doEdges (runExpanded typ)

      addNode :: etype -> StateT (TypeGraphEdges etype) m ()
      -- addNode a = expandType a >>= \ a' -> modify $ Map.insertWith (flip const) a' Set.empty
      addNode a = modify $ Map.alter (maybe (Just Set.empty) Just) a
      addEdge :: etype -> etype -> StateT (TypeGraphEdges etype) m ()
      addEdge a b = modify $ Map.update (Just . Set.insert b) a

      -- We know that the Type argument is actually fully expanded here.
      doEdges :: Type -> StateT (TypeGraphEdges etype) m ()
      -- Do we treat this as a distinct type?
      doEdges typ@(ForallT _ _ typ') = addEdge (markExpanded typ) (markExpanded typ') >> doNode (markExpanded typ')
      doEdges typ@(AppT container element) =
          addEdge (markExpanded typ) (markExpanded container) >>
          addEdge (markExpanded typ) (markExpanded element) >>
          doNode (markExpanded container) >>
          doNode (markExpanded element)
      -- Can this happen if typ is fully expanded?
      doEdges typ@(ConT name) = do
        info <- qReify name
        case info of
          TyConI dec -> doDec dec
          _ -> return ()
          where
            doDec :: Dec -> StateT (TypeGraphEdges etype) m ()
            doDec dec@(NewtypeD _ tname _ con _) = doCon tname dec con
            doDec dec@(DataD _ tname _ cons _) = mapM_ (doCon tname dec) cons
            doDec (TySynD tname _tvars typ') = expandType typ' >>= \typ'' -> synonym typ'' tname >> doNode typ''
            doDec _ = return ()

            doCon :: Name -> Dec -> Con -> StateT (TypeGraphEdges etype) m ()
            doCon tname dec (ForallC _ _ con) = doCon tname dec con
            doCon tname dec (NormalC cname fields) = mapM_ (doField tname dec cname) (zip (map Left ([1..] :: [Int])) (map (markExpanded . snd) fields))
            doCon tname dec (RecC cname fields) = mapM_ (doField tname dec cname) (map (\ (fname, _, typ') -> (Right fname, markExpanded typ')) fields)
            doCon tname dec (InfixC (_, lhs) cname (_, rhs)) = mapM_ (doField tname dec cname) [(Left 1, markExpanded lhs), (Left 2, markExpanded rhs)]

            doField _tname _dec _cname (_fld, ftype) = addEdge (markExpanded typ) ftype >> doNode ftype

      doEdges _typ = return ({-trace ("Unrecognized type: " ++ pprint' typ)-} ())

      synonym :: etype -> Name -> StateT (TypeGraphEdges etype) m ()
      synonym typ name = return ()

-- | Build a graph from the result of typeGraphEdges, each edge goes
-- from a type to one of the types it contains.  Thus, each edge
-- represents a primitive lens, and each path in the graph is a
-- composition of lenses.
typeGraph :: (DsMonad m, Expanded Type etype, Ord etype, node ~ etype, key ~ etype) =>
                (etype -> m (VertexStatus etype)) -> [etype] -> m (Graph, Vertex -> (node, key, [key]), key -> Maybe Vertex)
typeGraph augment types = do
  typeGraphEdges augment types >>= return . graphFromEdges . triples
    where
      triples mp = map (\ (k, ks) -> (k, k, Set.toList ks)) $ Map.toList mp
