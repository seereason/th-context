-- | Abstract operations on Maps containing graph edges.

{-# LANGUAGE ScopedTypeVariables #-}

module Language.Haskell.TH.Context.Graph
    ( GraphEdges
    , filterVertices
    , extendEdges
    , removeEdges
    , filterVerticesM
    , partitionM
    ) where

import Data.List as List
import Data.Map as Map
import Data.Set as Set

type GraphEdges v = Map v (Set v)

-- | Remove victim vertices according to a predicate (False means
-- remove.)  Extend paths so they bypass victims.
filterVertices :: forall a. Ord a => (GraphEdges a -> Set a -> Set a) -> (a -> Bool) -> GraphEdges a -> GraphEdges a
filterVertices updateEdges predicate edges = Map.map (updateEdges victims') survivors
    where
      -- Split the edge map into survivor keys and victim keys
      -- Remove the victim keys from the victim destinations
      (survivors, victims) = Map.partitionWithKey (\ k _ -> predicate k) edges
      -- Where ever a victim appears a survivor's destination set,
      -- extend that edge with the victim's destination set
      victims' = Map.map (Set.filter predicate) victims

-- | Use this function as first argument to filterVertices if, for
-- each victim, we want to connect the start points of the in edges to
-- the end points of the out edges.
extendEdges :: (Eq a, Ord a) => GraphEdges a -> Set a -> Set a
extendEdges victimEdges s = flatten (Set.map (\ v -> Map.findWithDefault (Set.singleton v) v victimEdges) s)

-- | Use this function as first argument to filterVertices if we want
-- to delete all the edges that were coming into or out of a victim
-- node.
removeEdges :: GraphEdges a -> Set a -> Set a
removeEdges _victimEdges _s = Set.empty

filterVerticesM :: forall m a. (Monad m, Ord a) => (GraphEdges a -> Set a -> Set a) -> (a -> m Bool) -> GraphEdges a -> m (GraphEdges a)
filterVerticesM updateEdges predicate edges = do
  (survivors, _victims) <- partitionM predicate (Map.keys edges)
  return $ filterVertices updateEdges (`Set.member` (Set.fromList survivors)) edges

partitionM :: forall m a. Monad m => (a -> m Bool) -> [a] -> m ([a], [a])
partitionM p l = do
  (flags :: [Bool]) <- mapM p l
  let pairs :: [(a, Bool)]
      pairs = zip l flags
      as :: [(a, Bool)]
      bs :: [(a, Bool)]
      (as, bs) = List.partition snd pairs
  return $ (List.map fst as, List.map fst bs)

flatten :: Ord a => Set (Set a) -> Set a
flatten = Set.fold Set.union Set.empty
