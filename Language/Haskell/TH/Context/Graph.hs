-- | Abstract operations on Maps containing graph edges.

{-# LANGUAGE ScopedTypeVariables #-}

module Language.Haskell.TH.Context.Graph
    ( deleteVertices
    , deleteVerticesM
    , partitionM
    ) where

import Data.List as List
import Data.Map as Map
import Data.Set as Set

-- | Remove victim vertices according to a predicate (False means
-- remove.)  Extend paths so they bypass victims.
deleteVertices :: forall a. Ord a => (a -> Bool) -> Map a (Set a) -> Map a (Set a)
deleteVertices predicate edges = Map.map (extendEdges victims') survivors
    where
      -- Split the edge map into survivor keys and victim keys
      -- Remove the victim keys from the victim destinations
      (survivors, victims) = Map.partitionWithKey (\ k _ -> predicate k) edges
      -- Where ever a victim appears a survivor's destination set,
      -- extend that edge with the victim's destination set
      victims' = Map.map (Set.filter predicate) victims

      extendEdges :: Map a (Set a) -> Set a -> Set a
      extendEdges extensions s = flatten (Set.map (\ v -> Map.findWithDefault (Set.singleton v) v extensions) s)

deleteVerticesM :: forall m a. (Monad m, Ord a) => (a -> m Bool) -> Map a (Set a) -> m (Map a (Set a))
deleteVerticesM predicate edges = do
  (survivors, _victims) <- partitionM predicate (Map.keys edges)
  return $ deleteVertices (`Set.member` (Set.fromList survivors)) edges

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
