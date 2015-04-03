module Common where

import Data.Set as Set
import Language.Haskell.TH
import Data.List as List (map)

data SetDifferences a = SetDifferences {extra :: Set a, missing :: Set a} deriving (Eq, Ord, Show)

setDifferences :: Ord a => Set a -> Set a -> SetDifferences a
setDifferences actual expected = SetDifferences {extra = Set.difference actual expected, missing = Set.difference expected actual}
noDifferences = SetDifferences {extra = Set.empty, missing = Set.empty}

toStrings :: Ppr a => (a, Set a) -> (String, [String])
toStrings (typ, types) = (pp typ, List.map pp (toList types))
    where pp = unwords . words . pprint
