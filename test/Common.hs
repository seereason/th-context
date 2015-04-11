{-# LANGUAGE FlexibleContexts #-}
module Common where

import Data.Generics (Data, everywhere, mkT)
import Data.List as List (map)
import Data.Set as Set
import Language.Haskell.TH
import Language.Haskell.TH.Context.Expand (E, runExpanded)
import Language.Haskell.TH.Context.Helpers (pprint')

data SetDifferences a = SetDifferences {extra :: Set a, missing :: Set a} deriving (Eq, Ord, Show)

setDifferences :: Ord a => Set a -> Set a -> SetDifferences a
setDifferences actual expected = SetDifferences {extra = Set.difference actual expected, missing = Set.difference expected actual}
noDifferences = SetDifferences {extra = Set.empty, missing = Set.empty}

toStrings :: Ppr a => (a, Set a) -> (String, [String])
toStrings (typ, types) = (pp typ, List.map pp (toList types))
    where pp = unwords . words . pprint

toStrings' :: (E Type, Set (E Type)) -> (String, [String])
toStrings' (k, s) = (pp k, List.map pp (toList s))
    where pp :: E Type -> String
          pp = pprint' . unReify . (runExpanded :: E Type -> Type)

unReify :: Data a => a -> a
unReify = everywhere (mkT unReifyName)

unReifyName :: Name -> Name
unReifyName = mkName . nameBase
