{-# LANGUAGE FlexibleContexts #-}
module Common where

import Data.List as List (map)
import Data.Map as Map (toList)
import Data.Set as Set (Set, difference, empty, toList)
import Data.Generics (Data, everywhere, mkT)
import Language.Haskell.TH
import Language.Haskell.TH.Context.Expand (E, runExpanded)
import Language.Haskell.TH.Context.Helpers (pprint')
import Language.Haskell.TH.Context.TypeGraph (TypeGraphEdges)

data SetDifferences a = SetDifferences {unexpected :: Set a, missing :: Set a} deriving (Eq, Ord, Show)

setDifferences :: Ord a => Set a -> Set a -> SetDifferences a
setDifferences actual expected = SetDifferences {unexpected = Set.difference actual expected, missing = Set.difference expected actual}
noDifferences = SetDifferences {unexpected = Set.empty, missing = Set.empty}

unReify :: Data a => a -> a
unReify = everywhere (mkT unReifyName)

unReifyName :: Name -> Name
unReifyName = mkName . nameBase

-- Some very nasty bug is triggered here in ghc-7.8 if we try to implement
-- a generic function that unReifies the symbols.  Ghc-7.10 works fine

-- pprint'' :: (Data a, Ppr a) => a -> String
-- pprint'' = pprint' . unReify

pprintDec :: Dec -> String
pprintDec = pprint' . unReify

pprintType :: E Type -> String
pprintType = pprint' . unReify . runExpanded

pprintPred :: E Pred -> String
pprintPred = pprint' . unReify . runExpanded

edgesToStrings :: TypeGraphEdges (E Type) -> [(String, [String])]
edgesToStrings mp = List.map (\ (t, ts) -> (pprintType t, map pprintType (Set.toList ts))) (Map.toList mp)
