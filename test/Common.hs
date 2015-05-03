{-# LANGUAGE FlexibleContexts, FlexibleInstances, TemplateHaskell #-}
module Common where

import Data.List as List (intercalate, map)
import Data.Map as Map (Map, fromList, toList)
import Data.Monoid ((<>))
import Data.Set as Set (Set, difference, empty, fromList, null, toList)
import Data.Generics (Data, everywhere, mkT)
import Language.Haskell.TH
import Language.Haskell.TH.Context.Expand (E, markExpanded, runExpanded)
import Language.Haskell.TH.Context.Helpers (pprint')
import Language.Haskell.TH.Context.TypeGraph (TypeGraphVertex(..), TypeGraphEdges)
import Language.Haskell.TH.Syntax (Lift(lift))

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

pprintVertex :: TypeGraphVertex -> String
pprintVertex (TypeGraphVertex {_field = fld, _syns = ns, _etype = typ}) =
    maybe "" printField fld ++
    pprint' (unReify typ) ++
    if Set.null ns then "" else (" (aka " ++ intercalate ", " (map (show . unReifyName) (Set.toList ns)) ++ ")")

printField :: (Name, Name, Either Int Name) -> String
printField (tname, cname, field) =
    show (unReifyName tname) ++ "." ++ either (\ n -> show (unReifyName cname) ++ "[" ++ show n ++ "]") (\ f -> show (unReifyName f)) field ++ "::"

pprintPred :: E Pred -> String
pprintPred = pprint' . unReify . runExpanded

edgesToStrings :: TypeGraphEdges -> [(String, [String])]
edgesToStrings mp = List.map (\ (t, ts) -> (pprintVertex t, map pprintVertex (Set.toList ts))) (Map.toList mp)

instance Lift TypeGraphVertex where
    lift (TypeGraphVertex {_field = f, _syns = ns, _etype = t}) =
        [|TypeGraphVertex {_field = $(lift f), _syns = $(lift ns), _etype = $(lift t)}|]

instance Lift a => Lift (Set a) where
    lift s = [|Set.fromList $(lift (Set.toList s))|]

instance (Lift a, Lift b) => Lift (Map a b) where
    lift mp = [|Map.fromList $(lift (Map.toList mp))|]

instance Lift (E Type) where
    lift etype = [|markExpanded $(lift (runExpanded etype))|]
