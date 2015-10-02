{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, TemplateHaskell #-}
module Common where

import Control.Lens (makeLenses, use, (.=))
import Control.Monad.State (evalStateT, StateT)
import Control.Monad.States (MonadStates(getPoly, putPoly))
import Data.List as List (map)
import Data.Map as Map (toList)
import Data.Set as Set (Set, difference, empty, toList)
import Data.Generics (Data, everywhere, mkT)
import Language.Haskell.TH
import Language.Haskell.TH.Context (DecStatus(Declared, Undeclared), InstMap)
import Language.Haskell.TH.TypeGraph.Edges (GraphEdges)
import Language.Haskell.TH.TypeGraph.Expand (ExpandMap)
import Language.Haskell.TH.TypeGraph.Prelude (pprint')
import Language.Haskell.TH.TypeGraph.Vertex (TypeGraphVertex(..), TGV)

data SetDifferences a = SetDifferences {unexpected :: Set a, missing :: Set a} deriving (Eq, Ord, Show)

setDifferences :: Ord a => Set a -> Set a -> SetDifferences a
setDifferences actual expected = SetDifferences {unexpected = Set.difference actual expected, missing = Set.difference expected actual}
noDifferences :: SetDifferences a
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

pprintDec' :: DecStatus Dec -> String
pprintDec' (Undeclared x) = "Undeclared (" ++ pprint' (unReify x) ++ ")"
pprintDec' (Declared x) = "Declared (" ++ pprint' (unReify x) ++ ")"

pprintType :: Type -> String
pprintType = pprint' . unReify

pprintVertex :: (Ppr v, TypeGraphVertex v) => v -> String
pprintVertex = pprint'

pprintPred :: Pred -> String
pprintPred = pprint' . unReify

edgesToStrings :: Ppr key => GraphEdges key -> [(String, [String])]
edgesToStrings mp = List.map (\ (t, ts) -> (pprint' t, map pprint' (Set.toList ts))) (Map.toList mp)

data S
    = S { _instMap :: InstMap
        , _visited :: Set TGV
        , _expanded :: ExpandMap }

$(makeLenses ''S)

instance Monad m => MonadStates InstMap (StateT S m) where
    getPoly = use instMap
    putPoly s = instMap .= s

instance Monad m => MonadStates ExpandMap (StateT S m) where
    getPoly = use expanded
    putPoly s = expanded .= s

instance Monad m => MonadStates (Set TGV) (StateT S m) where
    getPoly = use visited
    putPoly s = visited .= s

evalS :: Monad m => StateT S m a -> m a
evalS action = evalStateT action (S mempty mempty mempty)
