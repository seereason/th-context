{-# LANGUAGE CPP, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, TemplateHaskell #-}
module Common where

import Control.Lens (makeLenses, use, (.=))
import Control.Monad.State (evalStateT, StateT)
import Control.Monad.States (MonadStates(getPoly, putPoly))
import Data.Default (Default(def))
import Data.List as List (map)
import Data.Map as Map (toList)
import Data.Set as Set (Set, difference, empty, toList)
import Data.Generics (Data, everywhere, mkT)
import Language.Haskell.TH
import Language.Haskell.TH.Context (ContextM, DecStatus(Declared, Undeclared), InstMap)
import Language.Haskell.TH.Desugar (DsMonad)
import Language.Haskell.TH.Expand (ExpandMap, pprint1)
--import Language.Haskell.TH.TypeGraph.Edges (GraphEdges)
--import Language.Haskell.TH.TypeGraph.Expand (ExpandMap)
--import Language.Haskell.TH.TypeGraph.Vertex (TypeGraphVertex(..), TGV)

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

-- pprint' :: (Data a, Ppr a) => a -> String
-- pprint' = pprint1 . unReify

pprintDec :: Dec -> String
pprintDec = pprint1 . unReify

pprintDec' :: DecStatus Dec -> String
pprintDec' (Undeclared x) = "Undeclared (" ++ pprint1 (unReify x) ++ ")"
pprintDec' (Declared x) = "Declared (" ++ pprint1 (unReify x) ++ ")"

pprintType :: Type -> String
pprintType = pprint1 . unReify

#if 0
pprintVertex :: (Ppr v, Data v, TypeGraphVertex v) => v -> String
pprintVertex = pprint1
#endif

pprintPred :: Pred -> String
pprintPred = pprint1 . unReify

#if 0
edgesToStrings :: (Ppr key, Data key) => GraphEdges key -> [(String, [String])]
edgesToStrings mp = List.map (\ (t, ts) -> (pprint1 t, map pprint1 (Set.toList ts))) (Map.toList mp)
#endif

data S
    = S { _instMap :: InstMap
        -- , _visited :: Set TGV
        , _expanded :: ExpandMap
        , _prefix :: String }

instance Default S where
    def = S mempty mempty ""

instance DsMonad m => ContextM (StateT S m)

$(makeLenses ''S)

instance Monad m => MonadStates InstMap (StateT S m) where
    getPoly = use instMap
    putPoly s = instMap .= s

instance Monad m => MonadStates ExpandMap (StateT S m) where
    getPoly = use expanded
    putPoly s = expanded .= s

#if 0
instance Monad m => MonadStates (Set TGV) (StateT S m) where
    getPoly = use visited
    putPoly s = visited .= s
#endif

instance Monad m => MonadStates String (StateT S m) where
    getPoly = use prefix
    putPoly s = prefix .= s

evalS :: Monad m => StateT S m a -> m a
evalS action = evalStateT action def
