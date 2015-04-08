{-# LANGUAGE CPP #-}
module Language.Haskell.TH.Expand
    ( Expanded(Expanded, runExpanded)
    , expandTypes
    , expandType
    , unsafeExpanded
    ) where

#if __GLASGOW_HASKELL__ < 709
import Control.Applicative
#endif
import Data.Generics (Data, everywhereM, mkM)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH (Ppr(ppr), Type)
import Language.Haskell.TH.Desugar as DS (DsMonad, dsType, expand, typeToTH)
import Language.Haskell.TH.Instances ()

-- | Mark a value that was returned by ExpandType.  The constructor is
-- not exported, so we know when we see it that it was produced in
-- this module.
newtype Expanded a = Expanded {runExpanded :: a} deriving (Eq, Ord, Show)

instance Ppr a => Ppr (Expanded a) where
    ppr = ppr . runExpanded

-- | The ubiquitous cheat.  Merging TypeGraph.hs into this module eliminates this.
unsafeExpanded :: a -> Expanded a
unsafeExpanded = Expanded

-- | Expand Type everywhere in x and wrap it in the Expanded constructor.  Note
-- that the everywhereM is unnecessary when @a ~ Type@ because expandType does
-- the everywhere itself.  But it is necessary for other argument types.
expandTypes :: (DsMonad m, Data a) => a -> m (Expanded a)
expandTypes x = Expanded <$> everywhereM (mkM expandType) x

expandType :: DsMonad m => Type -> m Type
expandType t = DS.typeToTH <$> (DS.dsType t >>= DS.expand)
