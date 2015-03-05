{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- | An ExpandType instance using functions from Desugar.  This allows
-- the Context module to be used with m ~ DsMonad.
module Language.Haskell.TH.DesugarExpandType () where

import Control.Applicative ((<$>))
import Control.Monad.State (StateT)
import Control.Monad.Trans (lift)
import Language.Haskell.TH.Context (ExpandType(expandType))
import Language.Haskell.TH.Desugar as DS (DsMonad(localDeclarations), dsType)
import qualified Language.Haskell.TH.Desugar.Expand as DS (expandType)
import Language.Haskell.TH.Desugar.Sweeten as DS (typeToTH)

instance DsMonad m => ExpandType m where
    expandType t = DS.typeToTH <$> (DS.dsType t >>= DS.expandType)

-- This lets Context wrap some state around m and still use DsMonad.
instance DsMonad m => DsMonad (StateT s m) where
    localDeclarations = lift localDeclarations
