{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- | An ExpandType instance using functions from Desugar.  This allows
-- the Context module to be used with m ~ DsMonad.
module Language.Haskell.TH.DesugarExpandType () where

import Control.Applicative ((<$>))
import Language.Haskell.TH.Context (ExpandType(expandType))
import Language.Haskell.TH.Desugar as DS (DsMonad, dsType)
import qualified Language.Haskell.TH.Desugar.Expand as DS (expandType)
import Language.Haskell.TH.Desugar.Sweeten as DS (typeToTH)

instance DsMonad m => ExpandType m where
    expandType t = DS.typeToTH <$> (DS.dsType t >>= DS.expandType)
