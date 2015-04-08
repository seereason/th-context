{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Language.Haskell.TH.Expand
    ( Expanded(expanded, runExpanded)
    , expandType
    , expandPred
    , expandClassP
    , E
    ) where

#if __GLASGOW_HASKELL__ < 709
import Control.Applicative
#endif
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH
import Language.Haskell.TH.Desugar as DS (DsMonad, dsType, expand, typeToTH)
import Language.Haskell.TH.Instances ()

-- | This class lets us use the same expand* functions to work with
-- specially marked expanded types or with the original types.
class Expanded a b | b -> a where
    expanded :: a -> b
    runExpanded :: b -> a

expandType :: (DsMonad m, Expanded Type e)  => Type -> m e
expandType typ = expanded <$> DS.typeToTH <$> (DS.dsType typ >>= DS.expand)

expandPred :: (DsMonad m, Expanded Pred e)  => Pred -> m e
#if MIN_VERSION_template_haskell(2,10,0)
expandPred pred = expanded <$> expandType pred
#else
expandPred (ClassP className typeParameters) = expanded <$> ClassP className <$> mapM expandType typeParameters
expandPred (EqualP type1 type2) = expanded <$> (EqualP <$> expandType type1 <*> expandType type2)
#endif

expandClassP :: (DsMonad m, Expanded Pred e)  => Name -> [Type] -> m e
expandClassP className typeParameters =
    expanded <$>
#if MIN_VERSION_template_haskell(2,10,0)
      expandType $ foldl AppT (ConT className) typeParameters
#else
      ClassP className <$> mapM expandType typeParameters
#endif

-- | A wrapper denoting an expanded value with provided Expanded instances.
newtype E a = E a deriving (Eq, Ord, Show)

instance Expanded Type Type where
    expanded = id
    runExpanded = id

instance Expanded Type (E Type) where
    expanded = E
    runExpanded (E x) = x

instance Expanded Pred (E Pred) where
    expanded = E
    runExpanded (E x) = x

instance Ppr a => Ppr (E a) where
    ppr (E x) = ppr x
