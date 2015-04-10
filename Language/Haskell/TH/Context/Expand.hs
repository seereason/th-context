-- | The 'Expanded' class helps keep track of which 'Type' values have
-- been fully expanded to a canonical form.  This lets us use the 'Eq'
-- and 'Ord' relationships on 'Type' and 'Pred' values when reasoning
-- about instance context.
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.Haskell.TH.Context.Expand
    ( Expanded(markExpanded, runExpanded)
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
import Prelude hiding (pred)

-- | This class lets us use the same expand* functions to work with
-- specially marked expanded types or with the original types.
class Expanded un ex | ex -> un where
    markExpanded :: un -> ex -- | Unsafely mark a value as expanded
    runExpanded :: ex -> un -- | Strip mark off an expanded value

-- | Apply the th-desugar expand function to a 'Type' and mark it as expanded.
expandType :: (DsMonad m, Expanded Type e)  => Type -> m e
expandType typ = markExpanded <$> DS.typeToTH <$> (DS.dsType typ >>= DS.expand)

-- | Apply the th-desugar expand function to a 'Pred' and mark it as expanded.
-- Note that the definition of 'Pred' changed in template-haskell-2.10.0.0.
expandPred :: (DsMonad m, Expanded Pred e)  => Pred -> m e
#if MIN_VERSION_template_haskell(2,10,0)
expandPred pred = markExpanded <$> expandType pred
#else
expandPred (ClassP className typeParameters) = markExpanded <$> ClassP className <$> mapM expandType typeParameters
expandPred (EqualP type1 type2) = markExpanded <$> (EqualP <$> expandType type1 <*> expandType type2)
#endif

-- | Expand a list of 'Type' and build an expanded 'ClassP' 'Pred'.
expandClassP :: forall m e. (DsMonad m, Expanded Pred e)  => Name -> [Type] -> m e
expandClassP className typeParameters =
    markExpanded <$>
#if MIN_VERSION_template_haskell(2,10,0)
      (expandType $ foldl AppT (ConT className) typeParameters) :: m e
#else
      ClassP className <$> mapM expandType typeParameters
#endif

-- | A concrete type for which Expanded instances are declared below.
newtype E a = E a deriving (Eq, Ord, Show)

instance Expanded Type Type where
    markExpanded = id
    runExpanded = id

instance Expanded Type (E Type) where
    markExpanded = E
    runExpanded (E x) = x

#if !MIN_VERSION_template_haskell(2,10,0)
instance Expanded Pred Pred where
    markExpanded = id
    runExpanded = id

instance Expanded Pred (E Pred) where
    markExpanded = E
    runExpanded (E x) = x
#endif

instance Ppr a => Ppr (E a) where
    ppr (E x) = ppr x
