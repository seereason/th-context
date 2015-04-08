{-# LANGUAGE CPP, DeriveDataTypeable, RankNTypes, ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- | Some hopefully straightforward utility types, functions, and instances for template haskell.
module Language.Haskell.TH.Fold
    ( -- * Declaration shape
      FieldType(FieldType, fPos, fNameAndType)
    , fName
    , fType
    , prettyField
    , constructorFields
    , foldShape
      -- * Name reification
    , foldName
    -- * Constructor deconstructors
    , constructorName
    -- * Queries
    , typeArity
    , HasPrimitiveType(hasPrimitiveType)
    -- * Pretty print without extra whitespace
    , pprint'
    ) where

import Control.Applicative ((<$>), (<*>))
import Data.Data (Data)
import Data.Typeable (Typeable)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH
import Language.Haskell.TH.Desugar ({- instances -})
import Language.Haskell.TH.Syntax hiding (lift)

data FieldType
    = FieldType
      { fPos :: Int
      , fNameAndType :: Either StrictType VarStrictType }
    deriving (Eq, Ord, Show, Data, Typeable)

fName :: FieldType -> Maybe Name
fName = either (\ (_, _) -> Nothing) (\ (x, _, _) -> Just x) . fNameAndType

prettyField :: FieldType -> String
prettyField fld = maybe (show (fPos fld)) nameBase (fName fld)

-- | fType' with leading foralls stripped
fType :: FieldType -> Type
fType = either (\ (_, x) -> x) (\ (_, _, x) -> x) . fNameAndType

-- | Given the list of constructors from a Dec, dispatch on the
-- different levels of complexity of the type they represent - a
-- wrapper is a single arity one constructor, an enum is
-- several arity zero constructors, and so on.
foldShape :: Monad m =>
             ([(Con, [FieldType])] -> m r) -- dataFn - several constructors not all of which are arity zero
          -> (Con -> [FieldType] -> m r)   -- recordFn - one constructor which has arity greater than one
          -> ([Con] -> m r)                -- enumFn - all constructors are of arity zero
          -> (Con -> FieldType -> m r)     -- wrapperFn - one constructor of arity one
          -> [Con] -> m r
foldShape dataFn recordFn enumFn wrapperFn cons =
    case zip cons (map constructorFields cons) :: [(Con, [FieldType])] of
      [(con, [fld])] ->
          wrapperFn con fld
      [(con, flds)] ->
          recordFn con flds
      pairs | all (== 0) (map (length . snd) pairs) ->
          enumFn (map fst pairs)
      pairs ->
          dataFn pairs

constructorFields :: Con -> [FieldType]
constructorFields (ForallC _ _ con) = constructorFields con
constructorFields (NormalC _ ts) = map (uncurry FieldType) (zip [1..] (map Left ts))
constructorFields (RecC _ ts) = map (uncurry FieldType) (zip [1..] (map Right ts))
constructorFields (InfixC t1 _ t2) = map (uncurry FieldType) [(1, Left t1), (2, Left t2)]

typeArity :: Quasi m => Type -> m Int
typeArity (ForallT _ _ typ) = typeArity typ
typeArity ListT = return 1
typeArity (VarT _) = return 1
typeArity (TupleT n) = return n
typeArity (AppT t _) = typeArity t >>= \ n -> return $ n - 1
typeArity (ConT name) = foldName decArity (\_ _ _ -> return 0) infoArity name
    where
      decArity (DataD _ _ vs _ _) = return $ length vs
      decArity (NewtypeD _ _ vs _ _) = return $ length vs
      decArity (TySynD _ vs t) = typeArity t >>= \ n -> return $ n + length vs
      decArity (FamilyD _ _ vs _mk) = return $ {- not sure what to do with the kind mk here -} length vs
      decArity dec = error $ "decArity - unexpected: " ++ show dec
      infoArity (FamilyI dec _) = decArity dec
      infoArity info = error $ "typeArity - unexpected: " ++ pprint' info
typeArity typ = error $ "typeArity - unexpected type: " ++ show typ

-- | Combine a decFn and a primFn to make a nameFn in the Quasi monad.
-- This is used to build the first argument to the foldType function
-- when we need to know whether the name refers to a declared or a
-- primitive type.
foldName :: Quasi m =>
            (Dec -> m r)
         -> (Name -> Int -> Bool -> m r)
         -> (Info -> m r)
         -> Name -> m r
foldName decFn primFn otherFn name = do
  info <- qReify name
  case info of
    (TyConI dec) ->
        decFn dec
    (PrimTyConI a b c) -> primFn a b c
    _ -> otherFn info

-- indent :: String -> String -> String
-- indent i s = intercalate "\n" (map (i ++) (lines s))

pprint' :: Ppr a => a -> [Char]
pprint' typ = unwords $ words $ pprint typ

constructorName :: Con -> Name
constructorName (ForallC _ _ con) = constructorName con
constructorName (NormalC name _) = name
constructorName (RecC name _) = name
constructorName (InfixC _ name _) = name

-- | Returns true if any of the fields of the declaration are
-- primitive types.  Does not recurse into sub-types, but needs
-- the Quasi monad to see whether the named types are primitive.
{-
anyPrimitiveFields :: forall m. Quasi m => Dec -> [Con] -> m Bool
anyPrimitiveFields _dec cons =
    or <$> mapM (\ con -> foldCon (fldsFn con) con) cons
    where
      fldsFn :: Name -> [FieldType] -> m Bool
      fldsFn _name flds = or <$> mapM fldFn flds
      fldFn :: FieldType -> m Bool
      fldFn fld = foldType nfn afn ofn (fType fld)
      nfn :: Name -> m Bool
      nfn name = foldName (\ _ -> return False) (\ _ _ _ -> return True) {- primitive! -} name
      afn :: Type -> Type -> m Bool
      afn t1 t2 = (||) <$> foldType nfn afn ofn t1 <*> foldType nfn afn ofn t2
      ofn :: m Bool
      ofn = return False

-- | Is there a primitive type name inside this Type?
isPrimitiveType :: Quasi m => Type -> m Bool
isPrimitiveType = foldType nfn afn ofn
    where

-- | Is there a primitive type name inside this Type declaration?
primitiveDec :: Quasi m => Dec -> m Bool
primitiveDec = foldDec primitiveType (\ cons -> or <$> mapM primitiveCon cons)

primitiveCon :: Quasi m => Con -> Name -> [FieldType] -> m Bool
primitiveCon = foldCon ffn
    where
      ffn :: Name -> [FieldType] -> m Bool
      ffn name flds = or <$> mapM (primitiveType . fType . snd) flds
-}

-- | Is this the name of a primitive type, or does it contain any primitive type names?
class HasPrimitiveType t where
    hasPrimitiveType :: Quasi m => t -> m Bool

instance HasPrimitiveType Name where
    hasPrimitiveType = foldName (\ _ -> return False) (\ _ _ _ -> return True) (\ _ -> return False)

instance HasPrimitiveType Type where
    hasPrimitiveType (ConT name) = hasPrimitiveType name
    hasPrimitiveType (AppT t1 t2) = (||) <$> hasPrimitiveType t1 <*> hasPrimitiveType t2
    hasPrimitiveType _ = return False

instance HasPrimitiveType Dec where
    hasPrimitiveType (TySynD _ _ typ) = hasPrimitiveType typ
    hasPrimitiveType (NewtypeD _ _ _ con _) = hasPrimitiveType con
    hasPrimitiveType (DataD _ _ _ cons _) = or <$> mapM hasPrimitiveType cons
    hasPrimitiveType dec = error $ "hasPrimiveType: " ++ show dec

instance HasPrimitiveType Con where
    hasPrimitiveType (ForallC _ _ con) = hasPrimitiveType con
    hasPrimitiveType (NormalC _ ts) = or <$> mapM (hasPrimitiveType . snd) ts
    hasPrimitiveType (RecC _ ts) = or <$> mapM (\ (_, _, t) -> hasPrimitiveType t) ts
    hasPrimitiveType (InfixC t1 _ t2) = or <$> mapM (hasPrimitiveType . snd) [t1, t2]
