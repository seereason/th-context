{-# LANGUAGE CPP, DeriveDataTypeable, RankNTypes, ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- | Some hopefully straightforward utility types, functions, and instances for template haskell.
module Language.Haskell.TH.Fold
    ( decName
      -- * Constructor fields
    , FieldType(FieldType, fPos, fNameAndType)
    , fName
    , fType
    , prettyField
      -- * Folds
    , foldName
    , foldCon
    , foldShape
    -- * Constructor deconstructors
    , constructorName
    , constructorFields
    -- * Queries
    , typeArity
    , HasPrimitiveType(hasPrimitiveType)
    , pprint'
    ) where

import Control.Applicative ((<$>), (<*>))
import Data.Data (Data)
import Data.Typeable (Typeable)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH
import Language.Haskell.TH.Desugar ({- instances -})
import Language.Haskell.TH.Syntax hiding (lift)

decName :: Dec -> Name
decName (NewtypeD _ name _ _ _) = name
decName (DataD _ name _ _ _) = name
decName (TySynD name _ _) = name
decName x = error $ "decName - unimplemented: " ++ show x

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

#if 0
-- | Dispatch on the constructors of type Type.  This ignores the
-- "ForallT" constructor, it just uses the embeded Type field.
foldType :: Monad m => (Name -> m r) -> (Type -> Type -> m r) -> m r -> Type -> m r
foldType nfn afn ofn (ForallT _ _ typ) = foldType nfn afn ofn typ
foldType nfn _ _ (ConT name) = nfn name
foldType _ afn _ (AppT t1 t2) = afn t1 t2
foldType _ _ ofn _ = ofn

-- | Pure version of foldType.
foldTypeP :: (Name -> r) -> (Type -> Type -> r) -> r -> Type -> r
foldTypeP nfn afn ofn typ = runIdentity $ foldType (\ n -> Identity $ nfn n) (\ t1 t2 -> Identity $ afn t1 t2) (Identity ofn) typ
#endif

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

#if 0
-- | Dispatch on the different constructors of the Dec type.
foldDec :: Monad m =>
           (Type -> m r)
        -> ([Con] -> m r)
        -> Dec -> m r
foldDec typeFn shapeFn dec =
    case dec of
      TySynD _name _ typ -> typeFn typ
      NewtypeD _ _ _ con _ -> shapeFn [con]
      DataD _ _ _ cons _ -> shapeFn cons
      _ -> error $ "foldDec - unexpected: " ++ show dec

-- | Dispatch on whether a type is a type synonym or a "real" type, newtype or data.
foldDecP :: (Type -> r) -> ([Con] -> r) -> Dec -> r
foldDecP typeFn shapeFn dec = runIdentity $ foldDec (\ t -> Identity $ typeFn t) (\ cs -> Identity $ shapeFn cs) dec
#endif

-- | Deconstruct a constructor
foldCon :: (Name -> [FieldType] -> r) -> Con -> r
foldCon fldFn (NormalC name ts) = fldFn name $ map (uncurry FieldType) (zip [1..] (map Left ts))
foldCon fldFn (RecC name ts) = fldFn name (map (uncurry FieldType) (zip [1..] (map Right ts)))
foldCon fldFn (InfixC t1 name t2) = fldFn name (map (uncurry FieldType) [(1, Left t1), (2, Left t2)])
foldCon fldFn (ForallC _ _ con) = foldCon fldFn con

-- indent :: String -> String -> String
-- indent i s = intercalate "\n" (map (i ++) (lines s))

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

pprint' :: Ppr a => a -> [Char]
pprint' typ = unwords $ words $ pprint typ

constructorFields :: Con -> [FieldType]
constructorFields = foldCon (\ _ x -> x)

constructorName :: Con -> Name
constructorName = foldCon (\ x _ -> x)

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
    hasPrimitiveType = foldCon (\ _name flds -> or <$> mapM (hasPrimitiveType . fType) flds)
