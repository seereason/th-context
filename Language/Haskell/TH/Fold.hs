{-# LANGUAGE CPP, RankNTypes, ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- | Some hopefully straightforward utility types, functions, and instances for template haskell.
module Language.Haskell.TH.Fold
    ( decName
      -- * Constructor fields
    , FieldType
    , fName
    , fPos
    , fType'
    , fType
    , prettyField
      -- * Folds
    , foldType
    , foldTypeP
    , foldName
    , foldDec
    , foldDecP
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
import Control.Monad.Identity (Identity(Identity), runIdentity)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH
import Language.Haskell.TH.Desugar ({- instances -})
import Language.Haskell.TH.Syntax hiding (lift)

decName :: Dec -> Name
decName (NewtypeD _ name _ _ _) = name
decName (DataD _ name _ _ _) = name
decName (TySynD name _ _) = name
decName x = error $ "decName - unimplemented: " ++ show x

type FieldType = (Int, Either StrictType VarStrictType)

fName :: FieldType -> Maybe Name
fName (_, (Left _)) = Nothing
fName (_, (Right (name, _, _))) = Just name

fPos :: FieldType -> Int
fPos (n, _) = n

prettyField :: FieldType -> String
prettyField fld = maybe (show (fPos fld)) nameBase (fName fld)

-- | fType' with leading foralls stripped
fType :: FieldType -> Type
fType (n, Left (strict, ForallT _ _ typ)) = fType (n, Left (strict, typ))
fType (n, Right (name, strict, ForallT _ _ typ)) = fType (n, Right (name, strict, typ))
fType x = fType' x

fType' :: FieldType -> Type
-- fType' (_, (Left (_, typ))) = typ
-- fType' (_, (Right (_, _, typ))) = typ
fType' = either (\ (_, typ) -> typ) (\ (_, _, typ) -> typ) . snd

-- | Dispatch on the constructors of type Type.  This ignores the
-- "ForallT" constructor, it just uses the embeded Type field.
foldType :: Monad m => (Name -> m r) -> (Type -> Type -> m r) -> m r -> Type -> m r
foldType nfn afn ofn (ForallT _ _ typ) = foldType nfn afn ofn typ
foldType nfn _ _ (ConT name) = nfn name
foldType _ afn _ (AppT t1 t2) = afn t1 t2
foldType _ _ ofn _ = ofn

typeArity :: Quasi m => Type -> m Int
typeArity typ =
    foldType
      (foldName
         decArity
         (\_ _ _ -> return 0)
         infoArity)
      (\t _  -> typeArity t >>= \ n -> return $ n - 1)
      (return $ case typ of
                  ListT -> 1
                  TupleT n -> n
                  VarT _ -> 1
                  _ -> error $ "typeArity - unexpected type: " ++ show typ)
      typ
    where
      decArity (DataD _ _ vs _ _) = return $ length vs
      decArity (NewtypeD _ _ vs _ _) = return $ length vs
      decArity (TySynD _ vs t) = typeArity t >>= \ n -> return $ n + length vs
      decArity (FamilyD _ _ vs mk) = return $ {- not sure what to do with the kind mk here -} length vs
      decArity dec = error $ "decArity - unexpected: " ++ show dec
      infoArity (FamilyI dec _) = decArity dec

-- | Pure version of foldType.
foldTypeP :: (Name -> r) -> (Type -> Type -> r) -> r -> Type -> r
foldTypeP nfn afn ofn typ = runIdentity $ foldType (\ n -> Identity $ nfn n) (\ t1 t2 -> Identity $ afn t1 t2) (Identity ofn) typ

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

-- | Deconstruct a constructor
foldCon :: (Name -> [FieldType] -> r) -> Con -> r
foldCon fldFn (NormalC name ts) = fldFn name $ zip [1..] (map Left ts)
foldCon fldFn (RecC name ts) = fldFn name (zip [1..] (map Right ts))
foldCon fldFn (InfixC t1 name t2) = fldFn name [(1, Left t1), (2, Left t2)]
foldCon fldFn (ForallC _ _ con) = foldCon fldFn con

-- indent :: String -> String -> String
-- indent i s = intercalate "\n" (map (i ++) (lines s))

-- | Given the list of constructors from a Dec, dispatch on the
-- different levels of complexity of the type they represent - a
-- wrapper is a single arity one constructor, an enum is
-- several arity zero constructors, and so on.
foldShape :: Monad m =>
             (Dec -> [(Con, [FieldType])] -> m r) -- dataFn - several constructors not all of which are arity zero
          -> (Dec -> Con -> [FieldType] -> m r)   -- recordFn - one constructor which has arity greater than one
          -> (Dec -> [Con] -> m r)                -- enumFn - all constructors are of arity zero
          -> (Dec -> Con -> FieldType -> m r)     -- wrapperFn - one constructor of arity one
          -> Dec -> [Con] -> m r
foldShape dataFn recordFn enumFn wrapperFn dec cons =
    case zip cons (map constructorFields cons) :: [(Con, [FieldType])] of
      [(con, [fld])] ->
          wrapperFn dec con fld
      [(con, flds)] ->
          recordFn dec con flds
      pairs | all (== 0) (map (length . snd) pairs) ->
          enumFn dec (map fst pairs)
      pairs ->
          dataFn dec pairs

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
    hasPrimitiveType = foldType hasPrimitiveType afn ofn
        where
          afn t1 t2 = (||) <$> hasPrimitiveType t1 <*> hasPrimitiveType t2
          ofn = return False

instance HasPrimitiveType Dec where
    hasPrimitiveType = foldDec hasPrimitiveType (\ cons -> or <$> mapM hasPrimitiveType cons)

instance HasPrimitiveType Con where
    hasPrimitiveType = foldCon (\ _name flds -> or <$> mapM (hasPrimitiveType . fType) flds)
