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
    -- * Constructor deconstructors
    , constructorName
    -- * Queries
    , typeArity
    , unlifted
    -- * Pretty print without extra whitespace
    , pprint'
    ) where

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
typeArity (ConT name) = qReify name >>= infoArity
    where
      infoArity (TyConI dec) = decArity dec
      infoArity (PrimTyConI _ _ _) = return 0
      infoArity (FamilyI dec _) = decArity dec
      infoArity info = error $ "typeArity - unexpected: " ++ pprint' info
      decArity (DataD _ _ vs _ _) = return $ length vs
      decArity (NewtypeD _ _ vs _ _) = return $ length vs
      decArity (TySynD _ vs t) = typeArity t >>= \ n -> return $ n + length vs
      decArity (FamilyD _ _ vs _mk) = return $ {- not sure what to do with the kind mk here -} length vs
      decArity dec = error $ "decArity - unexpected: " ++ show dec
typeArity typ = error $ "typeArity - unexpected type: " ++ show typ

pprint' :: Ppr a => a -> [Char]
pprint' typ = unwords $ words $ pprint typ

constructorName :: Con -> Name
constructorName (ForallC _ _ con) = constructorName con
constructorName (NormalC name _) = name
constructorName (RecC name _) = name
constructorName (InfixC _ name _) = name

-- | Does the type or the declaration to which it refers contain a
-- primitive (aka unlifted) type?
class IsUnlifted t where
    unlifted :: Quasi m => t -> m Bool

instance IsUnlifted Type where
    unlifted (ForallT _ _ typ) = unlifted typ
    unlifted (ConT name) = qReify name >>= unlifted
    unlifted _ = return False

instance IsUnlifted Info where
    unlifted (PrimTyConI _ _ _) = return True
    unlifted _ = return False
