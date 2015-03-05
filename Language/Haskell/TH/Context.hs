-- | Compute whether any existing instance satisfies some
-- context in a nearly correct fashion.
-- @
--    instance A m => B m where ...
-- @
-- I say "nearly correct" because there are cases which are
-- not handled exactly the way GHC behaves, which may lead to
-- false (positives?  negatives?)
{-# LANGUAGE CPP, DeriveDataTypeable, FlexibleContexts, MultiParamTypeClasses, ScopedTypeVariables, StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}
module Language.Haskell.TH.Context
    ( ExpandType(expandType)
    , expandTypes
    , reifyInstancesWithContext -- was instances
    , testInstance
    , testContext
    , testContextWithState -- was testPred
    , missingInstances
    , simpleMissingInstanceTest
    ) where

import Control.Applicative ((<$>), (<*>))
import Control.Monad (filterM)
import Control.Monad.State (MonadState, StateT(StateT), get, modify, runStateT)
import Control.Monad.Trans (lift)
import Data.Generics (Data, everywhere, mkT, everywhereM, mkM)
import Data.List ({-dropWhileEnd,-} intercalate)
import Data.Map as Map (Map, lookup, insert)
import Data.Maybe (catMaybes)
import Language.Haskell.TH
import Language.Haskell.TH.Syntax hiding (lift)
import Language.Haskell.TH.Instances ({- Ord instances from th-orphans -})

instance Quasi m => Quasi (StateT s m) where
  qNewName          = lift . qNewName
  qReport a b       = lift $ qReport a b
  qRecover m1 m2    = StateT $ \ s -> runStateT m1 s `qRecover` runStateT m2 s
  qLookupName a b   = lift $ qLookupName a b
  qReify            = lift . qReify
  qReifyInstances a b = lift $ qReifyInstances a b
  qLocation         = lift qLocation
  qRunIO            = lift . qRunIO
  qAddDependentFile = lift . qAddDependentFile
#if MIN_VERSION_template_haskell(2,9,0)
  qReifyRoles       = lift . qReifyRoles
  qReifyAnnotations = lift . qReifyAnnotations
  qReifyModule      = lift . qReifyModule
  qAddTopDecls      = lift . qAddTopDecls
  qAddModFinalizer  = lift . qAddModFinalizer
  qGetQ             = lift qGetQ
  qPutQ             = lift . qPutQ
#endif

-- | Extend the Quasi class to require a function for expanding a TH Type.  The
-- th-desugar package has a function that can be used to implement this, but I
-- created the class to avoid becoming too tightly coupled with that package:
-- @@
--  import Language.Haskell.TH.Desugar as DS
--  instance DsMonad m => ExpandType m where
--    expandType t = DS.typeToTH <$> (DS.dsType t >>= DS.expandType)
-- @@
-- Extend the Quasi type to require a function for expanding a TH Type.
class ExpandType m where
    expandType :: Type -> m Type

expandTypes :: (Quasi m, ExpandType m, Data a) => a -> m a
expandTypes = everywhereM (mkM expandType)

-- | Like 'qReifyInstances', looks up all the instances that match the
-- given class name and argument types.  However, unlike
-- 'qReifyInstances', only the ones that satisfy all the instance
-- context predicates are returned.
reifyInstancesWithContext :: (Quasi m, ExpandType m, MonadState (Map Pred [InstanceDec]) m) =>
                             Name -> [Type] -> m [InstanceDec]
reifyInstancesWithContext className typeParameters = do
#if MIN_VERSION_template_haskell(2,10,0)
       p <- expandTypes (foldl AppT (ConT className) typeParameters)
#else
       p <- expandTypes (ClassP className typeParameters)
#endif
       mp <- get
       case Map.lookup p mp of
         Just x -> return x
         Nothing -> do
           -- Add an entry with a bogus value to limit recursion on
           -- the predicate we are currently testing
           modify (Map.insert p [])
           -- Get all the instances of className that unify with the type parameters.
           insts <- qReifyInstances className typeParameters
           -- Filter out the ones that conflict with the instance context
           r <- filterM (testInstance className typeParameters) insts
           -- Now insert the correct value into the map and return it.
           modify (Map.insert p r)
           return r

-- | Test one of the instances returned by qReifyInstances against the
-- context we have computed so far.  We have already added a ClassP predicate
-- for the class and argument types, we now need to unify those with the
-- type returned by the instance and generate some EqualP predicates.
testInstance :: (Quasi m, ExpandType m, MonadState (Map Pred [InstanceDec]) m) => Name -> [Type] -> InstanceDec -> m Bool
testInstance className typeParameters (InstanceD instanceContext instanceType _) = do
  -- The new context consists of predicates derived by unifying the
  -- type parameters with the instance type, plus the prediates in the
  -- instance context field.
  testContext (instancePredicates (reverse typeParameters) instanceType ++ instanceContext)
    where
      instancePredicates :: [Type] -> Type -> [Pred]
#if MIN_VERSION_template_haskell(2,10,0)
      instancePredicates (x : xs) (AppT l r) = AppT (AppT EqualityT x) r : instancePredicates xs l
#else
      instancePredicates (x : xs) (AppT l r) = EqualP x r : instancePredicates xs l
#endif
      instancePredicates [] (ConT className') | className == className' = []
      instancePredicates _ _ =
          error $ (unlines ["testInstance: Failure unifying instance with arguments.  This should never",
                            "happen because qReifyInstance returned this instance for these exact arguments:",
                            " typeParameters=[" ++ intercalate ", " (map show typeParameters) ++ "]",
                            " instanceType=" ++ show instanceType])
testInstance _ _ x = error $ "qReifyInstances returned something that doesn't appear to be an instance declaration: " ++ show x

-- | Now we have predicates representing the unification of the type
-- parameters with the instance type.  Are they consistent?  Find out
-- using type synonym expansion, variable substitution, elimination of
-- vacuous predicates, and unification.
testContext :: (Quasi m, ExpandType m, MonadState (Map Pred [InstanceDec]) m) => [Pred] -> m Bool
testContext context =
    and <$> (mapM consistent =<< simplifyContext context)

-- | Perform type expansion on the predicates, then simplify using
-- variable substitution and eliminate vacuous equivalences.
simplifyContext :: (Quasi m, ExpandType m, MonadState (Map Pred [InstanceDec]) m) => [Pred] -> m [Pred]
simplifyContext context =
    do (expanded :: [Pred]) <- expandTypes context
       let (context' :: [Pred]) = concat $ map unify expanded
       let context'' = foldl simplifyPredicate context' context'
       if (context'' == context) then return context'' else simplifyContext context''

-- | Try to simplify the context by eliminating of one of the predicates.
-- If we succeed start again with the new context.
simplifyPredicate :: [Pred] -> Pred -> [Pred]
#if MIN_VERSION_template_haskell(2,10,0)
simplifyPredicate context (AppT (AppT EqualityT v@(VarT _)) b) = everywhere (mkT (\ x -> if x == v then b else x)) context
simplifyPredicate context (AppT (AppT EqualityT a) v@(VarT _)) = everywhere (mkT (\ x -> if x == v then a else x)) context
simplifyPredicate context p@(AppT (AppT EqualityT a) b) | a == b = filter (/= p) context
#else
simplifyPredicate context (EqualP v@(VarT _) b) = everywhere (mkT (\ x -> if x == v then b else x)) context
simplifyPredicate context (EqualP a v@(VarT _)) = everywhere (mkT (\ x -> if x == v then a else x)) context
simplifyPredicate context p@(EqualP a b) | a == b = filter (/= p) context
#endif
simplifyPredicate context _ = context

-- | Test the context (predicates) against both the instances in the Q
-- monad and the additional instances that have accumulated in the
-- State monad.
testContextWithState :: (Quasi m, ExpandType m, MonadState (Map Pred [InstanceDec]) m) => Pred -> m Bool
testContextWithState predicate = do
  -- Is the instance already in the Q monad?
  flag <- testContext [predicate]
  case flag of
    True -> return True
    -- Have we already generated and inserted the instance into the map in the state monad?
    False -> maybe False (not . null) <$> (Map.lookup <$> expandTypes predicate <*> get)

-- | Unify the two arguments of an EqualP predicate, return a list of
-- simpler predicates associating types with a variables.
unify :: Pred -> [Pred]
#if MIN_VERSION_template_haskell(2,10,0)
unify (AppT (AppT EqualityT (AppT a b)) (AppT c d)) = unify (AppT (AppT EqualityT a) c) ++ unify (AppT (AppT EqualityT b) d)
unify (AppT (AppT EqualityT (ConT a)) (ConT b)) | a == b = []
unify (AppT (AppT EqualityT a@(VarT _)) b) = [AppT (AppT EqualityT a) b]
unify (AppT (AppT EqualityT a) b@(VarT _)) = [AppT (AppT EqualityT a) b]
#else
unify (EqualP (AppT a b) (AppT c d)) = unify (EqualP a c) ++ unify (EqualP b d)
unify (EqualP (ConT a) (ConT b)) | a == b = []
unify (EqualP a@(VarT _) b) = [EqualP a b]
unify (EqualP a b@(VarT _)) = [EqualP a b]
#endif
unify x = [x]

-- | Decide whether a predicate is consistent with the accumulated
-- context.  Use recursive calls to qReifyInstancesWithContext when
-- we encounter a class name applied to a list of type parameters.
consistent :: (Quasi m, ExpandType m, MonadState (Map Pred [InstanceDec]) m) => Pred -> m Bool
#if MIN_VERSION_template_haskell(2,10,0)
consistent (AppT (AppT EqualityT (AppT a b)) (AppT c d)) =
    -- I'm told this is incorrect in the presence of type functions
    (&&) <$> consistent (AppT (AppT EqualityT a) c) <*> consistent (AppT (AppT EqualityT b) d)
consistent (AppT (AppT EqualityT (VarT _)) _) = return True
consistent (AppT (AppT EqualityT _) (VarT _)) = return True
consistent (AppT (AppT EqualityT a) b) | a == b = return True
consistent (AppT (AppT EqualityT _) _) = return False
consistent (AppT cls arg) =
    consistent' cls [arg]
    where
      consistent' (VarT name) args = (not . null) <$> instances name args
      consistent' (AppT cls' typ) types = consistent' cls' (typ : types)
      consistent' _ _ = return False
consistent typ = error $ "Unexpected Pred: " ++ pprint typ
#else
consistent (EqualP (AppT a b) (AppT c d)) =
    -- I'm told this is incorrect in the presence of type functions
    (&&) <$> consistent (EqualP a c) <*> consistent (EqualP b d)
consistent (EqualP (VarT _) _) = return True
consistent (EqualP _ (VarT _)) = return True
consistent (EqualP a b) | a == b = return True
consistent (EqualP _ _) = return False
consistent (ClassP className typeParameters) =
    (not . null) <$> reifyInstancesWithContext className typeParameters -- Do we need additional context here?
#endif

-- | Apply a filter such as 'simpleMissingInstanceTest' to a list of
-- instances, resulting in a non-overlapping list of instances.
missingInstances :: Quasi m => (Dec -> m Bool) -> m [Dec] -> m [Dec]
missingInstances test decs = decs >>= mapM (\ dec -> test dec >>= \ flag -> return $ if flag then Just dec else Nothing) >>= return . catMaybes

-- | Return True if no instance matches the types (ignoring the instance context.)
-- Passing qReifyInstance as the reifyInstanceFunction argument gives a naive test,
-- passing qReifyInstanceWithContext will also accept (return True for) instances
-- which...
simpleMissingInstanceTest :: Quasi m => Dec -> m Bool
simpleMissingInstanceTest dec@(InstanceD _ typ _) =
    case unfoldInstance typ of
      Just (name, types) -> do
        -- trace ("name: " ++ show name ++ ", types=" ++ show types) (return ())
        insts <- qReifyInstances name types
        -- trace ("insts: " ++ show (map pprint insts)) (return ())
        return $ null insts
      Nothing -> error $ "simpleMissingInstanceTest - invalid instance: " ++ pprint dec
simpleMissingInstanceTest dec = error $ "simpleMissingInstanceTest - invalid instance: " ++ pprint dec

unfoldInstance :: Type -> Maybe (Name, [Type])
unfoldInstance (ConT name) = Just (name, [])
unfoldInstance (AppT t1 t2) = maybe Nothing (\ (name, types) -> Just (name, types ++ [t2])) (unfoldInstance t1)
unfoldInstance _ = Nothing
