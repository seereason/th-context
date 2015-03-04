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
    ( instances
    , testInstance
    , testContext
    , expandTypes
    , testPred
    , ExpandType(expandType)
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

-- Extend the Quasi type to require a function for expanding a TH Type.
class ExpandType m where
    expandType :: Type -> m Type

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

-- | Look up all the instances that match the given class name and
-- argument types, return only the ones (if any) that satisfy all the
-- instance context predicates.
instances :: (Quasi m, ExpandType m, MonadState (Map Pred [InstanceDec]) m) => Name -> [Type] -> m [InstanceDec]
-- Ask for matching instances for this list of types, then see whether
-- any of them can be unified with the instance context.
instances cls argTypes = do
#if MIN_VERSION_template_haskell(2,10,0)
       p <- expandTypes (foldl AppT (ConT cls) argTypes)
#else
       p <- expandTypes (ClassP cls argTypes)
#endif
       mp <- get
       case Map.lookup p mp of
         Just x -> return x
         Nothing -> do
           -- Add an entry with a bogus value to limit recursion on
           -- the predicate we are currently testing
           modify (Map.insert p [])
           insts <- qReifyInstances cls argTypes
           r <- filterM (testInstance cls argTypes) insts
           -- Now insert the correct value into the map.
           modify (Map.insert p r)
           return r

-- | Test one of the instances returned by qReifyInstances against the
-- context we have computed so far.  We have already added a ClassP predicate
-- for the class and argument types, we now need to unify those with the
-- type returned by the instance and generate some EqualP predicates.
testInstance :: (Quasi m, ExpandType m, MonadState (Map Pred [InstanceDec]) m) => Name -> [Type] -> InstanceDec -> m Bool
testInstance cls argTypes (InstanceD newContext instType _) = do
  testContext (instancePredicates (reverse argTypes) instType ++ newContext)
    where
      instancePredicates :: [Type] -> Type -> [Pred]
#if MIN_VERSION_template_haskell(2,10,0)
      instancePredicates (x : xs) (AppT l r) = AppT (AppT EqualityT x) r : instancePredicates xs l
#else
      instancePredicates (x : xs) (AppT l r) = EqualP x r : instancePredicates xs l
#endif
      instancePredicates [] (ConT cls') | cls == cls' = []
      instancePredicates _ _ = error $ (unlines ["testInstance: Failure unifying instance with arguments.  This should never",
                                                 "happen because qReifyInstance returned this instance for these exact arguments:",
                                                 " argTypes=[" ++ intercalate ", " (map show argTypes) ++ "]",
                                                 " instType=" ++ show instType])
testInstance _ _ x = error $ "Unexpected InstanceDec.  If this happens there must be some new sort of instance declaration I wasn't expecting: " ++ show x

-- | Is this list of predicates satisfiable?  Find out using type
-- synonym expansion, variable substitution, elimination of vacuous
-- predicates, and unification.
--
-- Elements of the Pred type correspond to elements of the list to the
-- left of the @=>@ in a Haskell declaration.  These can either be
-- @ClassP@ values which represent superclasses, or @EqualP@ values
-- which represent uses of the @~@ operator.
testContext :: (Quasi m, ExpandType m, MonadState (Map Pred [InstanceDec]) m) => [Pred] -> m Bool
testContext context =
    and <$> (mapM consistent =<< simplifyContext context)

-- | Perform type expansion on the predicates, then simplify using
-- variable substitution and eliminate vacuous equivalences.
simplifyContext :: (Quasi m, ExpandType m, MonadState (Map Pred [InstanceDec]) m) => [Pred] -> m [Pred]
simplifyContext context =
    do (expanded :: [Pred]) <- expandTypes context
       let (context' :: [Pred]) = concat $ map unify expanded
       let context'' = foldl testPredicate context' context'
       if (context'' == context) then return context'' else simplifyContext context''

-- | Try to simplify the context by eliminating of one of the predicates.
-- If we succeed start again with the new context.
testPredicate :: [Pred] -> Pred -> [Pred]
#if MIN_VERSION_template_haskell(2,10,0)
testPredicate context (AppT (AppT EqualityT v@(VarT _)) b) = everywhere (mkT (\ x -> if x == v then b else x)) context
testPredicate context (AppT (AppT EqualityT a) v@(VarT _)) = everywhere (mkT (\ x -> if x == v then a else x)) context
testPredicate context p@(AppT (AppT EqualityT a) b) | a == b = filter (/= p) context
#else
testPredicate context (EqualP v@(VarT _) b) = everywhere (mkT (\ x -> if x == v then b else x)) context
testPredicate context (EqualP a v@(VarT _)) = everywhere (mkT (\ x -> if x == v then a else x)) context
testPredicate context p@(EqualP a b) | a == b = filter (/= p) context
#endif
testPredicate context _ = context

expandTypes :: (Quasi m, ExpandType m, Data a) => a -> m a
expandTypes = everywhereM (mkM expandType)

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
      consistent' (AppT cls' arg) args = consistent' cls' (arg : args)
      consistent' _ _ = return False
#else
consistent (ClassP cls args) = (not . null) <$> instances cls args -- Do we need additional context here?
consistent (EqualP (AppT a b) (AppT c d)) =
    -- I'm told this is incorrect in the presence of type functions
    (&&) <$> consistent (EqualP a c) <*> consistent (EqualP b d)
consistent (EqualP (VarT _) _) = return True
consistent (EqualP _ (VarT _)) = return True
consistent (EqualP a b) | a == b = return True
consistent (EqualP _ _) = return False
#endif

-- testPred :: MonadMIMO m => Pred -> m Bool
testPred :: (Quasi m, ExpandType m, MonadState (Map Pred [InstanceDec]) m) => Pred -> m Bool
testPred predicate = do
  -- Is the instance already in the Q monad?
  flag <- testContext [predicate]
  case flag of
    True -> return True
    -- Have we already generated and inserted the instance into the map in the state monad?
    False -> maybe False (not . null) <$> (Map.lookup <$> expandTypes predicate <*> get)

-- | Apply a filter such as 'simpleMissingInstanceTest' to a list of
-- instances, resulting in a non-overlapping list of instances.
missingInstances :: Quasi m => (Dec -> m Bool) -> m [Dec] -> m [Dec]
missingInstances test decs = decs >>= mapM (\ dec -> test dec >>= \ flag -> return $ if flag then Just dec else Nothing) >>= return . catMaybes

-- | Return True if no instance matches the types (ignoring the instance context)
simpleMissingInstanceTest :: Quasi m => Dec -> m Bool
simpleMissingInstanceTest dec@(InstanceD _ typ _) =
    case unfoldInstance typ of
      Just (name, types) -> do
        trace ("name: " ++ show name ++ ", types=" ++ show types) (return ())
        insts <- qReifyInstances name types
        trace ("insts: " ++ show (map pprint insts)) (return ())
        return $ null insts
      Nothing -> error $ "simpleMissingInstanceTest - invalid instance: " ++ pprint dec
    where
      unfoldInstance (ConT name) = Just (name, [])
      unfoldInstance (AppT t1 t2) = maybe Nothing (\ (name, types) -> Just (name, types ++ [t2])) (unfoldInstance t1)
      unfoldInstance _ = Nothing
simpleMissingInstanceTest dec = error $ "simpleMissingInstanceTest - invalid instance: " ++ pprint dec
