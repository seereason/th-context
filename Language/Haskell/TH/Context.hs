-- | Compute whether any existing instance satisfies some
-- context in a nearly correct fashion.
-- @
--    instance A m => B m where ...
-- @
-- I say "nearly correct" because there are cases which are
-- not handled exactly the way GHC behaves, which may lead to
-- false (positives?  negatives?)
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wall -fno-warn-orphans #-}
module Language.Haskell.TH.Context
    ( InstMap
    , DecStatus(Declared, Undeclared, instanceDec)
    , reifyInstancesWithContext
    , tellInstance
    , tellUndeclared
    ) where

import Data.Maybe (isJust)
import Control.Monad (filterM)
import Control.Monad.State (get, modify, StateT)
import Control.Monad.Writer (MonadWriter, tell)
import Data.Generics (everywhere, mkT)
import Data.List (intercalate)
import Data.Map as Map (elems, insert, lookup, Map)
import Data.Maybe (mapMaybe)
-- import Debug.Trace (trace)
import Language.Haskell.TH
import Language.Haskell.TH.Desugar as DS (DsMonad)
import Language.Haskell.TH.PprLib (cat, ptext)
import Language.Haskell.TH.Syntax hiding (lift)
import Language.Haskell.TH.TypeGraph.Expand (ExpandMap, expandType, E(unE))
import Language.Haskell.TH.TypeGraph.HasState (HasState(getState, modifyState))
import Language.Haskell.TH.Instances ({- Ord instances from th-orphans -})

-- FIXME: Should actually be Map (E Pred) (Maybe (DecStatus
-- InstanceDec)), because having more than one instance would be a
-- compile error.
type InstMap = Map (E Pred) [DecStatus InstanceDec]

-- | Did we get this instance from the Q monad or does it still need to be spliced?
data DecStatus a
    = Declared {instanceDec :: a}
    -- ^ An instance we found in the Q monad
    | Undeclared {instanceDec :: a}
    -- ^ An instance we inserted via tellInstance
    deriving Show

instance Ppr a => Ppr (DecStatus a) where
    ppr (Undeclared x) = cat [ptext "Undeclared (", ppr x, ptext ")"]
    ppr (Declared x) = cat [ptext "Declared (", ppr x, ptext ")"]

-- | Like 'qReifyInstances', looks up all the instances that match the
-- given class name and argument types.  Unlike 'qReifyInstances',
-- only the ones that satisfy all the instance context predicates in
-- the environment are returned.  If there is already an instance that
-- satisfies the predicate built from the name and types it is
-- returned.  If not, this new predicate is inserted into the state
-- monad 'InstMap', associated with an empty list of predicates, and the
-- empty list is returned.  Later the caller can use 'tellInstance' to
-- associate instances with the predicate.
reifyInstancesWithContext :: forall m. (DsMonad m, HasState InstMap m, HasState ExpandMap m) =>
                             Name -> [Type] -> m [InstanceDec]
reifyInstancesWithContext className typeParameters = do
  p <- expandType $ foldInstance className typeParameters
  mp <- getState :: m InstMap
  case Map.lookup p mp of
    Just x -> return $ map instanceDec x
    Nothing -> do
      -- trace ("        -> reifyInstancesWithContext " ++ pprint (foldInstance className typeParameters) ++ "...") (return ())
      -- Add an entry with a bogus value to limit recursion on
      -- the predicate we are currently testing
      modifyState (Map.insert p [] :: InstMap -> InstMap)
      -- Get all the instances of className that unify with the type parameters.
      insts <- qReifyInstances className typeParameters
      -- Filter out the ones that conflict with the instance context
      r <- filterM (testInstance className typeParameters) insts
      -- Now insert the correct value into the map and return it.  Because
      -- this instance was discovered in the Q monad it is marked Declared.
      modifyState (Map.insert p (map Declared r))
      -- trace ("        <- reifyInstancesWithContext " ++ pprint (foldInstance className typeParameters) ++ " -> " ++ pprint r) (return ())
      return r

-- | Test one of the instances returned by qReifyInstances against the
-- context we have computed so far.  We have already added a ClassP predicate
-- for the class and argument types, we now need to unify those with the
-- type returned by the instance and generate some EqualP predicates.
testInstance :: (DsMonad m, HasState InstMap m, HasState ExpandMap m) => Name -> [Type] -> InstanceDec -> m Bool
testInstance className typeParameters (InstanceD instanceContext instanceType _) = do
  -- The new context consists of predicates derived by unifying the
  -- type parameters with the instance type, plus the prediates in the
  -- instance context field.
  mapM expandType (instancePredicates (reverse typeParameters) instanceType ++ instanceContext) >>= testContext . map unE
    where
      instancePredicates :: [Type] -> Type -> [Pred]
      instancePredicates (x : xs) (AppT l r) = AppT (AppT EqualityT x) r : instancePredicates xs l
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
testContext :: (DsMonad m, HasState InstMap m, HasState ExpandMap m) => [Pred] -> m Bool
testContext context =
    and <$> (simplifyContext context >>= mapM consistent)

-- | Perform type expansion on the predicates, then simplify using
-- variable substitution and eliminate vacuous equivalences.
simplifyContext :: (DsMonad m, HasState InstMap m) => [Pred] -> m [Pred]
simplifyContext context =
    do let context' = concat $ map unify context
       let context'' = foldl simplifyPredicate context' context'
       if (context'' == context) then return context'' else simplifyContext context''

-- | Try to simplify the context by eliminating of one of the predicates.
-- If we succeed start again with the new context.
simplifyPredicate :: [Pred] -> Pred -> [Pred]
simplifyPredicate context (AppT (AppT EqualityT v@(VarT _)) b) = everywhere (mkT (\ x -> if x == v then b else x)) context
simplifyPredicate context (AppT (AppT EqualityT a) v@(VarT _)) = everywhere (mkT (\ x -> if x == v then a else x)) context
simplifyPredicate context p@(AppT (AppT EqualityT a) b) | a == b = filter (/= p) context
simplifyPredicate context _ = context

-- | Unify the two arguments of an EqualP predicate, return a list of
-- simpler predicates associating types with a variables.
unify :: Pred -> [Pred]
unify (AppT (AppT EqualityT (AppT a b)) (AppT c d)) = unify (AppT (AppT EqualityT a) c) ++ unify (AppT (AppT EqualityT b) d)
unify (AppT (AppT EqualityT (ConT a)) (ConT b)) | a == b = []
unify (AppT (AppT EqualityT a@(VarT _)) b) = [AppT (AppT EqualityT a) b]
unify (AppT (AppT EqualityT a) b@(VarT _)) = [AppT (AppT EqualityT a) b]
unify x = [x]

-- | Decide whether a predicate is consistent with the accumulated
-- context.  Use recursive calls to reifyInstancesWithContext when
-- we encounter a class name applied to a list of type parameters.
consistent :: (DsMonad m, HasState InstMap m, HasState ExpandMap m) => Pred -> m Bool
consistent typ
    | isJust (unfoldInstance typ) =
        let Just (className, typeParameters) = unfoldInstance typ in
        (not . null) <$> reifyInstancesWithContext className typeParameters
consistent (AppT (AppT EqualityT (AppT a b)) (AppT c d)) =
    -- I'm told this is incorrect in the presence of type functions
    (&&) <$> consistent (AppT (AppT EqualityT a) c) <*> consistent (AppT (AppT EqualityT b) d)
consistent (AppT (AppT EqualityT (VarT _)) _) = return True
consistent (AppT (AppT EqualityT _) (VarT _)) = return True
consistent (AppT (AppT EqualityT a) b) | a == b = return True
consistent (AppT (AppT EqualityT _) _) = return False
consistent typ = error $ "Unexpected Pred: " ++ pprint typ

-- | Declare an instance in the state monad, marked Undeclared.  After
-- this, the instance predicate (constructed from class name and type
-- parameters) will be considered part of the context for subsequent
-- calls to reifyInstancesWithContext.
tellInstance :: (DsMonad m, HasState InstMap m, Quasi m, HasState ExpandMap m) => Dec -> m ()
tellInstance inst@(InstanceD _ instanceType _) =
    do let Just (className, typeParameters) = unfoldInstance instanceType
       p <- expandType $ foldInstance className typeParameters
       (mp :: InstMap) <- getState
       case Map.lookup p mp of
         Just (_ : _) -> return ()
          -- Here we set the instance list to a singleton - there is
          -- no point associating multiple instances with a predicate,
          -- compiling the resulting set of declarations is an error
          -- (overlapping instances.)
         _ -> modifyState (Map.insert p [Undeclared inst])
tellInstance inst = error $ "tellInstance - Not an instance: " ++ pprint inst

-- A basic HasState InstMap instance.
instance Monad m => HasState InstMap (StateT InstMap m) where
    getState = get
    modifyState = modify

-- | After all the declared and undeclared instances have been added
-- to the instance map using tellInstance, this returns the undeclared
-- instances only, not the ones that were discovered by
-- reifyInstances, and tells them to the writer monad.
tellUndeclared :: (MonadWriter [Dec] m, HasState InstMap m) => m ()
tellUndeclared =
    getState >>= \(mp :: InstMap) -> tell . mapMaybe undeclared . concat . Map.elems $ mp
    where
      undeclared :: DecStatus Dec -> Maybe Dec
      undeclared (Undeclared dec) = Just dec
      undeclared (Declared _) = Nothing

-- | Turn a type Name and a list of Type parameters into a Pred (which
-- is now just a Type.)
foldInstance :: Name -> [Type] -> Pred
foldInstance className typeParameters = foldl AppT (ConT className) typeParameters

-- | The inverse of foldInstance.  Returns Nothing if the Pred is
-- incorrectly formatted - i.e. not in a form that 'foldInstance' can
-- produce.
unfoldInstance :: Pred -> Maybe (Name, [Type])
unfoldInstance (ConT name) = Just (name, [])
unfoldInstance (AppT t1 t2) = maybe Nothing (\ (name, types) -> Just (name, types ++ [t2])) (unfoldInstance t1)
unfoldInstance _ = Nothing
