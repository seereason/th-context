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
module Language.Haskell.TH.Context.Reify
    (
    -- * State type and lenses
      S
    , instMap
    , visited
    , InstMap
    , DecStatus(Declared, Undeclared)
    -- * Reify
    , reifyInstancesWithContext
    , tellInstance
    -- * Monad runners
    , runContext
    , evalContext
    , evalContext_
    , execContext
    , tellUndeclared
    ) where

#if __GLASGOW_HASKELL__ < 709
import Control.Applicative ((<$>), (<*>))
import Data.Monoid (mempty)
#else
import Data.Maybe (isJust)
#endif
import Control.Lens
import Control.Monad (filterM)
import Control.Monad.Reader (ReaderT)
import Control.Monad.State (MonadState, StateT, evalStateT, runStateT)
import Control.Monad.Writer (MonadWriter, tell)
import Data.Generics (everywhere, mkT)
import Data.List ({-dropWhileEnd,-} intercalate)
import Data.Map as Map (elems, insert, lookup, Map)
import Data.Maybe (mapMaybe)
import Data.Set (Set)
import Language.Haskell.TH
import Language.Haskell.TH.Desugar as DS (DsMonad(localDeclarations))
import Language.Haskell.TH.PprLib (cat, ptext)
import Language.Haskell.TH.Syntax hiding (lift)
import Language.Haskell.TH.Instances ({- Ord instances from th-orphans -})
import Language.Haskell.TH.TypeGraph.Expand (E, expandPred, expandClassP, runExpanded)
import Language.Haskell.TH.TypeGraph.Prelude (HasSet(getSet, modifySet), pprint')
import Language.Haskell.TH.TypeGraph.Vertex (TGV)

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

data S
    = S { _instMap :: InstMap
        , _visited :: Set TGV }

$(makeLenses ''S)

instance Quasi m => DsMonad (ReaderT S m) where
    localDeclarations = view instMap >>= return . map instanceDec . concat . Map.elems

instance Monad m => HasSet TGV (StateT S m) where
    getSet = use visited
    modifySet f = visited %= f

-- | Like 'qReifyInstances', looks up all the instances that match the
-- given class name and argument types.  Unlike 'qReifyInstances',
-- only the ones that satisfy all the instance context predicates in
-- the environment are returned.  If there is already an instance that
-- satisfies the predicate built from the name and types it is
-- returned.  If not, this new predicate is inserted into the state
-- monad 'InstMap', associated with an empty list of predicates, and the
-- empty list is returned.  Later the caller can use 'tellInstance' to
-- associate instances with the predicate.
reifyInstancesWithContext :: forall m. (DsMonad m, MonadState S m) =>
                             Name -> [Type] -> m [InstanceDec]
reifyInstancesWithContext className typeParameters = do
       p <- expandClassP className typeParameters :: m (E Pred)
       mp <- use instMap
       case Map.lookup p mp of
         Just x -> return $ map instanceDec x
         Nothing -> do
           -- Add an entry with a bogus value to limit recursion on
           -- the predicate we are currently testing
           instMap %= Map.insert p []
           -- Get all the instances of className that unify with the type parameters.
           insts <- qReifyInstances className typeParameters
           -- Filter out the ones that conflict with the instance context
           r <- filterM (testInstance className typeParameters) insts
           -- Now insert the correct value into the map and return it.
           instMap %= Map.insert p (map Declared r)
           return r

-- | Test one of the instances returned by qReifyInstances against the
-- context we have computed so far.  We have already added a ClassP predicate
-- for the class and argument types, we now need to unify those with the
-- type returned by the instance and generate some EqualP predicates.
testInstance :: (DsMonad m, MonadState S m) => Name -> [Type] -> InstanceDec -> m Bool
testInstance className typeParameters (InstanceD instanceContext instanceType _) = do
  -- The new context consists of predicates derived by unifying the
  -- type parameters with the instance type, plus the prediates in the
  -- instance context field.
  mapM expandPred (instancePredicates (reverse typeParameters) instanceType ++ instanceContext) >>= testContext . map runExpanded
    where
      instancePredicates :: [Type] -> Type -> [Pred]
#if __GLASGOW_HASKELL__ >= 709
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
testContext :: (DsMonad m, MonadState S m) => [Pred] -> m Bool
testContext context =
    and <$> (simplifyContext context >>= mapM consistent)

-- | Perform type expansion on the predicates, then simplify using
-- variable substitution and eliminate vacuous equivalences.
simplifyContext :: (DsMonad m, MonadState S m) => [Pred] -> m [Pred]
simplifyContext context =
    do let context' = concat $ map unify context
       let context'' = foldl simplifyPredicate context' context'
       if (context'' == context) then return context'' else simplifyContext context''

-- | Try to simplify the context by eliminating of one of the predicates.
-- If we succeed start again with the new context.
simplifyPredicate :: [Pred] -> Pred -> [Pred]
#if __GLASGOW_HASKELL__ >= 709
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
#if 0
testContextWithState :: forall m pred. (DsMonad m, MonadState S m) => [Pred] -> m Bool
testContextWithState context = do
  -- Is the instance already in the Q monad?
  flag <- testContext context
  case flag of
    True -> return True
    -- Have we already generated and inserted the instance into the
    -- map in the state monad?  (Shouldn't we try this before calling
    -- testContext?)
    False -> and <$> mapM testPredicate context
    where
      testPredicate :: Pred -> m Bool
      testPredicate predicate = maybe False (not . null) <$> (Map.lookup predicate <$> get)
#endif

-- | Unify the two arguments of an EqualP predicate, return a list of
-- simpler predicates associating types with a variables.
unify :: Pred -> [Pred]
#if __GLASGOW_HASKELL__ >= 709
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
-- context.  Use recursive calls to reifyInstancesWithContext when
-- we encounter a class name applied to a list of type parameters.
consistent :: (DsMonad m, MonadState S m) => Pred -> m Bool
#if __GLASGOW_HASKELL__ >= 709
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

-- | Declare an instance in the state monad, marked Undeclared.  After
-- this, the instance predicate (constructed from class namd and type
-- parameters) will be considered part of the context for subsequent
-- calls to reifyInstancesWithContext.
tellInstance :: (DsMonad m, MonadState S m, Quasi m) =>
                Dec -> m ()
tellInstance inst@(InstanceD _ instanceType _) =
    do let Just (className, typeParameters) = unfoldInstance instanceType
#if __GLASGOW_HASKELL__ >= 709
       p <- expandPred $ foldInstance className typeParameters
#else
       p <- expandPred $ ClassP className typeParameters
#endif
       mp <- use instMap
       case Map.lookup p mp of
         Just (_ : _) -> return ()
         _ -> do instMap %= Map.insert p [Undeclared inst] -- There is no point associating multiple instances with a predicate, it is a compile error
tellInstance inst = error $ "tellInstance - Not an instance: " ++ pprint' inst

unfoldInstance :: Type -> Maybe (Name, [Type])
unfoldInstance (ConT name) = Just (name, [])
unfoldInstance (AppT t1 t2) = maybe Nothing (\ (name, types) -> Just (name, types ++ [t2])) (unfoldInstance t1)
unfoldInstance _ = Nothing

foldInstance :: Name -> [Type] -> Pred
foldInstance className typeParameters = foldl AppT (ConT className) typeParameters

runContext :: Monad m => StateT S m r -> m (r, S)
runContext action = runStateT action (S mempty mempty)

-- | Run the action, tell the undeclared instances to the writer
-- monad, and return the result.
evalContext :: MonadWriter [Dec] m => StateT S m r -> m r
evalContext action = do
  (r, s) <- runContext action
  tellUndeclared s
  return r

-- | Run the action, discard the undeclared instances, and return the
-- result.
evalContext_ :: Monad m => StateT S m r -> m r
evalContext_ action = evalStateT action (S mempty mempty)

-- | Run the action and tell the undeclared instances to the writer
-- monad.
execContext :: MonadWriter [Dec] m => StateT S m () -> m ()
execContext action = runContext action >>= tellUndeclared . snd

-- | Tell the the instances that were added to the context (not the
-- ones that were discovered by reifyInstances) to the writer monad.
tellUndeclared :: MonadWriter [Dec] m => S -> m ()
tellUndeclared = tell . mapMaybe undeclared . concat . Map.elems . _instMap
    where
      undeclared :: DecStatus Dec -> Maybe Dec
      undeclared (Undeclared dec) = Just dec
      undeclared (Declared _) = Nothing
