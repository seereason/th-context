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
module Language.Haskell.TH.Context.Reify
    ( InstMap
    , reifyInstancesWithContext
    , tellInstance
    -- * State/writer monad runners
    , evalContextState
    , execContextWriter
    , execContext
    , runContext
    ) where

#if __GLASGOW_HASKELL__ < 709
import Control.Applicative ((<$>), (<*>))
import Data.Monoid (mempty)
#else
import Data.Maybe (isJust)
#endif
import Control.Monad (filterM)
import Control.Monad.State (MonadState, StateT, get, modify, evalStateT)
import Control.Monad.Writer (MonadWriter, tell, WriterT, execWriterT, runWriterT)
import Data.Generics (everywhere, mkT)
import Data.List ({-dropWhileEnd,-} intercalate)
import Data.Map as Map (Map, lookup, insert, singleton, elems)
import Language.Haskell.TH
import Language.Haskell.TH.Desugar as DS (DsMonad)
import Language.Haskell.TH.Syntax hiding (lift)
import Language.Haskell.TH.Instances ({- Ord instances from th-orphans -})
import Language.Haskell.TH.TypeGraph.Core (pprint')
import Language.Haskell.TH.TypeGraph.Expand (E, expandPred, expandClassP, runExpanded)

type InstMap pred = Map pred [InstanceDec]

-- | Like 'qReifyInstances', looks up all the instances that match the
-- given class name and argument types.  Unlike 'qReifyInstances',
-- only the ones that satisfy all the instance context predicates in
-- the environment are returned.  If there is already an instance that
-- satisfies the predicate built from the name and types it is
-- returned.  If not, this new predicate is inserted into the state
-- monad 'InstMap', associated with an empty list of predicates, and the
-- empty list is returned.  Later the caller can use 'tellInstance' to
-- associate instances with the predicate.
reifyInstancesWithContext :: forall m. (DsMonad m, MonadState (InstMap (E Pred)) m) =>
                             Name -> [Type] -> m [InstanceDec]
reifyInstancesWithContext className typeParameters = do
       p <- expandClassP className typeParameters :: m (E Pred)
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
testInstance :: (DsMonad m, MonadState (InstMap (E Pred)) m) => Name -> [Type] -> InstanceDec -> m Bool
testInstance className typeParameters (InstanceD instanceContext instanceType _) = do
  -- The new context consists of predicates derived by unifying the
  -- type parameters with the instance type, plus the prediates in the
  -- instance context field.
  mapM expandPred (instancePredicates (reverse typeParameters) instanceType ++ instanceContext) >>= testContext . map runExpanded
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
testContext :: (DsMonad m, MonadState (InstMap (E Pred)) m) => [Pred] -> m Bool
testContext context =
    and <$> (mapM consistent =<< simplifyContext context)

-- | Perform type expansion on the predicates, then simplify using
-- variable substitution and eliminate vacuous equivalences.
simplifyContext :: (DsMonad m, MonadState (InstMap (E Pred)) m) => [Pred] -> m [Pred]
simplifyContext context =
    do let context' = concat $ map unify context
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
#if 0
testContextWithState :: forall m pred. (DsMonad m, MonadState (InstMap (E Pred)) m) => [Pred] -> m Bool
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
consistent :: (DsMonad m, MonadState (InstMap (E Pred)) m) => Pred -> m Bool
#if MIN_VERSION_template_haskell(2,10,0)
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

-- | Declare an instance to the state and writer monads.  After this,
-- the instance predicate (constructed from class namd and type
-- parameters) will be considered part of the context for subsequent
-- calls to qReifyInstancesWithContext.  The instance will be returned
-- when the writer monad exists so it can be spliced into to program.
tellInstance :: (DsMonad m, MonadWriter (InstMap (E Pred)) m, MonadState (InstMap (E Pred)) m, Quasi m) =>
                Dec -> m ()
tellInstance inst@(InstanceD _ instanceType _) =
    do let Just (className, typeParameters) = unfoldInstance instanceType
#if MIN_VERSION_template_haskell(2,10,0)
       p <- expandPred $ foldl AppT (ConT className) typeParameters
#else
       p <- expandPred $ ClassP className typeParameters
#endif
       st <- get
       case Map.lookup p st of
         Just (_ : _) -> return ()
         _ -> do -- trace ("  " ++ pprint' instanceType) (return ())
                 tell $ Map.singleton p [inst]
                 modify $ Map.insert p [inst]
tellInstance inst = error $ "tellInstance - Not an instance: " ++ pprint' inst

unfoldInstance :: Type -> Maybe (Name, [Type])
unfoldInstance (ConT name) = Just (name, [])
unfoldInstance (AppT t1 t2) = maybe Nothing (\ (name, types) -> Just (name, types ++ [t2])) (unfoldInstance t1)
unfoldInstance _ = Nothing

evalContextState :: Monad m => StateT (InstMap (E Pred)) m r -> m r
evalContextState action = evalStateT action (mempty :: (InstMap (E Pred)))

execContextWriter :: Monad m => WriterT (InstMap (E Pred)) m () -> m (InstMap (E Pred))
execContextWriter = execWriterT

-- | Typical use: run both state and writer monads to generate a list of
-- instance declarations.
execContext :: (Monad m, Functor m) => StateT (InstMap (E Pred)) (WriterT (InstMap (E Pred)) m) () -> m [Dec]
execContext action = (concat . Map.elems) <$> (execWriterT $ evalContextState action)

runContext :: (Monad m, Functor m) => StateT (InstMap (E Pred)) (WriterT (InstMap (E Pred)) m) r -> m (r, (InstMap (E Pred)))
runContext action = runWriterT $ evalContextState action
