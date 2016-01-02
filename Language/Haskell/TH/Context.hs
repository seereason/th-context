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
    , ContextM
    , DecStatus(Declared, Undeclared, instanceDec)
    , reifyInstancesWithContext
    , tellInstance
    , tellUndeclared
    , noInstance
    ) where

import Control.Lens (view)
import Control.Monad (filterM)
import Control.Monad.State (execStateT)
import Control.Monad.States (MonadStates, getPoly, modifyPoly)
import Control.Monad.Writer (MonadWriter, tell)
import Data.Generics (everywhere, mkT)
import Data.List (intercalate)
import Data.Logic.ATP.TH (expandBindings {-instance Unify [Type]-})
import Data.Logic.ATP.Unif (Unify(unify))
import Data.Map as Map (elems, insert, lookup, Map)
import Data.Maybe (mapMaybe)
import Debug.Trace (trace)
import Language.Haskell.TH
import Language.Haskell.TH.Desugar as DS (DsMonad)
import Language.Haskell.TH.PprLib (cat, ptext)
import Language.Haskell.TH.Syntax hiding (lift)
import Language.Haskell.TH.TypeGraph.Expand (ExpandMap, expandType, E, unE)
import Language.Haskell.TH.TypeGraph.Prelude (pprint')
import Language.Haskell.TH.Instances ({- Ord instances from th-orphans -})

-- FIXME: Should actually be Map (E Pred) (Maybe (DecStatus
-- InstanceDec)), because having more than one instance would be a
-- compile error.
type InstMap = Map (E Pred) [DecStatus InstanceDec]

-- | Combine the DsMonad (desugaring), which includes the Q monad, and
-- state to record declared instances, type expansions, and a string
-- for debugging messages.
class (DsMonad m, MonadStates InstMap m, MonadStates ExpandMap m, MonadStates String m) => ContextM m

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
reifyInstancesWithContext :: forall m. ContextM m => Name -> [Type] -> m [InstanceDec]
reifyInstancesWithContext className typeParameters = do
  p <- expandType $ foldInstance className typeParameters
  mp <- getPoly :: m InstMap
  case Map.lookup p mp of
    Just x -> return $ map instanceDec x
    Nothing -> do
      modifyPoly ("  " ++)
      pre <- getPoly :: m String
      -- Add an entry with a bogus value to limit recursion on
      -- the predicate we are currently testing
      modifyPoly (Map.insert p [] :: InstMap -> InstMap)
      -- Get all the instances of className that unify with the type parameters.
      insts <- qReifyInstances className typeParameters
      -- Filter out the ones that conflict with the instance context
      r <- filterM (testInstance className typeParameters) insts
      trace (intercalate ("\n" ++ pre ++ "    ")
                         ((pre ++ "reifyInstancesWithContext " ++ pprint' (foldInstance className typeParameters) ++ " -> [") :
                          map (\(InstanceD _ typ _) -> pprint' typ) r) ++
                         "]") (return ())
      -- Now insert the correct value into the map and return it.  Because
      -- this instance was discovered in the Q monad it is marked Declared.
      modifyPoly (Map.insert p (map Declared r))
      -- trace ("        <- reifyInstancesWithContext " ++ pprint (foldInstance className typeParameters) ++ " -> " ++ pprint r) (return ())
      modifyPoly (drop 2 :: String -> String)
      return r

-- | Test one of the instances returned by qReifyInstances against the
-- context we have computed so far.  We have already added a ClassP predicate
-- for the class and argument types, we now need to unify those with the
-- type returned by the instance and generate some EqualP predicates.
testInstance :: ContextM m => Name -> [Type] -> InstanceDec -> m Bool
testInstance className typeParameters (InstanceD instanceContext instanceType _) = do
  -- The new context consists of predicates derived by unifying the
  -- type parameters with the instance type, plus the prediates in the
  -- instance context field.
  mapM expandType (instancePredicates ++ instanceContext) >>= testContext . map (view unE)
    where
      instancePredicates :: [Pred]
      instancePredicates = maybe (error $ "Invalid instance type: " ++ show instanceType) instanceEqualities (unfoldInstance instanceType)
      instanceEqualities (_, instanceArgs)
          | length instanceArgs /= length typeParameters =
              error $ "type class arity error:" ++
                      "\n  class name = " ++ show className ++
                      "\n  type parameters = " ++ show typeParameters ++
                      "\n  instance args = " ++ show instanceArgs
      instanceEqualities (_, instanceArgs) = map (\(a, b) ->  AppT (AppT EqualityT a) b) (zip typeParameters instanceArgs)
testInstance _ _ x = error $ "qReifyInstances returned something that doesn't appear to be an instance declaration: " ++ show x

-- | Now we have predicates representing the unification of the type
-- parameters with the instance type, along with the instance
-- superclasses.  Are they consistent?  Find out using type synonym
-- expansion, variable substitution, elimination of vacuous
-- predicates, and unification.
testContext :: ContextM m => [Pred] -> m Bool
testContext context = and <$> (execStateT (unify context) mempty >>= \mp -> mapM consistent (everywhere (mkT (expandBindings mp)) context))

-- | Decide whether a predicate returned by 'unify' is
-- consistent with the accumulated context.  Use recursive calls to
-- reifyInstancesWithContext when we encounter a class name applied to
-- a list of type parameters.
consistent :: ContextM m => Pred -> m Bool
consistent (AppT (AppT EqualityT a) b) | a == b = return True
consistent typ =
    maybe (error $ "Unexpected Pred: " ++ pprint typ)
          (\(className, typeParameters) -> (not . null) <$> reifyInstancesWithContext className typeParameters)
          (unfoldInstance typ)

-- | Declare an instance in the state monad, marked Undeclared.  After
-- this, the instance predicate (constructed from class name and type
-- parameters) will be considered part of the context for subsequent
-- calls to reifyInstancesWithContext.
tellInstance :: ContextM m => Dec -> m ()
tellInstance inst@(InstanceD _ instanceType _) =
    do let Just (className, typeParameters) = unfoldInstance instanceType
       p <- expandType $ foldInstance className typeParameters
       (mp :: InstMap) <- getPoly
       case Map.lookup p mp of
         Just (_ : _) -> return ()
          -- Here we set the instance list to a singleton - there is
          -- no point associating multiple instances with a predicate,
          -- compiling the resulting set of declarations is an error
          -- (overlapping instances.)
         _ -> modifyPoly (Map.insert p [Undeclared inst])
tellInstance inst = error $ "tellInstance - Not an instance: " ++ pprint inst

-- | After all the declared and undeclared instances have been added
-- to the instance map using tellInstance, this returns the undeclared
-- instances only, not the ones that were discovered by
-- reifyInstances, and tells them to the writer monad.
tellUndeclared :: (MonadWriter [Dec] m, MonadStates InstMap m) => m ()
tellUndeclared =
    getPoly >>= \(mp :: InstMap) -> tell . mapMaybe undeclared . concat . Map.elems $ mp
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

noInstance :: ContextM m => Name -> Name -> m Bool
noInstance className typeName = do
  i <- qReify typeName
  typ <- case i of
           TyConI (DataD _cxt _name tvbs _fundeps _decs) ->
               do vs <- mapM (\c -> VarT <$> runQ (newName [c])) (take (length tvbs) ['a'..'z'])
                  return $ foldl AppT (ConT typeName) vs
           _ -> error "haven't thought about what happens here"
  r <- null <$> reifyInstancesWithContext className [typ]
  trace ("noInstance " ++ show className ++ " " ++ show typeName ++ " -> " ++ show r) (return ())
  return r
