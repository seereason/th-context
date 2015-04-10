-- | Naive instance filtering (as in @th-reify-many@.)  Mostly for comparison
-- to @qReifyInstancesWithContext@.
module Language.Haskell.TH.Context.Simple
    ( missingInstances
    , simpleMissingInstanceTest
    ) where

import Data.Maybe (catMaybes)
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Instances ({- Ord instances from th-orphans -})

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
