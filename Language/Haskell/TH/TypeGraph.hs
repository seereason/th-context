{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wall #-}
module Language.Haskell.TH.TypeGraph
    ( HasStack(withStack)
    , StackElement(..)
    , prettyStack
      -- * Stack+instance map monad
    , StackT
    , execStackT
      -- * Subtype traversal
    -- , visitSubtypes
    , subtypes
    , typeGraphEdges
    , typeGraphEdgesPlus
    , subtypeGraph
    ) where

import Debug.Trace

#if __GLASGOW_HASKELL__ < 709
import Control.Applicative
#endif
-- import Control.Category ((.))
import Control.Monad.RWS (RWST)
import Control.Monad.Reader (ask, local, ReaderT, runReaderT)
import Control.Monad.State (evalStateT, execStateT, modify, MonadState(get), StateT)
import Control.Monad.Trans (lift)
import Control.Monad.Writer (MonadWriter(tell), WriterT(runWriterT))
import Data.Generics (Data, Typeable)
import Data.Graph (Graph, Vertex, graphFromEdges)
import Data.Map as Map (Map, member, insert, update, keys, toList)
import Data.Monoid (Monoid, mempty)
import Data.Set as Set (insert, Set, empty, fromList, toList)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH -- (Con, Dec, nameBase, Type)
import Language.Haskell.TH.Context (expandTypes)
import Language.Haskell.TH.Desugar (DsMonad)
import Language.Haskell.TH.DesugarExpandType ()
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.Syntax (Quasi(..))
import Language.Haskell.TH.Fold (decName, FieldType, foldCon, foldDec, {-constructorFields, foldName, foldType, fType',-} foldTypeP, prettyField)

-- | The information required to extact a field value from a value.
-- We keep a stack of these as we traverse a declaration.  Generally,
-- we only need the field names.
data StackElement = StackElement FieldType Con Dec deriving (Eq, Show, Data, Typeable)

class Monad m => HasStack m where
    withStack :: ([StackElement] -> m a) -> m a -- Better name: askStack
    push :: FieldType -> Con -> Dec -> m a -> m a -- Better name: localStack

instance (Quasi m, Monoid w) => HasStack (RWST [StackElement] w s m) where
    withStack f = ask >>= f
    push fld con dec action = local (\ stk -> StackElement fld con dec : stk) action

instance HasStack m => HasStack (StateT s m) where
    withStack f = lift (withStack return) >>= f
    push fld con dec action = get >>= \ st -> lift $ push fld con dec (evalStateT action st)

instance Quasi m => HasStack (ReaderT [StackElement] m) where
    withStack f = ask >>= f
    push fld con dec action = local (\ stk -> StackElement fld con dec : stk) action

instance (HasStack m, Monoid w) => HasStack (WriterT w m) where
    withStack f = lift (withStack return) >>= f
    push fld con dec action =
        do (r, w') <- lift $ push fld con dec (runWriterT action)
           tell w'
           return r

prettyStack :: [StackElement] -> String
prettyStack = prettyStack' . reverse
    where
      prettyStack' :: [StackElement] -> String
      prettyStack' [] = "(empty)"
      prettyStack' (x : xs) = "[" ++ prettyElt x ++ prettyTail xs ++ "]"
      prettyTail [] = ""
      prettyTail (x : xs) = " → " ++ prettyElt x ++ prettyTail xs
      prettyElt (StackElement fld con dec) =
          foldDec prettyType (\ _ -> nameBase (decName dec)) dec ++ ":" ++
          foldCon (\ name _ -> nameBase name) con ++ "." ++
          prettyField fld
      prettyType typ = foldTypeP nameBase
                                 (\ t1 t2 -> "((" ++ prettyType t1 ++ ") (" ++ prettyType t2 ++ "))")
                                 ("(" ++ show typ ++ ")")
                                 typ

type StackT m = ReaderT [StackElement] m

execStackT :: Monad m => StackT m a -> m a
execStackT action = runReaderT action []

subtypes :: DsMonad m => [Type] -> m (Set Type)
subtypes types = do
  (Set.fromList . Map.keys) <$> typeGraphEdges types

typeGraphEdges :: forall m. DsMonad m => [Type] -> m (Map Type (Set Type))
typeGraphEdges = typeGraphEdgesPlus (return . Just)

typeGraphEdgesPlus
    :: forall m. DsMonad m =>
       (Type -> m (Maybe Type))
           -- ^ This function is applied to every expanded type before
           -- use, and the result is used instead.  If it returns
           -- Nothing, no arcs are added to the graph.  The current
           -- use case for this argument is to see if there is an
           -- instance of class @View a b@ where @a@ is the type
           -- passed to @doType@, and replace it with @b@, and use the
           -- lens returned by @View's@ method to convert between @a@
           -- and @b@.
    -> [Type]
    -> m (Map Type (Set Type))
typeGraphEdgesPlus augment types = do
  execStateT (mapM_ (doUnexpandedType Nothing) types) mempty
    where
      doUnexpandedType :: Maybe Type -> Type -> StateT (Map Type (Set Type)) m ()
      doUnexpandedType parent typ = expandTypes typ >>= lift . augment >>= maybe (return ()) (doType parent)

      doType :: Maybe Type -> Type -> StateT (Map Type (Set Type)) m ()
      doType parent typ = do
        mp <- get
        case Map.member typ mp of
          True -> return ()
          False -> do
            maybe (return ()) (\ ptype -> modify (Map.update (Just . (Set.insert typ)) ptype)) parent
            modify (Map.insert typ Set.empty) -- Indicate that we are processing a type
            case typ of
              -- Is forall a. T the same node as T?  Or should there
              -- be two nodes?  Or just a node for forall a. T?  Here
              -- we treat it as a different node.
              (ForallT _ _ typ') -> {- modify (Map.update (Just . (Set.insert typ')) typ) >> -} doUnexpandedType parent typ'
              (AppT container element) -> doApply container element
              (ConT name) -> do
                info <- qReify name
                case info of
                  TyConI dec -> doDec name dec
                  _ -> return ()
              _ -> return (trace ("Unrecognized type: " ++ show typ) ())

      doApply container element = do
        doUnexpandedType (Just (AppT container element)) container
        doUnexpandedType (Just (AppT container element)) element

      doDec :: DsMonad m => Name -> Dec -> StateT (Map Type (Set Type)) m ()
      doDec tname dec@(NewtypeD _ _cname _ con _) = doCon tname dec con
      doDec tname dec@(DataD _ _cname _ cons _) = mapM_ (doCon tname dec) cons
      doDec _ _ = return ()

      doCon :: DsMonad m => Name -> Dec -> Con -> StateT (Map Type (Set Type)) m ()
      doCon tname dec (ForallC _ _ con) = doCon tname dec con
      doCon tname dec (NormalC cname fields) = mapM_ (doField tname dec cname) (zip (map Left ([1..] :: [Int])) (map snd fields))
      doCon tname dec (RecC cname fields) = mapM_ (doField tname dec cname) (map (\ (fname, _, typ) -> (Right fname, typ)) fields)
      doCon tname dec (InfixC (_, lhs) cname (_, rhs)) = mapM_ (doField tname dec cname) [(Left 1, lhs), (Left 2, rhs)]

      doField tname _dec _cname (_fld, typ') = doUnexpandedType (Just (ConT tname)) typ'

-- | Build a graph from the result of typeGraphEdgesPlus, its edges
-- represent the primitive lenses, and each path in the graph is a
-- composition of lenses.
subtypeGraph :: (DsMonad m, node ~ Type, key ~ Type) =>
                (Type -> m (Maybe Type)) -> [Type] -> m (Graph, Vertex -> (node, key, [key]), key -> Maybe Vertex)
subtypeGraph augment types = do
  typeGraphEdgesPlus augment types >>= return . graphFromEdges . triples
    where
      triples mp = map (\ (k, ks) -> (k, k, Set.toList ks)) $ Map.toList mp

{-
adjacentTypes :: DsMonad m => Type -> m (Type, [Type])
adjacentTypes (ForallT _ _ typ) = adjacentTypes typ
adjacentTypes (AppT t1 t2) = [t1, t2]
adjacentTypes t@(ConT _) = [t]
adjacentTypes t@(VarT _) = [t]
adjacentTypes _ = []
-}
