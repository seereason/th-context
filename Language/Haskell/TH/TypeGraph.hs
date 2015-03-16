{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
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
    ) where

import Debug.Trace

-- import Control.Category ((.))
import Control.Monad.RWS (RWST)
import Control.Monad.Reader (ask, local, ReaderT, runReaderT)
import Control.Monad.State (evalStateT, execStateT, modify, MonadState(get), StateT)
import Control.Monad.Trans (lift)
import Control.Monad.Writer (MonadWriter(tell), WriterT(runWriterT))
import Data.Generics (Data, Typeable)
--import Data.Graph (Graph, Vertex, graphFromEdges)
import Data.Map as Map (Map, member, insert, update)
import Data.Monoid (Monoid, mempty)
import Data.Set as Set (insert, member, Set, empty)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH -- (Con, Dec, nameBase, Type)
import Language.Haskell.TH.Context (expandTypes)
import Language.Haskell.TH.Desugar (DsMonad)
import Language.Haskell.TH.DesugarExpandType ()
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.Syntax (Quasi(..))
import Language.Haskell.TH.Fold (decName, FieldType, foldCon, foldDec, {-constructorFields, foldName, foldType, fType',-} foldTypeP, prettyField, typeArity)

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

-- instance DsMonad m => MonadMIMO (StackT InstMap m)

subtypes :: DsMonad m => Type -> m (Set Type)
subtypes typ = do
  execStateT (visitSubtypes guard doApply doDec typ) mempty
      where
        guard = return . Just
        doApply _ _ = return ()
        doDec _ _ _ = return ()


typeGraphEdges :: forall m. DsMonad m =>
                  Type
               -> m (Map Type (Set Type))
typeGraphEdges unexpandedType = do
  typ <- expandTypes unexpandedType
  execStateT (doType Nothing typ) mempty
    where
      doType :: Maybe Type -> Type -> StateT (Map Type (Set Type)) m ()
      doType parent typ = do
        mp <- get
        case Map.member typ mp of
          True -> return ()
          False -> do
            maybe (return ()) (\ ptype -> modify (Map.update (Just . (Set.insert typ)) ptype)) parent
            modify (Map.insert typ Set.empty) -- Indicate that we are processing a type
            case typ of
              (ForallT _ _ typ') -> modify (Map.update (Just . (Set.insert typ')) typ) >> doType (Just typ) typ'
              (AppT container element) -> doApply container element
              (ConT name) -> do
                info <- qReify name
                case info of
                  TyConI dec -> doDec name dec
                  _ -> return ()
              _ -> return (trace ("Unrecognized type: " ++ show typ) ())
      doApply container element = do
        doType (Just (AppT container element)) container
        doType (Just (AppT container element)) element
      doDec :: DsMonad m => Name -> Dec -> StateT (Map Type (Set Type)) m ()
      doDec tname dec@(NewtypeD _ _cname _ con _) = doCon tname dec con
      doDec tname dec@(DataD _ _cname _ cons _) = mapM_ (doCon tname dec) cons
      doDec _ _ = return ()
      doCon :: DsMonad m => Name -> Dec -> Con -> StateT (Map Type (Set Type)) m ()
      doCon tname dec (ForallC _ _ con) = doCon tname dec con
      doCon tname dec (NormalC cname fields) = mapM_ (doField tname dec cname) (zip (map Left ([1..] :: [Int])) (map snd fields))
      doCon tname dec (RecC cname fields) = mapM_ (doField tname dec cname) (map (\ (fname, _, typ) -> (Right fname, typ)) fields)
      doCon tname dec (InfixC lhs cname rhs) = mapM_ (doField tname dec cname) [lhs, rhs]
      doField tname _dec _cname (_fld, unexpandedType') = do
        typ <- expandTypes unexpandedType'
        doType (Just (ConT tname)) typ

-- | A traversal of all the accessable types.
visitSubtypes :: forall m. (DsMonad m, Quasi m) =>
             (Type -> m (Maybe Type))
          -> (Type -> Type -> m ())
          -> (Type -> Dec -> [Con] -> m ())
          -> Type
          -> StateT (Set Type) m ()
visitSubtypes guard applyf decf unexpandedType =
    doType unexpandedType
    where
      doType :: Type -> StateT (Set Type) m ()
      doType unexpandedType' =
          do typ <- expandTypes unexpandedType'
             arity <- lift (typeArity typ)
             visited <- get
             case (arity, Set.member typ visited) of
               (n, _) | n > 0 -> return ()
               (_, True) -> return ()
               (_, False) -> do
                 mtyp <- lift (guard typ)
                 case mtyp of
                   Nothing -> return ()
                   Just typ' | typ' /= typ -> doType typ'
                   _ ->
                       do modify (Set.insert typ)
                          case typ of
                            (ForallT _ _ typ') -> doType typ'
                            (AppT container element) ->
                                do lift (applyf container element)
                                   doType container
                                   doType element
                            (ConT name) ->
                                do info <- qReify name
                                   case info of
                                     TyConI dec -> doDec typ dec
                                     _ -> return ()
                            _ -> return ()
      doDec :: DsMonad m => Type -> Dec -> StateT (Set Type) m ()
      doDec typ dec@(DataD _ _name _ cons _) = lift (decf typ dec cons) >> mapM_ doCon cons
      doDec typ dec@(NewtypeD _ _name _ con _) = lift (decf typ dec [con]) >> doCon con
      doDec _ _ = return ()
      doCon (NormalC _name fields) = mapM_ doField fields
      doCon (RecC _name fields) = mapM_ doField' fields
      doCon (InfixC lhs _op rhs) = mapM_ doField [lhs, rhs]
      doCon (ForallC _ _ con) = doCon con
      doField (_, typ) = doType typ
      doField' (_, _, typ) = doType typ

{-
subtypeGraph :: Monad m => Type -> m (Graph, Vertex -> (node, key, [key]), key -> Maybe Vertex)
subtypeGraph unexpandedType = do
  typ <- expandTypes unexpandedType
  graphFromEdges

adjacentTypes :: DsMonad m => Type -> m (Type, [Type])
adjacentTypes (ForallT _ _ typ) = adjacentTypes typ
adjacentTypes (AppT t1 t2) = [t1, t2]
adjacentTypes t@(ConT _) = [t]
adjacentTypes t@(VarT _) = [t]
adjacentTypes _ = []
-}
