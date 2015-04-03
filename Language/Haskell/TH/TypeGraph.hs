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
    ( Expanded(unExpanded)
    , expandTypes
    , expandType
    , unsafeExpanded
      -- * Subtype graph
    , typeGraphEdges
    , typeGraphEdgesPlus
    , subtypes
    ) where

import Debug.Trace

#if __GLASGOW_HASKELL__ < 709
import Control.Applicative
#endif
import Control.Monad.RWS (RWST)
import Control.Monad.Reader (ask, local, ReaderT, runReaderT)
import Control.Monad.State (evalStateT, execStateT, modify, MonadState(get), StateT)
import Control.Monad.Trans (lift)
import Control.Monad.Writer (MonadWriter(tell), WriterT(runWriterT))
import Data.Generics (Data, Typeable, everywhereM, mkM)
import Data.Graph (Graph, Vertex, graphFromEdges)
import Data.Map as Map (Map, insert, keys, lookup, toList, update)
import Data.Monoid (Monoid, mempty)
import Data.Set as Set (insert, Set, empty, fromList, toList)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH -- (Con, Dec, nameBase, Type)
import Language.Haskell.TH.Desugar as DS (DsMonad, dsType, expand, typeToTH)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.Syntax (Quasi(..))
import Language.Haskell.TH.Fold (decName, FieldType, foldCon, foldDec, {-constructorFields, foldName, foldType, fType',-} foldTypeP, prettyField)

-- | Mark a value that was returned by ExpandType.  The constructor is
-- not exported, so we know when we see it that it was produced in
-- this module.
newtype Expanded a = Expanded {unExpanded :: a} deriving (Eq, Ord, Show)

#ifdef PHANTOM
data Expanded = Expanded
data Unexpanded = Unexpanded

data TypeData status a = TypeData a
#endif

instance Ppr a => Ppr (Expanded a) where
    ppr = ppr . unExpanded

-- | The ubiquitous cheat.  Merging TypeGraph.hs into this module eliminates this.
unsafeExpanded :: a -> Expanded a
unsafeExpanded = Expanded

-- | Expand Type everywhere in x and wrap it in the Expanded constructor.  Note
-- that the everywhereM is unnecessary when @a ~ Type@ because expandType does
-- the everywhere itself.  But it is necessary for other argument types.
expandTypes :: (DsMonad m, Data a) => a -> m (Expanded a)
expandTypes x = Expanded <$> everywhereM (mkM expandType) x

expandType :: DsMonad m => Type -> m Type
expandType t = DS.typeToTH <$> (DS.dsType t >>= DS.expand)

type TypeGraph = Map (Expanded Type) (Set (Expanded Type))

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

-- | Return the set of (expanded) types embedded in the given type.
subtypes :: DsMonad m => [Expanded Type] -> m (Set (Expanded Type))
subtypes types = do
  (Set.fromList . Map.keys) <$> typeGraphEdges types

typeGraphEdges :: forall m. DsMonad m => [Expanded Type] -> m TypeGraph
typeGraphEdges = typeGraphEdgesPlus (\ _ -> return Vertex)

data VertexStatus
    = Vertex      -- ^ normal case
    | NoVertex    -- ^ exclude from graph
    | Sink        -- ^ out degree zero
    | Divert (Expanded Type) -- ^ send edge to an alternate type
    | Extra (Expanded Type)   -- ^ send edge to an additional type
    deriving Show

typeGraphEdgesPlus
    :: forall m. DsMonad m =>
       (Expanded Type -> m VertexStatus)
           -- ^ This function is applied to every expanded type before
           -- use, and the result is used instead.  If it returns
           -- NoVertex, no vertices or edges are added to the graph.
           -- If it returns Sink no outgoing edges are added.  The
           -- current use case Substitute is to see if there is an
           -- instance of class @View a b@ where @a@ is the type
           -- passed to @doType@, and replace it with @b@, and use the
           -- lens returned by @View's@ method to convert between @a@
           -- and @b@ (i.e. to implement the edge in the type graph.)
    -> [Expanded Type]
    -> m TypeGraph

typeGraphEdgesPlus augment types = do
  execStateT (mapM_ doNode types) mempty
    where
      doNode :: Expanded Type -> StateT TypeGraph m ()
      doNode typ = do
        mp <- get
        status <- lift (augment typ)
        case Map.lookup typ mp of
          Just _ -> return ()
          Nothing -> do
            trace ("doNode " ++ (unwords . words . show . ppr . unExpanded $ typ) ++ ", status=" ++ show status) (return ())
            case status of
              NoVertex -> return ()
              Sink -> addNode typ
              (Divert typ') -> addNode typ >> addEdge typ typ' >> doNode typ'
              (Extra typ') -> addNode typ >> doEdges (unExpanded typ) >> addEdge typ typ' >> doNode typ'
              Vertex -> addNode typ >> doEdges (unExpanded typ)

      addNode :: Expanded Type -> StateT TypeGraph m ()
      addNode typ = modify (Map.insert typ Set.empty)
      addEdge :: Expanded Type -> Expanded Type -> StateT TypeGraph m ()
      addEdge typ typ' = modify (Map.update (Just . Set.insert typ') typ)

      -- We are using Expanded constructor here unsafely - Be careful!
      doEdges :: Type -> StateT TypeGraph m ()
      doEdges typ@(ForallT _ _ typ') = addEdge (Expanded typ) (Expanded typ') >> doNode (Expanded typ')
      doEdges typ@(AppT container element) =
          addEdge (Expanded typ) (Expanded container) >> addEdge (Expanded typ) (Expanded element) >> doNode (Expanded container) >> doNode (Expanded element)
      doEdges typ@(ConT name) = do
        info <- qReify name
        case info of
          TyConI dec -> doDec dec
          _ -> return ()
          where
            doDec :: Dec -> StateT TypeGraph m ()
            doDec dec@(NewtypeD _ tname _ con _) = doCon tname dec con
            doDec dec@(DataD _ tname _ cons _) = mapM_ (doCon tname dec) cons
            doDec (TySynD _tname _tvars typ') = addEdge (Expanded typ) (Expanded typ') >> doNode (Expanded typ')
            doDec _ = return ()

            doCon :: Name -> Dec -> Con -> StateT TypeGraph m ()
            doCon tname dec (ForallC _ _ con) = doCon tname dec con
            doCon tname dec (NormalC cname fields) = mapM_ (doField tname dec cname) (zip (map Left ([1..] :: [Int])) (map snd fields))
            doCon tname dec (RecC cname fields) = mapM_ (doField tname dec cname) (map (\ (fname, _, typ') -> (Right fname, typ')) fields)
            doCon tname dec (InfixC (_, lhs) cname (_, rhs)) = mapM_ (doField tname dec cname) [(Left 1, lhs), (Left 2, rhs)]

            doField _tname _dec _cname (_fld, ftype) = addEdge (Expanded typ) (Expanded ftype) >> doNode (Expanded ftype)

      doEdges typ = return (trace ("Unrecognized type: " ++ show typ) ())

-- | Build a graph from the result of typeGraphEdgesPlus, its edges
-- represent the primitive lenses, and each path in the graph is a
-- composition of lenses.
subtypeGraph :: (DsMonad m, node ~ Expanded Type, key ~ Expanded Type) =>
                (Expanded Type -> m VertexStatus) -> [Expanded Type] -> m (Graph, Vertex -> (node, key, [key]), key -> Maybe Vertex)
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
