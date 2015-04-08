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
    ( Expanded(runExpanded)
    , expandTypes
    , expandType
    , unsafeExpanded
    , typeArity
      -- * Subtype graph
    , typeGraphEdges
    , VertexStatus(..)
    , subtypes
    , subtypeGraph
    ) where

import Debug.Trace

#if __GLASGOW_HASKELL__ < 709
import Control.Applicative
#endif
import Control.Monad.State (execStateT, modify, MonadState(get), StateT)
import Control.Monad.Trans (lift)
import Data.Generics (Data, everywhereM, mkM)
import Data.Graph (Graph, Vertex, graphFromEdges)
import Data.Map as Map (Map, insert, keys, lookup, toList, update)
import Data.Monoid (mempty)
import Data.Set as Set (insert, Set, empty, fromList, toList)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH -- (Con, Dec, nameBase, Type)
import Language.Haskell.TH.Desugar as DS (DsMonad, dsType, expand, typeToTH)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.Syntax (Quasi(..))

-- | Mark a value that was returned by ExpandType.  The constructor is
-- not exported, so we know when we see it that it was produced in
-- this module.
newtype Expanded a = Expanded {runExpanded :: a} deriving (Eq, Ord, Show)

instance Ppr a => Ppr (Expanded a) where
    ppr = ppr . runExpanded

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

-- | Return the set of (expanded) types embedded in the given type.
-- This is just the nodes of the type graph.
subtypes :: DsMonad m => [Expanded Type] -> m (Set (Expanded Type))
subtypes types = do
  (Set.fromList . Map.keys) <$> typeGraphEdges (const $ return Vertex) types

-- typeGraphEdges :: forall m. DsMonad m => [Expanded Type] -> m TypeGraph
-- typeGraphEdges = typeGraphEdgesPlus (\ _ -> return Vertex)

data VertexStatus
    = Vertex      -- ^ normal case
    | NoVertex    -- ^ exclude from graph
    | Sink        -- ^ out degree zero
    | Divert (Expanded Type) -- ^ send edge to an alternate type
    | Extra (Expanded Type)   -- ^ send edge to an additional type
    deriving Show

typeGraphEdges
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

typeGraphEdges augment types = do
  execStateT (mapM_ doNode types) mempty
    where
      doNode :: Expanded Type -> StateT TypeGraph m ()
      doNode typ = do
        mp <- get
        status <- lift (augment typ)
        case Map.lookup typ mp of
          Just _ -> return ()
          Nothing -> do
            trace ("doNode " ++ (unwords . words . show . ppr . runExpanded $ typ) ++ ", status=" ++ show status) (return ())
            case status of
              NoVertex -> return ()
              Sink -> addNode typ
              (Divert typ') -> addNode typ >> addEdge typ typ' >> doNode typ'
              (Extra typ') -> addNode typ >> doEdges (runExpanded typ) >> addEdge typ typ' >> doNode typ'
              Vertex -> addNode typ >> doEdges (runExpanded typ)

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

      doEdges typ = return (trace ("Unrecognized type: " ++ pprint' typ) ())

-- | Build a graph from the result of typeGraphEdgesPlus, its edges
-- represent the primitive lenses, and each path in the graph is a
-- composition of lenses.
subtypeGraph :: (DsMonad m, node ~ Expanded Type, key ~ Expanded Type) =>
                (Expanded Type -> m VertexStatus) -> [Expanded Type] -> m (Graph, Vertex -> (node, key, [key]), key -> Maybe Vertex)
subtypeGraph augment types = do
  typeGraphEdges augment types >>= return . graphFromEdges . triples
    where
      triples mp = map (\ (k, ks) -> (k, k, Set.toList ks)) $ Map.toList mp

typeArity :: Quasi m => Type -> m Int
typeArity (ForallT _ _ typ) = typeArity typ
typeArity (VarT _) = return 1
typeArity ListT = return 1
typeArity (TupleT n) = return n
typeArity (AppT t _) = typeArity t >>= \ n -> return $ n - 1
typeArity (ConT name) =
    do info <- qReify name
       case info of
         (TyConI dec) -> decArity dec
         (PrimTyConI _ _ _) -> return 0
         (FamilyI dec _) -> decArity dec
         _ -> error $ "typeArity - unexpected type: " ++ pprint name ++ " -> " ++ pprint' info
    where
      decArity (DataD _ _ vs _ _) = return $ length vs
      decArity (NewtypeD _ _ vs _ _) = return $ length vs
      decArity (TySynD _ vs t) = typeArity t >>= \ n -> return $ n + length vs
      decArity (FamilyD _ _ vs mk) = return $ {- not sure what to do with the kind mk here -} length vs
      decArity dec = error $ "decArity - unexpected: " ++ pprint' dec
typeArity typ = error $ "typeArity - unexpected type: " ++ pprint' typ

pprint' :: Ppr a => a -> [Char]
pprint' typ = unwords $ words $ pprint typ

{-
type FieldType = (Int, Either StrictType VarStrictType)

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

-- | Combine a decFn and a primFn to make a nameFn in the Quasi monad.
-- This is used to build the first argument to the foldType function
-- when we need to know whether the name refers to a declared or a
-- primitive type.
foldName :: Quasi m =>
            (Dec -> m r)
         -> (Name -> Int -> Bool -> m r)
         -> (Info -> m r)
         -> Name -> m r
foldName decFn primFn otherFn name = do
  info <- qReify name
  case info of
    (TyConI dec) ->
        decFn dec
    (PrimTyConI a b c) -> primFn a b c
    _ -> otherFn info

-- | Dispatch on the different constructors of the Dec type.
foldDec :: Monad m =>
           (Type -> m r)
        -> ([Con] -> m r)
        -> Dec -> m r
foldDec typeFn shapeFn dec =
    case dec of
      TySynD _name _ typ -> typeFn typ
      NewtypeD _ _ _ con _ -> shapeFn [con]
      DataD _ _ _ cons _ -> shapeFn cons
      _ -> error $ "foldDec - unexpected: " ++ show dec

decName :: Dec -> Name
decName (NewtypeD _ name _ _ _) = name
decName (DataD _ name _ _ _) = name
decName (TySynD name _ _) = name
decName x = error $ "decName - unimplemented: " ++ show x

-- | Deconstruct a constructor
foldCon :: (Name -> [FieldType] -> r) -> Con -> r
foldCon fldFn (NormalC name ts) = fldFn name $ zip [1..] (map Left ts)
foldCon fldFn (RecC name ts) = fldFn name (zip [1..] (map Right ts))
foldCon fldFn (InfixC t1 name t2) = fldFn name [(1, Left t1), (2, Left t2)]
foldCon fldFn (ForallC _ _ con) = foldCon fldFn con

prettyField :: FieldType -> String
prettyField fld = maybe (show (fPos fld)) nameBase (fName fld)

-- | Pure version of foldType.
foldTypeP :: (Name -> r) -> (Type -> Type -> r) -> r -> Type -> r
foldTypeP nfn afn ofn typ = runIdentity $ foldType (\ n -> Identity $ nfn n) (\ t1 t2 -> Identity $ afn t1 t2) (Identity ofn) typ

fPos :: FieldType -> Int
fPos (n, _) = n

fName :: FieldType -> Maybe Name
fName (_, (Left _)) = Nothing
fName (_, (Right (name, _, _))) = Just name

-- | Dispatch on the constructors of type Type.  This ignores the
-- "ForallT" constructor, it just uses the embeded Type field.
foldType :: Monad m => (Name -> m r) -> (Type -> Type -> m r) -> m r -> Type -> m r
foldType nfn afn ofn (ForallT _ _ typ) = foldType nfn afn ofn typ
foldType nfn _ _ (ConT name) = nfn name
foldType _ afn _ (AppT t1 t2) = afn t1 t2
foldType _ _ ofn _ = ofn
-}

{-
adjacentTypes :: DsMonad m => Type -> m (Type, [Type])
adjacentTypes (ForallT _ _ typ) = adjacentTypes typ
adjacentTypes (AppT t1 t2) = [t1, t2]
adjacentTypes t@(ConT _) = [t]
adjacentTypes t@(VarT _) = [t]
adjacentTypes _ = []
-}
