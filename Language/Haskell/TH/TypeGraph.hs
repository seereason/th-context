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
    ( VertexStatus(..)
    , typeGraphEdges
    , typeGraphVertices
    , typeGraph
    ) where

#if __GLASGOW_HASKELL__ < 709
import Control.Applicative
#endif
import Control.Monad.State (execStateT, modify, MonadState(get), StateT)
import Control.Monad.Trans (lift)
import Data.Default (Default(def))
import Data.Graph (Graph, Vertex, graphFromEdges)
import Data.Map as Map (Map, keys, lookup, toList, update, alter)
import Data.Monoid (mempty)
import Data.Set as Set (insert, Set, empty, fromList, toList)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH -- (Con, Dec, nameBase, Type)
import Language.Haskell.TH.Desugar as DS (DsMonad)
import Language.Haskell.TH.Expand (Expanded, markExpanded, runExpanded)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.Syntax (Quasi(..))

type TypeGraphEdges typ = Map typ (Set typ)

-- | When a VertexStatus value is associated with a Type it describes
-- alterations in the type graph from the usual default.
data VertexStatus typ
    = Vertex      -- ^ normal case
    | NoVertex    -- ^ exclude this type from the graph
    | Sink        -- ^ out degree zero - don't create any outgoing edges
    | Divert typ  -- ^ replace all outgoing edges with an edge to an alternate type
    | Extra typ   -- ^ add an extra outgoing edge to the given type
    deriving Show

instance Default (VertexStatus typ) where
    def = Vertex

-- | Return the set of types embedded in the given type.  This is just
-- the nodes of the type graph.  The type aliases are expanded by the
-- th-desugar package to make them suitable for use as map keys.
typeGraphVertices :: (DsMonad m, Expanded Type typ, Ord typ, Show typ) =>
                     (typ -> m (VertexStatus typ))
                  -> [typ]
                  -> m (Set typ)
typeGraphVertices augment types =
    (Set.fromList . Map.keys) <$> typeGraphEdges augment types

typeGraphEdges
    :: forall m typ. (DsMonad m, Expanded Type typ, Ord typ, Show typ) =>
       (typ -> m (VertexStatus typ))
           -- ^ This function is applied to every expanded type before
           -- use, and the result is used instead.  If it returns
           -- NoVertex, no vertices or edges are added to the graph.
           -- If it returns Sink no outgoing edges are added.  The
           -- current use case Substitute is to see if there is an
           -- instance of class @View a b@ where @a@ is the type
           -- passed to @doType@, and replace it with @b@, and use the
           -- lens returned by @View's@ method to convert between @a@
           -- and @b@ (i.e. to implement the edge in the type graph.)
    -> [typ]
    -> m (TypeGraphEdges typ)

typeGraphEdges augment types = do
  execStateT (mapM_ doNode types) mempty
    where
      doNode :: typ -> StateT (TypeGraphEdges typ) m ()
      doNode typ = do
        mp <- get
        status <- lift (augment typ)
        case Map.lookup typ mp of
          Just _ -> return ()
          Nothing ->
            case status of
              NoVertex -> return ()
              Sink -> addNode typ
              (Divert typ') -> addNode typ >> addEdge typ typ' >> doNode typ'
              (Extra typ') -> addNode typ >> doEdges (runExpanded typ) >> addEdge typ typ' >> doNode typ'
              Vertex -> addNode typ >> doEdges (runExpanded typ)

      addNode :: typ -> StateT (TypeGraphEdges typ) m ()
      -- addNode a = expandType a >>= \ a' -> modify $ Map.insertWith (flip const) a' Set.empty
      addNode a = modify $ Map.alter (maybe (Just Set.empty) Just) a
      addEdge :: typ -> typ -> StateT (TypeGraphEdges typ) m ()
      addEdge a b = modify $ Map.update (Just . Set.insert b) a

      -- We know that the Type argument is actually fully expanded here.
      doEdges :: Type -> StateT (TypeGraphEdges typ) m ()
      doEdges typ@(ForallT _ _ typ') = addEdge (markExpanded typ) (markExpanded typ') >> doNode (markExpanded typ')
      doEdges typ@(AppT container element) =
          addEdge (markExpanded typ) (markExpanded container) >>
          addEdge (markExpanded typ) (markExpanded element) >>
          doNode (markExpanded container) >>
          doNode (markExpanded element)
      -- Can this happen if typ is fully expanded?
      doEdges typ@(ConT name) = do
        info <- qReify name
        case info of
          TyConI dec -> doDec dec
          _ -> return ()
          where
            doDec :: Dec -> StateT (TypeGraphEdges typ) m ()
            doDec dec@(NewtypeD _ tname _ con _) = doCon tname dec con
            doDec dec@(DataD _ tname _ cons _) = mapM_ (doCon tname dec) cons
            doDec (TySynD _tname _tvars typ') = addEdge (markExpanded typ) (markExpanded typ') >> doNode (markExpanded typ')
            doDec _ = return ()

            doCon :: Name -> Dec -> Con -> StateT (TypeGraphEdges typ) m ()
            doCon tname dec (ForallC _ _ con) = doCon tname dec con
            doCon tname dec (NormalC cname fields) = mapM_ (doField tname dec cname) (zip (map Left ([1..] :: [Int])) (map (markExpanded . snd) fields))
            doCon tname dec (RecC cname fields) = mapM_ (doField tname dec cname) (map (\ (fname, _, typ') -> (Right fname, markExpanded typ')) fields)
            doCon tname dec (InfixC (_, lhs) cname (_, rhs)) = mapM_ (doField tname dec cname) [(Left 1, markExpanded lhs), (Left 2, markExpanded rhs)]

            doField _tname _dec _cname (_fld, ftype) = addEdge (markExpanded typ) ftype >> doNode ftype

      doEdges _typ = return ({-trace ("Unrecognized type: " ++ pprint' typ)-} ())

-- | Build a graph from the result of typeGraphEdges, each edge goes
-- from a type to one of the types it contains.  Thus, each edge
-- represents a primitive lens, and each path in the graph is a
-- composition of lenses.
typeGraph :: (DsMonad m, Expanded Type typ, Ord typ, Show typ, node ~ typ, key ~ typ) =>
                (typ -> m (VertexStatus typ)) -> [typ] -> m (Graph, Vertex -> (node, key, [key]), key -> Maybe Vertex)
typeGraph augment types = do
  typeGraphEdges augment types >>= return . graphFromEdges . triples
    where
      triples mp = map (\ (k, ks) -> (k, k, Set.toList ks)) $ Map.toList mp

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
