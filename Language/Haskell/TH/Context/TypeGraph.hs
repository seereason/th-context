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
module Language.Haskell.TH.Context.TypeGraph
    ( VertexHint(..)
    , TypeGraphVertex(..)
    , typeVertex
    , fieldVertex
    , TypeGraphInfo
    , hints, typeSet, edges, expanded
    , typeVertices
    , typeNames
    , typeGraphInfo
    , TypeGraphEdges
    , typeGraphEdges
    , typeGraphVertices
    , typeGraph
    , simpleVertex
    , simpleEdges
    , typeSynonymMap
    , typeSynonymMapSimple
    ) where

#if __GLASGOW_HASKELL__ < 709
import Control.Applicative
import Data.Monoid (mempty)
#endif
import Control.Lens (makeLenses, view)
import Control.Monad.Reader (MonadReader)
import Control.Monad.State (execStateT, modify, MonadState(get), StateT)
import Control.Monad.Trans (lift)
import Data.Default (Default(def))
import Data.Generics (Data, everywhere, mkT)
import Data.Graph (Graph, Vertex, graphFromEdges)
import Data.List as List (concatMap, intersperse, map)
import Data.Map as Map (Map, filter, findWithDefault, fromList, fromListWith, insert, insertWith,
                        keys, lookup, map, mapKeys, toList, update, alter)
import Data.Maybe (mapMaybe)
import Data.Set as Set (empty, fromList, insert, map, member, null, Set, singleton, toList, union)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH -- (Con, Dec, nameBase, Type)
import Language.Haskell.TH.Context.Expand (E(E), expandType, runExpanded)
import Language.Haskell.TH.Desugar as DS (DsMonad)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.PprLib (hcat, ptext)
import Language.Haskell.TH.Syntax (Quasi(..))

import Debug.Trace

-- | For simple type graphs always set _field and _synonyms to Nothing.
data TypeGraphVertex
    = TypeGraphVertex
      { _field :: Maybe (Name, Name, Either Int Name) -- ^ The record filed which contains this type
      , _syns :: Set Name -- ^ All the type synonyms that expand to this type
      , _etype :: E Type -- ^ The fully expanded type
      } deriving (Eq, Ord, Show)

instance Ppr TypeGraphVertex where
    ppr (TypeGraphVertex {_field = fld, _syns = ns, _etype = typ}) =
        hcat (ppr (unReify (runExpanded typ)) :
              case (fld, Set.toList ns) of
                 (Nothing, []) -> []
                 _ ->   [ptext " ("] ++
                        intersperse (ptext ", ")
                          (List.concatMap (\ n -> [ptext ("aka " ++ show (unReifyName n))]) (Set.toList ns) ++
                           maybe [] (\ f -> [ptext (printField f)]) fld) ++
                        [ptext ")"])
        where
          printField :: (Name, Name, Either Int Name) -> String
          printField (tname, cname, field) =
              "field " ++
              show (unReifyName tname) ++ "." ++
              either (\ n -> show (unReifyName cname) ++ "[" ++ show n ++ "]") (\ f -> show (unReifyName f)) field

          unReify :: Data a => a -> a
          unReify = everywhere (mkT unReifyName)

          unReifyName :: Name -> Name
          unReifyName = mkName . nameBase

-- | Build a TypeGraphVertex from an unexpanded type.  This records the
-- type synonyms we expand to reach the "real" type.
typeVertex :: forall m. DsMonad m => Type -> m TypeGraphVertex
typeVertex typ =
    case typ of
      (ConT name) -> doName name -- special case to catch top level type synonyms.  Others are removed by expandType below.
      _ -> doType typ
    where
      -- What happens to ForallT types here?
      doType :: Type -> m TypeGraphVertex
      doType typ' = expandType typ' >>= \(etype :: E Type) -> return $ TypeGraphVertex {_field = Nothing, _syns = Set.empty, _etype = etype}
      doName name = runQ (reify name) >>= doInfo name
      doInfo name (TyConI dec) = doDec name dec
      doInfo name _ = doType (ConT name)
      doDec _ (TySynD name _ typ') = doType typ' >>= \node -> return $ node {_syns = Set.insert name (_syns node)}
      doDec name _dec = doType (ConT name)

-- | Build a TypeGraphVertex for a field of a record.  This calls
-- 'typeVertex' and then sets the _field value.
fieldVertex :: forall m. DsMonad m => Type -> (Name, Name, Either Int Name) -> m TypeGraphVertex
fieldVertex typ field = typeVertex typ >>= \node -> return $ node {_field = Just field}

type TypeGraphEdges = Map TypeGraphVertex (Set TypeGraphVertex)

-- | When a VertexHint value is associated with a Type it describes
-- alterations in the type graph from the usual default.
data VertexHint
    = Normal      -- ^ normal case
    | Hidden      -- ^ don't create this vertex, no in or out edges
    | Sink        -- ^ out degree zero - don't create any out edges
    | Divert Type -- ^ replace all out edges with an edge to an alternate type
    | Extra Type  -- ^ add an extra out edge to the given type
    deriving (Eq, Ord, Show)

instance Default VertexHint where
    def = Normal

-- | Information collected about the graph implied by the structure of
-- one or more 'Type' values.
data TypeGraphInfo
    = TypeGraphInfo
      { _typeSet :: Set (E Type)
      -- All the types encountered, including embedded types such as the
      -- 'Maybe' and the 'Int' in @Maybe Int@.
      , _expanded :: Map Type (E Type)
      -- The types with all type synonyms replaced with their expansions.
      , _synonyms :: Map (E Type) (Set Name)
      -- The names of all the type synonyms which expand to a type
      , _fields :: Map (E Type) (Set (Name, Name, Either Int Name))
      -- Information about record fields which contain a given type
      , _edges :: Map (E Type) (Set (E Type))
      -- The edges of the "has this subtype" graph.  A type has
      -- subtypes via either type application ('AppT'), field type
      -- ('StrictType', 'VarStrictType') or the 'VertexHint'
      -- mechanism.
      , _hints :: Map TypeGraphVertex [VertexHint]
      }

$(makeLenses ''TypeGraphInfo)

-- | Find all the 'TypeGraphVertex' that involve this type.  All
-- returned nodes will have the same set of type synonyms, but there
-- will be one for each field where the type appears and one with
-- field Nothing.
typeVertices :: MonadReader TypeGraphInfo m => E Type -> m (Set TypeGraphVertex)
typeVertices typ = do
  syns <- view synonyms >>= return . Map.findWithDefault Set.empty typ
  flds <- view fields >>= return . Set.insert Nothing . Set.map Just . Map.findWithDefault Set.empty typ
  return $ Set.map (\ f -> TypeGraphVertex {_etype = typ, _syns = syns, _field = f}) flds

-- | Return the set of 'Name' of a type's synonyms, plus the name (if
-- any) used in its data declaration.  Note that this might return the
-- empty set.
typeNames :: TypeGraphVertex -> Set Name
typeNames (TypeGraphVertex {_etype = E (ConT tname), _syns = s}) = Set.insert tname s
typeNames (TypeGraphVertex {_syns = s}) = s

-- | This is now the only function that actually recurses through the
-- type structure.  It collects the set of all accessable types.
scanTypes :: forall m. DsMonad m => [Type] -> m (Set Type)
scanTypes types =
    execStateT (mapM doType types) mempty
    where
      doType :: Type -> StateT (Set Type) m ()
      doType typ = do
        (s :: Set Type) <- get
        case Set.member typ s of
          True -> return ()
          False -> modify (Set.insert typ) >> doType' typ

      doType' :: Type -> StateT (Set Type) m ()
      doType' (ConT name) = qReify name >>= doInfo name
      doType' (AppT typ1 typ2) = doType typ1 >> doType typ2
      doType' ListT = return ()
      doType' (VarT _) = return ()
      doType' (TupleT _) = return ()
      doType' typ = error $ "scanTypes: " ++ show typ

      doInfo :: Name -> Info -> StateT (Set Type) m ()
      doInfo _tname (TyConI dec) = doDec dec
      doInfo _tname (PrimTyConI _ _ _) = return ()
      doInfo _ info = error $ "scanTypes: " ++ show info

      doDec :: Dec -> StateT (Set Type) m ()
      doDec (TySynD _ _ typ) = doType typ
      doDec (NewtypeD _ _ _ con _) = doCon con
      doDec (DataD _ _ _ cons _) = mapM_ doCon cons
      doDec dec = error $ "scanTypes: " ++ pprint dec

      doCon :: Con -> StateT (Set Type) m ()
      doCon (ForallC _ _ con) = doCon con
      doCon (NormalC _ flds) = mapM_ doField (zip (List.map Left ([1..] :: [Int])) (List.map snd flds))
      doCon (RecC _ flds) = mapM_ doField (List.map (\ (fname, _, ftype) -> (Right fname, ftype)) flds)
      doCon (InfixC (_, lhs) _ (_, rhs)) = mapM_ doField [(Left 1, lhs), (Left 2, rhs)]

      doField :: (Either Int Name, Type) -> StateT (Set Type) m ()
      doField (_, ftyp) = doType ftyp

findExpanded :: DsMonad m => Set Type -> m (Map Type (E Type))
findExpanded types =
    execStateT (mapM (\typ -> expandType typ >>= \etyp -> modify (Map.insert typ etyp)) (Set.toList types)) mempty

findSynonyms :: DsMonad m => Set Type -> m (Map Type (Set Name))
findSynonyms types =
    execStateT (mapM_ doType (Set.toList types)) mempty
    where
      doType (ConT name) = qReify name >>= doInfo
      doType (AppT typ1 typ2) = doType typ1 >> doType typ2
      doType _ = return ()
      doInfo (TyConI dec) = doDec dec
      doInfo _ = return ()
      doDec (TySynD tname _ typ) = modify (Map.insertWith union typ (singleton tname))
      doDec _ = return ()

findFields :: DsMonad m => Set Type -> m (Map Type (Set (Name, Name, Either Int Name)))
findFields types =
    execStateT (mapM_ doType (Set.toList types)) mempty
    where
      doType (ConT name) = qReify name >>= doInfo
      doType (AppT typ1 typ2) = doType typ1 >> doType typ2
      doType _ = return ()

      doInfo (TyConI dec) = doDec dec
      doInfo _ = return ()

      doDec (NewtypeD _ tname _ con _) = doCon tname con
      doDec (DataD _ tname _ cons _) = mapM_ (doCon tname) cons
      doDec _ = return ()

      doCon tname (ForallC _ _ con) = doCon tname con
      doCon tname (NormalC cname flds) = mapM_ (doField tname cname) (zip (List.map Left ([1..] :: [Int])) (List.map snd flds))
      doCon tname (RecC cname flds) = mapM_ (doField tname cname) (List.map (\ (fname, _, ftype) -> (Right fname, ftype)) flds)
      doCon tname (InfixC (_, lhs) cname (_, rhs)) = mapM_ (doField tname cname) [(Left 1, lhs), (Left 2, rhs)]

      doField tname cname (fname, ftyp) = modify (Map.insertWith union ftyp (singleton (tname, cname, fname)))

findEdges :: DsMonad m => Set Type -> m (Map Type (Set Type))
findEdges types =
    execStateT (mapM_ doType (Set.toList types)) mempty
    where
      doType (ConT name) = qReify name >>= doInfo
      doType typ@(AppT typ1 typ2) = modify (Map.insertWith union typ (singleton typ1)) >> modify (Map.insertWith union typ (singleton typ2))
      doType _ = return ()

      doInfo (TyConI dec) = doDec dec
      doInfo _ = return ()

      doDec :: (DsMonad m, MonadState (Map Type (Set Type)) m) => Dec -> m ()
      doDec (TySynD tname _ typ') = modify (Map.insertWith union (ConT tname) (singleton typ'))
      doDec (NewtypeD _ tname _ con _) = doCon tname con
      doDec (DataD _ tname _ cons _) = mapM_ (doCon tname) cons
      doDec _ = return ()

      doCon :: (DsMonad m, MonadState (Map Type (Set Type)) m) => Name -> Con -> m ()
      doCon tname (ForallC _ _ con) = doCon tname con
      doCon tname (NormalC _ flds) = mapM_ (doField tname) (List.map snd flds)
      doCon tname (RecC _ flds) = mapM_ (doField tname) (List.map (\ (_, _, ftype) -> ftype) flds)
      doCon tname (InfixC (_, lhs) _ (_, rhs)) = mapM_ (doField tname) [lhs, rhs]

      doField :: (DsMonad m, MonadState (Map Type (Set Type)) m) => Name -> Type -> m ()
      doField tname ftyp = modify (Map.insertWith union (ConT tname) (singleton ftyp))

typeGraphInfo :: forall m. DsMonad m => [(TypeGraphVertex, VertexHint)] -> [Type] -> m TypeGraphInfo
typeGraphInfo hs types = do
  let hintTypes = mapMaybe hintType hs
  types' <- scanTypes (types ++ hintTypes)
  (ex :: Map Type (E Type)) <- findExpanded types'
  (sy :: Map (E Type) (Set Name)) <- findSynonyms types' >>= return . Map.fromListWith union . List.map (\ (typ, names) -> let Just etyp = Map.lookup typ ex in (etyp, names))  . Map.toList
  fl <- findFields types' >>= return . Map.fromListWith union . List.map (\ (typ, names) -> (exptyp ex typ, names))  . Map.toList
  ed <- findEdges types' >>= return . Map.fromListWith union . List.map (\ (typ, types'') -> (exptyp ex typ, Set.map (exptyp ex) types'')) . Map.toList
{-
  hs <- let mp = Map.map sequence (Map.fromListWith (++) (List.map (\ (node, hint) -> (node, [hint])) hints)) in
        \node -> Map.findWithDefault (return []) node mp
-}
  let etypes' = Set.fromList $ List.map (exptyp ex) (Set.toList types')
  return $ TypeGraphInfo { _expanded = ex
                         , _synonyms = sy
                         , _fields = fl
                         , _typeSet = etypes'
                         , _edges = ed
                         , _hints =  Map.fromListWith (++) (List.map (\ (n, h) -> (n, [h])) hs)
                         }
      where exptyp ex typ = let Just etyp = Map.lookup typ ex in etyp
            hintType :: (TypeGraphVertex, VertexHint) -> Maybe Type
            hintType (_, Divert x) = Just x
            hintType (_, Extra x) = Just x
            hintType _ = Nothing

-- | Return the set of types embedded in the given type.  This is just
-- the nodes of the type graph.  The type synonymes are expanded by the
-- th-desugar package to make them suitable for use as map keys.
typeGraphVertices :: forall m. DsMonad m =>
                     (TypeGraphVertex -> m VertexHint)
                  -> [Type]
                  -> m (Set TypeGraphVertex)
typeGraphVertices augment types =
    (Set.fromList . Map.keys) <$> (typeGraphEdges augment types :: m TypeGraphEdges)

typeGraphEdges
    :: forall m. DsMonad m =>
       (TypeGraphVertex -> m VertexHint)
           -- ^ This function is used to obtain hints about the graph
           -- structure around a given node.  If it returns NoVertex,
           -- no vertices or edges are added to the graph.  If it
           -- returns Sink no outgoing edges are added.  The current
           -- use case Substitute is to see if there is an instance of
           -- class @View a b@ where @a@ is the type passed to
           -- @doType@, and replace it with @b@, and use the lens
           -- returned by @View's@ method to convert between @a@ and
           -- @b@ (i.e. to implement the edge in the type graph.)
    -> [Type]
    -> m TypeGraphEdges
typeGraphEdges augment types = do
  execStateT (mapM_ (\ typ -> typeVertex typ >>= doVertex Set.empty) types) mempty
    where
      doVertex :: Set (TypeGraphVertex, VertexHint) -> TypeGraphVertex -> StateT TypeGraphEdges m ()
      doVertex used node = do
        (mp :: TypeGraphEdges) <- get
        status <- lift (augment node)
        case Map.lookup node mp of
          Just _ -> return ()
          Nothing ->
            case status of
              _ | Set.member (node, status) used -> addVertex >> doEdges node
              Normal -> addVertex >> doEdges node
              Hidden -> return ()
              Sink -> addVertex
              hint@(Divert typ') -> typeVertex typ' >>= \node' -> addVertex >> addEdge node' >> doVertex (Set.insert (node, hint) used) node'
              (Extra typ') -> typeVertex typ' >>= \node' -> addVertex >> doEdges node >> addEdge node' >> doVertex (Set.insert (node, status) used) node'
        where
          addVertex :: StateT TypeGraphEdges m ()
          -- addVertex a = expandType a >>= \ a' -> modify $ Map.insertWith (flip const) a' Set.empty
          addVertex = modify $ Map.alter (maybe (Just Set.empty) Just) node
          addEdge :: TypeGraphVertex -> StateT TypeGraphEdges m ()
          addEdge node' = modify $ Map.update (Just . Set.insert node') node

          -- Find and add the out edges from a node.
          doEdges :: TypeGraphVertex -> StateT TypeGraphEdges m ()
          -- Do we treat this as a distinct type?
          doEdges (TypeGraphVertex {_etype = E (ForallT _ _ typ')}) =
              -- typeGraphVertex (_field node) (_synonyms node) typ' >>= \node' -> addEdge node' >> doVertex node'
              doEdges (node {_etype = E typ'})
          doEdges (TypeGraphVertex {_etype = E (AppT container element)}) = do
            cnode <- typeVertex container
            enode <- typeVertex element
            addEdge cnode
            addEdge enode
            doVertex used cnode
            doVertex used enode
          doEdges (TypeGraphVertex {_etype = E (ConT name)}) = do
            info <- qReify name
            case info of
              TyConI dec -> doDec dec
              _ -> return ()
              where
                doDec :: Dec -> StateT TypeGraphEdges m ()
                doDec dec@(NewtypeD _ tname _ con _) = doCon tname dec con
                doDec dec@(DataD _ tname _ cons _) = mapM_ (doCon tname dec) cons
                doDec (TySynD _tname _tvars typ') = trace "unexpected synonym" (return ()) >> typeVertex typ' >>= \node' -> doVertex used node'
                doDec _ = return ()

                doCon :: Name -> Dec -> Con -> StateT TypeGraphEdges m ()
                doCon tname dec (ForallC _ _ con) = doCon tname dec con
                doCon tname dec (NormalC cname flds) = mapM_ (doField tname dec cname) (zip (List.map Left ([1..] :: [Int])) (List.map snd flds))
                doCon tname dec (RecC cname flds) = mapM_ (doField tname dec cname) (List.map (\ (fname, _, typ') -> (Right fname, typ')) flds)
                doCon tname dec (InfixC (_, lhs) cname (_, rhs)) = mapM_ (doField tname dec cname) [(Left 1, lhs), (Left 2, rhs)]

                doField :: Name -> Dec -> Name -> (Either Int Name, Type) -> StateT TypeGraphEdges m ()
                doField tname _dec cname (field, ftype) = fieldVertex ftype (tname, cname, field) >>= \node' -> addEdge node' >> doVertex used node'

          doEdges _ = return ({-trace ("Unrecognized type: " ++ pprint' typ)-} ())

-- | Build a graph from the result of typeGraphEdges, each edge goes
-- from a type to one of the types it contains.  Thus, each edge
-- represents a primitive lens, and each path in the graph is a
-- composition of lenses.
typeGraph :: forall m node key. (DsMonad m, node ~ TypeGraphVertex, key ~ TypeGraphVertex) =>
                (TypeGraphVertex -> m VertexHint) -> [Type] -> m (Graph, Vertex -> (node, key, [key]), key -> Maybe Vertex)
typeGraph augment types = do
  typeGraphEdges augment types >>= return . graphFromEdges . triples
    where
      triples :: Map TypeGraphVertex (Set TypeGraphVertex) -> [(TypeGraphVertex, TypeGraphVertex, [TypeGraphVertex])]
      triples mp = List.map (\ (k, ks) -> (k, k, Set.toList ks)) $ Map.toList mp

-- | Simplify a graph by throwing away the field and type synonym
-- information in each node.  This means the nodes only contain the
-- fully expanded Type value.
simpleEdges :: TypeGraphEdges -> TypeGraphEdges
simpleEdges = Map.mapKeys simpleVertex . Map.map (Set.map simpleVertex)

simpleVertex :: TypeGraphVertex -> TypeGraphVertex
simpleVertex node = node {_syns = Set.empty, _field = Nothing}

-- | Find all the reachable type synonyms and return then in a Map.
typeSynonymMap :: forall m. DsMonad m => (TypeGraphVertex -> m VertexHint) -> [Type] -> m (Map TypeGraphVertex (Set Name))
typeSynonymMap augment types =
     (Map.filter (not . Set.null) .
      Map.fromList .
      List.map (\node -> (node, _syns node)) .
      Map.keys) <$> typeGraphEdges augment types

typeSynonymMapSimple :: forall m. DsMonad m => (TypeGraphVertex -> m VertexHint) -> [Type] -> m (Map (E Type) (Set Name))
typeSynonymMapSimple augment types =
    simplify <$> typeSynonymMap augment types
    where
      simplify :: Map TypeGraphVertex (Set Name) -> Map (E Type) (Set Name)
      simplify mp = Map.fromListWith Set.union (List.map (\ (k, a) -> (_etype k, a)) (Map.toList mp))
