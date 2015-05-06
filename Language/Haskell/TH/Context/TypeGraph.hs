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
    , withTypeGraphInfo
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
import Control.Lens -- (makeLenses, view)
import Control.Monad (when)
import Control.Monad.Reader (MonadReader, ReaderT, runReaderT)
import Control.Monad.State (execStateT, modify, MonadState(get), StateT)
import Data.Default (Default(def))
import Data.Generics (Data, everywhere, mkT)
import Data.Graph (Graph, Vertex)
import Data.List as List (concatMap, intercalate, intersperse, map)
import Data.Map as Map (filter, findWithDefault, fromList, fromListWith, insert, insertWith,
                        keys, lookup, Map, map, mapKeys, mapWithKey, toList, update, alter)
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Set as Set (delete, empty, fromList, insert, map, member, null, Set, singleton, toList, union)
import Language.Haskell.Exts.Syntax ()
import Language.Haskell.TH -- (Con, Dec, nameBase, Type)
import Language.Haskell.TH.Context.Expand (E(E), expandType, runExpanded)
import Language.Haskell.TH.Context.Graph (GraphEdges, graphFromMap)
import Language.Haskell.TH.Context.Helpers (pprint', typeArity)
import Language.Haskell.TH.Desugar as DS (DsMonad)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.PprLib (hcat, ptext)
import Language.Haskell.TH.Syntax (Quasi(..))

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

instance Ppr TypeGraphEdges where
    ppr x =
        ptext $ intercalate "\n  " $
          "edges:" : (List.map
                       (\ (k, ks) -> intercalate "\n    " ((pprint' k ++ "->") : List.map pprint' (Set.toList ks)))
                       (Map.toList x))

instance Ppr (Set TypeGraphVertex) where
    ppr x = ptext (intercalate "\n  " ("vertices:" : List.map pprint' (Set.toList x)))

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

type TypeGraphEdges = GraphEdges TypeGraphVertex

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
      , _edges :: GraphEdges (E Type)
      -- The edges of the "has this subtype" graph.  A type has
      -- subtypes via either type application ('AppT'), field type
      -- ('StrictType', 'VarStrictType') or the 'VertexHint'
      -- mechanism.
      , _hints :: Map TypeGraphVertex [VertexHint]
      } deriving Show

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
      doInfo _tname (FamilyI _ _) = return () -- Not sure what to do here
      doInfo _ info = error $ "scanTypes: " ++ show info

      doDec :: Dec -> StateT (Set Type) m ()
      doDec (TySynD _ _ typ) = doType typ
      doDec (NewtypeD _ _ _ constr _) = doCon constr
      doDec (DataD _ _ _ constrs _) = mapM_ doCon constrs
      doDec dec = error $ "scanTypes: " ++ pprint' dec

      doCon :: Con -> StateT (Set Type) m ()
      doCon (ForallC _ _ con) = doCon con
      doCon (NormalC _ flds) = mapM_ doField (zip (List.map Left ([1..] :: [Int])) (List.map snd flds))
      doCon (RecC _ flds) = mapM_ doField (List.map (\ (fname, _, ftype) -> (Right fname, ftype)) flds)
      doCon (InfixC (_, lhs) _ (_, rhs)) = mapM_ doField [(Left 1, lhs), (Left 2, rhs)]

      doField :: (Either Int Name, Type) -> StateT (Set Type) m ()
      doField (_, ftyp) = doType ftyp

-- | Discover the types with all type synonyms fully expanded.
findExpanded :: DsMonad m => Set Type -> m (Map Type (E Type))
findExpanded types =
    execStateT (mapM (\typ -> expandType typ >>= \etyp -> modify (Map.insert typ etyp)) (Set.toList types)) mempty

-- | Discover the type synonyms
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

-- | Discover the field types
findFields :: DsMonad m => Set Type -> m (Map Type (Set (Name, Name, Either Int Name)))
findFields types =
    execStateT (mapM_ doType (Set.toList types)) mempty
    where
      doType (ConT name) = qReify name >>= doInfo
      doType (AppT typ1 typ2) = doType typ1 >> doType typ2
      doType _ = return ()

      doInfo (TyConI dec) = doDec dec
      doInfo _ = return ()

      doDec (NewtypeD _ tname _ constr _) = doCon tname constr
      doDec (DataD _ tname _ constrs _) = mapM_ (doCon tname) constrs
      doDec _ = return ()

      doCon tname (ForallC _ _ con) = doCon tname con
      doCon tname (NormalC cname flds) = mapM_ (doField tname cname) (zip (List.map Left ([1..] :: [Int])) (List.map snd flds))
      doCon tname (RecC cname flds) = mapM_ (doField tname cname) (List.map (\ (fname, _, ftype) -> (Right fname, ftype)) flds)
      doCon tname (InfixC (_, lhs) cname (_, rhs)) = mapM_ (doField tname cname) [(Left 1, lhs), (Left 2, rhs)]

      doField tname cname (fname, ftyp) = modify (Map.insertWith union ftyp (singleton (tname, cname, fname)))

-- | Discover the edges of the graph of the subtype relation.  Ignores SigT.
findEdges :: DsMonad m => Set Type -> m (GraphEdges Type)
findEdges types =
    execStateT (mapM_ doType (Set.toList types)) mempty
    where
      doType (ConT name) = qReify name >>= doInfo
      doType typ@(AppT typ1 typ2) = modify (Map.insertWith union typ (singleton typ1)) >> modify (Map.insertWith union typ (singleton typ2))
      doType _ = return ()

      doInfo (TyConI dec) = doDec dec
      doInfo _ = return ()

      doDec :: (DsMonad m, MonadState (GraphEdges Type) m) => Dec -> m ()
      doDec (TySynD tname _ typ') = modify (Map.insertWith union (ConT tname) (singleton typ'))
      doDec (NewtypeD _ tname _ constr _) = doCon tname constr
      doDec (DataD _ tname _ constrs _) = mapM_ (doCon tname) constrs
      doDec _ = return ()

      doCon :: (DsMonad m, MonadState (GraphEdges Type) m) => Name -> Con -> m ()
      doCon tname (ForallC _ _ con) = doCon tname con
      doCon tname (NormalC _ flds) = mapM_ (doField tname) (List.map snd flds)
      doCon tname (RecC _ flds) = mapM_ (doField tname) (List.map (\ (_, _, ftype) -> ftype) flds)
      doCon tname (InfixC (_, lhs) _ (_, rhs)) = mapM_ (doField tname) [lhs, rhs]

      doField :: (DsMonad m, MonadState (GraphEdges Type) m) => Name -> Type -> m ()
      doField tname ftyp = modify (Map.insertWith union (ConT tname) (singleton ftyp))

withTypeGraphInfo :: forall m a. DsMonad m => [(TypeGraphVertex, VertexHint)] -> [Type] -> ReaderT TypeGraphInfo m a -> m a
withTypeGraphInfo hintList types action = typeGraphInfo hintList types >>= runReaderT action

typeGraphInfo :: forall m. DsMonad m => [(TypeGraphVertex, VertexHint)] -> [Type] -> m TypeGraphInfo
typeGraphInfo hintList types = do
  let hintTypes = mapMaybe hintType hintList
  types' <- scanTypes (types ++ hintTypes)
  (ex :: Map Type (E Type)) <- findExpanded types'
  (sy :: Map (E Type) (Set Name)) <-
      -- Build the type synonym map and then expand the types in its
      -- keys.  This will collapse some of the nodes if they differed
      -- only in the use of synonyms.
      findSynonyms types' >>= return . Map.fromListWith union . List.map (\ (typ, names) -> (expand ex typ, names))  . Map.toList
  fl <- findFields types' >>= return . Map.fromListWith union . List.map (\ (typ, names) -> (expand ex typ, names))  . Map.toList
  ed <- findEdges types' >>= return . Map.fromListWith union . List.map (\ (typ, dests) -> (expand ex typ, Set.map (expand ex) dests)) . Map.toList
  let etypes' = Set.fromList $ List.map (expand ex) (Set.toList types')
  return $ TypeGraphInfo { _expanded = ex
                         , _synonyms = sy
                         , _fields = fl
                         , _typeSet = etypes'
                         , _edges = ed
                         , _hints =  Map.fromListWith (++) (List.map (\ (n, h) -> (n, [h])) hintList)
                         }
      where expand ex typ = let Just etyp = Map.lookup typ ex in etyp
            hintType :: (TypeGraphVertex, VertexHint) -> Maybe Type
            hintType (_, Divert x) = Just x
            hintType (_, Extra x) = Just x
            hintType _ = Nothing

-- | Build the edges of a graph whose nodes are expanded types
-- augmented with their known type synonyms and information about the
-- field name that contains the type.  Thus, each type node turns into
-- multiple augmented nodes, one for each field that contains that
-- type, and perhaps one without field information if the type appears
-- embedded in a type application or as a top level type.
typeGraphEdges :: forall m. (DsMonad m, MonadReader TypeGraphInfo m) => m TypeGraphEdges
typeGraphEdges = do
  execStateT (view typeSet >>= mapM_ doType . Set.toList) mempty
    where
      doType :: (E Type) -> StateT TypeGraphEdges m ()
      doType typ = typeNodes typ >>= mapM_ doNode

      doNode :: TypeGraphVertex -> StateT TypeGraphEdges m ()
      doNode node = do
        mp <- get
        case Map.lookup node mp of
          Just _ -> return () -- already visited
          Nothing -> Map.findWithDefault [] node <$> view hints >>= doHints node
      doHints node [] = do
        addNode node
        ((Set.toList  . Map.findWithDefault Set.empty (_etype node)) <$> view edges) >>= mapM_ (\typ' -> typeNodes typ' >>= mapM_ (addEdge node))
      doHints _node (Hidden : _) = return () -- this should be alone
      doHints node (Sink : _) = addNode node -- so should this
      doHints node (Normal : _) = doHints node []
      doHints node (Divert typ' : _) = do
        addNode node
        etyp <- expandType typ'
        -- By setting _field to Nothing here we make it possible for a
        -- Divert to the same type to work, as long as the _field was
        -- something before.
        let node' = node {_etype = etyp, _field = Nothing}
        when (node == node') (error $ "diverted to self: " ++ show node)
        addNode node'
        addEdge node node'
        doNode node'
      doHints node (Extra typ' : more) = do
        doHints node (Divert typ' : more)
        etyp <- expandType typ'
        let node' = node {_etype = etyp}
        doHints node' more

      addNode :: TypeGraphVertex -> StateT TypeGraphEdges m ()
      addNode node = modify $ Map.alter (maybe (Just Set.empty) Just) node

      addEdge :: TypeGraphVertex -> TypeGraphVertex -> StateT TypeGraphEdges m ()
      addEdge node node' | node == node' = return () -- Self nodes make no sense in a subtype graph
      addEdge node node' = modify $ Map.update (Just . Set.insert node') node

      typeNodes :: E Type -> StateT TypeGraphEdges m [TypeGraphVertex]
      typeNodes typ = do
        mainNode <- TypeGraphVertex
                      <$> pure Nothing
                      <*> ((fromMaybe Set.empty . Map.lookup typ) <$> view synonyms)
                      <*> pure typ
        fieldNodes <- (List.map (\ fld -> mainNode {_field = Just fld}) . Set.toList . Map.findWithDefault Set.empty typ) <$> view fields
        return $ mainNode : fieldNodes

-- | Return the set of types embedded in the given type.  This is just
-- the nodes of the type graph.  The type synonymes are expanded by the
-- th-desugar package to make them suitable for use as map keys.
typeGraphVertices :: forall m. (DsMonad m, MonadReader TypeGraphInfo m) => m (Set TypeGraphVertex)
typeGraphVertices = (Set.fromList . Map.keys) <$> typeGraphEdges

-- | Build a graph from the result of typeGraphEdges, each edge goes
-- from a type to one of the types it contains.  Thus, each edge
-- represents a primitive lens, and each path in the graph is a
-- composition of lenses.
typeGraph :: forall m node key. (DsMonad m, MonadReader TypeGraphInfo m, node ~ TypeGraphVertex, key ~ TypeGraphVertex) =>
                m (Graph, Vertex -> (node, key, [key]), key -> Maybe Vertex)
typeGraph = graphFromMap <$> typeGraphEdges

-- | Simplify a graph by throwing away the field information in each
-- node.  This means the nodes only contain the fully expanded Type
-- value (and any type synonyms.)
simpleEdges :: TypeGraphEdges -> TypeGraphEdges
simpleEdges = Map.mapWithKey Set.delete . Map.mapKeys simpleVertex . Map.map (Set.map simpleVertex)

simpleVertex :: TypeGraphVertex -> TypeGraphVertex
simpleVertex node = node {_field = Nothing}

-- | Find all the reachable type synonyms and return then in a Map.
typeSynonymMap :: forall m. (DsMonad m, MonadReader TypeGraphInfo m) => m (Map TypeGraphVertex (Set Name))
typeSynonymMap =
     (Map.filter (not . Set.null) .
      Map.fromList .
      List.map (\node -> (node, _syns node)) .
      Map.keys) <$> typeGraphEdges

typeSynonymMapSimple :: forall m. (DsMonad m, MonadReader TypeGraphInfo m) => m (Map (E Type) (Set Name))
typeSynonymMapSimple =
    simplify <$> typeSynonymMap
    where
      simplify :: Map TypeGraphVertex (Set Name) -> Map (E Type) (Set Name)
      simplify mp = Map.fromListWith Set.union (List.map (\ (k, a) -> (_etype k, a)) (Map.toList mp))
