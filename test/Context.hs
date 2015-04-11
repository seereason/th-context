{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wall #-}
module Context where

import Control.DeepSeq
import Data.Array.IArray
import Data.Array.Unboxed
import Data.List as List (map, null)
import Data.Map as Map (Map, map, mapKeys, toList, fromList)
import Data.Set as Set (Set, fromList)
import Language.Haskell.TH
import Language.Haskell.TH.Context (reifyInstancesWithContext, runContext)
import Language.Haskell.TH.Context.Expand (E, expandType, runExpanded)
import Language.Haskell.TH.Context.Helpers (pprint')
import Language.Haskell.TH.Context.Simple (missingInstances, simpleMissingInstanceTest)
import Language.Haskell.TH.Desugar (withLocalDeclarations)
import Language.Haskell.TH.Syntax (Lift(lift), Quasi(qReifyInstances))
import System.Exit (ExitCode)
import Test.Hspec hiding (runIO)
import Test.Hspec.Core.Spec (SpecM)

import Common

tests :: SpecM () ()
tests = do
  it "can run the Q monad" $ do
     typ <- runQ [t|Int|]
     typ `shouldBe` ConT ''Int

  -- String becomes [Char], Maybe String becomes Maybe [Char], Maybe (Maybe String) becomes Maybe (Maybe [Char])
  it "expands types as expected" $ do
     (expected :: [Type]) <- runQ (sequence [ [t| [Char] |], [t|Maybe [Char] |], [t|Maybe (Maybe [Char])|] ])
     let expanded = $(withLocalDeclarations [] (do (types :: [E Type]) <- runQ (sequence [ [t|String|], [t|Maybe String|], [t|Maybe (Maybe String)|] ]) >>= mapM expandType
                                                   runQ . lift . List.map runExpanded $ types))
     expanded `shouldBe` expected

  -- Test the behavior of th-reify-many
  it "can tell that there is an instance NFData Char" $
     $(do insts <- qReifyInstances ''NFData [ConT ''Char]
          lift $ List.map (pprint' . unReify) insts) `shouldBe` (["instance NFData Char"] :: [String])

  it "can tell that there is no instance NFData ExitCode" $
     $(do insts <- qReifyInstances ''NFData [ConT ''ExitCode]
          lift $ List.map (pprint' . unReify) insts) `shouldBe` ([] :: [String])

  it "can tell that an instance hasn't been declared" $
     $(missingInstances simpleMissingInstanceTest [d|instance NFData ExitCode|] >>= lift . List.null)
          `shouldBe` False

  it "can tell that an instance has been declared" $
     $(missingInstances simpleMissingInstanceTest [d|instance NFData Char|] >>= lift . List.null)
          `shouldBe` True

-- GHCs older than 7.10 that haven't been specially patched cannot deal with
-- the unbound type variable a.
#if __GLASGOW_HASKELL__ >= 709 || defined(PATCHED_FOR_TRAC_9262)
  -- Doesn't actually use any th-context functions, but it tests
  -- for trac 9262.
  it "can find all the Eq instances" $ do
     (setDifferences
        (Set.fromList
           $(do insts <- qReifyInstances ''Eq [VarT (mkName "a")]
                lift (List.map (pprint' . unReify) insts)))
        eqInstances)
      `shouldBe` noDifferences

  it "Is using a ghc without bug https://ghc.haskell.org/trac/ghc/ticket/9262 (i.e. either 7.10 or a custom patched ghc)" $ do
     $(do insts <- qReifyInstances ''Eq [ListT `AppT` VarT (mkName "a")]
          -- runIO $ putStrLn (pprint insts)
          lift "ok")
         `shouldBe` "ok"

  it "can match all the Enum instances" $ do
     (\ (insts, _pairs) -> (setDifferences (Set.fromList insts) enumInstances))
             $(do (insts, mp) <- runContext (reifyInstancesWithContext ''Enum [VarT (mkName "a")])
                  lift (List.map (pprint' . unReify) insts,
                        Map.toList (Map.map (List.map (pprint' . unReify)) (Map.mapKeys (pprint' . unReify . runExpanded) mp))))
          `shouldBe` noDifferences

  it "can handle multi param class IArray" $ do
     (\ (insts, pairs) -> (setDifferences (Set.fromList insts) arrayInstances,
                           Map.map Set.fromList (Map.fromList pairs)))
             -- Unquote the template haskell Q monad expression
             $(do -- Run instances and save the result and the state monad result
                  (insts, mp) <- runContext (reifyInstancesWithContext ''IArray [ConT ''UArray, VarT (mkName "a")])
                  -- Convert to lists of text so we can lift out of Q
                  lift (List.map (pprint' . unReify) insts,
                        Map.toList (Map.map (List.map (pprint' . unReify)) (Map.mapKeys (pprint' . unReify . runExpanded) mp))))
          `shouldBe` (noDifferences,
                      -- I don't think this is right
                      Map.fromList [{-("Data.Array.Base.IArray Data.Array.Base.UArray a", arrayInstances)-}] :: Map String (Set String))
#endif

eqInstances :: Set String
eqInstances =
    Set.fromList
    [ -- "instance (Eq (f p), Eq (g p)) => Eq (:*: f g p)",
      -- "instance (Eq (f p), Eq (g p)) => Eq (:+: f g p)",
      "instance (Eq a, Eq b) => Eq ((a, b))",
      "instance (Eq a, Eq b) => Eq (Either a b)",
      "instance (Eq a, Eq b, Eq c) => Eq ((a, b, c))",
      "instance (Eq a, Eq b, Eq c, Eq d) => Eq ((a, b, c, d))",
      "instance (Eq a, Eq b, Eq c, Eq d, Eq e) => Eq ((a, b, c, d, e))",
      "instance (Eq a, Eq b, Eq c, Eq d, Eq e, Eq f) => Eq ((a, b, c, d, e, f))",
      "instance (Eq a, Eq b, Eq c, Eq d, Eq e, Eq f, Eq g) => Eq ((a, b, c, d, e, f, g))",
      "instance (Eq a, Eq b, Eq c, Eq d, Eq e, Eq f, Eq g, Eq h) => Eq ((a, b, c, d, e, f, g, h))",
      "instance (Eq a, Eq b, Eq c, Eq d, Eq e, Eq f, Eq g, Eq h, Eq i) => Eq ((a, b, c, d, e, f, g, h, i))",
      "instance (Eq a, Eq b, Eq c, Eq d, Eq e, Eq f, Eq g, Eq h, Eq i, Eq j) => Eq ((a, b, c, d, e, f, g, h, i, j))",
      "instance (Eq a, Eq b, Eq c, Eq d, Eq e, Eq f, Eq g, Eq h, Eq i, Eq j, Eq k) => Eq ((a, b, c, d, e, f, g, h, i, j, k))",
      "instance (Eq a, Eq b, Eq c, Eq d, Eq e, Eq f, Eq g, Eq h, Eq i, Eq j, Eq k, Eq l) => Eq ((a, b, c, d, e, f, g, h, i, j, k, l))",
      "instance (Eq a, Eq b, Eq c, Eq d, Eq e, Eq f, Eq g, Eq h, Eq i, Eq j, Eq k, Eq l, Eq m) => Eq ((a, b, c, d, e, f, g, h, i, j, k, l, m))",
      "instance (Eq a, Eq b, Eq c, Eq d, Eq e, Eq f, Eq g, Eq h, Eq i, Eq j, Eq k, Eq l, Eq m, Eq n) => Eq ((a, b, c, d, e, f, g, h, i, j, k, l, m, n))",
      "instance (Eq a, Eq b, Eq c, Eq d, Eq e, Eq f, Eq g, Eq h, Eq i, Eq j, Eq k, Eq l, Eq m, Eq n, Eq o) => Eq ((a, b, c, d, e, f, g, h, i, j, k, l, m, n, o))",
      "instance (Eq e, Eq1 m, Eq a) => Eq (ErrorT e m a)",
      "instance (Eq k, Eq a) => Eq (Map k a)",
      "instance (Eq w, Eq1 m, Eq a) => Eq (WriterT w m a)",
      "instance (Ix i, Eq e) => Eq (Array i e)",
      "instance Eq ()",
      "instance Eq (:~: a b)",
      "instance Eq (Coercion a b)",
      "instance Eq (Fixed a)",
      "instance Eq (ForeignPtr a)",
      "instance Eq (FunPtr a)",
      "instance Eq (IORef a)",
      "instance Eq (MVar a)",
      "instance Eq (Proxy s)",
      "instance Eq (Ptr a)",
      "instance Eq (STArray s i e)",
      "instance Eq (StableName a)",
      "instance Eq (StablePtr a)",
      "instance Eq (TVar a)",
      -- "instance Eq (U1 p)",
      -- "instance Eq (f (g p)) => Eq (:.: f g p)",
      "instance Eq (f a) => Eq (Alt f a)",
      -- "instance Eq (f p) => Eq (M1 i c f p)",
      -- "instance Eq (f p) => Eq (Rec1 f p)",
      "instance Eq Activation",
      "instance Eq All",
      "instance Eq Alt",
      "instance Eq AnnLookup",
      "instance Eq AnnTarget",
      "instance Eq Annotation",
      "instance Eq Any",
      -- "instance Eq Arity",
      "instance Eq ArrayException",
      "instance Eq Assoc",
      -- "instance Eq Associativity",
      "instance Eq Asst",
      "instance Eq AsyncException",
      "instance Eq BangType",
      "instance Eq BigNat",
      "instance Eq Binds",
      "instance Eq BlockReason",
      "instance Eq Body",
      "instance Eq Bool",
      "instance Eq BooleanFormula",
      "instance Eq Boxed",
      "instance Eq Bracket",
      "instance Eq BufferMode",
      "instance Eq CChar",
      "instance Eq CClock",
      "instance Eq CDouble",
      "instance Eq CFloat",
      "instance Eq CInt",
      "instance Eq CIntMax",
      "instance Eq CIntPtr",
      "instance Eq CLLong",
      "instance Eq CLong",
      "instance Eq CName",
      "instance Eq CPtrdiff",
      "instance Eq CSChar",
      "instance Eq CSUSeconds",
      "instance Eq CShort",
      "instance Eq CSigAtomic",
      "instance Eq CSize",
      "instance Eq CTime",
      "instance Eq CUChar",
      "instance Eq CUInt",
      "instance Eq CUIntMax",
      "instance Eq CUIntPtr",
      "instance Eq CULLong",
      "instance Eq CULong",
      "instance Eq CUSeconds",
      "instance Eq CUShort",
      "instance Eq CWchar",
      "instance Eq CallConv",
      "instance Eq Callconv",
      "instance Eq Char",
      "instance Eq ClassDecl",
      "instance Eq Clause",
      "instance Eq Con",
      "instance Eq ConDecl",
      "instance Eq Constr",
      "instance Eq ConstrRep",
      "instance Eq DataOrNew",
      "instance Eq DataRep",
      "instance Eq Dec",
      "instance Eq Decl",
      "instance Eq Double",
      "instance Eq ExitCode",
      "instance Eq Exp",
      "instance Eq ExportSpec",
      "instance Eq FamFlavour",
      "instance Eq FieldType",
      "instance Eq FieldUpdate",
      "instance Eq Fingerprint",
      "instance Eq Fixity",
      "instance Eq FixityDirection",
      "instance Eq Float",
      "instance Eq Foreign",
      "instance Eq FunDep",
      "instance Eq GadtDecl",
      "instance Eq Guard",
      "instance Eq GuardedRhs",
      "instance Eq Handle",
      "instance Eq IOErrorType",
      "instance Eq IOException",
      "instance Eq IPBind",
      "instance Eq IPName",
      "instance Eq ImportDecl",
      "instance Eq ImportSpec",
      "instance Eq Info",
      "instance Eq Inline",
      "instance Eq InstDecl",
      "instance Eq Int",
      "instance Eq Int16",
      "instance Eq Int32",
      "instance Eq Int64",
      "instance Eq Int8",
      "instance Eq Integer",
      "instance Eq Kind",
      "instance Eq Lit",
      "instance Eq Literal",
      "instance Eq Loc",
      "instance Eq LocalTime",
      "instance Eq MaskingState",
      "instance Eq Match",
      "instance Eq ModName",
      "instance Eq Module",
      "instance Eq ModuleInfo",
      "instance Eq ModuleName",
      "instance Eq ModulePragma",
      "instance Eq Name",
      "instance Eq NameFlavour",
      "instance Eq NameSpace",
      "instance Eq Namespace",
      "instance Eq Natural",
      "instance Eq NewOrData",
      "instance Eq Newline",
      "instance Eq NewlineMode",
      "instance Eq OccName",
      "instance Eq Op",
      "instance Eq Ordering",
      "instance Eq Overlap",
      "instance Eq PXAttr",
      "instance Eq Pat",
      "instance Eq PatField",
      "instance Eq Phases",
      "instance Eq PkgName",
      "instance Eq Pragma",
      "instance Eq Promoted",
      "instance Eq QName",
      "instance Eq QOp",
      "instance Eq QualConDecl",
      "instance Eq QualStmt",
      "instance Eq RPat",
      "instance Eq RPatOp",
      "instance Eq Range",
      "instance Eq Result",
      "instance Eq Rhs",
      "instance Eq Role",
      "instance Eq Rule",
      "instance Eq RuleBndr",
      "instance Eq RuleMatch",
      "instance Eq RuleVar",
      "instance Eq Safety",
      "instance Eq Sign",
      "instance Eq SpecialCon",
      "instance Eq Splice",
      "instance Eq SrcLoc",
      "instance Eq SrcSpan",
      "instance Eq SrcSpanInfo",
      "instance Eq Stmt",
      "instance Eq Strict",
      "instance Eq ThreadId",
      "instance Eq ThreadStatus",
      "instance Eq Tool",
      "instance Eq TyCon",
      "instance Eq TyLit",
      "instance Eq TySynEqn",
      "instance Eq TyVarBind",
      "instance Eq TyVarBndr",
      "instance Eq Type",
      "instance Eq TypeEqn",
      "instance Eq TypeRep",
      "instance Eq Unique",
      "instance Eq Version",
      "instance Eq Void",
      "instance Eq WarningText",
      "instance Eq Word",
      "instance Eq Word16",
      "instance Eq Word32",
      "instance Eq Word64",
      "instance Eq Word8",
      "instance Eq XAttr",
      "instance Eq XName",
      "instance Eq a => Eq (Complex a)",
      "instance Eq a => Eq (Const a b)",
      "instance Eq a => Eq (Down a)",
      "instance Eq a => Eq (Dual a)",
      "instance Eq a => Eq (E a)",
      "instance Eq a => Eq (First a)",
      "instance Eq a => Eq (Identity a)",
      "instance Eq a => Eq (Last a)",
      "instance Eq a => Eq (Loc a)",
      "instance Eq a => Eq (Maybe a)",
      "instance Eq a => Eq (Product a)",
      "instance Eq a => Eq (Ratio a)",
      "instance Eq a => Eq (Set a)",
      "instance Eq a => Eq (SetDifferences a)",
      "instance Eq a => Eq (Sum a)",
      "instance Eq a => Eq (ZipList a)",
      "instance Eq a => Eq ([a])",
      -- "instance Eq c => Eq (K1 i c p)",
      "instance Eq l => Eq (Activation l)",
      "instance Eq l => Eq (Alt l)",
      "instance Eq l => Eq (Annotation l)",
      "instance Eq l => Eq (Assoc l)",
      "instance Eq l => Eq (Asst l)",
      "instance Eq l => Eq (BangType l)",
      "instance Eq l => Eq (Binds l)",
      "instance Eq l => Eq (BooleanFormula l)",
      "instance Eq l => Eq (Bracket l)",
      "instance Eq l => Eq (CName l)",
      "instance Eq l => Eq (CallConv l)",
      "instance Eq l => Eq (ClassDecl l)",
      "instance Eq l => Eq (ConDecl l)",
      "instance Eq l => Eq (Context l)",
      "instance Eq l => Eq (DataOrNew l)",
      "instance Eq l => Eq (Decl l)",
      "instance Eq l => Eq (DeclHead l)",
      "instance Eq l => Eq (Deriving l)",
      "instance Eq l => Eq (Exp l)",
      "instance Eq l => Eq (ExportSpec l)",
      "instance Eq l => Eq (ExportSpecList l)",
      "instance Eq l => Eq (FieldDecl l)",
      "instance Eq l => Eq (FieldUpdate l)",
      "instance Eq l => Eq (FunDep l)",
      "instance Eq l => Eq (GadtDecl l)",
      "instance Eq l => Eq (GuardedRhs l)",
      "instance Eq l => Eq (IPBind l)",
      "instance Eq l => Eq (IPName l)",
      "instance Eq l => Eq (ImportDecl l)",
      "instance Eq l => Eq (ImportSpec l)",
      "instance Eq l => Eq (ImportSpecList l)",
      "instance Eq l => Eq (InstDecl l)",
      "instance Eq l => Eq (InstHead l)",
      "instance Eq l => Eq (InstRule l)",
      "instance Eq l => Eq (Kind l)",
      "instance Eq l => Eq (Literal l)",
      "instance Eq l => Eq (Match l)",
      "instance Eq l => Eq (Module l)",
      "instance Eq l => Eq (ModuleHead l)",
      "instance Eq l => Eq (ModuleName l)",
      "instance Eq l => Eq (ModulePragma l)",
      "instance Eq l => Eq (Name l)",
      "instance Eq l => Eq (Namespace l)",
      "instance Eq l => Eq (Op l)",
      "instance Eq l => Eq (Overlap l)",
      "instance Eq l => Eq (PXAttr l)",
      "instance Eq l => Eq (Pat l)",
      "instance Eq l => Eq (PatField l)",
      "instance Eq l => Eq (Promoted l)",
      "instance Eq l => Eq (QName l)",
      "instance Eq l => Eq (QOp l)",
      "instance Eq l => Eq (QualConDecl l)",
      "instance Eq l => Eq (QualStmt l)",
      "instance Eq l => Eq (RPat l)",
      "instance Eq l => Eq (RPatOp l)",
      "instance Eq l => Eq (Rhs l)",
      "instance Eq l => Eq (Rule l)",
      "instance Eq l => Eq (RuleVar l)",
      "instance Eq l => Eq (Safety l)",
      "instance Eq l => Eq (Sign l)",
      "instance Eq l => Eq (SpecialCon l)",
      "instance Eq l => Eq (Splice l)",
      "instance Eq l => Eq (Stmt l)",
      "instance Eq l => Eq (TyVarBind l)",
      "instance Eq l => Eq (Type l)",
      "instance Eq l => Eq (TypeEqn l)",
      "instance Eq l => Eq (WarningText l)",
      "instance Eq l => Eq (XAttr l)",
      "instance Eq l => Eq (XName l)",
      -- "instance Eq p => Eq (Par1 p)",

      -- "instance (Ix ix, Eq e, IArray UArray e) => Eq (UArray ix e)",
      -- "instance Eq (STUArray s i e)",
      "instance Eq Day",
      -- "instance Eq Doc",
      "instance Eq IntSet",
      -- "instance Eq Mode",
      "instance Eq NominalDiffTime",
      "instance Eq SpecConstrAnnotation",
      -- "instance Eq Style",
      -- "instance Eq TextDetails",
      "instance Eq UTCTime",
      "instance Eq a => Eq (DList a)",
      "instance Eq a => Eq (IntMap a)",
      "instance Eq a => Eq (Seq a)",
      "instance Eq a => Eq (ViewL a)",
      "instance Eq a => Eq (ViewR a)"
    ]

enumInstances :: Set String
enumInstances =
    Set.fromList
    [ "instance Enum ()",
      "instance Enum (Fixed a)",
      "instance Enum (Proxy s)",
      "instance Enum (f a) => Enum (Alt f a)",
      "instance Enum Bool",
      "instance Enum CChar",
      "instance Enum CClock",
      "instance Enum CDouble",
      "instance Enum CFloat",
      "instance Enum CInt",
      "instance Enum CIntMax",
      "instance Enum CIntPtr",
      "instance Enum CLLong",
      "instance Enum CLong",
      "instance Enum CPtrdiff",
      "instance Enum CSChar",
      "instance Enum CSUSeconds",
      "instance Enum CShort",
      "instance Enum CSigAtomic",
      "instance Enum CSize",
      "instance Enum CTime",
      "instance Enum CUChar",
      "instance Enum CUInt",
      "instance Enum CUIntMax",
      "instance Enum CUIntPtr",
      "instance Enum CULLong",
      "instance Enum CULong",
      "instance Enum CUSeconds",
      "instance Enum CUShort",
      "instance Enum CWchar",
      "instance Enum Char",
      "instance Enum Double",
      "instance Enum Float",
      "instance Enum Int",
      "instance Enum Int16",
      "instance Enum Int32",
      "instance Enum Int64",
      "instance Enum Int8",
      "instance Enum Integer",
      "instance Enum Natural",
      "instance Enum Ordering",
      "instance Enum Word",
      "instance Enum Word16",
      "instance Enum Word32",
      "instance Enum Word64",
      "instance Enum Word8",
      "instance Integral a => Enum (Ratio a)",
      "instance a ~ b => Enum (:~: a b)",
      "instance Enum Day",
      "instance Enum NominalDiffTime"
    ]

arrayInstances :: Set String
arrayInstances =
    Set.fromList
    [ "instance IArray UArray (FunPtr a)",
      "instance IArray UArray (Ptr a)",
      "instance IArray UArray (StablePtr a)",
      "instance IArray UArray Bool",
      "instance IArray UArray Char",
      "instance IArray UArray Double",
      "instance IArray UArray Float",
      "instance IArray UArray Int",
      "instance IArray UArray Int16",
      "instance IArray UArray Int32",
      "instance IArray UArray Int64",
      "instance IArray UArray Int8",
      "instance IArray UArray Word",
      "instance IArray UArray Word16",
      "instance IArray UArray Word32",
      "instance IArray UArray Word64",
      "instance IArray UArray Word8"
    ]
