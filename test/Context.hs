{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wall #-}
module Context where

import Control.DeepSeq
import Data.List as List (map, null)
import Data.Set as Set (Set, fromList, difference)
import Language.Haskell.TH
import Language.Haskell.TH.Context (reifyInstancesWithContext, testContext, missingInstances, simpleMissingInstanceTest)
import Language.Haskell.TH.DesugarExpandType ()
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

  -- Test the behavior of th-reify-many
  it "can tell that there is an instance NFData Char" $
     $(do insts <- qReifyInstances ''NFData [ConT ''Char]
          lift $ List.map (unwords . words .pprint) insts) `shouldBe` (["instance Control.DeepSeq.NFData GHC.Types.Char"] :: [String])

  it "can tell that there is no instance NFData ExitCode" $
     $(do insts <- qReifyInstances ''NFData [ConT ''ExitCode]
          lift $ List.map (unwords . words .pprint) insts) `shouldBe` ([] :: [String])

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
                lift (List.map (unwords . words . pprint) insts)))
        eqInstances)
      `shouldBe` noDifferences

  it "Is using a ghc without bug https://ghc.haskell.org/trac/ghc/ticket/9262 (i.e. either 7.10 or a custom patched ghc)" $ do
     $(do insts <- qReifyInstances ''Eq [ListT `AppT` VarT (mkName "a")]
          -- runIO $ putStrLn (pprint insts)
          lift "ok")
         `shouldBe` "ok"

  it "can match all the Enum instances" $ do
     (\ (insts, _pairs) -> (setDifferences (Set.fromList insts) enumInstances))
             $(do (insts, mp) <- runStateT (reifyInstancesWithContext ''Enum [VarT (mkName "a")]) mempty
                  lift (List.map (unwords . words . pprint) insts, Map.toList (Map.map (List.map (unwords . words . pprint)) (Map.mapKeys pprint mp))))
          `shouldBe` noDifferences

  it "can handle multi param class IArray" $ do
     (\ (insts, pairs) -> (setDifferences (Set.fromList insts) arrayInstances,
                           Map.map Set.fromList (Map.fromList pairs)))
             -- Unquote the template haskell Q monad expression
             $(do -- Run instances and save the result and the state monad result
                  (insts, mp) <- runStateT (reifyInstancesWithContext ''IArray [ConT ''UArray, VarT (mkName "a")]) mempty
                  -- Convert to lists of text so we can lift out of Q
                  lift (List.map (unwords . words . pprint) insts, Map.toList (Map.map (List.map (unwords . words . pprint)) (Map.mapKeys pprint mp))))
          `shouldBe` (noDifferences,
                      Map.fromList [("Data.Array.Base.IArray Data.Array.Base.UArray a", arrayInstances)])
#endif

eqInstances :: Set String
eqInstances
    = (Set.fromList
                      ["instance (GHC.Arr.Ix ix_0, GHC.Classes.Eq e_1, Data.Array.Base.IArray Data.Array.Base.UArray e_1) => GHC.Classes.Eq (Data.Array.Base.UArray ix_0 e_1)",
                       "instance (GHC.Classes.Eq a_0, GHC.Classes.Eq b_1) => GHC.Classes.Eq ((a_0, b_1))",
                       "instance (GHC.Classes.Eq a_0, GHC.Classes.Eq b_1, GHC.Classes.Eq c_2) => GHC.Classes.Eq ((a_0, b_1, c_2))",
                       "instance (GHC.Classes.Eq a_0, GHC.Classes.Eq b_1, GHC.Classes.Eq c_2, GHC.Classes.Eq d_3) => GHC.Classes.Eq ((a_0, b_1, c_2, d_3))",
                       "instance (GHC.Classes.Eq a_0, GHC.Classes.Eq b_1, GHC.Classes.Eq c_2, GHC.Classes.Eq d_3, GHC.Classes.Eq e_4) => GHC.Classes.Eq ((a_0, b_1, c_2, d_3, e_4))",
                       "instance (GHC.Classes.Eq a_0, GHC.Classes.Eq b_1, GHC.Classes.Eq c_2, GHC.Classes.Eq d_3, GHC.Classes.Eq e_4, GHC.Classes.Eq f_5) => GHC.Classes.Eq ((a_0, b_1, c_2, d_3, e_4, f_5))",
                       "instance (GHC.Classes.Eq a_0, GHC.Classes.Eq b_1, GHC.Classes.Eq c_2, GHC.Classes.Eq d_3, GHC.Classes.Eq e_4, GHC.Classes.Eq f_5, GHC.Classes.Eq g_6) => GHC.Classes.Eq ((a_0, b_1, c_2, d_3, e_4, f_5, g_6))",
                       "instance (GHC.Classes.Eq a_0, GHC.Classes.Eq b_1, GHC.Classes.Eq c_2, GHC.Classes.Eq d_3, GHC.Classes.Eq e_4, GHC.Classes.Eq f_5, GHC.Classes.Eq g_6, GHC.Classes.Eq h_7) => GHC.Classes.Eq ((a_0, b_1, c_2, d_3, e_4, f_5, g_6, h_7))",
                       "instance (GHC.Classes.Eq a_0, GHC.Classes.Eq b_1, GHC.Classes.Eq c_2, GHC.Classes.Eq d_3, GHC.Classes.Eq e_4, GHC.Classes.Eq f_5, GHC.Classes.Eq g_6, GHC.Classes.Eq h_7, GHC.Classes.Eq i_8) => GHC.Classes.Eq ((a_0, b_1, c_2, d_3, e_4, f_5, g_6, h_7, i_8))",
                       "instance (GHC.Classes.Eq a_0, GHC.Classes.Eq b_1, GHC.Classes.Eq c_2, GHC.Classes.Eq d_3, GHC.Classes.Eq e_4, GHC.Classes.Eq f_5, GHC.Classes.Eq g_6, GHC.Classes.Eq h_7, GHC.Classes.Eq i_8, GHC.Classes.Eq j_9) => GHC.Classes.Eq ((a_0, b_1, c_2, d_3, e_4, f_5, g_6, h_7, i_8, j_9))",
                       "instance (GHC.Classes.Eq a_0, GHC.Classes.Eq b_1, GHC.Classes.Eq c_2, GHC.Classes.Eq d_3, GHC.Classes.Eq e_4, GHC.Classes.Eq f_5, GHC.Classes.Eq g_6, GHC.Classes.Eq h_7, GHC.Classes.Eq i_8, GHC.Classes.Eq j_9, GHC.Classes.Eq k_10) => GHC.Classes.Eq ((a_0, b_1, c_2, d_3, e_4, f_5, g_6, h_7, i_8, j_9, k_10))",
                       "instance (GHC.Classes.Eq a_0, GHC.Classes.Eq b_1, GHC.Classes.Eq c_2, GHC.Classes.Eq d_3, GHC.Classes.Eq e_4, GHC.Classes.Eq f_5, GHC.Classes.Eq g_6, GHC.Classes.Eq h_7, GHC.Classes.Eq i_8, GHC.Classes.Eq j_9, GHC.Classes.Eq k_10, GHC.Classes.Eq l_11) => GHC.Classes.Eq ((a_0, b_1, c_2, d_3, e_4, f_5, g_6, h_7, i_8, j_9, k_10, l_11))",
                       "instance (GHC.Classes.Eq a_0, GHC.Classes.Eq b_1, GHC.Classes.Eq c_2, GHC.Classes.Eq d_3, GHC.Classes.Eq e_4, GHC.Classes.Eq f_5, GHC.Classes.Eq g_6, GHC.Classes.Eq h_7, GHC.Classes.Eq i_8, GHC.Classes.Eq j_9, GHC.Classes.Eq k_10, GHC.Classes.Eq l_11, GHC.Classes.Eq m_12) => GHC.Classes.Eq ((a_0, b_1, c_2, d_3, e_4, f_5, g_6, h_7, i_8, j_9, k_10, l_11, m_12))",
                       "instance (GHC.Classes.Eq a_0, GHC.Classes.Eq b_1, GHC.Classes.Eq c_2, GHC.Classes.Eq d_3, GHC.Classes.Eq e_4, GHC.Classes.Eq f_5, GHC.Classes.Eq g_6, GHC.Classes.Eq h_7, GHC.Classes.Eq i_8, GHC.Classes.Eq j_9, GHC.Classes.Eq k_10, GHC.Classes.Eq l_11, GHC.Classes.Eq m_12, GHC.Classes.Eq n_13) => GHC.Classes.Eq ((a_0, b_1, c_2, d_3, e_4, f_5, g_6, h_7, i_8, j_9, k_10, l_11, m_12, n_13))",
                       "instance (GHC.Classes.Eq a_0, GHC.Classes.Eq b_1, GHC.Classes.Eq c_2, GHC.Classes.Eq d_3, GHC.Classes.Eq e_4, GHC.Classes.Eq f_5, GHC.Classes.Eq g_6, GHC.Classes.Eq h_7, GHC.Classes.Eq i_8, GHC.Classes.Eq j_9, GHC.Classes.Eq k_10, GHC.Classes.Eq l_11, GHC.Classes.Eq m_12, GHC.Classes.Eq n_13, GHC.Classes.Eq o_14) => GHC.Classes.Eq ((a_0, b_1, c_2, d_3, e_4, f_5, g_6, h_7, i_8, j_9, k_10, l_11, m_12, n_13, o_14))",
                       "instance (GHC.Classes.Eq e_0, Data.Functor.Classes.Eq1 m_1, GHC.Classes.Eq a_2) => GHC.Classes.Eq (Control.Monad.Trans.Error.ErrorT e_0 m_1 a_2)",
                       "instance (GHC.Classes.Eq k_0, GHC.Classes.Eq a_1) => GHC.Classes.Eq (Data.Map.Base.Map k_0 a_1)",
                       "instance GHC.Classes.Eq ()",
                       "instance GHC.Classes.Eq (Data.Array.Base.STUArray s_0 i_1 e_2)",
                       "instance GHC.Classes.Eq Data.Data.Constr",
                       "instance GHC.Classes.Eq Data.Data.ConstrRep",
                       "instance GHC.Classes.Eq Data.Data.DataRep",
                       "instance GHC.Classes.Eq Data.Data.Fixity",
                       "instance GHC.Classes.Eq Data.Monoid.All",
                       "instance GHC.Classes.Eq Data.Monoid.Any",
                       "instance GHC.Classes.Eq Data.Time.LocalTime.LocalTime.LocalTime",
                       "instance GHC.Classes.Eq Data.Typeable.Internal.TyCon",
                       "instance GHC.Classes.Eq Data.Typeable.Internal.TypeRep",
                       "instance GHC.Classes.Eq GHC.IO.MaskingState",
                       "instance GHC.Classes.Eq GHC.Integer.Type.Integer",
                       "instance GHC.Classes.Eq GHC.Types.Bool",
                       "instance GHC.Classes.Eq GHC.Types.Char",
                       "instance GHC.Classes.Eq GHC.Types.Double",
                       "instance GHC.Classes.Eq GHC.Types.Float",
                       "instance GHC.Classes.Eq GHC.Types.Int",
                       "instance GHC.Classes.Eq GHC.Types.Ordering",
                       "instance GHC.Classes.Eq GHC.Types.Word",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Desugar.Core.NewOrData",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.AnnLookup",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.AnnTarget",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.Body",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.Callconv",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.Clause",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.Con",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.Dec",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.Exp",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.FamFlavour",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.Fixity",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.FixityDirection",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.Foreign",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.FunDep",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.Guard",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.Info",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.Inline",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.Lit",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.Loc",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.Match",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.ModName",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.Module",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.Name",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.NameFlavour",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.NameSpace",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.OccName",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.Pat",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.Phases",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.PkgName",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.Pragma",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.Range",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.Role",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.RuleBndr",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.RuleMatch",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.Safety",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.Stmt",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.Strict",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.TyLit",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.TySynEqn",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.TyVarBndr",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.Type",
                       "instance GHC.Classes.Eq Test.Hspec.Core.Runner.Summary",
                       "instance GHC.Classes.Eq a_0 => GHC.Classes.Eq (Control.Applicative.ZipList a_0)",
                       "instance GHC.Classes.Eq a_0 => GHC.Classes.Eq (Data.Monoid.Dual a_0)",
                       "instance GHC.Classes.Eq a_0 => GHC.Classes.Eq (Data.Monoid.First a_0)",
                       "instance GHC.Classes.Eq a_0 => GHC.Classes.Eq (Data.Monoid.Last a_0)",
                       "instance GHC.Classes.Eq a_0 => GHC.Classes.Eq (Data.Monoid.Product a_0)",
                       "instance GHC.Classes.Eq a_0 => GHC.Classes.Eq (Data.Monoid.Sum a_0)",
                       "instance GHC.Classes.Eq a_0 => GHC.Classes.Eq (Data.Set.Base.Set a_0)",
                       "instance GHC.Classes.Eq a_0 => GHC.Classes.Eq (GHC.Real.Ratio a_0)",
                       "instance GHC.Classes.Eq a_0 => GHC.Classes.Eq ([a_0])",
                       "instance (GHC.Classes.Eq (f_0 p_1), GHC.Classes.Eq (g_2 p_1)) => GHC.Classes.Eq (GHC.Generics.:*: f_0 g_2 p_1)",
                       "instance (GHC.Classes.Eq (f_0 p_1), GHC.Classes.Eq (g_2 p_1)) => GHC.Classes.Eq (GHC.Generics.:+: f_0 g_2 p_1)",
                       "instance (GHC.Classes.Eq a_0, GHC.Classes.Eq b_1) => GHC.Classes.Eq (Data.Either.Either a_0 b_1)",
                       "instance GHC.Classes.Eq (Data.Type.Equality.:~: a_0 b_1)",
                       "instance GHC.Classes.Eq (GHC.Generics.U1 p_0)",
                       "instance GHC.Classes.Eq (f_0 (g_1 p_2)) => GHC.Classes.Eq (GHC.Generics.:.: f_0 g_1 p_2)",
                       "instance GHC.Classes.Eq (f_0 p_1) => GHC.Classes.Eq (GHC.Generics.M1 i_2 c_3 f_0 p_1)",
                       "instance GHC.Classes.Eq (f_0 p_1) => GHC.Classes.Eq (GHC.Generics.Rec1 f_0 p_1)",
                       "instance GHC.Classes.Eq Data.Text.Internal.Text",
                       "instance GHC.Classes.Eq GHC.Exts.SpecConstrAnnotation",
                       "instance GHC.Classes.Eq GHC.Generics.Arity",
                       "instance GHC.Classes.Eq GHC.Generics.Associativity",
                       "instance GHC.Classes.Eq GHC.Generics.Fixity",
                       "instance GHC.Classes.Eq Test.Hspec.Core.Example.Result",
                       "instance GHC.Classes.Eq c_0 => GHC.Classes.Eq (GHC.Generics.K1 i_1 c_0 p_2)",
                       "instance GHC.Classes.Eq p_0 => GHC.Classes.Eq (GHC.Generics.Par1 p_0)",
                       "instance GHC.Classes.Eq GHC.IO.Exception.ArrayException",
                       "instance GHC.Classes.Eq GHC.IO.Exception.AsyncException",
                       "instance GHC.Classes.Eq GHC.IO.Exception.ExitCode",
                       "instance GHC.Classes.Eq GHC.IO.Exception.IOErrorType",
                       "instance GHC.Classes.Eq GHC.IO.Exception.IOException",
                       "instance (GHC.Classes.Eq w_0, Data.Functor.Classes.Eq1 m_1, GHC.Classes.Eq a_2) => GHC.Classes.Eq (Control.Monad.Trans.Writer.Lazy.WriterT w_0 m_1 a_2)",
#if __GLASGOW_HASKELL__ >= 709
                       "instance (GHC.Arr.Ix i_0, GHC.Classes.Eq e_1) => GHC.Classes.Eq (GHC.Arr.Array i_0 e_1)",
                       "instance (GHC.Classes.Eq a_0, GHC.Classes.Eq b_1) => GHC.Classes.Eq (Data.Either.Either a_0 b_1)",
                       "instance GHC.Classes.Eq (GHC.Arr.STArray s_0 i_1 e_2)",
                       "instance GHC.Classes.Eq (f_0 a_1) => GHC.Classes.Eq (Data.Monoid.Alt f_0 a_1)",
                       "instance GHC.Classes.Eq GHC.Int.Int16",
                       "instance GHC.Classes.Eq GHC.Int.Int32",
                       "instance GHC.Classes.Eq GHC.Int.Int64",
                       "instance GHC.Classes.Eq GHC.Int.Int8",
                       "instance GHC.Classes.Eq GHC.Integer.Type.BigNat",
                       "instance GHC.Classes.Eq GHC.Natural.Natural",
                       "instance GHC.Classes.Eq GHC.Word.Word16",
                       "instance GHC.Classes.Eq GHC.Word.Word32",
                       "instance GHC.Classes.Eq GHC.Word.Word64",
                       "instance GHC.Classes.Eq GHC.Word.Word8",
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.ModuleInfo",
                       "instance GHC.Classes.Eq Test.Hspec.Core.Example.Result",
                       "instance GHC.Classes.Eq Text.PrettyPrint.HughesPJ.Doc",
                       "instance GHC.Classes.Eq Text.PrettyPrint.HughesPJ.Mode",
                       "instance GHC.Classes.Eq Text.PrettyPrint.HughesPJ.Style",
                       "instance GHC.Classes.Eq Text.PrettyPrint.HughesPJ.TextDetails",
                       "instance GHC.Classes.Eq a_0 => GHC.Classes.Eq (Control.Applicative.Const a_0 b_1)",
                       "instance GHC.Classes.Eq a_0 => GHC.Classes.Eq (GHC.Base.Maybe a_0)",
                       "instance GHC.Classes.Eq (Data.Fixed.Fixed a_0)",
                       "instance GHC.Classes.Eq (Data.Proxy.Proxy s_0)",
                       "instance GHC.Classes.Eq (GHC.Conc.Sync.TVar a_0)",
                       "instance GHC.Classes.Eq (System.Mem.StableName.StableName a_0)",
                       "instance GHC.Classes.Eq Data.Unique.Unique",
                       "instance GHC.Classes.Eq Data.Version.Version",
                       "instance GHC.Classes.Eq Data.Void.Void",
                       "instance GHC.Classes.Eq Foreign.C.Types.CChar",
                       "instance GHC.Classes.Eq Foreign.C.Types.CClock",
                       "instance GHC.Classes.Eq Foreign.C.Types.CDouble",
                       "instance GHC.Classes.Eq Foreign.C.Types.CFloat",
                       "instance GHC.Classes.Eq Foreign.C.Types.CInt",
                       "instance GHC.Classes.Eq Foreign.C.Types.CIntMax",
                       "instance GHC.Classes.Eq Foreign.C.Types.CIntPtr",
                       "instance GHC.Classes.Eq Foreign.C.Types.CLLong",
                       "instance GHC.Classes.Eq Foreign.C.Types.CLong",
                       "instance GHC.Classes.Eq Foreign.C.Types.CPtrdiff",
                       "instance GHC.Classes.Eq Foreign.C.Types.CSChar",
                       "instance GHC.Classes.Eq Foreign.C.Types.CSUSeconds",
                       "instance GHC.Classes.Eq Foreign.C.Types.CShort",
                       "instance GHC.Classes.Eq Foreign.C.Types.CSigAtomic",
                       "instance GHC.Classes.Eq Foreign.C.Types.CSize",
                       "instance GHC.Classes.Eq Foreign.C.Types.CTime",
                       "instance GHC.Classes.Eq Foreign.C.Types.CUChar",
                       "instance GHC.Classes.Eq Foreign.C.Types.CUInt",
                       "instance GHC.Classes.Eq Foreign.C.Types.CUIntMax",
                       "instance GHC.Classes.Eq Foreign.C.Types.CUIntPtr",
                       "instance GHC.Classes.Eq Foreign.C.Types.CULLong",
                       "instance GHC.Classes.Eq Foreign.C.Types.CULong",
                       "instance GHC.Classes.Eq Foreign.C.Types.CUSeconds",
                       "instance GHC.Classes.Eq Foreign.C.Types.CUShort",
                       "instance GHC.Classes.Eq Foreign.C.Types.CWchar",
                       "instance GHC.Classes.Eq GHC.Conc.Sync.BlockReason",
                       "instance GHC.Classes.Eq GHC.Conc.Sync.ThreadId",
                       "instance GHC.Classes.Eq GHC.Conc.Sync.ThreadStatus",
                       "instance GHC.Classes.Eq GHC.Fingerprint.Type.Fingerprint",
                       "instance GHC.Classes.Eq GHC.IO.Exception.ArrayException",
                       "instance GHC.Classes.Eq GHC.IO.Exception.AsyncException",
                       "instance GHC.Classes.Eq GHC.IO.Exception.ExitCode",
                       "instance GHC.Classes.Eq GHC.IO.Exception.IOErrorType",
                       "instance GHC.Classes.Eq GHC.IO.Exception.IOException",
                       "instance GHC.Classes.Eq GHC.TypeLits.SomeNat",
                       "instance GHC.Classes.Eq GHC.TypeLits.SomeSymbol",
                       "instance GHC.Classes.Eq a_0 => GHC.Classes.Eq (Data.Complex.Complex a_0)",
                       "instance GHC.Classes.Eq a_0 => GHC.Classes.Eq (Data.Functor.Identity.Identity a_0)",
                       "instance GHC.Classes.Eq a_0 => GHC.Classes.Eq (Data.Ord.Down a_0)"
#else
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.Pred",
                       "instance GHC.Classes.Eq a_0 => GHC.Classes.Eq (Data.Maybe.Maybe a_0)"
#endif
                      ])

enumInstances :: Set String
enumInstances =
    Set.fromList     ["instance GHC.Enum.Enum GHC.Types.Double",
                      "instance GHC.Enum.Enum GHC.Types.Float",
                      "instance GHC.Enum.Enum GHC.Types.Word",
                      "instance GHC.Enum.Enum ()",
                      "instance GHC.Enum.Enum GHC.Types.Bool",
                      "instance GHC.Enum.Enum GHC.Types.Char",
                      "instance GHC.Enum.Enum GHC.Types.Int",
                      "instance GHC.Enum.Enum GHC.Integer.Type.Integer",
                      "instance GHC.Enum.Enum GHC.Types.Ordering",
#if __GLASGOW_HASKELL__ >= 709
                      "instance GHC.Enum.Enum (Data.Fixed.Fixed a_0)",
                      "instance GHC.Enum.Enum (Data.Proxy.Proxy s_0)",
                      "instance GHC.Enum.Enum Foreign.C.Types.CChar",
                      "instance GHC.Enum.Enum Foreign.C.Types.CClock",
                      "instance GHC.Enum.Enum Foreign.C.Types.CDouble",
                      "instance GHC.Enum.Enum Foreign.C.Types.CFloat",
                      "instance GHC.Enum.Enum Foreign.C.Types.CInt",
                      "instance GHC.Enum.Enum Foreign.C.Types.CIntMax",
                      "instance GHC.Enum.Enum Foreign.C.Types.CIntPtr",
                      "instance GHC.Enum.Enum Foreign.C.Types.CLLong",
                      "instance GHC.Enum.Enum Foreign.C.Types.CLong",
                      "instance GHC.Enum.Enum Foreign.C.Types.CPtrdiff",
                      "instance GHC.Enum.Enum Foreign.C.Types.CSChar",
                      "instance GHC.Enum.Enum Foreign.C.Types.CSUSeconds",
                      "instance GHC.Enum.Enum Foreign.C.Types.CShort",
                      "instance GHC.Enum.Enum Foreign.C.Types.CSigAtomic",
                      "instance GHC.Enum.Enum Foreign.C.Types.CSize",
                      "instance GHC.Enum.Enum Foreign.C.Types.CTime",
                      "instance GHC.Enum.Enum Foreign.C.Types.CUChar",
                      "instance GHC.Enum.Enum Foreign.C.Types.CUInt",
                      "instance GHC.Enum.Enum Foreign.C.Types.CUIntMax",
                      "instance GHC.Enum.Enum Foreign.C.Types.CUIntPtr",
                      "instance GHC.Enum.Enum Foreign.C.Types.CULLong",
                      "instance GHC.Enum.Enum Foreign.C.Types.CULong",
                      "instance GHC.Enum.Enum Foreign.C.Types.CUSeconds",
                      "instance GHC.Enum.Enum Foreign.C.Types.CUShort",
                      "instance GHC.Enum.Enum Foreign.C.Types.CWchar",
                      "instance GHC.Enum.Enum GHC.Int.Int16",
                      "instance GHC.Enum.Enum GHC.Int.Int32",
                      "instance GHC.Enum.Enum GHC.Int.Int64",
                      "instance GHC.Enum.Enum GHC.Int.Int8",
                      "instance GHC.Enum.Enum GHC.Natural.Natural",
                      "instance GHC.Enum.Enum GHC.Word.Word16",
                      "instance GHC.Enum.Enum GHC.Word.Word32",
                      "instance GHC.Enum.Enum GHC.Word.Word64",
                      "instance GHC.Enum.Enum GHC.Word.Word8",
#else
                      "instance GHC.Real.Integral a_0 => GHC.Enum.Enum (GHC.Real.Ratio a_0)",
#endif
                      "instance a_0 ~ b_1 => GHC.Enum.Enum (Data.Type.Equality.:~: a_0 b_1)"
                      ]

arrayInstances :: Set String
arrayInstances =
    Set.fromList
                     ["instance Data.Array.Base.IArray Data.Array.Base.UArray GHC.Types.Bool",
                      "instance Data.Array.Base.IArray Data.Array.Base.UArray GHC.Types.Char",
                      "instance Data.Array.Base.IArray Data.Array.Base.UArray GHC.Types.Double",
                      "instance Data.Array.Base.IArray Data.Array.Base.UArray GHC.Types.Float",
                      "instance Data.Array.Base.IArray Data.Array.Base.UArray (GHC.Ptr.FunPtr a_0)",
                      "instance Data.Array.Base.IArray Data.Array.Base.UArray GHC.Types.Int",
                      "instance Data.Array.Base.IArray Data.Array.Base.UArray GHC.Int.Int16",
                      "instance Data.Array.Base.IArray Data.Array.Base.UArray GHC.Int.Int32",
                      "instance Data.Array.Base.IArray Data.Array.Base.UArray GHC.Int.Int64",
                      "instance Data.Array.Base.IArray Data.Array.Base.UArray GHC.Int.Int8",
                      "instance Data.Array.Base.IArray Data.Array.Base.UArray (GHC.Ptr.Ptr a_0)",
                      "instance Data.Array.Base.IArray Data.Array.Base.UArray (GHC.Stable.StablePtr a_0)",
                      "instance Data.Array.Base.IArray Data.Array.Base.UArray GHC.Types.Word",
                      "instance Data.Array.Base.IArray Data.Array.Base.UArray GHC.Word.Word16",
                      "instance Data.Array.Base.IArray Data.Array.Base.UArray GHC.Word.Word32",
                      "instance Data.Array.Base.IArray Data.Array.Base.UArray GHC.Word.Word64",
                      "instance Data.Array.Base.IArray Data.Array.Base.UArray GHC.Word.Word8"]
