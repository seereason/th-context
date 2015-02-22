{-# LANGUAGE TemplateHaskell #-}
module Main where

import Control.Monad.State (evalStateT)
import Data.Array.Base
import Data.List (intercalate)
import Data.Set (fromList)
import Data.Monoid (mempty)
import Language.Haskell.TH
import Language.Haskell.TH.Context (instances, testContext)
import Language.Haskell.TH.Desugar (withLocalDeclarations)
import Language.Haskell.TH.Syntax (lift, Quasi(qReifyInstances))
import Test.Hspec hiding (runIO)
import Expand

main :: IO ()
main = hspec $ do
  it "Is using a ghc without bug https://ghc.haskell.org/trac/ghc/ticket/9262 (i.e. either 7.10 or a custom patched ghc)" $ do
     $(do insts <- reifyInstances ''Eq [ListT `AppT` VarT (mkName "a")]
          runIO $ putStrLn (pprint insts)
          lift "ok")
         `shouldBe` "ok"
  it "Can run the Q monad" $ do
     typ <- runQ [t|Int|]
     typ `shouldBe` ConT ''Int

  it "can find all the Eq instances" $ do
     fromList $(do insts <- qReifyInstances ''Eq [VarT (mkName "a")]
                   lift (map (unwords . words . pprint) insts))
          `shouldBe` (fromList
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
                       "instance GHC.Classes.Eq Language.Haskell.TH.Syntax.Pred",
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
                       "instance GHC.Classes.Eq a_0 => GHC.Classes.Eq (Data.Maybe.Maybe a_0)",
                       "instance GHC.Classes.Eq a_0 => GHC.Classes.Eq (Data.Monoid.Dual a_0)",
                       "instance GHC.Classes.Eq a_0 => GHC.Classes.Eq (Data.Monoid.First a_0)",
                       "instance GHC.Classes.Eq a_0 => GHC.Classes.Eq (Data.Monoid.Last a_0)",
                       "instance GHC.Classes.Eq a_0 => GHC.Classes.Eq (Data.Monoid.Product a_0)",
                       "instance GHC.Classes.Eq a_0 => GHC.Classes.Eq (Data.Monoid.Sum a_0)",
                       "instance GHC.Classes.Eq a_0 => GHC.Classes.Eq (Data.Set.Base.Set a_0)",
                       "instance GHC.Classes.Eq a_0 => GHC.Classes.Eq (GHC.Real.Ratio a_0)",
                       "instance GHC.Classes.Eq a_0 => GHC.Classes.Eq ([a_0])"])

  it "can match all the Enum instances" $ do
     fromList $(do insts <- evalStateT (instances ''Enum [VarT (mkName "a")]) mempty
                   lift (map (unwords . words . pprint) insts))
          `shouldBe` (fromList
                      ["instance GHC.Enum.Enum GHC.Types.Double",
                      "instance GHC.Enum.Enum GHC.Types.Float",
                      "instance GHC.Real.Integral a_0 => GHC.Enum.Enum (GHC.Real.Ratio a_0)",
                      "instance GHC.Enum.Enum GHC.Types.Word",
                      "instance GHC.Enum.Enum ()",
                      "instance GHC.Enum.Enum GHC.Types.Bool",
                      "instance GHC.Enum.Enum GHC.Types.Char",
                      "instance GHC.Enum.Enum GHC.Types.Int",
                      "instance GHC.Enum.Enum GHC.Integer.Type.Integer",
                      "instance GHC.Enum.Enum GHC.Types.Ordering"])

  it "can handle multi param class IArray" $ do
     fromList $(do insts <- evalStateT (instances ''IArray [ConT ''UArray, VarT (mkName "a")]) mempty
                   lift (map (unwords . words . pprint) insts))
          `shouldBe` (fromList
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
                      "instance Data.Array.Base.IArray Data.Array.Base.UArray GHC.Word.Word8"])
