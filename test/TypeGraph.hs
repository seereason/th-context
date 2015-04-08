{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wall #-}
module TypeGraph where

import Control.Monad (filterM)
import Data.Map as Map (toList)
import Data.Set as Set (Set, fromList, toList, union)
import GHC.Prim
import Language.Haskell.TH
import Language.Haskell.TH.Desugar (withLocalDeclarations)
import Language.Haskell.TH.Expand (expandType, runExpanded, E)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.TypeGraph (subtypes, typeGraphEdges, VertexStatus(Vertex), typeArity)
import Test.Hspec hiding (runIO)
import Test.Hspec.Core.Spec (SpecM)

import Common

tests :: SpecM () ()
tests = do
  it "can find the subtypes of Type" $ do
     setDifferences (fromList $(withLocalDeclarations [] $
                                  runQ [t|Type|] >>=
                                  expandType >>= \ (typ :: E Type) ->
                                  subtypes [typ] >>=
                                  runQ . lift . map runExpanded . Set.toList)) subtypesOfType
        `shouldBe` noDifferences

  it "can find the edges of the subtype graph of Type" $ do
     setDifferences (fromList $(withLocalDeclarations [] $
                                runQ [t|Type|] >>=
                                expandType >>= \ (typ :: E Type) ->
                                typeGraphEdges (const $ return Vertex) [typ] >>=
                                runQ . lift . map toStrings . Map.toList)) typeEdges
        `shouldBe` noDifferences

  it "can find the edges of the subtype graph of Dec" $ do
     setDifferences (fromList $(withLocalDeclarations [] $
                                runQ [t|Dec|] >>=
                                expandType >>= \ (typ :: E Type) ->
                                typeGraphEdges (const $ return Vertex) [typ] >>=
                                runQ . lift . map toStrings . Map.toList)) decEdges
        `shouldBe` noDifferences

  it "can find the subtypes of Dec" $ do
     setDifferences (fromList $(withLocalDeclarations [] $
                                runQ [t|Dec|] >>=
                                expandType >>= \ (typ :: E Type) ->
                                subtypes [typ] >>=
                                runQ . lift . map (unwords . words . pprint) . Set.toList)) subtypesOfDec
        `shouldBe` noDifferences

  it "can find the arity 0 subtypes of Dec" $ do
     setDifferences (fromList $(withLocalDeclarations [] $
                                runQ [t|Dec|] >>=
                                expandType >>= \ (typ :: E Type) ->
                                subtypes [typ] >>=
                                filterM (\ t -> typeArity (runExpanded t) >>= \ a -> return (a == 0)) . Set.toList >>=
                                runQ . lift . map (unwords . words . pprint))) arity0SubtypesOfDec
        `shouldBe` noDifferences

subtypesOfType :: Set Type
subtypesOfType =
    fromList
      $(lookupTypeName "ByteArray#" >>= \ (Just byteArray) ->
        lookupTypeName "Char#" >>= \ (Just char) ->
        lookupTypeName "Int#" >>= \ (Just int) ->
        sequence
          [ [t| String |],
            [t| [Char] |],
            [t| [Pred] |],
            [t| [TyVarBndr] |],
            [t| [Type] |],
            conT byteArray,
            conT char,
            conT int,
            [t| Char |],
            [t| Cxt |],
            [t| Int |],
            [t| Integer |],
            [t| Kind |],
            [t| ModName |],
            [t| Name |],
            [t| NameFlavour |],
            [t| NameSpace |],
            [t| OccName |],
            [t| PkgName |],
            [t| Pred |],
            [t| TyLit |],
            [t| TyVarBndr |],
            [t| Type |],
            (return ListT)
          ] >>= lift)

decEdges :: Set (String, [String])
decEdges =
    fromList
      [("(,)",[]),
       ("(,,)",[]),
       ("Data.Maybe.Maybe",["a_0"]),
       ("GHC.Prim.ByteArray#",[]),
       ("GHC.Prim.Char#",[]),
       ("GHC.Prim.Int#",[]),
       ("GHC.Prim.Word#",[]),
       ("GHC.Real.Ratio",["a_0"]),
       ("GHC.Types.Char",["GHC.Prim.Char#"]),
       ("GHC.Word.Word8",["GHC.Prim.Word#"]),
       ("Language.Haskell.TH.Syntax.Callconv",[]),
       ("Language.Haskell.TH.Syntax.FamFlavour",[]),
       ("Language.Haskell.TH.Syntax.FixityDirection",[]),
       ("Language.Haskell.TH.Syntax.Inline",[]),
       ("Language.Haskell.TH.Syntax.Name",["Language.Haskell.TH.Syntax.NameFlavour","Language.Haskell.TH.Syntax.OccName"]),
       ("Language.Haskell.TH.Syntax.NameFlavour",["GHC.Prim.Int#","Language.Haskell.TH.Syntax.ModName","Language.Haskell.TH.Syntax.NameSpace","Language.Haskell.TH.Syntax.PkgName"]),
       ("Language.Haskell.TH.Syntax.NameSpace",[]),
       ("Language.Haskell.TH.Syntax.Role",[]),
       ("Language.Haskell.TH.Syntax.RuleMatch",[]),
       ("Language.Haskell.TH.Syntax.Safety",[]),
       ("Language.Haskell.TH.Syntax.Strict",[]),
       ("[GHC.Types.Char]",["GHC.Types.Char","[]"]),
       ("[]",[]),
       ("a_0",[]),
       ("(,) Language.Haskell.TH.Syntax.Guard",["Language.Haskell.TH.Syntax.Guard","(,)"]),
       ("(,) Language.Haskell.TH.Syntax.Name",["Language.Haskell.TH.Syntax.Name","(,)"]),
       ("(,) Language.Haskell.TH.Syntax.Strict",["Language.Haskell.TH.Syntax.Strict","(,)"]),
       ("(,,) Language.Haskell.TH.Syntax.Name",["Language.Haskell.TH.Syntax.Name","(,,)"]),
       ("(,,) Language.Haskell.TH.Syntax.Name Language.Haskell.TH.Syntax.Strict",["(,,) Language.Haskell.TH.Syntax.Name","Language.Haskell.TH.Syntax.Strict"]),
       ("(Language.Haskell.TH.Syntax.Guard, Language.Haskell.TH.Syntax.Exp)",["(,) Language.Haskell.TH.Syntax.Guard","Language.Haskell.TH.Syntax.Exp"]),
       ("(Language.Haskell.TH.Syntax.Name, Language.Haskell.TH.Syntax.Exp)",["(,) Language.Haskell.TH.Syntax.Name","Language.Haskell.TH.Syntax.Exp"]),
       ("(Language.Haskell.TH.Syntax.Name, Language.Haskell.TH.Syntax.Pat)",["(,) Language.Haskell.TH.Syntax.Name","Language.Haskell.TH.Syntax.Pat"]),
       ("(Language.Haskell.TH.Syntax.Name, Language.Haskell.TH.Syntax.Strict, Language.Haskell.TH.Syntax.Type)",["(,,) Language.Haskell.TH.Syntax.Name Language.Haskell.TH.Syntax.Strict","Language.Haskell.TH.Syntax.Type"]),
       ("(Language.Haskell.TH.Syntax.Strict, Language.Haskell.TH.Syntax.Type)",["(,) Language.Haskell.TH.Syntax.Strict","Language.Haskell.TH.Syntax.Type"]),
       ("Data.Maybe.Maybe Language.Haskell.TH.Syntax.Exp",["Data.Maybe.Maybe","Language.Haskell.TH.Syntax.Exp"]),
       ("Data.Maybe.Maybe Language.Haskell.TH.Syntax.Inline",["Data.Maybe.Maybe","Language.Haskell.TH.Syntax.Inline"]),
       ("Data.Maybe.Maybe Language.Haskell.TH.Syntax.Kind",["Data.Maybe.Maybe","Language.Haskell.TH.Syntax.Kind"]),
       ("GHC.Base.String",["[GHC.Types.Char]"]),
       ("GHC.Integer.Type.Integer",["GHC.Prim.ByteArray#","GHC.Prim.Int#"]),
       ("GHC.Real.Ratio GHC.Integer.Type.Integer",["GHC.Real.Ratio","GHC.Integer.Type.Integer"]),
       ("GHC.Real.Rational",["GHC.Real.Ratio GHC.Integer.Type.Integer"]),
       ("GHC.Types.Int",["GHC.Prim.Int#"]),
       ("Language.Haskell.TH.Syntax.AnnTarget",["Language.Haskell.TH.Syntax.Name"]),
       ("Language.Haskell.TH.Syntax.Body",["[(Language.Haskell.TH.Syntax.Guard, Language.Haskell.TH.Syntax.Exp)]","Language.Haskell.TH.Syntax.Exp"]),
       ("Language.Haskell.TH.Syntax.Clause",["[Language.Haskell.TH.Syntax.Dec]","[Language.Haskell.TH.Syntax.Pat]","Language.Haskell.TH.Syntax.Body"]),
       ("Language.Haskell.TH.Syntax.Con",["[Language.Haskell.TH.Syntax.StrictType]","[Language.Haskell.TH.Syntax.TyVarBndr]","[Language.Haskell.TH.Syntax.VarStrictType]","Language.Haskell.TH.Syntax.Con","Language.Haskell.TH.Syntax.Cxt","Language.Haskell.TH.Syntax.Name","Language.Haskell.TH.Syntax.StrictType"]),
       ("Language.Haskell.TH.Syntax.Cxt",["[Language.Haskell.TH.Syntax.Pred]"]),
       ("Language.Haskell.TH.Syntax.Dec",["Data.Maybe.Maybe Language.Haskell.TH.Syntax.Kind","[Language.Haskell.TH.Syntax.Clause]","[Language.Haskell.TH.Syntax.Con]","[Language.Haskell.TH.Syntax.Dec]","[Language.Haskell.TH.Syntax.FunDep]","[Language.Haskell.TH.Syntax.Name]","[Language.Haskell.TH.Syntax.Role]","[Language.Haskell.TH.Syntax.TySynEqn]","[Language.Haskell.TH.Syntax.TyVarBndr]","[Language.Haskell.TH.Syntax.Type]","Language.Haskell.TH.Syntax.Body","Language.Haskell.TH.Syntax.Con","Language.Haskell.TH.Syntax.Cxt","Language.Haskell.TH.Syntax.FamFlavour","Language.Haskell.TH.Syntax.Fixity","Language.Haskell.TH.Syntax.Foreign","Language.Haskell.TH.Syntax.Name","Language.Haskell.TH.Syntax.Pat","Language.Haskell.TH.Syntax.Pragma","Language.Haskell.TH.Syntax.TySynEqn","Language.Haskell.TH.Syntax.Type"]),
       ("Language.Haskell.TH.Syntax.Exp",["Data.Maybe.Maybe Language.Haskell.TH.Syntax.Exp","[(Language.Haskell.TH.Syntax.Guard, Language.Haskell.TH.Syntax.Exp)]","[Language.Haskell.TH.Syntax.Dec]","[Language.Haskell.TH.Syntax.Exp]","[Language.Haskell.TH.Syntax.FieldExp]","[Language.Haskell.TH.Syntax.Match]","[Language.Haskell.TH.Syntax.Pat]","[Language.Haskell.TH.Syntax.Stmt]","Language.Haskell.TH.Syntax.Exp","Language.Haskell.TH.Syntax.Lit","Language.Haskell.TH.Syntax.Name","Language.Haskell.TH.Syntax.Range","Language.Haskell.TH.Syntax.Type"]),
       ("Language.Haskell.TH.Syntax.FieldExp",["(Language.Haskell.TH.Syntax.Name, Language.Haskell.TH.Syntax.Exp)"]),
       ("Language.Haskell.TH.Syntax.FieldPat",["(Language.Haskell.TH.Syntax.Name, Language.Haskell.TH.Syntax.Pat)"]),
       ("Language.Haskell.TH.Syntax.Fixity",["GHC.Types.Int","Language.Haskell.TH.Syntax.FixityDirection"]),
       ("Language.Haskell.TH.Syntax.Foreign",["GHC.Base.String","Language.Haskell.TH.Syntax.Callconv","Language.Haskell.TH.Syntax.Name","Language.Haskell.TH.Syntax.Safety","Language.Haskell.TH.Syntax.Type"]),
       ("Language.Haskell.TH.Syntax.FunDep",["[Language.Haskell.TH.Syntax.Name]"]),
       ("Language.Haskell.TH.Syntax.Guard",["[Language.Haskell.TH.Syntax.Stmt]","Language.Haskell.TH.Syntax.Exp"]),
       ("Language.Haskell.TH.Syntax.Kind",["Language.Haskell.TH.Syntax.Type"]),
       ("Language.Haskell.TH.Syntax.Lit",["[GHC.Word.Word8]","GHC.Base.String","GHC.Real.Rational","GHC.Types.Char","GHC.Integer.Type.Integer"]),
       ("Language.Haskell.TH.Syntax.Match",["[Language.Haskell.TH.Syntax.Dec]","Language.Haskell.TH.Syntax.Body","Language.Haskell.TH.Syntax.Pat"]),
       ("Language.Haskell.TH.Syntax.ModName",["GHC.Base.String"]),
       ("Language.Haskell.TH.Syntax.OccName",["GHC.Base.String"]),
       ("Language.Haskell.TH.Syntax.Pat",["[Language.Haskell.TH.Syntax.FieldPat]","[Language.Haskell.TH.Syntax.Pat]","Language.Haskell.TH.Syntax.Exp","Language.Haskell.TH.Syntax.Lit","Language.Haskell.TH.Syntax.Name","Language.Haskell.TH.Syntax.Pat","Language.Haskell.TH.Syntax.Type"]),
       ("Language.Haskell.TH.Syntax.Phases",["GHC.Types.Int"]),
       ("Language.Haskell.TH.Syntax.PkgName",["GHC.Base.String"]),
       ("Language.Haskell.TH.Syntax.Pragma",["Data.Maybe.Maybe Language.Haskell.TH.Syntax.Inline","[Language.Haskell.TH.Syntax.RuleBndr]","GHC.Base.String","Language.Haskell.TH.Syntax.AnnTarget","Language.Haskell.TH.Syntax.Exp","Language.Haskell.TH.Syntax.Inline","Language.Haskell.TH.Syntax.Name","Language.Haskell.TH.Syntax.Phases","Language.Haskell.TH.Syntax.RuleMatch","Language.Haskell.TH.Syntax.Type"]),
       ("Language.Haskell.TH.Syntax.Pred",["[Language.Haskell.TH.Syntax.Type]","Language.Haskell.TH.Syntax.Name","Language.Haskell.TH.Syntax.Type"]),
       ("Language.Haskell.TH.Syntax.Range",["Language.Haskell.TH.Syntax.Exp"]),
       ("Language.Haskell.TH.Syntax.RuleBndr",["Language.Haskell.TH.Syntax.Name","Language.Haskell.TH.Syntax.Type"]),
       ("Language.Haskell.TH.Syntax.Stmt",["[[Language.Haskell.TH.Syntax.Stmt]]","[Language.Haskell.TH.Syntax.Dec]","Language.Haskell.TH.Syntax.Exp","Language.Haskell.TH.Syntax.Pat"]),
       ("Language.Haskell.TH.Syntax.StrictType",["(Language.Haskell.TH.Syntax.Strict, Language.Haskell.TH.Syntax.Type)"]),
       ("Language.Haskell.TH.Syntax.TyLit",["GHC.Base.String","GHC.Integer.Type.Integer"]),
       ("Language.Haskell.TH.Syntax.TySynEqn",["[Language.Haskell.TH.Syntax.Type]","Language.Haskell.TH.Syntax.Type"]),
       ("Language.Haskell.TH.Syntax.TyVarBndr",["Language.Haskell.TH.Syntax.Kind","Language.Haskell.TH.Syntax.Name"]),
       ("Language.Haskell.TH.Syntax.Type",["[Language.Haskell.TH.Syntax.TyVarBndr]","GHC.Types.Int","Language.Haskell.TH.Syntax.Cxt","Language.Haskell.TH.Syntax.Kind","Language.Haskell.TH.Syntax.Name","Language.Haskell.TH.Syntax.TyLit","Language.Haskell.TH.Syntax.Type"]),
       ("Language.Haskell.TH.Syntax.VarStrictType",["(Language.Haskell.TH.Syntax.Name, Language.Haskell.TH.Syntax.Strict, Language.Haskell.TH.Syntax.Type)"]),
       ("[(Language.Haskell.TH.Syntax.Guard, Language.Haskell.TH.Syntax.Exp)]",["(Language.Haskell.TH.Syntax.Guard, Language.Haskell.TH.Syntax.Exp)","[]"]),
       ("[GHC.Word.Word8]",["GHC.Word.Word8","[]"]),
       ("[Language.Haskell.TH.Syntax.Clause]",["Language.Haskell.TH.Syntax.Clause","[]"]),
       ("[Language.Haskell.TH.Syntax.Con]",["Language.Haskell.TH.Syntax.Con","[]"]),
       ("[Language.Haskell.TH.Syntax.Dec]",["Language.Haskell.TH.Syntax.Dec","[]"]),
       ("[Language.Haskell.TH.Syntax.Exp]",["Language.Haskell.TH.Syntax.Exp","[]"]),
       ("[Language.Haskell.TH.Syntax.FieldExp]",["Language.Haskell.TH.Syntax.FieldExp","[]"]),
       ("[Language.Haskell.TH.Syntax.FieldPat]",["Language.Haskell.TH.Syntax.FieldPat","[]"]),
       ("[Language.Haskell.TH.Syntax.FunDep]",["Language.Haskell.TH.Syntax.FunDep","[]"]),
       ("[Language.Haskell.TH.Syntax.Match]",["Language.Haskell.TH.Syntax.Match","[]"]),
       ("[Language.Haskell.TH.Syntax.Name]",["Language.Haskell.TH.Syntax.Name","[]"]),
       ("[Language.Haskell.TH.Syntax.Pat]",["Language.Haskell.TH.Syntax.Pat","[]"]),
       ("[Language.Haskell.TH.Syntax.Pred]",["Language.Haskell.TH.Syntax.Pred","[]"]),
       ("[Language.Haskell.TH.Syntax.Role]",["Language.Haskell.TH.Syntax.Role","[]"]),
       ("[Language.Haskell.TH.Syntax.RuleBndr]",["Language.Haskell.TH.Syntax.RuleBndr","[]"]),
       ("[Language.Haskell.TH.Syntax.Stmt]",["Language.Haskell.TH.Syntax.Stmt","[]"]),
       ("[Language.Haskell.TH.Syntax.StrictType]",["Language.Haskell.TH.Syntax.StrictType","[]"]),
       ("[Language.Haskell.TH.Syntax.TySynEqn]",["Language.Haskell.TH.Syntax.TySynEqn","[]"]),
       ("[Language.Haskell.TH.Syntax.TyVarBndr]",["Language.Haskell.TH.Syntax.TyVarBndr","[]"]),
       ("[Language.Haskell.TH.Syntax.Type]",["Language.Haskell.TH.Syntax.Type","[]"]),
       ("[Language.Haskell.TH.Syntax.VarStrictType]",["Language.Haskell.TH.Syntax.VarStrictType","[]"]),
       ("[[Language.Haskell.TH.Syntax.Stmt]]",["[Language.Haskell.TH.Syntax.Stmt]","[]"])]

typeEdges :: Set (String, [String])
typeEdges =
    fromList
      [("GHC.Base.String",["[GHC.Types.Char]"]),
       ("GHC.Integer.Type.Integer",["GHC.Prim.ByteArray#","GHC.Prim.Int#"]),
       ("GHC.Prim.ByteArray#",[]),
       ("GHC.Prim.Char#",[]),
       ("GHC.Prim.Int#",[]),
       ("GHC.Types.Char",["GHC.Prim.Char#"]),
       ("GHC.Types.Int",["GHC.Prim.Int#"]),
       ("Language.Haskell.TH.Syntax.Cxt",["[Language.Haskell.TH.Syntax.Pred]"]),
       ("Language.Haskell.TH.Syntax.Kind",["Language.Haskell.TH.Syntax.Type"]),
       ("Language.Haskell.TH.Syntax.ModName",["GHC.Base.String"]),
       ("Language.Haskell.TH.Syntax.Name",["Language.Haskell.TH.Syntax.NameFlavour","Language.Haskell.TH.Syntax.OccName"]),
       ("Language.Haskell.TH.Syntax.NameFlavour",["GHC.Prim.Int#","Language.Haskell.TH.Syntax.ModName","Language.Haskell.TH.Syntax.NameSpace","Language.Haskell.TH.Syntax.PkgName"]),
       ("Language.Haskell.TH.Syntax.NameSpace",[]),
       ("Language.Haskell.TH.Syntax.OccName",["GHC.Base.String"]),
       ("Language.Haskell.TH.Syntax.PkgName",["GHC.Base.String"]),
       ("Language.Haskell.TH.Syntax.Pred",["[Language.Haskell.TH.Syntax.Type]","Language.Haskell.TH.Syntax.Name","Language.Haskell.TH.Syntax.Type"]),
       ("Language.Haskell.TH.Syntax.TyLit",["GHC.Base.String","GHC.Integer.Type.Integer"]),
       ("Language.Haskell.TH.Syntax.Type",["[Language.Haskell.TH.Syntax.TyVarBndr]","GHC.Types.Int","Language.Haskell.TH.Syntax.Cxt","Language.Haskell.TH.Syntax.Kind","Language.Haskell.TH.Syntax.Name","Language.Haskell.TH.Syntax.TyLit","Language.Haskell.TH.Syntax.Type"]),
       ("Language.Haskell.TH.Syntax.TyVarBndr",["Language.Haskell.TH.Syntax.Kind","Language.Haskell.TH.Syntax.Name"]),
       ("[GHC.Types.Char]",["GHC.Types.Char","[]"]),
       ("[Language.Haskell.TH.Syntax.Pred]",["Language.Haskell.TH.Syntax.Pred","[]"]),
       ("[Language.Haskell.TH.Syntax.Type]",["Language.Haskell.TH.Syntax.Type","[]"]),
       ("[Language.Haskell.TH.Syntax.TyVarBndr]",["Language.Haskell.TH.Syntax.TyVarBndr","[]"]),
       ("[]",[])]
      {-[("GHC.Base.String",[]),
       ("GHC.Integer.Type.Integer",["GHC.Prim.ByteArray#","GHC.Prim.Int#"]),
       ("GHC.Prim.ByteArray#",[]),
       ("GHC.Prim.Int#",[]),
       ("GHC.Types.Int",["GHC.Prim.Int#"]),
       ("Language.Haskell.TH.Syntax.Cxt",[]),
       ("Language.Haskell.TH.Syntax.Kind",[]),
       ("Language.Haskell.TH.Syntax.ModName",["GHC.Base.String"]),
       ("Language.Haskell.TH.Syntax.Name",["Language.Haskell.TH.Syntax.NameFlavour","Language.Haskell.TH.Syntax.OccName"]),
       ("Language.Haskell.TH.Syntax.NameFlavour",["GHC.Prim.Int#","Language.Haskell.TH.Syntax.ModName","Language.Haskell.TH.Syntax.NameSpace","Language.Haskell.TH.Syntax.PkgName"]),
       ("Language.Haskell.TH.Syntax.NameSpace",[]),
       ("Language.Haskell.TH.Syntax.OccName",["GHC.Base.String"]),
       ("Language.Haskell.TH.Syntax.PkgName",["GHC.Base.String"]),
       ("Language.Haskell.TH.Syntax.TyLit",["GHC.Base.String","GHC.Integer.Type.Integer"]),
       ("Language.Haskell.TH.Syntax.TyVarBndr",["Language.Haskell.TH.Syntax.Kind","Language.Haskell.TH.Syntax.Name"]),
       ("Language.Haskell.TH.Syntax.Type",["[Language.Haskell.TH.Syntax.TyVarBndr]",
                                           "GHC.Types.Int",
                                           "Language.Haskell.TH.Syntax.Cxt",
                                           "Language.Haskell.TH.Syntax.Kind",
                                           "Language.Haskell.TH.Syntax.Name",
                                           "Language.Haskell.TH.Syntax.TyLit",
                                           "Language.Haskell.TH.Syntax.Type"]),
       ("[Language.Haskell.TH.Syntax.TyVarBndr]",["Language.Haskell.TH.Syntax.TyVarBndr"])]-}
    

arity0SubtypesOfDec 
    :: Set String
arity0SubtypesOfDec =
    fromList
         [ "(Language.Haskell.TH.Syntax.Guard, Language.Haskell.TH.Syntax.Exp)",
           "(Language.Haskell.TH.Syntax.Name, Language.Haskell.TH.Syntax.Exp)",
           "(Language.Haskell.TH.Syntax.Name, Language.Haskell.TH.Syntax.Pat)",
           "(Language.Haskell.TH.Syntax.Name, Language.Haskell.TH.Syntax.Strict, Language.Haskell.TH.Syntax.Type)",
           "(Language.Haskell.TH.Syntax.Strict, Language.Haskell.TH.Syntax.Type)",
           "Data.Maybe.Maybe Language.Haskell.TH.Syntax.Exp",
           "Data.Maybe.Maybe Language.Haskell.TH.Syntax.Inline",
           "Data.Maybe.Maybe Language.Haskell.TH.Syntax.Kind",
           "GHC.Base.String",
           "GHC.Integer.Type.Integer",
           "GHC.Prim.ByteArray#",
           "GHC.Prim.Char#",
           "GHC.Prim.Int#",
           "GHC.Prim.Word#",
           "GHC.Real.Rational",
           "GHC.Real.Ratio GHC.Integer.Type.Integer",
           "GHC.Types.Char",
           "GHC.Types.Int",
           "GHC.Word.Word8",
           "Language.Haskell.TH.Syntax.AnnTarget",
           "Language.Haskell.TH.Syntax.Body",
           "Language.Haskell.TH.Syntax.Callconv",
           "Language.Haskell.TH.Syntax.Clause",
           "Language.Haskell.TH.Syntax.Con",
           "Language.Haskell.TH.Syntax.Cxt",
           "Language.Haskell.TH.Syntax.FieldExp",
           "Language.Haskell.TH.Syntax.FieldPat",
           "Language.Haskell.TH.Syntax.Kind",
           "Language.Haskell.TH.Syntax.StrictType",
           "Language.Haskell.TH.Syntax.VarStrictType",
           "Language.Haskell.TH.Syntax.Dec",
           "Language.Haskell.TH.Syntax.Exp",
           "Language.Haskell.TH.Syntax.FamFlavour",
           "Language.Haskell.TH.Syntax.Fixity",
           "Language.Haskell.TH.Syntax.FixityDirection",
           "Language.Haskell.TH.Syntax.Foreign",
           "Language.Haskell.TH.Syntax.FunDep",
           "Language.Haskell.TH.Syntax.Guard",
           "Language.Haskell.TH.Syntax.Inline",
           "Language.Haskell.TH.Syntax.Lit",
           "Language.Haskell.TH.Syntax.Match",
           "Language.Haskell.TH.Syntax.ModName",
           "Language.Haskell.TH.Syntax.Name",
           "Language.Haskell.TH.Syntax.NameFlavour",
           "Language.Haskell.TH.Syntax.NameSpace",
           "Language.Haskell.TH.Syntax.OccName",
           "Language.Haskell.TH.Syntax.Pat",
           "Language.Haskell.TH.Syntax.Phases",
           "Language.Haskell.TH.Syntax.PkgName",
           "Language.Haskell.TH.Syntax.Pragma",
           "Language.Haskell.TH.Syntax.Pred",
           "Language.Haskell.TH.Syntax.Range",
           "Language.Haskell.TH.Syntax.Role",
           "Language.Haskell.TH.Syntax.RuleBndr",
           "Language.Haskell.TH.Syntax.RuleMatch",
           "Language.Haskell.TH.Syntax.Safety",
           "Language.Haskell.TH.Syntax.Stmt",
           "Language.Haskell.TH.Syntax.Strict",
           "Language.Haskell.TH.Syntax.TyLit",
           "Language.Haskell.TH.Syntax.TySynEqn",
           "Language.Haskell.TH.Syntax.TyVarBndr",
           "Language.Haskell.TH.Syntax.Type",
           "[(Language.Haskell.TH.Syntax.Guard, Language.Haskell.TH.Syntax.Exp)]",
           "[GHC.Types.Char]",
           "[GHC.Word.Word8]",
           "[Language.Haskell.TH.Syntax.Clause]",
           "[Language.Haskell.TH.Syntax.Con]",
           "[Language.Haskell.TH.Syntax.Dec]",
           "[Language.Haskell.TH.Syntax.Exp]",
           "[Language.Haskell.TH.Syntax.FunDep]",
           "[Language.Haskell.TH.Syntax.Match]",
           "[Language.Haskell.TH.Syntax.Name]",
           "[Language.Haskell.TH.Syntax.Pat]",
           "[Language.Haskell.TH.Syntax.Pred]",
           "[Language.Haskell.TH.Syntax.Role]",
           "[Language.Haskell.TH.Syntax.RuleBndr]",
           "[Language.Haskell.TH.Syntax.Stmt]",
           "[Language.Haskell.TH.Syntax.TySynEqn]",
           "[Language.Haskell.TH.Syntax.TyVarBndr]",
           "[Language.Haskell.TH.Syntax.Type]",
           "[[Language.Haskell.TH.Syntax.Stmt]]",
           "[Language.Haskell.TH.Syntax.FieldExp]",
           "[Language.Haskell.TH.Syntax.FieldPat]",
           "[Language.Haskell.TH.Syntax.StrictType]",
           "[Language.Haskell.TH.Syntax.VarStrictType]"
         ]


subtypesOfDec :: Set String
subtypesOfDec =
    union
       arity0SubtypesOfDec
       (fromList
          ["(,)",
           "(,) Language.Haskell.TH.Syntax.Guard",
           "(,) Language.Haskell.TH.Syntax.Name",
           "(,) Language.Haskell.TH.Syntax.Strict",
           "(,,)",
           "(,,) Language.Haskell.TH.Syntax.Name",
           "(,,) Language.Haskell.TH.Syntax.Name Language.Haskell.TH.Syntax.Strict",
           "Data.Maybe.Maybe",
           "GHC.Real.Ratio",
           "a_0",
           "[]"])
