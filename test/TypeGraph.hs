{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wall #-}
module TypeGraph where

import Control.Monad (filterM)
import Data.Map as Map (toList)
import Data.Set as Set (Set, fromList, toList, union)
import GHC.Prim -- ByteArray#, Char#, etc
import Language.Haskell.TH
import Language.Haskell.TH.Desugar (withLocalDeclarations)
import Language.Haskell.TH.Context.Expand (expandType, runExpanded, E)
import Language.Haskell.TH.Context.Helpers (pprint', typeArity)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.TypeGraph (typeGraphVertices, typeGraphEdges, VertexStatus(Vertex))
import Test.Hspec hiding (runIO)
import Test.Hspec.Core.Spec (SpecM)

import Common

tests :: SpecM () ()
tests = do
  it "can find the subtypes of Type" $ do
     setDifferences (fromList $(withLocalDeclarations [] $
                                  runQ [t|Type|] >>=
                                  expandType >>= \ (typ :: E Type) ->
                                  typeGraphVertices (const $ return Vertex) [typ] >>=
                                  runQ . lift . map (pprint' . unReify . runExpanded) . Set.toList)) subtypesOfType
        `shouldBe` noDifferences

  it "can find the edges of the subtype graph of Type" $ do
     setDifferences (fromList $(withLocalDeclarations [] $
                                runQ [t|Type|] >>=
                                expandType >>= \ (typ :: E Type) ->
                                typeGraphEdges (const $ return Vertex) [typ] >>=
                                runQ . lift . map toStrings' . Map.toList)) typeEdges
        `shouldBe` noDifferences

  it "can find the edges of the subtype graph of Dec" $ do
     setDifferences (fromList $(withLocalDeclarations [] $
                                runQ [t|Dec|] >>=
                                expandType >>= \ (typ :: E Type) ->
                                typeGraphEdges (const $ return Vertex) [typ] >>=
                                runQ . lift . map toStrings' . Map.toList)) decEdges
        `shouldBe` noDifferences

  it "can find the subtypes of Dec" $ do
     setDifferences (fromList $(withLocalDeclarations [] $
                                runQ [t|Dec|] >>=
                                expandType >>= \ (typ :: E Type) ->
                                typeGraphVertices (const $ return Vertex) [typ] >>=
                                runQ . lift . map (pprint' . unReify . runExpanded) . Set.toList)) subtypesOfDec
        `shouldBe` noDifferences

  it "can find the arity 0 subtypes of Dec" $ do
     setDifferences (fromList $(withLocalDeclarations [] $
                                runQ [t|Dec|] >>=
                                expandType >>= \ (typ :: E Type) ->
                                typeGraphVertices (const $ return Vertex) [typ] >>=
                                filterM (\ t -> typeArity (runExpanded t) >>= \ a -> return (a == 0)) . Set.toList >>=
                                runQ . lift . map (pprint' . unReify . runExpanded))) arity0SubtypesOfDec
        `shouldBe` noDifferences

subtypesOfType :: Set String
subtypesOfType =
    fromList ["BigNat","ByteArray#","Char","Char#","Cxt","Int","Int#","Integer","Kind","ModName","Name","NameFlavour","NameSpace","OccName","PkgName","Pred","String","TyLit","TyVarBndr","Type","[Char]","[Pred]","[TyVarBndr]","[]"]

decEdges :: Set (String, [String])
decEdges =
    fromList
      [("(,)",[]),("(,,)",[]),("[]",[]),("(,) Guard",["Guard","(,)"]),("(,) Name",["Name","(,)"]),("(,) Strict",["Strict","(,)"]),("(,,) Name",["Name","(,,)"]),("(,,) Name Strict",["(,,) Name","Strict"]),("(Guard, Exp)",["(,) Guard","Exp"]),("(Name, Exp)",["(,) Name","Exp"]),("(Name, Pat)",["(,) Name","Pat"]),("(Name, Strict, Type)",["(,,) Name Strict","Type"]),("(Strict, Type)",["(,) Strict","Type"]),("AnnTarget",["Name"]),("BigNat",["ByteArray#"]),("Body",["[(Guard, Exp)]","Exp"]),("ByteArray#",[]),("Callconv",[]),("Char",["Char#"]),("Char#",[]),("Clause",["[Dec]","[Pat]","Body"]),("Con",["[StrictType]","[TyVarBndr]","[VarStrictType]","Con","Cxt","Name","StrictType"]),("Cxt",["[Pred]"]),("Dec",["Maybe Kind","[Clause]","[Con]","[Dec]","[FunDep]","[Name]","[Role]","[TySynEqn]","[TyVarBndr]","[Type]","Body","Con","Cxt","FamFlavour","Fixity","Foreign","Name","Pat","Pragma","TySynEqn","Type"]),("Exp",["Maybe Exp","[(Guard, Exp)]","[Dec]","[Exp]","[FieldExp]","[Match]","[Pat]","[Stmt]","Exp","Lit","Name","Range","Type"]),("FamFlavour",[]),("FieldExp",["(Name, Exp)"]),("FieldPat",["(Name, Pat)"]),("Fixity",["Int","FixityDirection"]),("FixityDirection",[]),("Foreign",["String","Callconv","Name","Safety","Type"]),("FunDep",["[Name]"]),("Guard",["[Stmt]","Exp"]),("Inline",[]),("Int",["Int#"]),("Int#",[]),("Integer",["Int#","BigNat"]),("Kind",["Type"]),("Lit",["[Word8]","String","Rational","Char","Integer"]),("Match",["[Dec]","Body","Pat"]),("Maybe",["a"]),("Maybe Exp",["Maybe","Exp"]),("Maybe Inline",["Maybe","Inline"]),("Maybe Kind",["Maybe","Kind"]),("ModName",["String"]),("Name",["NameFlavour","OccName"]),("NameFlavour",["Int","ModName","NameSpace","PkgName"]),("NameSpace",[]),("OccName",["String"]),("Pat",["[FieldPat]","[Pat]","Exp","Lit","Name","Pat","Type"]),("Phases",["Int"]),("PkgName",["String"]),("Pragma",["Maybe Inline","[RuleBndr]","String","Int","AnnTarget","Exp","Inline","Name","Phases","RuleMatch","Type"]),("Pred",["Type"]),("Range",["Exp"]),("Ratio",["a"]),("Ratio Integer",["Ratio","Integer"]),("Rational",["Ratio Integer"]),("Role",[]),("RuleBndr",["Name","Type"]),("RuleMatch",[]),("Safety",[]),("Stmt",["[[Stmt]]","[Dec]","Exp","Pat"]),("Strict",[]),("StrictType",["(Strict, Type)"]),("String",["[Char]"]),("TyLit",["String","Integer"]),("TySynEqn",["[Type]","Type"]),("TyVarBndr",["Kind","Name"]),("Type",["[TyVarBndr]","Int","Cxt","Kind","Name","TyLit","Type"]),("VarStrictType",["(Name, Strict, Type)"]),("Word#",[]),("Word8",["Word#"]),("[(Guard, Exp)]",["(Guard, Exp)","[]"]),("[Char]",["Char","[]"]),("[Clause]",["Clause","[]"]),("[Con]",["Con","[]"]),("[Dec]",["Dec","[]"]),("[Exp]",["Exp","[]"]),("[FieldExp]",["FieldExp","[]"]),("[FieldPat]",["FieldPat","[]"]),("[FunDep]",["FunDep","[]"]),("[Match]",["Match","[]"]),("[Name]",["Name","[]"]),("[Pat]",["Pat","[]"]),("[Pred]",["Pred","[]"]),("[Role]",["Role","[]"]),("[RuleBndr]",["RuleBndr","[]"]),("[Stmt]",["Stmt","[]"]),("[StrictType]",["StrictType","[]"]),("[TySynEqn]",["TySynEqn","[]"]),("[TyVarBndr]",["TyVarBndr","[]"]),("[Type]",["Type","[]"]),("[VarStrictType]",["VarStrictType","[]"]),("[Word8]",["Word8","[]"]),("[[Stmt]]",["[Stmt]","[]"]),("a",[])]

typeEdges :: Set (String, [String])
typeEdges =
    fromList
      [("BigNat",["ByteArray#"]),("ByteArray#",[]),("Char",["Char#"]),("Char#",[]),("Cxt",["[Pred]"]),("Int",["Int#"]),("Int#",[]),("Integer",["Int#","BigNat"]),("Kind",["Type"]),("ModName",["String"]),("Name",["NameFlavour","OccName"]),("NameFlavour",["Int","ModName","NameSpace","PkgName"]),("NameSpace",[]),("OccName",["String"]),("PkgName",["String"]),("Pred",["Type"]),("String",["[Char]"]),("TyLit",["String","Integer"]),("TyVarBndr",["Kind","Name"]),("Type",["[TyVarBndr]","Int","Cxt","Kind","Name","TyLit","Type"]),("[Char]",["Char","[]"]),("[Pred]",["Pred","[]"]),("[TyVarBndr]",["TyVarBndr","[]"]),("[]",[])]

arity0SubtypesOfDec :: Set String
arity0SubtypesOfDec =
    fromList ["(Guard, Exp)","(Name, Exp)","(Name, Pat)","(Name, Strict, Type)","(Strict, Type)","AnnTarget","BigNat","Body","ByteArray#","Callconv","Char","Char#","Clause","Con","Cxt","Dec","Exp","FamFlavour","FieldExp","FieldPat","Fixity","FixityDirection","Foreign","FunDep","Guard","Inline","Int","Int#","Integer","Kind","Lit","Match","Maybe Exp","Maybe Inline","Maybe Kind","ModName","Name","NameFlavour","NameSpace","OccName","Pat","Phases","PkgName","Pragma","Pred","Range","Ratio Integer","Rational","Role","RuleBndr","RuleMatch","Safety","Stmt","Strict","StrictType","String","TyLit","TySynEqn","TyVarBndr","Type","VarStrictType","Word#","Word8","[(Guard, Exp)]","[Char]","[Clause]","[Con]","[Dec]","[Exp]","[FieldExp]","[FieldPat]","[FunDep]","[Match]","[Name]","[Pat]","[Pred]","[Role]","[RuleBndr]","[Stmt]","[StrictType]","[TySynEqn]","[TyVarBndr]","[Type]","[VarStrictType]","[Word8]","[[Stmt]]"]

subtypesOfDec :: Set String
subtypesOfDec =
    union
       arity0SubtypesOfDec
       (fromList ["(,)","(,) Guard","(,) Name","(,) Strict","(,,)","(,,) Name","(,,) Name Strict","Maybe","Ratio","[]","a"])
