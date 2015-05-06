{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}
module Values where

import Control.Monad (filterM)
import Data.Map as Map (Map, fromList, toList)
import Data.Ratio (Ratio)
import Data.Set as Set (Set, empty, fromList, toList, union)
import GHC.Prim -- ByteArray#, Char#, etc
import Language.Haskell.TH
import Language.Haskell.TH.Context.Expand (E(E), expandType, markExpanded)
import Language.Haskell.TH.Context.Helpers (typeArity)
import Language.Haskell.TH.Context.TypeGraph (TypeGraphVertex(..), typeGraphVertices, typeGraphEdges, VertexHint(Normal))
import Language.Haskell.TH.Desugar (withLocalDeclarations)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.Syntax
import Test.Hspec hiding (runIO)
import Test.Hspec.Core.Spec (SpecM)

import Common

subtypesOfType :: Set String
subtypesOfType =
    Set.fromList
    [
#if MIN_VERSION_template_haskell(2,10,0)
     "BigNat","BigNat (field Integer.Jn#[1])","BigNat (field Integer.Jp#[1])","ByteArray#","ByteArray# (field BigNat.BN#[1])","Char","Char#","Char# (field Char.C#[1])","Int","Int (field NameFlavour.NameL[1])","Int (field NameFlavour.NameU[1])","Int (field Type.PromotedTupleT[1])","Int (field Type.TupleT[1])","Int (field Type.UnboxedTupleT[1])","Int#","Int# (field Int.I#[1])","Int# (field Integer.S#[1])","Integer","Integer (field TyLit.NumTyLit[1])","ModName","ModName (field NameFlavour.NameG[3])","ModName (field NameFlavour.NameQ[1])","Name","Name (field TyVarBndr.KindedTV[1])","Name (field TyVarBndr.PlainTV[1])","Name (field Type.ConT[1])","Name (field Type.PromotedT[1])","Name (field Type.VarT[1])","NameFlavour","NameFlavour (field Name.Name[2])","NameSpace","NameSpace (field NameFlavour.NameG[1])","OccName","OccName (field Name.Name[1])","PkgName","PkgName (field NameFlavour.NameG[2])","TyLit","TyLit (field Type.LitT[1])","TyVarBndr","Type (aka Kind, aka Pred)","Type (aka Kind, aka Pred, field TyVarBndr.KindedTV[2])","Type (aka Kind, aka Pred, field Type.AppT[1])","Type (aka Kind, aka Pred, field Type.AppT[2])","Type (aka Kind, aka Pred, field Type.ForallT[3])","Type (aka Kind, aka Pred, field Type.SigT[1])","Type (aka Kind, aka Pred, field Type.SigT[2])","[Char] (aka String)","[Char] (aka String, field ModName.ModName[1])","[Char] (aka String, field OccName.OccName[1])","[Char] (aka String, field PkgName.PkgName[1])","[Char] (aka String, field TyLit.StrTyLit[1])","[TyVarBndr]","[TyVarBndr] (field Type.ForallT[1])","[Type] (aka Cxt)","[Type] (aka Cxt, field Type.ForallT[2])","[]"
#else
     "ByteArray#","ByteArray# (field Integer.J#[2])","Char","Char#","Char# (field Char.C#[1])","Int","Int (field Type.PromotedTupleT[1])","Int (field Type.TupleT[1])","Int (field Type.UnboxedTupleT[1])","Int#","Int# (field Int.I#[1])","Int# (field Integer.J#[1])","Int# (field Integer.S#[1])","Int# (field NameFlavour.NameL[1])","Int# (field NameFlavour.NameU[1])","Integer","Integer (field TyLit.NumTyLit[1])","ModName","ModName (field NameFlavour.NameG[3])","ModName (field NameFlavour.NameQ[1])","Name","Name (field Pred.ClassP[1])","Name (field TyVarBndr.KindedTV[1])","Name (field TyVarBndr.PlainTV[1])","Name (field Type.ConT[1])","Name (field Type.PromotedT[1])","Name (field Type.VarT[1])","NameFlavour","NameFlavour (field Name.Name[2])","NameSpace","NameSpace (field NameFlavour.NameG[1])","OccName","OccName (field Name.Name[1])","PkgName","PkgName (field NameFlavour.NameG[2])","Pred","TyLit","TyLit (field Type.LitT[1])","TyVarBndr","Type (aka Kind)","Type (aka Kind, field Pred.EqualP[1])","Type (aka Kind, field Pred.EqualP[2])","Type (aka Kind, field TyVarBndr.KindedTV[2])","Type (aka Kind, field Type.AppT[1])","Type (aka Kind, field Type.AppT[2])","Type (aka Kind, field Type.ForallT[3])","Type (aka Kind, field Type.SigT[1])","Type (aka Kind, field Type.SigT[2])","[Char] (aka String)","[Char] (aka String, field ModName.ModName[1])","[Char] (aka String, field OccName.OccName[1])","[Char] (aka String, field PkgName.PkgName[1])","[Char] (aka String, field TyLit.StrTyLit[1])","[Pred] (aka Cxt)","[Pred] (aka Cxt, field Type.ForallT[2])","[TyVarBndr]","[TyVarBndr] (field Type.ForallT[1])","[Type]","[Type] (field Pred.ClassP[2])","[]"
#endif
    ]

typeEdges :: Set (String, [String])
typeEdges =
  Set.fromList
    [
#if MIN_VERSION_template_haskell(2,10,0)
     ("BigNat",["ByteArray#"]),
     ("ByteArray#",[]),
     ("Char",["Char#"]),
     ("Char#",[]),
     ("Int",["Int#"]),
     ("Int#",[]),
     ("Integer",["Int#","BigNat"]),
     ("ModName",["[Char] (aka String)"]),
     ("Name",["NameFlavour","OccName"]),
     ("NameFlavour",["Int","ModName","NameSpace","PkgName"]),
     ("NameSpace",[]),
     ("OccName",["[Char] (aka String)"]),
     ("PkgName",["[Char] (aka String)"]),
     ("TyLit",["Integer","[Char] (aka String)"]),
     ("TyVarBndr",["Name","Type (aka Kind, aka Pred)"]),
     ("Type (aka Kind, aka Pred)",["[TyVarBndr]","Int","Name","TyLit","[Type] (aka Cxt)"]),
     ("[Char] (aka String)",["Char","[]"]),
     ("[TyVarBndr]",["TyVarBndr","[]"]),
     ("[Type] (aka Cxt)",["[]","Type (aka Kind, aka Pred)"]),
     ("[]",[])
#else
     ("ByteArray#",[]),
     ("Char",["Char#"]),
     ("Char#",[]),
     ("Int",["Int#"]),
     ("Int#",[]),
     ("Integer",["ByteArray#","Int#"]),
     ("ModName",["[Char] (aka String)"]),
     ("Name",["NameFlavour","OccName"]),
     ("NameFlavour",["Int#","ModName","NameSpace","PkgName"]),
     ("NameSpace",[]),
     ("OccName",["[Char] (aka String)"]),
     ("PkgName",["[Char] (aka String)"]),
     ("Pred",["[Type]","Name","Type (aka Kind)"]),
     ("TyLit",["Integer","[Char] (aka String)"]),
     ("TyVarBndr",["Name","Type (aka Kind)"]),
     ("Type (aka Kind)",["[TyVarBndr]","Int","Name","TyLit","[Pred] (aka Cxt)"]),
     ("[Char] (aka String)",["Char","[]"]),
     ("[Pred] (aka Cxt)",["Pred","[]"]),
     ("[TyVarBndr]",["TyVarBndr","[]"]),
     ("[Type]",["[]","Type (aka Kind)"]),
     ("[]",[])
#endif
    ]

arity0TypeEdges :: Set (String, [String])
arity0TypeEdges =
  Set.fromList
    [
#if MIN_VERSION_template_haskell(2,10,0)
     ("BigNat",["ByteArray#"]),
     ("ByteArray#",[]),
     ("Char",["Char#"]),
     ("Char#",[]),
     ("Int",["Int#"]),
     ("Int#",[]),
     ("Integer",["Int#","BigNat"]),
     ("ModName",["[Char] (aka String)"]),
     ("Name",["NameFlavour","OccName"]),
     ("NameFlavour",["Int","ModName","NameSpace","PkgName"]),
     ("NameSpace",[]),
     ("OccName",["[Char] (aka String)"]),
     ("PkgName",["[Char] (aka String)"]),
     ("TyLit",["Integer","[Char] (aka String)"]),
     ("TyVarBndr",["Name","Type (aka Kind, aka Pred)"]),
     ("Type (aka Kind, aka Pred)",["[TyVarBndr]","Int","Name","TyLit","[Type] (aka Cxt)"]),
     ("[Char] (aka String)",["Char"]),
     ("[TyVarBndr]",["TyVarBndr"]),
     ("[Type] (aka Cxt)",["Type (aka Kind, aka Pred)"])
#else
     ("ByteArray#",[]),
     ("Char",["Char#"]),
     ("Char#",[]),
     ("Int",["Int#"]),
     ("Int#",[]),
     ("Integer",["ByteArray#","Int#"]),
     ("ModName",["[Char] (aka String)"]),
     ("Name",["NameFlavour","OccName"]),
     ("NameFlavour",["Int#","ModName","NameSpace","PkgName"]),
     ("NameSpace",[]),
     ("OccName",["[Char] (aka String)"]),
     ("PkgName",["[Char] (aka String)"]),
     ("Pred",["[Type]","Name","Type (aka Kind)"]),
     ("TyLit",["Integer","[Char] (aka String)"]),
     ("TyVarBndr",["Name","Type (aka Kind)"]),
     ("Type (aka Kind)",["[TyVarBndr]","Int","Name","TyLit","[Pred] (aka Cxt)"]),
     ("[Char] (aka String)",["Char"]),
     ("[Pred] (aka Cxt)",["Pred"]),
     ("[TyVarBndr]",["TyVarBndr"]),
     ("[Type]",["Type (aka Kind)"])
#endif
    ]

arity0TypeEdges' :: Set (String, [String])
arity0TypeEdges' =
  Set.fromList
    [
#if MIN_VERSION_template_haskell(2,10,0)
#else
     ("ByteArray#",[]),
     ("Char",[]),
     ("Char#",[]),
     ("Int",[]),
     ("Int#",[]),
     ("Integer",[]),
     ("ModName",["Char","[]","[Char] (aka String)"]),
     ("Name",["Int#","ModName","NameSpace","PkgName","[Char] (aka String)"]),
     ("NameFlavour",["[Char] (aka String)"]),
     ("NameSpace",[]),
     ("OccName",["Char","[]","[Char] (aka String)"]),
     ("PkgName",["Char","[]","[Char] (aka String)"]),
     ("Pred",["[TyVarBndr]","Int","Name","NameFlavour","OccName","TyLit","[]","[Pred] (aka Cxt)","Type (aka Kind)"]),
     ("TyLit",["ByteArray#","Int#","Char","[]","[Char] (aka String)"]),
     ("TyVarBndr",["[TyVarBndr]","Int","Name","NameFlavour","OccName","TyLit","[Pred] (aka Cxt)","Type (aka Kind)"]),
     ("Type (aka Kind)",["[TyVarBndr]","Int#","Int","Integer","Name","NameFlavour","OccName","Pred","TyLit","TyVarBndr","[]","[Char] (aka String)","[Pred] (aka Cxt)","Type (aka Kind)"]),
     ("[Char] (aka String)",["Char#","Char","[]","[Char] (aka String)"]),
     ("[Pred] (aka Cxt)",["[Type]","Name","Pred","[]","[Pred] (aka Cxt)","Type (aka Kind)"]),
     ("[TyVarBndr]",["Name","[]","Type (aka Kind)"]),
     ("[Type]",["[TyVarBndr]","Int","Name","TyLit","[]","[Pred] (aka Cxt)","Type (aka Kind)"])
#endif
    ]

decEdges :: Set (String, [String])
decEdges =
  Set.fromList
    [
#if MIN_VERSION_template_haskell(2,10,0)
     ("(,)",[]),
     ("(,) Guard",["Guard","(,)"]),
     ("(,) Name",["Name","(,)"]),
     ("(,) Strict",["Strict","(,)"]),
     ("(,,)",[]),
     ("(,,) Name",["Name","(,,)"]),
     ("(,,) Name Strict",["(,,) Name","Strict"]),
     ("(Guard, Exp)",["(,) Guard","Exp"]),
     ("(Name, Exp) (aka FieldExp)",["(,) Name","Exp"]),
     ("(Name, Pat) (aka FieldPat)",["(,) Name","Pat"]),
     ("(Name, Strict, Type) (aka VarStrictType)",["(,,) Name Strict","Type (aka Kind, aka Pred)"]),
     ("(Strict, Type) (aka StrictType)",["(,) Strict","Type (aka Kind, aka Pred)"]),
     ("AnnTarget",["Name"]),
     ("BigNat",["ByteArray#"]),
     ("Body",["[(Guard, Exp)]","Exp"]),
     ("ByteArray#",[]),
     ("Callconv",[]),
     ("Char",["Char#"]),
     ("Char#",[]),
     ("Clause",["[Dec]","[Pat]","Body"]),
     ("Con",["[(Name, Strict, Type)]","[(Strict, Type)]","[TyVarBndr]","Name","[Type] (aka Cxt)","(Strict, Type) (aka StrictType)"]),
     ("Dec",["Maybe Type","[Clause]","[Con]","[Dec]","[FunDep]","[Name]","[Role]","[TySynEqn]","[TyVarBndr]","Body","Con","FamFlavour","Fixity","Foreign","Name","Pat","Pragma","TySynEqn","[Type] (aka Cxt)","Type (aka Kind, aka Pred)"]),
     ("Exp",["Maybe Exp","[(Guard, Exp)]","[(Name, Exp)]","[Dec]","[Exp]","[Match]","[Pat]","[Stmt]","Lit","Name","Range","Type (aka Kind, aka Pred)"]),
     ("FamFlavour",[]),
     ("Fixity",["Int","FixityDirection"]),
     ("FixityDirection",[]),
     ("Foreign",["Callconv","Name","Safety","[Char] (aka String)","Type (aka Kind, aka Pred)"]),
     ("FunDep",["[Name]"]),
     ("Guard",["[Stmt]","Exp"]),
     ("Inline",[]),
     ("Int",["Int#"]),
     ("Int#",[]),
     ("Integer",["Int#","BigNat"]),
     ("Lit",["[Word8]","Char","Integer","[Char] (aka String)","Ratio Integer (aka Rational)"]),
     ("Match",["[Dec]","Body","Pat"]),
     ("Maybe",["a"]),
     ("Maybe Exp",["Maybe","Exp"]),
     ("Maybe Inline",["Maybe","Inline"]),
     ("Maybe Type",["Maybe","Type (aka Kind, aka Pred)"]),
     ("ModName",["[Char] (aka String)"]),
     ("Name",["NameFlavour","OccName"]),
     ("NameFlavour",["Int","ModName","NameSpace","PkgName"]),
     ("NameSpace",[]),
     ("OccName",["[Char] (aka String)"]),
     ("Pat",["[(Name, Pat)]","[Pat]","Exp","Lit","Name","Type (aka Kind, aka Pred)"]),
     ("Phases",["Int"]),
     ("PkgName",["[Char] (aka String)"]),
     ("Pragma",["Maybe Inline","[RuleBndr]","Int","AnnTarget","Exp","Inline","Name","Phases","RuleMatch","[Char] (aka String)","Type (aka Kind, aka Pred)"]),
     ("Range",["Exp"]),
     ("Ratio",["a"]),
     ("Ratio Integer (aka Rational)",["Ratio","Integer"]),
     ("Role",[]),
     ("RuleBndr",["Name","Type (aka Kind, aka Pred)"]),
     ("RuleMatch",[]),
     ("Safety",[]),
     ("Stmt",["[[Stmt]]","[Dec]","Exp","Pat"]),
     ("Strict",[]),
     ("TyLit",["Integer","[Char] (aka String)"]),
     ("TySynEqn",["[Type] (aka Cxt)","Type (aka Kind, aka Pred)"]),
     ("TyVarBndr",["Name","Type (aka Kind, aka Pred)"]),
     ("Type (aka Kind, aka Pred)",["[TyVarBndr]","Int","Name","TyLit","[Type] (aka Cxt)"]),
     ("Word#",[]),
     ("Word8",["Word#"]),
     ("[(Guard, Exp)]",["(Guard, Exp)","[]"]),
     ("[(Name, Exp)]",["[]","(Name, Exp) (aka FieldExp)"]),
     ("[(Name, Pat)]",["[]","(Name, Pat) (aka FieldPat)"]),
     ("[(Name, Strict, Type)]",["[]","(Name, Strict, Type) (aka VarStrictType)"]),
     ("[(Strict, Type)]",["[]","(Strict, Type) (aka StrictType)"]),
     ("[Char] (aka String)",["Char","[]"]),
     ("[Clause]",["Clause","[]"]),
     ("[Con]",["Con","[]"]),
     ("[Dec]",["Dec","[]"]),
     ("[Exp]",["Exp","[]"]),
     ("[FunDep]",["FunDep","[]"]),
     ("[Match]",["Match","[]"]),
     ("[Name]",["Name","[]"]),
     ("[Pat]",["Pat","[]"]),
     ("[Role]",["Role","[]"]),
     ("[RuleBndr]",["RuleBndr","[]"]),
     ("[Stmt]",["Stmt","[]"]),
     ("[TySynEqn]",["TySynEqn","[]"]),
     ("[TyVarBndr]",["TyVarBndr","[]"]),
     ("[Type] (aka Cxt)",["[]","Type (aka Kind, aka Pred)"]),
     ("[Word8]",["Word8","[]"]),
     ("[[Stmt]]",["[Stmt]","[]"]),
     ("[]",[]),
     ("a",[])
#else
     ("(,)",[]),
     ("(,) Guard",["Guard","(,)"]),
     ("(,) Name",["Name","(,)"]),
     ("(,) Strict",["Strict","(,)"]),
     ("(,,)",[]),
     ("(,,) Name",["Name","(,,)"]),
     ("(,,) Name Strict",["(,,) Name","Strict"]),
     ("(Guard, Exp)",["(,) Guard","Exp"]),
     ("(Name, Exp) (aka FieldExp)",["(,) Name","Exp"]),
     ("(Name, Pat) (aka FieldPat)",["(,) Name","Pat"]),
     ("(Name, Strict, Type) (aka VarStrictType)",["(,,) Name Strict","Type (aka Kind)"]),
     ("(Strict, Type) (aka StrictType)",["(,) Strict","Type (aka Kind)"]),
     ("AnnTarget",["Name"]),
     ("Body",["[(Guard, Exp)]","Exp"]),
     ("ByteArray#",[]),
     ("Callconv",[]),
     ("Char",["Char#"]),
     ("Char#",[]),
     ("Clause",["[Dec]","[Pat]","Body"]),
     ("Con",["[(Name, Strict, Type)]","[(Strict, Type)]","[TyVarBndr]","Name","[Pred] (aka Cxt)","(Strict, Type) (aka StrictType)"]),
     ("Dec",["Maybe Type","[Clause]","[Con]","[Dec]","[FunDep]","[Name]","[Role]","[TySynEqn]","[TyVarBndr]","[Type]","Body","Con","FamFlavour","Fixity","Foreign","Name","Pat","Pragma","TySynEqn","[Pred] (aka Cxt)","Type (aka Kind)"]),
     ("Exp",["Maybe Exp","[(Guard, Exp)]","[(Name, Exp)]","[Dec]","[Exp]","[Match]","[Pat]","[Stmt]","Lit","Name","Range","Type (aka Kind)"]),
     ("FamFlavour",[]),
     ("Fixity",["Int","FixityDirection"]),
     ("FixityDirection",[]),
     ("Foreign",["Callconv","Name","Safety","[Char] (aka String)","Type (aka Kind)"]),
     ("FunDep",["[Name]"]),
     ("Guard",["[Stmt]","Exp"]),
     ("Inline",[]),
     ("Int",["Int#"]),
     ("Int#",[]),
     ("Integer",["ByteArray#","Int#"]),
     ("Lit",["[Word8]","Char","Integer","[Char] (aka String)","Ratio Integer (aka Rational)"]),
     ("Match",["[Dec]","Body","Pat"]),
     ("Maybe",["a"]),
     ("Maybe Exp",["Maybe","Exp"]),
     ("Maybe Inline",["Maybe","Inline"]),
     ("Maybe Type",["Maybe","Type (aka Kind)"]),
     ("ModName",["[Char] (aka String)"]),
     ("Name",["NameFlavour","OccName"]),
     ("NameFlavour",["Int#","ModName","NameSpace","PkgName"]),
     ("NameSpace",[]),
     ("OccName",["[Char] (aka String)"]),
     ("Pat",["[(Name, Pat)]","[Pat]","Exp","Lit","Name","Type (aka Kind)"]),
     ("Phases",["Int"]),
     ("PkgName",["[Char] (aka String)"]),
     ("Pragma",["Maybe Inline","[RuleBndr]","AnnTarget","Exp","Inline","Name","Phases","RuleMatch","[Char] (aka String)","Type (aka Kind)"]),
     ("Pred",["[Type]","Name","Type (aka Kind)"]),
     ("Range",["Exp"]),
     ("Ratio",["a"]),
     ("Ratio Integer (aka Rational)",["Ratio","Integer"]),
     ("Role",[]),
     ("RuleBndr",["Name","Type (aka Kind)"]),
     ("RuleMatch",[]),
     ("Safety",[]),
     ("Stmt",["[[Stmt]]","[Dec]","Exp","Pat"]),
     ("Strict",[]),
     ("TyLit",["Integer","[Char] (aka String)"]),
     ("TySynEqn",["[Type]","Type (aka Kind)"]),
     ("TyVarBndr",["Name","Type (aka Kind)"]),
     ("Type (aka Kind)",["[TyVarBndr]","Int","Name","TyLit","[Pred] (aka Cxt)"]),
     ("Word#",[]),
     ("Word8",["Word#"]),
     ("[(Guard, Exp)]",["(Guard, Exp)","[]"]),
     ("[(Name, Exp)]",["[]","(Name, Exp) (aka FieldExp)"]),
     ("[(Name, Pat)]",["[]","(Name, Pat) (aka FieldPat)"]),
     ("[(Name, Strict, Type)]",["[]","(Name, Strict, Type) (aka VarStrictType)"]),
     ("[(Strict, Type)]",["[]","(Strict, Type) (aka StrictType)"]),
     ("[Char] (aka String)",["Char","[]"]),
     ("[Clause]",["Clause","[]"]),
     ("[Con]",["Con","[]"]),
     ("[Dec]",["Dec","[]"]),
     ("[Exp]",["Exp","[]"]),
     ("[FunDep]",["FunDep","[]"]),
     ("[Match]",["Match","[]"]),
     ("[Name]",["Name","[]"]),
     ("[Pat]",["Pat","[]"]),
     ("[Pred] (aka Cxt)",["Pred","[]"]),
     ("[Role]",["Role","[]"]),
     ("[RuleBndr]",["RuleBndr","[]"]),
     ("[Stmt]",["Stmt","[]"]),
     ("[TySynEqn]",["TySynEqn","[]"]),
     ("[TyVarBndr]",["TyVarBndr","[]"]),
     ("[Type]",["[]","Type (aka Kind)"]),
     ("[Word8]",["Word8","[]"]),
     ("[[Stmt]]",["[Stmt]","[]"]),
     ("[]",[]),
     ("a",[])
#endif
    ]

arity0DecEdges :: Set (String, [String])
arity0DecEdges =
  Set.fromList
    [
#if MIN_VERSION_template_haskell(2,10,0)
     ("(Guard, Exp)",["Exp","Guard"]),
     ("(Name, Exp) (aka FieldExp)",["Exp","Name"]),
     ("(Name, Pat) (aka FieldPat)",["Name","Pat"]),
     ("(Name, Strict, Type) (aka VarStrictType)",["Name","Strict","Type (aka Kind, aka Pred)"]),
     ("(Strict, Type) (aka StrictType)",["Strict","Type (aka Kind, aka Pred)"]),
     ("AnnTarget",["Name"]),
     ("BigNat",["ByteArray#"]),
     ("Body",["[(Guard, Exp)]","Exp"]),
     ("ByteArray#",[]),
     ("Callconv",[]),
     ("Char",["Char#"]),
     ("Char#",[]),
     ("Clause",["[Dec]","[Pat]","Body"]),
     ("Con",["[(Name, Strict, Type)]","[(Strict, Type)]","[TyVarBndr]","Name","[Type] (aka Cxt)","(Strict, Type) (aka StrictType)"]),
     ("Dec",["Maybe Type","[Clause]","[Con]","[Dec]","[FunDep]","[Name]","[Role]","[TySynEqn]","[TyVarBndr]","Body","Con","FamFlavour","Fixity","Foreign","Name","Pat","Pragma","TySynEqn","[Type] (aka Cxt)","Type (aka Kind, aka Pred)"]),
     ("Exp",["Maybe Exp","[(Guard, Exp)]","[(Name, Exp)]","[Dec]","[Exp]","[Match]","[Pat]","[Stmt]","Lit","Name","Range","Type (aka Kind, aka Pred)"]),
     ("FamFlavour",[]),
     ("Fixity",["Int","FixityDirection"]),
     ("FixityDirection",[]),
     ("Foreign",["Callconv","Name","Safety","[Char] (aka String)","Type (aka Kind, aka Pred)"]),
     ("FunDep",["[Name]"]),
     ("Guard",["[Stmt]","Exp"]),
     ("Inline",[]),
     ("Int",["Int#"]),
     ("Int#",[]),
     ("Integer",["Int#","BigNat"]),
     ("Lit",["[Word8]","Char","Integer","[Char] (aka String)","Ratio Integer (aka Rational)"]),
     ("Match",["[Dec]","Body","Pat"]),
     ("Maybe Exp",["Exp"]),
     ("Maybe Inline",["Inline"]),
     ("Maybe Type",["Type (aka Kind, aka Pred)"]),
     ("ModName",["[Char] (aka String)"]),
     ("Name",["NameFlavour","OccName"]),
     ("NameFlavour",["Int","ModName","NameSpace","PkgName"]),
     ("NameSpace",[]),
     ("OccName",["[Char] (aka String)"]),
     ("Pat",["[(Name, Pat)]","[Pat]","Exp","Lit","Name","Type (aka Kind, aka Pred)"]),
     ("Phases",["Int"]),
     ("PkgName",["[Char] (aka String)"]),
     ("Pragma",["Maybe Inline","[RuleBndr]","Int","AnnTarget","Exp","Inline","Name","Phases","RuleMatch","[Char] (aka String)","Type (aka Kind, aka Pred)"]),
     ("Range",["Exp"]),
     ("Ratio Integer (aka Rational)",["Integer"]),
     ("Role",[]),
     ("RuleBndr",["Name","Type (aka Kind, aka Pred)"]),
     ("RuleMatch",[]),
     ("Safety",[]),
     ("Stmt",["[[Stmt]]","[Dec]","Exp","Pat"]),
     ("Strict",[]),
     ("TyLit",["Integer","[Char] (aka String)"]),
     ("TySynEqn",["[Type] (aka Cxt)","Type (aka Kind, aka Pred)"]),
     ("TyVarBndr",["Name","Type (aka Kind, aka Pred)"]),
     ("Type (aka Kind, aka Pred)",["[TyVarBndr]","Int","Name","TyLit","[Type] (aka Cxt)"]),
     ("Word#",[]),
     ("Word8",["Word#"]),
     ("[(Guard, Exp)]",["(Guard, Exp)"]),
     ("[(Name, Exp)]",["(Name, Exp) (aka FieldExp)"]),
     ("[(Name, Pat)]",["(Name, Pat) (aka FieldPat)"]),
     ("[(Name, Strict, Type)]",["(Name, Strict, Type) (aka VarStrictType)"]),
     ("[(Strict, Type)]",["(Strict, Type) (aka StrictType)"]),
     ("[Char] (aka String)",["Char"]),
     ("[Clause]",["Clause"]),
     ("[Con]",["Con"]),
     ("[Dec]",["Dec"]),
     ("[Exp]",["Exp"]),
     ("[FunDep]",["FunDep"]),
     ("[Match]",["Match"]),
     ("[Name]",["Name"]),
     ("[Pat]",["Pat"]),
     ("[Role]",["Role"]),
     ("[RuleBndr]",["RuleBndr"]),
     ("[Stmt]",["Stmt"]),
     ("[TySynEqn]",["TySynEqn"]),
     ("[TyVarBndr]",["TyVarBndr"]),
     ("[Type] (aka Cxt)",["Type (aka Kind, aka Pred)"]),
     ("[Word8]",["Word8"]),
     ("[[Stmt]]",["[Stmt]"])
#else
     ("(Guard, Exp)",["Exp","Guard"]),
     ("(Name, Exp) (aka FieldExp)",["Exp","Name"]),
     ("(Name, Pat) (aka FieldPat)",["Name","Pat"]),
     ("(Name, Strict, Type) (aka VarStrictType)",["Name","Strict","Type (aka Kind)"]),
     ("(Strict, Type) (aka StrictType)",["Strict","Type (aka Kind)"]),
     ("AnnTarget",["Name"]),
     ("Body",["[(Guard, Exp)]","Exp"]),
     ("ByteArray#",[]),
     ("Callconv",[]),
     ("Char",["Char#"]),
     ("Char#",[]),
     ("Clause",["[Dec]","[Pat]","Body"]),
     ("Con",["[(Name, Strict, Type)]","[(Strict, Type)]","[TyVarBndr]","Name","[Pred] (aka Cxt)","(Strict, Type) (aka StrictType)"]),
     ("Dec",["Maybe Type","[Clause]","[Con]","[Dec]","[FunDep]","[Name]","[Role]","[TySynEqn]","[TyVarBndr]","[Type]","Body","Con","FamFlavour","Fixity","Foreign","Name","Pat","Pragma","TySynEqn","[Pred] (aka Cxt)","Type (aka Kind)"]),
     ("Exp",["Maybe Exp","[(Guard, Exp)]","[(Name, Exp)]","[Dec]","[Exp]","[Match]","[Pat]","[Stmt]","Lit","Name","Range","Type (aka Kind)"]),
     ("FamFlavour",[]),
     ("Fixity",["Int","FixityDirection"]),
     ("FixityDirection",[]),
     ("Foreign",["Callconv","Name","Safety","[Char] (aka String)","Type (aka Kind)"]),
     ("FunDep",["[Name]"]),
     ("Guard",["[Stmt]","Exp"]),
     ("Inline",[]),
     ("Int",["Int#"]),
     ("Int#",[]),
     ("Integer",["ByteArray#","Int#"]),
     ("Lit",["[Word8]","Char","Integer","[Char] (aka String)","Ratio Integer (aka Rational)"]),
     ("Match",["[Dec]","Body","Pat"]),
     ("Maybe Exp",["Exp"]),
     ("Maybe Inline",["Inline"]),
     ("Maybe Type",["Type (aka Kind)"]),
     ("ModName",["[Char] (aka String)"]),
     ("Name",["NameFlavour","OccName"]),
     ("NameFlavour",["Int#","ModName","NameSpace","PkgName"]),
     ("NameSpace",[]),
     ("OccName",["[Char] (aka String)"]),
     ("Pat",["[(Name, Pat)]","[Pat]","Exp","Lit","Name","Type (aka Kind)"]),
     ("Phases",["Int"]),
     ("PkgName",["[Char] (aka String)"]),
     ("Pragma",["Maybe Inline","[RuleBndr]","AnnTarget","Exp","Inline","Name","Phases","RuleMatch","[Char] (aka String)","Type (aka Kind)"]),
     ("Pred",["[Type]","Name","Type (aka Kind)"]),
     ("Range",["Exp"]),
     ("Ratio Integer (aka Rational)",["Integer"]),
     ("Role",[]),
     ("RuleBndr",["Name","Type (aka Kind)"]),
     ("RuleMatch",[]),
     ("Safety",[]),
     ("Stmt",["[[Stmt]]","[Dec]","Exp","Pat"]),
     ("Strict",[]),
     ("TyLit",["Integer","[Char] (aka String)"]),
     ("TySynEqn",["[Type]","Type (aka Kind)"]),
     ("TyVarBndr",["Name","Type (aka Kind)"]),
     ("Type (aka Kind)",["[TyVarBndr]","Int","Name","TyLit","[Pred] (aka Cxt)"]),
     ("Word#",[]),
     ("Word8",["Word#"]),
     ("[(Guard, Exp)]",["(Guard, Exp)"]),
     ("[(Name, Exp)]",["(Name, Exp) (aka FieldExp)"]),
     ("[(Name, Pat)]",["(Name, Pat) (aka FieldPat)"]),
     ("[(Name, Strict, Type)]",["(Name, Strict, Type) (aka VarStrictType)"]),
     ("[(Strict, Type)]",["(Strict, Type) (aka StrictType)"]),
     ("[Char] (aka String)",["Char"]),
     ("[Clause]",["Clause"]),
     ("[Con]",["Con"]),
     ("[Dec]",["Dec"]),
     ("[Exp]",["Exp"]),
     ("[FunDep]",["FunDep"]),
     ("[Match]",["Match"]),
     ("[Name]",["Name"]),
     ("[Pat]",["Pat"]),
     ("[Pred] (aka Cxt)",["Pred"]),
     ("[Role]",["Role"]),
     ("[RuleBndr]",["RuleBndr"]),
     ("[Stmt]",["Stmt"]),
     ("[TySynEqn]",["TySynEqn"]),
     ("[TyVarBndr]",["TyVarBndr"]),
     ("[Type]",["Type (aka Kind)"]),
     ("[Word8]",["Word8"]),
     ("[[Stmt]]",["[Stmt]"])
#endif
    ]

arity0SubtypesOfDec :: Set String
arity0SubtypesOfDec =
  Set.fromList
    [
#if MIN_VERSION_template_haskell(2,10,0)
     "(Guard, Exp)","(Name, Exp) (aka FieldExp)","(Name, Pat) (aka FieldPat)","(Name, Strict, Type) (aka VarStrictType)","(Strict, Type) (aka StrictType)","AnnTarget","BigNat","Body","ByteArray#","Callconv","Char","Char#","Clause","Con","Dec","Exp","FamFlavour","Fixity","FixityDirection","Foreign","FunDep","Guard","Inline","Int","Int#","Integer","Lit","Match","Maybe Exp","Maybe Inline","Maybe Type","ModName","Name","NameFlavour","NameSpace","OccName","Pat","Phases","PkgName","Pragma","Range","Ratio Integer (aka Rational)","Role","RuleBndr","RuleMatch","Safety","Stmt","Strict","TyLit","TySynEqn","TyVarBndr","Type (aka Kind, aka Pred)","Word#","Word8","[(Guard, Exp)]","[(Name, Exp)]","[(Name, Pat)]","[(Name, Strict, Type)]","[(Strict, Type)]","[Char] (aka String)","[Clause]","[Con]","[Dec]","[Exp]","[FunDep]","[Match]","[Name]","[Pat]","[Role]","[RuleBndr]","[Stmt]","[TySynEqn]","[TyVarBndr]","[Type] (aka Cxt)","[Word8]","[[Stmt]]"
#else
     "(Guard, Exp)","(Name, Exp) (aka FieldExp)","(Name, Pat) (aka FieldPat)","(Name, Strict, Type) (aka VarStrictType)","(Strict, Type) (aka StrictType)","AnnTarget","Body","ByteArray#","Callconv","Char","Char#","Clause","Con","Dec","Exp","FamFlavour","Fixity","FixityDirection","Foreign","FunDep","Guard","Inline","Int","Int#","Integer","Lit","Match","Maybe Exp","Maybe Inline","Maybe Type","ModName","Name","NameFlavour","NameSpace","OccName","Pat","Phases","PkgName","Pragma","Pred","Range","Ratio Integer (aka Rational)","Role","RuleBndr","RuleMatch","Safety","Stmt","Strict","TyLit","TySynEqn","TyVarBndr","Type (aka Kind)","Word#","Word8","[(Guard, Exp)]","[(Name, Exp)]","[(Name, Pat)]","[(Name, Strict, Type)]","[(Strict, Type)]","[Char] (aka String)","[Clause]","[Con]","[Dec]","[Exp]","[FunDep]","[Match]","[Name]","[Pat]","[Pred] (aka Cxt)","[Role]","[RuleBndr]","[Stmt]","[TySynEqn]","[TyVarBndr]","[Type]","[Word8]","[[Stmt]]"
#endif
    ]

subtypesOfDec :: Set String
subtypesOfDec =
    union
       arity0SubtypesOfDec
       (Set.fromList
           [ "(,)"
           , "(,) Guard"
           , "(,) Name"
           , "(,) Strict"
           , "(,,)"
           , "(,,) Name"
           , "(,,) Name Strict"
           , "Maybe"
           , "Ratio"
           , "[]"
           , "a"
           ])

simpleSubtypesOfDec :: Set String
simpleSubtypesOfDec =
  Set.fromList
    [
#if MIN_VERSION_template_haskell(2,10,0)
              "BigNat",
              "Type (aka Kind, aka Pred)",
              "[Type] (aka Cxt)",
#else
              "Pred",
              "[Pred] (aka Cxt)",
              "Type (aka Kind)",
              "[Type]",
#endif
              "(,)",
              "(,) Guard",
              "(,) Name",
              "(,) Strict",
              "(,,)",
              "(,,) Name",
              "(,,) Name Strict",
              "(Guard, Exp)",
              "(Name, Exp) (aka FieldExp)",
              "(Name, Pat) (aka FieldPat)",
              "(Name, Strict, Type) (aka VarStrictType)",
              "(Strict, Type) (aka StrictType)",
              "AnnTarget",
              "Body",
              "ByteArray#",
              "Callconv",
              "Char",
              "Char#",
              "Clause",
              "Con",
              "Dec",
              "Exp",
              "FamFlavour",
              "Fixity",
              "FixityDirection",
              "Foreign",
              "FunDep",
              "Guard",
              "Inline",
              "Int",
              "Int#",
              "Integer",
              "Lit",
              "Match",
              "Maybe",
              "Maybe Exp",
              "Maybe Inline",
              "Maybe Type",
              "ModName",
              "Name",
              "NameFlavour",
              "NameSpace",
              "OccName",
              "Pat",
              "Phases",
              "PkgName",
              "Pragma",
              "Range",
              "Ratio",
              "Ratio Integer (aka Rational)",
              "Role",
              "RuleBndr",
              "RuleMatch",
              "Safety",
              "Stmt",
              "Strict",
              "TyLit",
              "TySynEqn",
              "TyVarBndr",
              "Word#",
              "Word8",
              "[(Guard, Exp)]",
              "[(Name, Exp)]",
              "[(Name, Pat)]",
              "[(Name, Strict, Type)]",
              "[(Strict, Type)]",
              "[Char] (aka String)",
              "[Clause]",
              "[Con]",
              "[Dec]",
              "[Exp]",
              "[FunDep]",
              "[Match]",
              "[Name]",
              "[Pat]",
              "[Role]",
              "[RuleBndr]",
              "[Stmt]",
              "[TySynEqn]",
              "[TyVarBndr]",
              "[Word8]",
              "[[Stmt]]",
              "[]",
              "a"
    ]

bitsInstances :: Set String
bitsInstances =
  Set.fromList
    [
#if MIN_VERSION_template_haskell(2,10,0)
      "instance Bits CChar","instance Bits CInt","instance Bits CIntMax","instance Bits CIntPtr","instance Bits CLLong","instance Bits CLong","instance Bits CPtrdiff","instance Bits CSChar","instance Bits CShort","instance Bits CSigAtomic","instance Bits CSize","instance Bits CUChar","instance Bits CUInt","instance Bits CUIntMax","instance Bits CUIntPtr","instance Bits CULLong","instance Bits CULong","instance Bits CUShort","instance Bits CWchar",
#endif
      "instance Bits Bool","instance Bits Int","instance Bits Integer","instance Bits Word","instance Bits Word16","instance Bits Word32","instance Bits Word64","instance Bits Word8",
      -- These come and go depending on the version of something.
      "instance Bits Int16","instance Bits Int32","instance Bits Int64","instance Bits Int8","instance Bits Natural"
    ]

enumInstances :: Set String
enumInstances =
  Set.fromList
    [
#if MIN_VERSION_template_haskell(2,10,0)
      "instance Enum (Fixed a)","instance Enum (Proxy s)","instance Enum (f a) => Enum (Alt f a)","instance Enum CChar","instance Enum CClock","instance Enum CDouble","instance Enum CFloat","instance Enum CInt","instance Enum CIntMax","instance Enum CIntPtr","instance Enum CLLong","instance Enum CLong","instance Enum CPtrdiff","instance Enum CSChar","instance Enum CSUSeconds","instance Enum CShort","instance Enum CSigAtomic","instance Enum CSize","instance Enum CTime","instance Enum CUChar","instance Enum CUInt","instance Enum CUIntMax","instance Enum CUIntPtr","instance Enum CULLong","instance Enum CULong","instance Enum CUSeconds","instance Enum CUShort","instance Enum CWchar","instance Enum Day","instance Enum NominalDiffTime",
#endif
      "instance Enum ()","instance Enum Bool","instance Enum Char","instance Enum Double","instance Enum Float","instance Enum Int","instance Enum Int16","instance Enum Int32","instance Enum Int64","instance Enum Int8","instance Enum Integer","instance Enum Natural","instance Enum Ordering","instance Enum Word","instance Enum Word16","instance Enum Word32","instance Enum Word64","instance Enum Word8","instance Integral a => Enum (Ratio a)"
    ]

arrayInstances :: Set String
arrayInstances =
  Set.fromList
    ["instance IArray UArray (FunPtr a)","instance IArray UArray (Ptr a)","instance IArray UArray (StablePtr a)","instance IArray UArray Bool","instance IArray UArray Char","instance IArray UArray Double","instance IArray UArray Float","instance IArray UArray Int","instance IArray UArray Int16","instance IArray UArray Int32","instance IArray UArray Int64","instance IArray UArray Int8","instance IArray UArray Word","instance IArray UArray Word16","instance IArray UArray Word32","instance IArray UArray Word64","instance IArray UArray Word8"]

decTypeSynonyms :: Map (E Type) (Set Name)
decTypeSynonyms =
  Map.fromList
    [
#if MIN_VERSION_template_haskell(2,10,0)
     (E (AppT (AppT (AppT (TupleT 3) (ConT ''Name)) (ConT ''Strict)) (ConT ''Type)), Set.fromList [''VarStrictType]),
     (E (AppT (AppT (TupleT 2) (ConT ''Name)) (ConT ''Exp)),                         Set.fromList [''FieldExp]),
     (E (AppT (AppT (TupleT 2) (ConT ''Name)) (ConT ''Pat)),                         Set.fromList [''FieldPat]),
     (E (AppT (AppT (TupleT 2) (ConT ''Strict)) (ConT ''Type)),                      Set.fromList [''StrictType]),
     (E (AppT (ConT ''Ratio) (ConT ''Integer)),                                      Set.fromList [''Rational]),
     (E (AppT ListT (ConT ''Char)),                                                  Set.fromList [''String]),
     (E (AppT ListT (ConT ''Type)),                                                  Set.fromList [''Cxt]),
     (E (ConT ''Type),                                                               Set.fromList [''Kind,''Pred])
#else
     (E (AppT (AppT (AppT (TupleT 3) (ConT ''Name)) (ConT ''Strict)) (ConT ''Type)), Set.fromList [''VarStrictType]),
     (E (AppT (AppT (TupleT 2) (ConT ''Name)) (ConT ''Exp)),                         Set.fromList [''FieldExp]),
     (E (AppT (AppT (TupleT 2) (ConT ''Name)) (ConT ''Pat)),                         Set.fromList [''FieldPat]),
     (E (AppT (AppT (TupleT 2) (ConT ''Strict)) (ConT ''Type)),                      Set.fromList [''StrictType]),
     (E (AppT (ConT ''Ratio) (ConT ''Integer)),                                      Set.fromList [''Rational]),
     (E (AppT ListT (ConT ''Char)),                                                  Set.fromList [''String]),
     (E (AppT ListT (ConT ''Pred)),                                                  Set.fromList [''Cxt]),
     (E (ConT ''Type),                                                               Set.fromList [''Kind])
#endif
    ]
