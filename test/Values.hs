{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}
module Values where

import Control.Monad (filterM)
import Data.Map as Map (toList)
import Data.Set as Set (Set, fromList, toList, union)
import GHC.Prim -- ByteArray#, Char#, etc
import Language.Haskell.TH
import Language.Haskell.TH.Context.Expand (expandType)
import Language.Haskell.TH.Context.Helpers (typeArity)
import Language.Haskell.TH.Context.TypeGraph (typeGraphVertices, typeGraphEdges, VertexStatus(Vertex))
import Language.Haskell.TH.Desugar (withLocalDeclarations)
import Language.Haskell.TH.Instances ()
import Language.Haskell.TH.Syntax
import Test.Hspec hiding (runIO)
import Test.Hspec.Core.Spec (SpecM)

import Common

subtypesOfType :: Set String
subtypesOfType =
    fromList
    [
#if MIN_VERSION_template_haskell(2,10,0)
      "BigNat",
#else
      "[Type]",
#endif
      "ByteArray#","Char","Char#","Cxt","Int","Int#","Integer","Kind","ModName","Name","NameFlavour","NameSpace","OccName","PkgName","Pred","String","TyLit","TyVarBndr","Type","[Char]","[Pred]","[TyVarBndr]", "[]" ]

decEdges :: Set (String, [String])
decEdges =
    fromList
      [
#if MIN_VERSION_template_haskell(2,10,0)
       ("BigNat",["ByteArray#"]),
       ("Integer",["Int#","BigNat"]),
       ("NameFlavour",["Int","ModName","NameSpace","PkgName"]),
       ("Pragma",["Maybe Inline","[RuleBndr]","String","Int","AnnTarget","Exp","Inline","Name","Phases","RuleMatch","Type"]),
       ("Pred",["Type"]),
#else
       ("Integer",["ByteArray#","Int#"]),
       ("NameFlavour",["Int#","ModName","NameSpace","PkgName"]),
       ("Pragma",["Maybe Inline","[RuleBndr]","String","AnnTarget","Exp","Inline","Name","Phases","RuleMatch","Type"]),
       ("Pred",["[Type]","Name","Type"]),
#endif
       ("(,)",[]),("(,,)",[]),("[]",[]),("(,) Guard",["Guard","(,)"]),("(,) Name",["Name","(,)"]),("(,) Strict",["Strict","(,)"]),("(,,) Name",["Name","(,,)"]),("(,,) Name Strict",["(,,) Name","Strict"]),("(Guard, Exp)",["(,) Guard","Exp"]),("(Name, Exp)",["(,) Name","Exp"]),("(Name, Pat)",["(,) Name","Pat"]),("(Name, Strict, Type)",["(,,) Name Strict","Type"]),("(Strict, Type)",["(,) Strict","Type"]),("AnnTarget",["Name"]),("Body",["[(Guard, Exp)]","Exp"]),("ByteArray#",[]),("Callconv",[]),("Char",["Char#"]),("Char#",[]),("Clause",["[Dec]","[Pat]","Body"]),("Con",["[StrictType]","[TyVarBndr]","[VarStrictType]","Con","Cxt","Name","StrictType"]),("Cxt",["[Pred]"]),("Dec",["Maybe Kind","[Clause]","[Con]","[Dec]","[FunDep]","[Name]","[Role]","[TySynEqn]","[TyVarBndr]","[Type]","Body","Con","Cxt","FamFlavour","Fixity","Foreign","Name","Pat","Pragma","TySynEqn","Type"]),("Exp",["Maybe Exp","[(Guard, Exp)]","[Dec]","[Exp]","[FieldExp]","[Match]","[Pat]","[Stmt]","Exp","Lit","Name","Range","Type"]),("FamFlavour",[]),("FieldExp",["(Name, Exp)"]),("FieldPat",["(Name, Pat)"]),("Fixity",["Int","FixityDirection"]),("FixityDirection",[]),("Foreign",["String","Callconv","Name","Safety","Type"]),("FunDep",["[Name]"]),("Guard",["[Stmt]","Exp"]),("Inline",[]),("Int",["Int#"]),("Int#",[]),("Kind",["Type"]),("Lit",["[Word8]","String","Rational","Char","Integer"]),("Match",["[Dec]","Body","Pat"]),("Maybe",["a"]),("Maybe Exp",["Maybe","Exp"]),("Maybe Inline",["Maybe","Inline"]),("Maybe Kind",["Maybe","Kind"]),("ModName",["String"]),("Name",["NameFlavour","OccName"]),("NameSpace",[]),("OccName",["String"]),("Pat",["[FieldPat]","[Pat]","Exp","Lit","Name","Pat","Type"]),("Phases",["Int"]),("PkgName",["String"]),("Range",["Exp"]),("Ratio",["a"]),("Ratio Integer",["Ratio","Integer"]),("Rational",["Ratio Integer"]),("Role",[]),("RuleBndr",["Name","Type"]),("RuleMatch",[]),("Safety",[]),("Stmt",["[[Stmt]]","[Dec]","Exp","Pat"]),("Strict",[]),("StrictType",["(Strict, Type)"]),("String",["[Char]"]),("TyLit",["String","Integer"]),("TySynEqn",["[Type]","Type"]),("TyVarBndr",["Kind","Name"]),("Type",["[TyVarBndr]","Int","Cxt","Kind","Name","TyLit","Type"]),("VarStrictType",["(Name, Strict, Type)"]),("Word#",[]),("Word8",["Word#"]),("[(Guard, Exp)]",["(Guard, Exp)","[]"]),("[Char]",["Char","[]"]),("[Clause]",["Clause","[]"]),("[Con]",["Con","[]"]),("[Dec]",["Dec","[]"]),("[Exp]",["Exp","[]"]),("[FieldExp]",["FieldExp","[]"]),("[FieldPat]",["FieldPat","[]"]),("[FunDep]",["FunDep","[]"]),("[Match]",["Match","[]"]),("[Name]",["Name","[]"]),("[Pat]",["Pat","[]"]),("[Pred]",["Pred","[]"]),("[Role]",["Role","[]"]),("[RuleBndr]",["RuleBndr","[]"]),("[Stmt]",["Stmt","[]"]),("[StrictType]",["StrictType","[]"]),("[TySynEqn]",["TySynEqn","[]"]),("[TyVarBndr]",["TyVarBndr","[]"]),("[Type]",["Type","[]"]),("[VarStrictType]",["VarStrictType","[]"]),("[Word8]",["Word8","[]"]),("[[Stmt]]",["[Stmt]","[]"]),("a",[])]

typeEdges :: Set (String, [String])
typeEdges =
    fromList
      [
#if MIN_VERSION_template_haskell(2,10,0)
       ("BigNat",["ByteArray#"]),
       ("Integer",["Int#","BigNat"]),
       ("NameFlavour",["Int","ModName","NameSpace","PkgName"]),("Pred",["Type"]),
#else
       ("Integer",["ByteArray#","Int#"]),
       ("NameFlavour",["Int#","ModName","NameSpace","PkgName"]),
       ("Pred",["[Type]","Name","Type"]),("[Type]",["Type","[]"]),
#endif
       ("[]",[]),("ByteArray#",[]),("Char",["Char#"]),("Char#",[]),("Cxt",["[Pred]"]),("Int",["Int#"]),("Int#",[]),("Kind",["Type"]),("ModName",["String"]),("Name",["NameFlavour","OccName"]),("NameSpace",[]),("OccName",["String"]),("PkgName",["String"]),("String",["[Char]"]),("TyLit",["String","Integer"]),("TyVarBndr",["Kind","Name"]),("Type",["[TyVarBndr]","Int","Cxt","Kind","Name","TyLit","Type"]),("[Char]",["Char","[]"]),("[Pred]",["Pred","[]"]),("[TyVarBndr]",["TyVarBndr","[]"])]

arity0SubtypesOfDec :: Set String
arity0SubtypesOfDec =
    fromList
         [
#if MIN_VERSION_template_haskell(2,10,0)
           "BigNat",
#endif
           "(Guard, Exp)","(Name, Exp)","(Name, Pat)","(Name, Strict, Type)","(Strict, Type)","AnnTarget","Body","ByteArray#","Callconv","Char","Char#","Clause","Con","Cxt","Dec","Exp","FamFlavour","FieldExp","FieldPat","Fixity","FixityDirection","Foreign","FunDep","Guard","Inline","Int","Int#","Integer","Kind","Lit","Match","Maybe Exp","Maybe Inline","Maybe Kind","ModName","Name","NameFlavour","NameSpace","OccName","Pat","Phases","PkgName","Pragma","Pred","Range","Ratio Integer","Rational","Role","RuleBndr","RuleMatch","Safety","Stmt","Strict","StrictType","String","TyLit","TySynEqn","TyVarBndr","Type","VarStrictType","Word#","Word8","[(Guard, Exp)]","[Char]","[Clause]","[Con]","[Dec]","[Exp]","[FieldExp]","[FieldPat]","[FunDep]","[Match]","[Name]","[Pat]","[Pred]","[Role]","[RuleBndr]","[Stmt]","[StrictType]","[TySynEqn]","[TyVarBndr]","[Type]","[VarStrictType]","[Word8]","[[Stmt]]" ]


subtypesOfDec :: Set String
subtypesOfDec =
    union
       arity0SubtypesOfDec
       (fromList
          [
           "a",
           "Maybe",
           "Ratio",
           "(,) Guard",
           "(,) Name",
           "(,) Strict",
           "(,,) Name",
           "(,,) Name Strict",
           "(,,)",
           "(,)",
           "[]"])

bitsInstances :: Set String
bitsInstances
    = Set.fromList
       [
#if MIN_VERSION_template_haskell(2,10,0)
        "instance Bits CChar","instance Bits CInt","instance Bits CIntMax","instance Bits CIntPtr","instance Bits CLLong","instance Bits CLong","instance Bits CPtrdiff","instance Bits CSChar","instance Bits CShort","instance Bits CSigAtomic","instance Bits CSize","instance Bits CUChar","instance Bits CUInt","instance Bits CUIntMax","instance Bits CUIntPtr","instance Bits CULLong","instance Bits CULong","instance Bits CUShort","instance Bits CWchar",
#endif
        "instance Bits Bool","instance Bits Int","instance Bits Integer","instance Bits Word","instance Bits Word16","instance Bits Word32","instance Bits Word64","instance Bits Word8",
        -- These come and go depending on the version of something.
        "instance Bits Int16","instance Bits Int32","instance Bits Int64","instance Bits Int8","instance Bits Natural" ]

enumInstances :: Set String
enumInstances =
    Set.fromList
    [
#if MIN_VERSION_template_haskell(2,10,0)
     "instance Enum (Fixed a)","instance Enum (Proxy s)","instance Enum (f a) => Enum (Alt f a)","instance Enum CChar","instance Enum CClock","instance Enum CDouble","instance Enum CFloat","instance Enum CInt","instance Enum CIntMax","instance Enum CIntPtr","instance Enum CLLong","instance Enum CLong","instance Enum CPtrdiff","instance Enum CSChar","instance Enum CSUSeconds","instance Enum CShort","instance Enum CSigAtomic","instance Enum CSize","instance Enum CTime","instance Enum CUChar","instance Enum CUInt","instance Enum CUIntMax","instance Enum CUIntPtr","instance Enum CULLong","instance Enum CULong","instance Enum CUSeconds","instance Enum CUShort","instance Enum CWchar","instance Enum Day","instance Enum NominalDiffTime",
#endif
     "instance Enum ()","instance Enum Bool","instance Enum Char","instance Enum Double","instance Enum Float","instance Enum Int","instance Enum Int16","instance Enum Int32","instance Enum Int64","instance Enum Int8","instance Enum Integer","instance Enum Natural","instance Enum Ordering","instance Enum Word","instance Enum Word16","instance Enum Word32","instance Enum Word64","instance Enum Word8","instance Integral a => Enum (Ratio a)"]

arrayInstances :: Set String
arrayInstances =
    Set.fromList ["instance IArray UArray (FunPtr a)","instance IArray UArray (Ptr a)","instance IArray UArray (StablePtr a)","instance IArray UArray Bool","instance IArray UArray Char","instance IArray UArray Double","instance IArray UArray Float","instance IArray UArray Int","instance IArray UArray Int16","instance IArray UArray Int32","instance IArray UArray Int64","instance IArray UArray Int8","instance IArray UArray Word","instance IArray UArray Word16","instance IArray UArray Word32","instance IArray UArray Word64","instance IArray UArray Word8"]
