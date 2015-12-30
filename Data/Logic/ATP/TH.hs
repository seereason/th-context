-- | ATP instances for the template haskell type 'Type', and the
-- conjunction of such types, @[Type]@.  In these instances, almost
-- every role is played by 'Type'.  It might a case where the tagged
-- package could be used to advantage.  A list represents conjunction,
-- but there is no disjunction operation, nor any derived from it like
-- implication or equivalence.

{-# LANGUAGE CPP, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, TypeFamilies #-}
module Data.Logic.ATP.TH
    ( unfoldApply
    ) where

import Control.Monad.State (modify)
import Data.List (intersperse)
import Data.Logic.ATP (IsAtom, IsVariable(..), IsFunction, IsPredicate, HasEquate(..))
import Data.Logic.ATP.Apply (HasApply(PredOf, TermOf, applyPredicate, foldApply', overterms, onterms))
import Data.Logic.ATP.Formulas (IsFormula(..))
import Data.Logic.ATP.Lit (IsLiteral(..), JustLiteral)
import Data.Logic.ATP.Pretty (hcat, HasFixity(..), Pretty(pPrint), text)
import Data.Logic.ATP.Prop (IsPropositional(..))
import Data.Logic.ATP.Term (IsTerm(..))
import Data.Logic.ATP.Unif (Unify(unify, UTermOf), unify_literals)
import Data.Map as Map (insert)
import Data.Monoid ((<>))
import Data.String (IsString(fromString))
import Language.Haskell.TH
import Language.Haskell.TH.PprLib (to_HPJ_Doc)
import Language.Haskell.TH.TypeGraph.Prelude (pprint')

newtype Context = Context [Type] deriving (Eq, Ord, Show)

-- | Helper function to interpret a type application:
--     @unfoldApply (AppT (AppT (AppT (VarT (mkName "a")) StarT) ListT) ArrowT) -> (VarT (mkName "a"), [StarT, ListT, ArrowT])@
-- The inverse is @uncurry . foldl AppT@.
unfoldApply :: Type -> [Type] -> (Type, [Type])
unfoldApply (AppT t1 t2) ts = unfoldApply t1 (t2 : ts)
unfoldApply t ts = (t, ts)

instance HasFixity Type where
    precedence _ = undefined
    associativity _ = undefined

instance Pretty Type where
    pPrint = to_HPJ_Doc . ppr

instance Pretty Context where
    pPrint (Context ts) = text "(" <> hcat (intersperse (text ", ") (map pPrint ts)) <> text ")"

instance IsAtom Type

instance IsAtom Context

instance IsString Type where
    fromString = VarT . mkName

instance IsString Context where
    fromString = Context . (: []) . fromString

instance IsVariable Type where
    variant _v _vs = error "variant" -- Maybe we should use newName here?  That means using the Q monad everywhere.
    prefix p (VarT name) = VarT (mkName (p ++ nameBase name))
    prefix _p typ = error $ "IsVariable " ++ pprint typ

instance IsFunction Type

-- For type Type, the domain elements are concrete types, while
-- predicates are either EqualityT or class names applied to a
-- suitable number of class type parameters.
instance IsPredicate Type

instance IsTerm Type where
    type (TVarOf Type) = Type
    type (FunOf Type) = Type
    vt = id
    fApp _fn _ts = error "fApp"
    foldTerm vf _af x@(VarT _) = vf x
    foldTerm _vf af x@(ConT _) = af x []
    foldTerm _vf af x = af x []
    -- foldTerm _vf _af t = error $ "foldTerm: " ++ show t

instance HasApply Type where
    type (PredOf Type) = Type
    type (TermOf Type) = Type
    applyPredicate p ts = foldl AppT p ts
    foldApply' _atomf applyf x = uncurry applyf (unfoldApply x []) -- Not yet clear what values comprise the atom type
    overterms _f _r0 _x = error "overterms"
    onterms _f _x = error "onterms"

-- EqualityT is the only predicate I am aware of.
instance HasEquate Type where
    equate a b = AppT (AppT EqualityT a) b
    foldEquate eq _ap (AppT (AppT EqualityT a) b) = eq a b
    foldEquate _eq ap t = uncurry ap (unfoldApply t [])

instance IsFormula Type where
    type (AtomOf Type) = Type
    true = error "true"
    false = error "false"
    asBool = error "asBool"
    atomic = id
    overatoms _f _fm _r0 = error "overatoms"
    onatoms _f _fm = error "onatoms"

instance IsLiteral Type where
    naiveNegate x = error $ "naiveNegate " ++ show x
    foldNegation _f _ne x = error $ "foldNegation " ++ show x
    foldLiteral' _ho _ne _tf at x = at x -- I don't yet know what types are true, false, or negation.  They may not exist.
    -- foldLiteral' _ho _ne _tf _at x = error $ "foldLiteral' " ++ show x

instance JustLiteral Type

instance HasFixity Context where
    precedence _ = undefined
    associativity _ = undefined

instance IsFormula Context where
    type (AtomOf Context) = Type
    true = error "true"
    false = error "false"
    asBool = error "asBool"
    atomic = Context . (: [])
    overatoms _f _fm _r0 = error "overatoms"
    onatoms _f _fm = error "onatoms"

-- A list of types are considered to be AND-ed, as in the 'Cxt' type.
instance IsLiteral Context where
    naiveNegate (Context [x]) = Context [naiveNegate x]
    naiveNegate _lits = error "Invalid Literal"
    foldNegation _f _ne x = error $ "foldNegation " ++ show x
    foldLiteral' _ho _ne _tf at (Context [x]) = at x -- I don't yet know what types are true, false, or negation.  They may not exist.
    foldLiteral' _ho _ne _tf _at x = error $ "foldLiteral' " ++ show x

instance IsPropositional Context where
    Context a .&. Context b = Context (a <> b)
    (.|.) = error "IsPropositional Type: Disjunction not supported"
    (.<=>.) = error "IsPropositional Type: IFF not supported"
    (.=>.) = error "IsPropositional Type: Imp not supported"
    foldPropositional' = error "foldPropositional'"
    foldCombination = error "foldCombination"

-- Unify a (concrete) type with a predicate type, such @Ord a@.
instance (TVarOf Type ~ Type, TermOf Type ~ Type, JustLiteral Type) => Unify (Type, Type) where
    type UTermOf (Type, Type) = TermOf Type
    unify (AppT a b, AppT c d) = unify (a, c) >> unify (b, d)
    unify (a@(VarT _), b) = modify (Map.insert a b)
    unify (a, b@(VarT _)) = modify (Map.insert b a)
    unify (a, b) | a == b = return ()
    unify (a, b) = fail $ "Cannot unify: (" ++ pprint' a ++ ", " ++ pprint' b ++ ")"
    -- unify (typ, cxt) = error $ "Unimplemented: unify (" ++ pprint' typ ++ " :: Type, " ++ pprint' cxt ++ " :: Type)"

-- Unify a (concrete) type with a set of context, resulting in a map
-- of variable assignments.
instance (TVarOf Type ~ Type, TermOf Type ~ Type, JustLiteral Type) => Unify (Type, [Type]) where
    type UTermOf (Type, [Type]) = TermOf Type
    unify (typ, cxt) = error $ "Unimplemented: unify (" ++ pprint' typ ++ " :: Type, " ++ pprint' cxt ++ " :: [Type])"
