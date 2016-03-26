-- | ATP instances for the template haskell type 'Type', and the
-- conjunction of such types, @[Type]@.  In these instances, almost
-- every role is played by 'Type'.  It might a case where the tagged
-- package could be used to advantage.  A list represents conjunction,
-- but there is no disjunction operation, nor any derived from it like
-- implication or equivalence.

{-# LANGUAGE CPP, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, TypeFamilies, UndecidableInstances #-}
module Data.Logic.ATP.TH
    ( unfoldApply
    , expandBindings
    ) where

import Control.Monad.State (modify)
import Data.Generics (everywhere, mkT)
import Data.List (intersperse)
import Data.Logic.ATP (IsAtom, IsVariable(..), IsFunction, IsPredicate, HasEquate(..))
import Data.Logic.ATP.Apply (HasApply(PredOf, TermOf, applyPredicate, foldApply', overterms, onterms))
import Data.Logic.ATP.Formulas (IsFormula(..))
import Data.Logic.ATP.Lit (IsLiteral(..), JustLiteral)
import Data.Logic.ATP.Pretty (hcat, HasFixity(..), Pretty(pPrint), text)
import Data.Logic.ATP.Prop (IsPropositional(..))
import Data.Logic.ATP.Term (IsTerm(..))
import Data.Logic.ATP.Unif (Unify(UTermOf, unify'), unify_literals)
import Data.Map as Map (insertWithKey, lookup, Map)
import Data.Maybe (fromMaybe)
import Data.Monoid ((<>))
import Data.String (IsString(fromString))
import Language.Haskell.TH
import Language.Haskell.TH.PprLib (to_HPJ_Doc)
import Language.Haskell.TH.TypeGraph.Prelude (pprint1)

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

instance Monad m => Unify m Type where
    type UTermOf Type = TermOf Type
    unify' (AppT (AppT EqualityT a@(VarT _)) b) = modify (bind a b)
    unify' (AppT (AppT EqualityT a) b@(VarT _)) = modify (bind b a)
    unify' (AppT (AppT EqualityT (AppT a b)) (AppT c d)) =
        -- I'm told this is incorrect in the presence of type functions
        unify' (AppT (AppT EqualityT a) c) >> unify' (AppT (AppT EqualityT b) d)
    unify' (AppT (AppT EqualityT a) b) | a == b = return ()
    unify' (AppT (AppT EqualityT a) b) = fail $ "Cannot unify: (" ++ pprint1 a ++ ", " ++ pprint1 b ++ ")"
    unify' _ = return ()

instance Monad m => Unify m [Type] where
    type UTermOf [Type] = TermOf Type
    unify' = mapM_ unify'

-- | Create a new variable binding, making sure all bound variables in
-- are expanded in the resulting map.
bind :: Pred -> Pred -> Map Pred Pred -> Map Pred Pred
bind v@(VarT _) a mp =
    -- First, expand all occurrences of the new variable in existing bindings
    let mp' = everywhere (mkT (expandBinding v a)) mp in
    -- Next, expand all bound variables in the new binding
    let a' = everywhere (mkT (expandBindings mp')) a in
    -- Does this introduce any recursive bindings?
    let a'' = everywhere (mkT (expandBinding v (error $ "Recursive binding of " ++ show v))) a' in
    -- If the value is already bound, make sure the binding is identical
    Map.insertWithKey (\v' a1 a2 ->
                           if a1 == a2
                           then a1
                           else error ("Conflicting definitions of " ++ show v' ++ ":\n  " ++ show a1 ++ "\n  " ++ show a2)) v a'' mp'

expandBindings :: Map Pred Pred -> Pred -> Pred
expandBindings mp x@(VarT _) = fromMaybe x (Map.lookup x mp)
expandBindings _ x = x

expandBinding :: Pred -> Pred -> Pred -> Pred
expandBinding v a x = if x == v then a else x
