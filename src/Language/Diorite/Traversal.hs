{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE UndecidableInstances #-}

module Language.Diorite.Traversal
    (
    -- * "Pattern matching" on ASTs.
      QualArgs(..)
    , Args(..)
    , SmartApply
    , match
    , constMatch
    , transMatch
    ) where

import Language.Diorite.Signatures (Signature(..), Result)
import Language.Diorite.Qualifiers (Qualifier(..), Union, Qual(..), QualRep(..))
import Language.Diorite.Syntax (Name, Ev, Symbol, Beta(..), Eta(..), ASTF)

import qualified Control.Applicative as A

--------------------------------------------------------------------------------
-- * Traversal.
--------------------------------------------------------------------------------

-- | ...
type QualArgs :: * -> *
data QualArgs p = Empty | Fun (Qualifier p) (QualArgs p) | Pre p (QualArgs p)
-- todo: this is basically the "spine" of 'Exists', also causes name-clash.

-- | List of a symbol's arguments.
type Args :: forall p . Symbol p * -> QualArgs p -> Signature p * -> *
data Args sym qs sig where
    Nil  :: Args sym 'Empty ('Const a)
    (:*) :: Eta sym ps a -> Args sym qs sig -> Args sym ('Fun ps qs) (a ':-> sig)
    (:~) :: Ev p -> Args sym qs sig -> Args sym ('Pre p qs) (p ':=> sig)

infixr :*, :~

-- | ...
type SmartApply :: forall p . Qualifier p -> QualArgs p -> Qualifier p
type family SmartApply qs ex where
    SmartApply qs ('Empty)     = qs
    SmartApply qs ('Fun ps rs) = SmartApply (Union qs ps) rs
    SmartApply qs ('Pre p ps)  = SmartApply (p ':. qs) ps

--------------------------------------------------------------------------------
  
-- | \"Pattern match\" on a fully applied 'AST' using:
--   1. a \"symbol\" function that gets direct access to the top-most symbol and
--      its sub-trees given as 'Args'.
--   2. a \"variable\" function that gets the top-most symbol's name, a
--      repersentation of the symbol's constraints, and its sub-trees given as
--      'Args'.
match :: forall p sym qs a (c :: Signature p * -> *)
    .  (forall ps sig . (a ~ Result sig, qs ~ SmartApply 'None ps)
            => sym sig -> Args sym ps sig -> c ('Const a))
       -- ^ Match on a symbol (ps ~ qs).
    -> (forall ps rs sig . (a ~ Result sig, qs ~ SmartApply rs ps)
            => Name -> QualRep rs -> Args sym ps sig -> c ('Const a))
       -- ^ Lookup and instantiate a variable (rs + ps ~ qs).
    -> ASTF sym qs a
       -- ^ Expression to traverse.
    -> c ('Const a)
match matchSym matchVar = flip matchBeta Nil
  where
    matchBeta :: forall ps rs sig
        .  ( a ~ Result sig
           , qs ~ SmartApply ps rs
           )
        => Beta sym ps sig
        -> Args sym rs sig
        -> c ('Const a)
    matchBeta (Var n)  as = matchVar n (qualifier :: QualRep ps) as
    matchBeta (Sym s)  as = matchSym s as
    matchBeta (b :$ e) as = matchBeta b (e :* as)
    matchBeta (b :# q) as = matchBeta b (q :~ as)

--------------------------------------------------------------------------------

-- | A version of 'match' with a simpler, constant result type.
constMatch :: forall sym qs a b
    .  (forall ps sig . (a ~ Result sig, qs ~ SmartApply 'None ps) =>
            sym sig -> Args sym ps sig -> b)
    -> (forall ps rs sig . (a ~ Result sig, qs ~ SmartApply rs ps) =>
            Name -> QualRep rs -> Args sym ps sig -> b)
    -> ASTF sym qs a -> b
constMatch f g = A.getConst . match (\s -> A.Const . f s) (\n r -> A.Const . g n r)

newtype WrapBeta c sym qs sig = WrapBeta { unWrapBeta :: c (Beta sym qs sig) }
-- note: Only used in the definition of 'transMatch'.

-- | A version of 'match' where the result is a transformed syntax tree, wrapped
--   in some type constructor.
transMatch :: forall sym sym' qs c a
    .  (forall ps sig . (a ~ Result sig, qs ~ SmartApply 'None ps) =>
            sym sig -> Args sym ps sig -> c (ASTF sym' qs a))
    -> (forall ps rs sig . (a ~ Result sig, qs ~ SmartApply rs ps) =>
            Name -> QualRep rs -> Args sym ps sig -> c (ASTF sym' qs a))
    -> ASTF sym qs a -> c (ASTF sym' qs a)
transMatch f g = unWrapBeta . match (\s -> WrapBeta . f s) (\n r -> WrapBeta . g n r)

--------------------------------------------------------------------------------
-- Fin.
