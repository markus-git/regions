{-# OPTIONS_GHC -Wall #-}

module Language.Diorite.Traversal
    (
    -- * "Pattern matching" on ASTs.
      Args(..)
    , match
    , constMatch
    , transMatch
    ) where

import Language.Diorite.Signatures (Signature(..), Result)
import Language.Diorite.Qualifiers (Qualifier(..), Union)
import Language.Diorite.Syntax (Name, Ev, Beta(..), Eta(..), ASTF)

import qualified Control.Applicative as A

--------------------------------------------------------------------------------
-- * Traversal.
--------------------------------------------------------------------------------

-- | List of a symbol's arguments.
type Args :: forall p . (Signature p * -> *) -> Qualifier p -> Signature p * -> *
data Args sym qs sig where
    Nil  :: Args sym qs ('Const a)
    (:*) :: Eta sym ps a -> Args sym (Union qs ps) sig -> Args sym qs (a ':-> sig)
    (:~) :: Ev p -> Args sym (p ':. qs) sig -> Args sym qs (p ':=> sig)

infixr :*, :~
  
-- | "Pattern match" on a fully applied 'AST' using a function that gets direct
--   access to the top-most symbol and its sub-trees given as 'Args'.
match :: forall sym qs a c
    .  (forall sig . a ~ Result sig =>
            sym sig -> Args sym 'None sig -> c ('Const a))
       -- ^ Match on a symbol.
    -> (forall ps sig . (a ~ Result sig) =>
            Name -> Args sym ps sig -> c ('Const a))
       -- ^ Lookup and instantiate a variable.
    -> ASTF sym qs a
       -- ^ Expression to traverse.
    -> c ('Const a)
match matchSym matchVar = flip matchBeta Nil
  where
    matchBeta :: forall ps sig . (a ~ Result sig) =>
        Beta sym ps sig -> Args sym ps sig -> c ('Const a)
    matchBeta (Var n)  as = matchVar n as
    matchBeta (Sym s)  as = matchSym s as
    matchBeta (b :$ e) as = matchBeta b (e :* as)
    matchBeta (b :# p) as = matchBeta b (p :~ as)
-- todo: I'm sure 'matchVar' needs to constrain 'ps' to be useful.

-- | A version of 'match' with a simpler, constant result type.
constMatch :: forall sym qs a b
    .  (forall sig . a ~ Result sig =>
            sym sig -> Args sym 'None sig -> b)
    -> (forall ps sig . (a ~ Result sig) =>
            Name -> Args sym ps sig -> b)
    -> ASTF sym qs a -> b
constMatch f g = A.getConst . match (\s -> A.Const . f s) (\s -> A.Const . g s)

newtype WrapBeta c sym qs sig = WrapBeta { unWrapBeta :: c (Beta sym qs sig) }
-- note: Only used in the definition of 'transMatch'.

-- | A version of 'match' where the result is a transformed syntax tree, wrapped
--   in some type constructor.
transMatch :: forall sym sym' qs c a
    .  (forall sig . a ~ Result sig =>
            sym sig -> Args sym 'None sig -> c (ASTF sym' qs a))
    -> (forall ps sig . (a ~ Result sig) =>
            Name -> Args sym ps sig -> c (ASTF sym' qs a))
    -> ASTF sym qs a -> c (ASTF sym' qs a)
transMatch f g = unWrapBeta . match (\s -> WrapBeta . f s) (\s -> WrapBeta . g s)

--------------------------------------------------------------------------------
-- Fin.
