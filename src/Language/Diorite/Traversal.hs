{-# OPTIONS_GHC -Wall #-}

module Language.Diorite.Traversal
    (
    -- * "Pattern matching" on ASTs.
      Result
    , Args(..)
    , match
    , constMatch
    , transMatch
    ) where

import Language.Diorite.Syntax
    (Signature(..), Result, Sig, Name, Ev, Beta(..), Eta(..), ASTF)

import qualified Control.Applicative as A

--------------------------------------------------------------------------------
-- * Traversal.
--------------------------------------------------------------------------------

-- | List of a symbol's arguments.
data Args sym (sig :: Signature * *) where
    Nil  :: Args c ('Const a)
    (:*) :: Eta sym a -> Args sym sig -> Args sym (a ':-> sig)
    (:~) :: Ev r -> Args sym sig -> Args sym (p ':=> sig)

infixr :*, :~

-- | "Pattern match" on a fully applied 'AST' using a function that gets direct
--   access to the top-most symbol and its sub-trees given as 'Args'.
match :: forall sym a c
    .  (forall sig . a ~ Result sig =>
            sym sig -> Args sym sig -> c ('Const a))
         -- ^ Match on a symbol.
    -> (forall sig . (a ~ Result sig, Sig sig) =>
            Name -> Args sym sig -> c ('Const a))
         -- ^ Lookup and instantiate a variable.
    -> Beta sym ('Const a)
         -- ^ Expression to traverse.
    -> c ('Const a)
match matchSym matchVar = flip matchBeta Nil
  where
    matchBeta :: forall sig . a ~ Result sig =>
        Beta sym sig -> Args sym sig -> c ('Const a)
    matchBeta (Var n)  as = matchVar n as
    matchBeta (Sym s)  as = matchSym s as
    matchBeta (b :$ e) as = matchBeta b (e :* as)
    matchBeta (b :# p) as = matchBeta b (p :~ as)

-- | A version of 'match' with a simpler, constant result type.
constMatch :: forall sym a b
    .  (forall sig . a ~ Result sig =>
            sym sig -> Args sym sig -> b)
    -> (forall sig . (a ~ Result sig, Sig sig) =>
            Name -> Args sym sig -> b)
    -> ASTF sym a -> b
constMatch f g = A.getConst . match (\s -> A.Const . f s) (\s -> A.Const . g s)

newtype WrapBeta c sym sig = WrapBeta { unWrapBeta :: c (Beta sym sig) }
  -- note: Only used in the definition of 'transMatch'.

-- | A version of 'match' where the result is a transformed syntax tree, wrapped
--   in some type constructor.
transMatch :: forall sym sym' c a
    .  (forall sig . a ~ Result sig =>
            sym sig -> Args sym sig -> c (ASTF sym' a))
    -> (forall sig . (a ~ Result sig, Sig sig) =>
            Name -> Args sym sig -> c (ASTF sym' a))
    -> ASTF sym a -> c (ASTF sym' a)
transMatch f g = unWrapBeta . match (\s -> WrapBeta . f s) (\s -> WrapBeta . g s)

--------------------------------------------------------------------------------
-- Fin.
