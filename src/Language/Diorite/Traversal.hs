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
    ( Put(..), Qualifiers(..)
    , Signature(..), Result, Sig
    , Name, Place, Beta(..), Eta(..), ASTF)

import qualified Control.Applicative as A

--------------------------------------------------------------------------------
-- * Traversal.
--------------------------------------------------------------------------------

-- | List of a symbol's arguments.
data Args sym rs (sig :: Signature (Put *) *) where
    Nil  :: Args c rs ('Const a)
    (:*) :: Eta sym rs a -> Args sym rs sig -> Args sym rs (a ':-> sig)
    (:~) :: Place r -> Args sym ('Put r ':- rs) sig -> Args sym rs ('Put r ':=> sig)

infixr :*, :~

-- | "Pattern match" on a fully applied 'AST' using a function that gets direct
--   access to the top-most symbol and its sub-trees given as 'Args'.
match :: forall sym rs a c
    .  (forall ps sig . a ~ Result sig =>
            sym sig -> Args sym ps sig -> c ('Const a))
         -- ^ Match on a symbol.
    -> (forall ps sig . (a ~ Result sig, Sig sig) =>
            Name -> Args sym ps sig -> c ('Const a))
         -- ^ Lookup and instantiate a variable.
    -> Beta sym rs ('Const a)
         -- ^ Expression to traverse.
    -> c ('Const a)
match matchSym matchVar = flip matchBeta Nil
  where
    matchBeta :: forall rs sig . a ~ Result sig =>
        Beta sym rs sig -> Args sym rs sig -> c ('Const a)
    matchBeta (Var n)  as = matchVar n as
    matchBeta (Sym s)  as = matchSym s as
    matchBeta (b :$ e) as = matchBeta b (e :* as)
    matchBeta (b :# p) as = matchBeta b (p :~ as)
  -- todo: The inner 'ps' should really be 'rs'.

-- | A version of 'match' with a simpler, constant result type.
constMatch :: forall sym a b
    .  (forall rs sig . a ~ Result sig =>
            sym sig -> Args sym rs sig -> b)
    -> (forall rs sig . (a ~ Result sig, Sig sig) =>
            Name -> Args sym rs sig -> b)
    -> ASTF sym a -> b
constMatch f g = A.getConst . match (\s -> A.Const . f s) (\s -> A.Const . g s)

newtype WrapBeta c sym sig = WrapBeta { unWrapBeta :: c (Beta sym 'None sig) }
  -- note: Only used in the definition of 'transMatch'.

-- | A version of 'match' where the result is a transformed syntax tree, wrapped
--   in some type constructor.
transMatch :: forall sym sym' c a
    .  (forall rs sig . a ~ Result sig =>
            sym sig -> Args sym rs sig -> c (ASTF sym' a))
    -> (forall rs sig . (a ~ Result sig, Sig sig) =>
            Name -> Args sym rs sig -> c (ASTF sym' a))
    -> ASTF sym a -> c (ASTF sym' a)
transMatch f g = unWrapBeta . match (\s -> WrapBeta . f s) (\s -> WrapBeta . g s)

--------------------------------------------------------------------------------
-- Fin.
