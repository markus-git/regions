{-# OPTIONS_GHC -Wall #-}

module Language.Diorite.Traversal
    ( Result
    , Args(..)
    -- 
    , match
    , constMatch
    , transMatch
    ) where

import Language.Diorite.Syntax
    (Name, Place, Put(..), Signature(..), Beta(..), Eta(..))

--import Data.Typeable (Typeable)

import qualified Control.Applicative as A

--------------------------------------------------------------------------------
-- * Traversal.
--------------------------------------------------------------------------------

-- | List of arguments.
data Args c (sig :: Signature *) where
    Nil  :: Args c ('Const a)
    (:*) :: c a -> Args c sig -> Args c (a ':-> sig)
    (:~) :: Place -> Args c sig -> Args c ('Put ':=> sig)

infixr :*, :~

-- | Denotational result of a symbol's signature.
type family Result sig where
    Result ('Const a)    = a
    Result (a ':-> b)    = Result b
    Result ('Put ':=> a) = Result a
  
-- | "Pattern match" on a fully applied 'AST' using a function that gets direct
--   access to the top-most symbol and its sub-trees given as 'Args'.
match :: forall sym a c
    .  (forall sig . (a ~ Result sig) =>
            sym sig -> Args (Eta sym) sig -> c ('Const a))
         -- ^ ...
    -> (forall sig . (a ~ Result sig) =>
            Name -> Args (Eta sym) sig -> c ('Const a))
         -- ^ ...
    -> Beta sym ('Const a)
         -- ^ Expression to traverse.
    -> c ('Const a)
match matchSym matchVar = flip matchBeta Nil
  where
    matchBeta :: forall sig . a ~ Result sig =>
        Beta sym sig -> Args (Eta sym) sig -> c ('Const a)
    matchBeta (Var n)  as = matchVar n as
    matchBeta (Sym s)  as = matchSym s as
    matchBeta (b :$ e) as = matchBeta b (e :* as)
    matchBeta (b :# p) as = matchBeta b (p :~ as)

-- | A version of 'match' with a simpler, constant result type.
constMatch :: forall sym a b
    .  (forall sig . (a ~ Result sig) =>
            sym sig -> Args (Eta sym) sig -> b)
    -> (forall sig . (a ~ Result sig) =>
            Name -> Args (Eta sym) sig -> b)
    -> Beta sym ('Const a) -> b
constMatch f g = A.getConst . match (\s -> A.Const . f s) (\s -> A.Const . g s)

newtype WrapBeta c sym sig = WrapBeta { unWrapBeta :: c (Beta sym sig) }
  -- note: Only used in the definition of 'transMatch'

-- | A version of 'match' where the result is a transformed syntax tree, wrapped
--   in some type constructor.
transMatch :: forall sym sym' c a
    .  (forall sig . (a ~ Result sig) =>
            sym sig -> Args (Eta sym) sig -> c (Beta sym' ('Const a)))
    -> (forall sig . (a ~ Result sig) =>
            Name -> Args (Eta sym) sig -> c (Beta sym' ('Const a)))
    -> Beta sym ('Const a) -> c (Beta sym' ('Const a))
transMatch f g = unWrapBeta . match (\s -> WrapBeta . f s) (\s -> WrapBeta . g s)

--------------------------------------------------------------------------------
-- Fin.
