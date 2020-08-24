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
    ( Put(..), Signature(..), Place, Beta(..), Eta(..))

import qualified Control.Applicative as A

--------------------------------------------------------------------------------
-- * Traversal.
--------------------------------------------------------------------------------

-- | List of arguments.
data Args c (sig :: Signature *) where
    (:*) :: Eta c a -> Args c sig -> Args c (a ':-> sig)
    (:~) :: Place   -> Args c sig -> Args c ('Put ':=> sig)
    Nil  :: Args c ('Const a)

infixr :*, :~

-- | Denotational result of a symbol's signature.
type family Result sig where
    Result ('Const a)    = a
    Result (a ':-> b)    = Result b
    Result ('Put ':=> a) = Result a
  
-- | \"Pattern match\" on a fully applied \"AST\" using a function that gets
--   direct access to the top-most symbol and its sub-trees given as \"Args\".
match :: forall sym a c
    .  (forall sig . a ~ Result sig => sym sig -> Args sym sig -> c ('Const a))
         -- ^ ...
    -> ()
         -- ^ ...
    -> Beta sym ('Const a)
         -- ^ Expression to traverse.
    -> c ('Const a)
match matchSym _ = flip matchBeta Nil
  where
    matchBeta :: forall sig . a ~ Result sig => Beta sym sig -> Args sym sig -> c ('Const a)
    matchBeta (Var _)  _  = undefined
    matchBeta (Sym s)  as = matchSym s as
    matchBeta (b :$ e) as = matchBeta b (e :* as)
    matchBeta (b :# p) as = matchBeta b (p :~ as)
  -- todo: handle the matching of variables.

-- | A version of \"match\" with a simpler, constant result type.
constMatch :: forall sym a b
    .  (forall sig . (a ~ Result sig) => sym sig -> Args sym sig -> b)
    -> ()
    -> Beta sym ('Const a) -> b
constMatch f _ = A.getConst . match (\s -> A.Const . f s) undefined

newtype WrapBeta c sym sig = WrapBeta { unWrapBeta :: c (Beta sym sig) }
  -- Only used in the definition of 'transMatch'

-- | A version of \"match\" where the result is a transformed syntax tree,
--   wrapped in some type constructor.
transMatch :: forall sym sym' c a
    .  (forall sig . (a ~ Result sig) => sym sig -> Args sym sig -> c (Beta sym' ('Const a)))
    -> ()
    -> Beta sym ('Const a) -> c (Beta sym' ('Const a))
transMatch f _ = unWrapBeta . match (\s -> WrapBeta . f s) undefined

--------------------------------------------------------------------------------
-- Fin.
