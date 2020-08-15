{-# OPTIONS_GHC -Wall #-}

module Language.Diorite.Traversal
    ( Result, Arg(..), Args(..)
    , argS
    -- 
    , match, constMatch, transMatch
    ) where

import Language.Diorite.Syntax
    ( Put(..), Signature(..), Name, Place, Beta(..), Eta(..), SigRep(..)
    , Sym(..))

import qualified Control.Applicative as A

--------------------------------------------------------------------------------
-- * Traversal.
--------------------------------------------------------------------------------

-- | Denotational result of a symbol's signature.
type family Result sig where
    Result ('Const a)    = a
    Result (a ':-> b)    = Result b
    Result ('Put ':=> a) = Result a

-- | Argument parameterized on variables and places.
data Arg c (sig :: Signature *) where
    AVar   :: Name -> Arg c a -> Arg c (sig ':-> a)
    APlace :: Place -> Arg c a -> Arg c ('Put ':=> a)
    ASym   :: c ('Const a) -> Arg c ('Const a)

-- | List of symbol arguments.
data Args c (sig :: Signature *) where
    Nil  :: Args c ('Const a)
    (:*) :: Arg c a -> Args c sig -> Args c (a ':-> sig)
    (:~) :: Place -> Args c sig -> Args c ('Put ':=> sig)

infixr :*, :~

-- | ...
argS :: forall sym sig . Sym sym => Arg sym sig -> SigRep sig
argS (AVar _ arg)   = SigPart undefined undefined (argS arg)
argS (APlace _ arg) = SigPred undefined (argS arg)
argS (ASym s)       = symbol s
  
--------------------------------------------------------------------------------
  
-- | \"Pattern match\" on a fully applied \"AST\" using a function that gets
--   direct access to the top-most symbol and its sub-trees given as \"Args\".
match :: forall sym a c
    .  (forall sig . (a ~ Result sig)
           => sym sig -> Args (Beta sym) sig -> c ('Const a))
    -> (forall sig . (a ~ Result sig)
           => Name    -> Args (Beta sym) sig -> c ('Const a))
    -> Beta sym ('Const a)
    -> c ('Const a)
match f g = flip matchBeta Nil
  where
    matchBeta :: forall sig . (a ~ Result sig)
        => Beta sym sig -> Args (Beta sym) sig -> c ('Const a)
    matchBeta (Var v)  as = g v as
    matchBeta (Sym s)  as = f s as
    matchBeta (b :$ e) as = matchBeta b (matchEta e :* as)
    matchBeta (b :# p) as = matchBeta b (p :~ as)

    matchEta :: Eta sym sig -> Arg (Beta sym) sig
    matchEta (Lam v e)  = AVar v (matchEta e)
    matchEta (ELam p e) = APlace p (matchEta e)
    matchEta (Spine b)  = ASym b
  -- todo: users can probably use their 'f' in the definition of 'g' but I feel
  -- like I should be able to define that myself somehow, like 'f (g ..) as'

-- | A version of \"match\" with a simpler, constant result type.
constMatch :: forall sym a b
    .  (forall sig . (a ~ Result sig)
           => sym sig -> Args (Beta sym) sig -> b)
    -> (forall sig . (a ~ Result sig)
           => Name    -> Args (Beta sym) sig -> b)
    -> Beta sym ('Const a) -> b
constMatch f g = A.getConst . match (\s -> A.Const . f s) (\v -> A.Const . g v)

newtype WrapBeta c sym sig = WrapBeta { unWrapBeta :: c (Beta sym sig) }
  -- Only used in the definition of 'transMatch'

-- | A version of \"match\" where the result is a transformed syntax tree,
--   wrapped in some type constructor.
transMatch :: forall sym sym' c a
    .  (forall sig . (a ~ Result sig)
           => sym sig -> Args (Beta sym) sig -> c (Beta sym' ('Const a)))
    -> (forall sig . (a ~ Result sig)
           => Name    -> Args (Beta sym) sig -> c (Beta sym' ('Const a)))
    -> Beta sym ('Const a) -> c (Beta sym' ('Const a))
transMatch f g = unWrapBeta . match (\s -> WrapBeta . f s) (\v -> WrapBeta . g v)

--------------------------------------------------------------------------------
-- Fin.
