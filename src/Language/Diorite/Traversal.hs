{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}

module Language.Diorite.Traversal
    (
    -- * "Pattern matching" on ASTs.
      Args(..)
    , match
    -- , constMatch
    -- , transMatch
    ) where

import Language.Diorite.Signatures (Signature(..), Result)
import Language.Diorite.Qualifiers (Qualifier(..), Union, Difference, Subset, Qual(..), QualRep(..), union)
import qualified Language.Diorite.Qualifiers.Witness as W
import Language.Diorite.Syntax (Name, Ev, Symbol, Beta(..), Eta(..), ASTF, (|-))

-- import qualified Control.Applicative as A
--import Data.Proxy (Proxy)
import Data.Type.Equality ((:~:)(..))

--------------------------------------------------------------------------------
-- * Traversal.
--------------------------------------------------------------------------------

-- type Args :: forall p . Symbol p * -> Qualifier p -> Signature p * -> *
-- data Args sym qs sig where
--     Nil  :: Args sym qs ('Const a)
--     (:*) :: Eta sym ps a -> Args sym (Union qs ps) sig -> Args sym qs (a ':-> sig)
--     (:~) :: Ev p -> Args sym (p ':. qs) sig -> Args sym qs (p ':=> sig)

-- | List of a symbol's arguments.
type Args :: forall p . Symbol p * -> Qualifier p -> Qualifier p -> Signature p * -> *
data Args sym qs ps sig where
    Nil  :: Args sym qs 'None ('Const a)
    (:*) :: Eta sym rs a -> Args sym (Union qs rs) ps sig
         -> Args sym qs (Union ps rs) (a ':-> sig)
    (:~) :: Ev p -> Args sym (p ':. qs) ps sig
         -> Args sym qs (p ':. ps) (p ':=> sig)

infixr :*, :~

--------------------------------------------------------------------------------

recover :: forall a b . QualRep (Union a b) -> QualRep b -> QualRep (Difference (Union a b) b)
recover = undefined
-- note: 'a' is not given a 'QualRep', and thus ambiguous, because we want to
--       avoid building such a rep. if possible. It should be enough to fix 'a'
--       with a type application later on.

--------------------------------------------------------------------------------
  
-- | \"Pattern match\" on a fully applied 'AST' using:
--   1. a \"symbol\" function that gets direct access to the top-most symbol and
--      its sub-trees given as 'Args'.
--   2. a \"variable\" function ...
match :: forall p (sym :: Symbol p *) (qs :: Qualifier p) a (c :: Signature p * -> *)
    .  (Qual qs)
    => (forall ps sig . (a ~ Result sig) => sym sig -> Args sym 'None ps sig -> c ('Const a))
       -- ^ Match on a symbol.
    -> (forall ps rs sig . (a ~ Result sig) => Name -> Args sym ps rs sig -> c ('Const a))
       -- ^ Lookup and instantiate a variable.
    -> ASTF sym qs a
       -- ^ Expression to traverse.
    -> c ('Const a)
match matchSym matchVar beta =
    W.witUniIdent qs |-
    W.witSubRefl  qs |-
    matchBeta beta Nil qs QualNone
  where
    qs :: QualRep qs
    qs = qualifier
    
    matchBeta :: forall ps rs sig
        .  ( a ~ Result sig
           , Subset (Union ps rs) qs ~ 'True
           , Subset qs (Union ps rs) ~ 'True
           )
        => Beta sym ps sig
        -> Args sym ps rs sig
        -> QualRep ps
        -> QualRep rs
        -> c ('Const a)
    matchBeta (Var n)  as _ _ = matchVar n as
    matchBeta (Sym s)  as _ _ = matchSym s as
    matchBeta ((b :: Beta sym xs (y ':-> sig)) :$ (e :: Eta sym zs y)) as ps rs
        =
        let xs :: QualRep xs = undefined in
        let zs :: QualRep zs = undefined in
        let Refl :: ps :~: (Union xs zs) = Refl in
        let Refl :: Subset (Difference (Union xs zs) zs) xs :~: 'True = undefined xs zs in
        let Refl :: Subset xs (Difference (Union xs zs) zs) :~: 'True = undefined xs zs in
        --
        -- ???
        --
        matchBeta b (e :* as) xs (union rs zs) -- I can't use xs or zs here!
        -- Could not deduce:
        --   Subset qs (Union qs1 (Union rs ps1)) ~ 'True
        --     > qs1 ~ xs, ps1 ~ zs
        --   Subset qs (Union xs (Union rs zs)) ~ 'True
        --
        -- from the context:
        --   ( Subset (Union ps rs) qs ~ 'True
        --   , Subset qs (Union ps rs) ~ 'True)
        --     > ps ~ Union qs1 ps1, qs1 ~ xs, ps1 ~ zs
        --   ( Subset (Union (Union xs zs) rs) qs ~ 'True
        --   , Subset qs (Union (Union xs zs) rs) ~ 'True
        --
        -- 1:
        --   Subset (Union (Union xs zs) rs) qs ~ 'True
        --     > ???
        --   Subset 
        -- 
        -- 
    matchBeta (b :# q) as (QualPred p ps) rs =
        W.witSU1  p ps rs qs |-
        W.witSU1' p qs ps rs |-
        matchBeta b (q :~ as) ps (QualPred p rs)

--------------------------------------------------------------------------------

-- -- | A version of 'match' with a simpler, constant result type.
-- constMatch :: forall sym qs a b
--     .  (forall sig . a ~ Result sig =>
--             sym sig -> Args sym 'None sig -> b)
--     -> (forall ps sig . (a ~ Result sig) =>
--             Name -> Args sym ps sig -> b)
--     -> ASTF sym qs a -> b
-- constMatch f g = A.getConst . match (\s -> A.Const . f s) (\s -> A.Const . g s)

-- newtype WrapBeta c sym qs sig = WrapBeta { unWrapBeta :: c (Beta sym qs sig) }
-- -- note: Only used in the definition of 'transMatch'.

-- -- | A version of 'match' where the result is a transformed syntax tree, wrapped
-- --   in some type constructor.
-- transMatch :: forall sym sym' qs c a
--     .  (forall sig . a ~ Result sig =>
--             sym sig -> Args sym 'None sig -> c (ASTF sym' qs a))
--     -> (forall ps sig . (a ~ Result sig) =>
--             Name -> Args sym ps sig -> c (ASTF sym' qs a))
--     -> ASTF sym qs a -> c (ASTF sym' qs a)
-- transMatch f g = unWrapBeta . match (\s -> WrapBeta . f s) (\s -> WrapBeta . g s)

--------------------------------------------------------------------------------
-- Fin.
