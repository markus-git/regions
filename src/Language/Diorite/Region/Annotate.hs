--{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE TypeApplications #-}

module Language.Diorite.Region.Annotate
    (
    ) where

import Language.Diorite.Signatures (Signature, Result, SigRep(..))
import Language.Diorite.Qualifiers (Qualifier(..), Remove, Union, Difference, QualRep(..))
import Language.Diorite.Syntax (Name, Ev(..), Beta(..), Eta(..), AST, ASTF, elam, (:+:)(..), (:<:)(..))
--import Language.Diorite.Traversal (Args(..), constMatch)
import qualified Language.Diorite.Signatures as S (Signature(..))

import Data.Proxy (Proxy(..))
import Data.Type.Equality ((:~:)(..))

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------
--
-- ** What I (sorta) have:
--
-- > beta :: B [] ('Int -> 'Int -> 'Int)
-- > beta = \x. \y. x + y
--
-- ** What I (sorta) want:
--
-- > beta :: B [1,2,3,4,5] ('Int^1 ->^2 'Int^3 ->^4 'Int^5)
-- > beta = (\x . (\y . (local <1,3> in (x + y)) at 5) at 4) at 2
--   ~alternatively~
-- > beta = \x .^2 \y .^4 local <1,3> in (x + y)^5
--
-- note: rules must now match on "sym a at r" and "\x . e at r"
-- instead of just "sym a" and "\x . e" with a rule for "e at r".
--
-- ** What I thus (sorta) need:
--
-- Terms for region annotations:
-- > local r in E  where  local :: AST (r : rs) 'Int -> AST rs 'Int
-- > E at r        where  at    :: AST rs 'Int       -> AST ...
--
-- Symbol signatures extended with region annotations:
-- > t ::= a | t -> t | p => t | t ^ Put r
--
--------------------------------------------------------------------------------

-- | Kind for 'Put' predicates, which assert that a region 'r' is allocated.
data Put r = Put r

-- | Evidence that a region 'r' is allocated.
type Place :: forall r . r -> *
type Place r = Ev ('Put r)

-- | Term annotations for region labels.
type Rgn :: forall r . Signature (Put r) * -> *
data Rgn sig where
    Local :: Rgn (('Put r 'S.:=> 'S.Const a) 'S.:-> 'S.Const a)
    At    :: Rgn ('Put r 'S.:=> a 'S.:-> sig)

-- | Introduce a local binding for place associated with region 'r'.
local :: forall sym r qs a . (Rgn :<: sym) => ASTF sym ('Put r ':. qs) a -> Place r -> ASTF sym qs a
local ast p = (inj Local :: AST sym 'None (('Put r 'S.:=> 'S.Const a) 'S.:-> 'S.Const a)) :$ (p :\\ Spine ast)

-- | Annotate an value-expression with the place to store its result in.
atBeta :: forall sym r qs a . (Rgn :<: sym, Remove ('Put r) qs ~ qs) => ASTF sym qs a -> Place r -> ASTF sym ('Put r ':. qs) a
atBeta ast p = (inj At :: AST sym 'None ('Put r 'S.:=> 'S.Const a 'S.:-> 'S.Const a)) :# p :$ (Spine ast)

-- | Annotate a function with the place to store its closure in.
atEta :: forall sym r qs sig . (Rgn :<: sym, Remove ('Put r) qs ~ qs) => Eta sym qs sig -> Place r -> AST sym ('Put r ':. qs) sig
atEta ast p = (inj At :: AST sym 'None ('Put r 'S.:=> sig 'S.:-> sig)) :# p :$ ast

-- note: Since our region inference rules only introduce bindings at terms with
--       a first-order type it's fine to limit 'local' to 'ASTF' values.
-- note: 'Spine' is for values, hence sep. 'Beta'/'Eta' variants of 'at'.
-- note: 'a' is not annotated here since 'AST' uses un-labelled signatures.
--------------------------------------------------------------------------------

-- | Signature with region labels.
data Label r a =
      Const a
    | Label r a :-> Label r a
    | Put r :=> Label r a
    | Label r a :^ r

infixr 2 :->, :=>
infixl 1 :^

--------------------------------------------------------------------------------
--
-- But Beta/Eta operates on signatures, not labelled signatures.
--
--------------------------------------------------------------------------------
  
-- -- | Witness of equality between a symbol's signature and its erased annotation.
-- newtype sig :~~: lbl = Stripped (sig :~: Strip lbl)

-- infixr :~~:

-- type Labelled :: forall r . (Signature (Put r) * -> *) -> Label r * -> *
-- data Labelled ast lbl = forall sig . Labelled
--     { _ast :: ast sig
--     , _lbl :: sig :~~: lbl
--     }

-- type LAST  sym qs lbl = Labelled (Beta sym qs) lbl
-- type LASTF sym qs a   = LAST sym qs ('Const a)

-- wrap :: AST sym qs ('S.Const a) -> LAST sym qs ('Const a)
-- wrap = flip Labelled (Stripped Refl)

-- local :: forall sym r qs a lbl . (Rgn :<: sym, Strip lbl ~ 'S.Const a) => LAST sym ('Put r ':. qs) lbl -> Place r -> LAST sym qs lbl
-- local (Labelled b (Stripped Refl)) p = Labelled (ast b) (Stripped Refl)
--   where
--     ast :: ASTF sym ('Put r ':. qs) a -> ASTF sym qs a
--     ast b = local' :$ (p :\\ (Spine b))
    
--     local' :: AST sym 'None (('Put r 'S.:=> 'S.Const a) 'S.:-> 'S.Const a)
--     local' = inj Local

-- at :: forall sym r qs a . (Rgn :<: sym, Remove ('Put r) qs ~ qs) => LASTF sym qs a -> Place r -> LAST sym ('Put r ':. qs) ('Const a :^ r)
-- at (Labelled b (Stripped Refl)) p = Labelled (ast b) (Stripped Refl)
--   where
--     ast :: ASTF sym qs a -> ASTF sym ('Put r ':. qs) a
--     ast b = at' :# p :$ (Spine b)
    
--     at' :: AST sym 'None ('Put r 'S.:=> 'S.Const a 'S.:-> 'S.Const a)
--     at' = inj At

--------------------------------------------------------------------------------
--
-- Turning a 'Beta' into a 'Labelled Beta' means turning every:
--
-- > ('Const a) ~> {}                 ('Const a)^r
-- > (a ':-> b) ~> {a ~> a', b ~> b'} (a' ':-> b')^r
-- > (p ':=> b) ~> {b ~> b'}          (p  ':=> b')^r
--
-- For some 'r' which we need to generate somehow. However, unlike the solution
-- in 'SmartBeta', we cannot rely on the user to specify ...

--
-- annotate :: forall r (sym :: Signature (Put r) * -> *) (qs :: Qualifier (Put r)) (ps :: Qualifier (Put r)) (a :: *) (lbl :: Label r *)
--     .  ( Strip lbl ~ 'S.Const a
--        )
--     => AST sym qs ('S.Const a)
--     -> LAST (sym :+: Rgn) ? ?
-- annotate = constMatch ...

--------------------------------------------------------------------------------
-- Fin.
