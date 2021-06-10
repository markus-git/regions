--{-# OPTIONS_GHC -Wall #-}

module Language.Diorite.Region.Annotate
    (
    -- * ...
      Rgn(..)
    , local
    , at
    ) where

import Language.Diorite.Signatures (Signature, Result, SigRep(..))
import Language.Diorite.Qualifiers (Qualifier(..), Remove, Union, Difference, QualRep(..))
import Language.Diorite.Syntax (Name, Ev(..), Beta(..), Eta(..), AST, ASTF, elam, (:+:)(..), (:<:)(..))
import Language.Diorite.Traversal (Args(..), constMatch)
import qualified Language.Diorite.Signatures as S (Signature(..))

import Language.Diorite.Region.Labels 

import Data.Proxy (Proxy(..))
import Data.Type.Equality ((:~:)(..))

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------
--
-- What I (sorta) have:
--
-- > beta :: B [] ('Int -> 'Int -> 'Int)
-- > beta = \x. \y. x + y
--
-- What I (sorta) want:
--
-- > beta :: B [1,2,3,4,5] ('Int^1 ->^2 'Int^3 ->^4 'Int^5)
-- > beta = (\x . (\y . (x + y) at 5) at 4) at 2
--   ~alternatively~
-- > beta = \x .^2 \y .^4 (x + y)^5
--
-- note: rules must now match on "sym a at r" and "\x . e at r"
-- instead of just "sym a" and "\x . e" with a rule for "e at r".
--
-- What I thus (sorta) need:
--
-- > local r in E  where  local :: AST (r : rs) 'Int -> AST rs 'Int
-- > E at r        where  at    :: AST rs 'Int       -> AST ...
--
-- But Beta/Eta operates on signatures, not labelled signatures.

-- | Witness of equality between a symbol's signature and its erased annotation.
newtype sig :~~: lbl = Stripped (sig :~: Strip lbl)

infixr :~~:

type Labelled :: forall r . (Signature (Put r) * -> *) -> Label r * -> *
data Labelled ast lbl = forall sig . Labelled
    { _ast :: ast sig
    , _lbl :: sig :~~: lbl
    }

type LAST  sym qs lbl = Labelled (Beta sym qs) lbl
type LASTF sym qs a   = LAST sym qs ('Const a)

type Place :: forall r . r -> *
type Place r = Ev ('Put r)

type Rgn :: forall r . Signature (Put r) * -> *
data Rgn sig where
    Local :: Rgn (('Put r 'S.:=> a) 'S.:-> a)
    At    :: Rgn ('Put r 'S.:=> sig 'S.:-> sig)

wrap :: AST sym qs ('S.Const a) -> LAST sym qs ('Const a)
wrap = flip Labelled (Stripped Refl)

local :: forall sym r qs a lbl . (Rgn :<: sym, Strip lbl ~ 'S.Const a) => LAST sym ('Put r ':. qs) lbl -> Place r -> LAST sym qs lbl
local (Labelled b (Stripped Refl)) p = Labelled (ast b) (Stripped Refl)
  where
    ast :: ASTF sym ('Put r ':. qs) a -> ASTF sym qs a
    ast b = local' :$ (p :\\ (Spine b))
    
    local' :: AST sym 'None (('Put r 'S.:=> 'S.Const a) 'S.:-> 'S.Const a)
    local' = inj Local

at :: forall sym r qs a . (Rgn :<: sym, Remove ('Put r) qs ~ qs) => LASTF sym qs a -> Place r -> LAST sym ('Put r ':. qs) ('Const a :^ r)
at (Labelled b (Stripped Refl)) p = Labelled (ast b) (Stripped Refl)
  where
    ast :: ASTF sym qs a -> ASTF sym ('Put r ':. qs) a
    ast b = at' :# p :$ (Spine b)
    
    at' :: AST sym 'None ('Put r 'S.:=> 'S.Const a 'S.:-> 'S.Const a)
    at' = inj At
-- note: Since 'Spine' is limited to values, 'ast' cannot simply cast a labelled
--       'Beta' into an 'Eta' argument for 'At'. Annotation of lambdas must(?)
--       therefore be done when pattern-matching on a given 'Eta'.

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
-- data Nat = Z | S Nat
-- data Indices = Val Nat | Fun Nat Indices Indices | Pre Indices
-- type Annotate :: Signature (Put Nat) * -> Indices -> Label Nat *
-- type family Annotate sig is where
--     Annotate ('S.Const a) ('Val r)     = 'Const a ':^ r
--     Annotate (a 'S.:-> b) ('Fun r x y) = Annotate a x :-> Annotate b y ':^ r
--     Annotate (p 'S.:=> b) ('Pre x)     = p :=> Annotate b x
--
-- ...
--
-- annotate :: forall r (sym :: Signature (Put r) * -> *) (qs :: Qualifier (Put r)) (ps :: Qualifier (Put r)) (a :: *) (lbl :: Label r *)
--     .  ( Strip lbl ~ 'S.Const a
--        )
--     => AST sym qs ('S.Const a)
--     -> LAST (sym :+: Rgn) ? ?
-- annotate = constMatch ...

--------------------------------------------------------------------------------
-- Fin.
