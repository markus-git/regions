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
import Language.Diorite.Region.Labels (Put(..), Label(..), (:~~:)(..), Strip(..), LblRep)
import qualified Language.Diorite.Signatures as S (Signature(..))

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
-- > beta :: B .. ('Int^1 ->^2 'Int^3 ->^4 'Int^5)
-- > beta = (\x . (\y . (x + y) at 5) at 4) at 2
--   ~alternatively~
-- > beta = \x .^2 \y .^4 (x + y)^5
--
-- note: rules must now match on "sym a at r" and "\x . e at r"
-- instead of just "sym a" and "\x . e" with a rule for "e at r".
--
-- What I thus (sorta) need:
--
-- > local r in E
-- > E at r
--
-- But Beta/Eta operates on signatures, not labelled signatures, so their
-- "smart" constructors need to take a "labelled" Beta/Eta that takes a
-- labelled signature instead.

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
-- 'Beta' into an 'Eta' argument for 'At'. Annotation of lambdas must therefore
-- be done by matching.

--------------------------------------------------------------------------------
--
-- Turning a 'Beta' into a 'Labelled Beta' means turning every:
--
-- > ('Const a) ~> ('Const a)^r
-- > (a ':-> b) ~> (a ':-> b)^r
-- > (p ':=> b) ~> (p ':=> b)
--
-- For some 'r' which we need to generate somehow. However, unlike the solution
-- in 'SmartBeta', we cannot rely on the user to specify ...

data Nat = Z | S Nat

data Indices = Val Nat | Fun Nat Indices Indices | Pre Indices

type IxRep :: Indices -> *
data IxRep is where
    IxVal :: IxRep ('Val n)
    IxFun :: Proxy n -> IxRep a -> IxRep b -> IxRep ('Fun n a b)
    IxPre :: IxRep a -> IxRep ('Pre a)

type Annotate :: Signature (Put Nat) * -> Indices -> Label Nat *
type family Annotate sig is where
    Annotate ('S.Const a) ('Val r)     = 'Const a ':^ r
    Annotate (a 'S.:-> b) ('Fun r x y) = Annotate a x :-> Annotate b y ':^ r
    Annotate (p 'S.:=> b) ('Pre x)     = p :=> Annotate b x

wrap :: AST sym qs ('S.Const a) -> LAST sym qs ('Const a)
wrap = flip Labelled (Stripped Refl)

annotateBeta :: forall sym qs sig is ps lbl n
    .  ( Rgn :<: sym
       , lbl ~ Annotate sig ('Val n)
       , ps  ~ ('Put n ':. qs)
       , Remove ('Put n) qs ~ qs
       )
    => AST  sym qs sig
    -> Args sym qs sig
    -> IxRep ('Val n)
    -> LAST sym ps lbl
annotateBeta ast (Nil) (IxVal) =
  at (wrap ast) undefined

annotate :: forall sym qs ps a lbl . Strip lbl ~ 'S.Const a => AST sym qs ('S.Const a) -> LAST (sym :+: Rgn) ps lbl
annotate = undefined --constMatch annotateSym instantiateVar

--------------------------------------------------------------------------------
-- Fin.
