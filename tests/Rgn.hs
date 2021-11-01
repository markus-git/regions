{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE TypeApplications #-}

module Rgn where

import Language.Diorite.Signatures
--import qualified Language.Diorite.Signatures as S
import Language.Diorite.Qualifiers
import Language.Diorite.Syntax
import Language.Diorite.Decoration
import Language.Diorite.Interpretation
import qualified Language.Diorite.Region.Annotation as A
import qualified Language.Diorite.Region.Labels as L

import Data.Typeable
import Data.Constraint (Constraint)

import GHC.TypeNats

--------------------------------------------------------------------------------
-- * Region annotation.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- ** Example language based on 'D'.

type D :: Signature (L.Put Nat) * -> *
data D a where
    -- Numerical
    Num :: Int -> D ('Const Int)
    Neg :: D ('Const Int ':-> 'Const Int)
    Add :: D ('Const Int ':-> 'Const Int ':-> 'Const Int)
    -- Sharing
    Let :: D ('Const Int ':-> ('Const Int ':-> 'Const Int) ':-> 'Const Int)
    -- Tuples
    Tup :: (Typeable a, Typeable b) => D ('Const a ':-> 'Const b ':-> 'Const (a, b))
    Fst :: (Typeable a, Typeable b) => D ('Const (a, b) ':-> 'Const a)
    Snd :: (Typeable a, Typeable b) => D ('Const (a, b) ':-> 'Const b)

instance Sym D where
    symbol (Num _) = signature
    symbol (Neg)   = signature
    symbol (Add)   = signature
    symbol (Let)   = signature
    symbol (Tup)   = signature
    symbol (Fst)   = signature
    symbol (Snd)   = signature

instance Render D where
    renderSym (Num i) = show i
    renderSym (Neg)   = "-"
    renderSym (Add)   = "+"
    renderSym (Let)   = "let"
    renderSym (Tup)   = "(,)"
    renderSym (Fst)   = "1_"
    renderSym (Snd)   = "2_"

type TR :: * -> *
data TR a where
    TInt :: TR Int
    TTup :: TR a -> TR b -> TR (a, b)

type T :: * -> Constraint
class (Eq a, Show a, Typeable a) => T a where
    tyrep :: TR a

instance T Int where
    tyrep = TInt

instance (T a, T b) => T (a, b) where
    tyrep = TTup tyrep tyrep

type B :: * -> *
type B a = Beta (D :&: TR) ('None :: Qualifier (L.Put Nat)) ('Const a)

smartD ::
    forall
       (es  :: Exists    (L.Put Nat))
       (sub :: Signature (L.Put Nat) * -> *)
       (sig :: Signature (L.Put Nat) *)
       (f   :: *)
    .  ( Sig sig
       , Ex es
       , f          ~ SmartBeta (D :&: TR) ('None) es sig
       , es         ~ SmartEx  f
       , sig        ~ SmartSig f
       , (D :&: TR) ~ SmartSym f
       , sub :<: D
       , T (Result sig)
       )
    => sub sig -> f
smartD = smartSymDecor tyrep

--------------------------------------------------------------------------------
-- ** Some functions and expressions in 'D'.

num :: Int -> B Int
num = smartD . Num

neg :: B Int -> B Int
neg = smartD Neg

add :: B Int -> B Int -> B Int
add = smartD Add

share :: B Int -> (B Int -> B Int) -> B Int
share = smartD Let

tup :: (T a, T b) => B a -> B b -> B (a, b)
tup = smartD Tup

l_ :: (T a, Typeable b) => B (a, b) -> B a
l_ = smartD Fst

r_ :: (Typeable a, T b) => B (a, b) -> B b
r_ = smartD Snd

ex1 :: B Int
ex1 = add (num 1) (neg (num 2))

ex2 :: B Int
ex2 = share (num 2) (\x -> add (num 1) x)

ex3 :: B Int
ex3 = share (num 2) (\x -> l_ (tup x (add x (neg x))))

--------------------------------------------------------------------------------
-- ** Annotation of expressions in 'D'.

-- type L :: forall p . Signature p * -> *
-- data L sig where
--     LTR :: TR a -> L ('Const a)

-- int : () -> Int^a
-- neg : Int^a -> Int^b
-- add : Int^a, Int^b -> Int^c
-- let : Int^a, (Int^a -> Int^b) -> Int^b
-- ...
-- instance A.Label D where
--     type Lbl D = L
--     label (X _) (A.Nil) = undefined
--     label (Y) (_ A.:* A.Nil) = undefined
--     label (Z) (_ A.:* _ A.:* A.Nil) = undefined
--     label (A) (_ A.:* _ A.:* A.Nil) = undefined

--type EB a = A.Beta2 (A.L (D :+: L.Rgn)) ((A.>=) 'None) ('Const @(L.Put Nat) a)

--ann :: B Int -> EB Int
--ann = fst (A.annotateASTF b)

--------------------------------------------------------------------------------
-- Fin.
