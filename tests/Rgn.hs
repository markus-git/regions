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
import qualified Language.Diorite.Region.Labels.Witness as AW
import Data.Typeable
import Data.Constraint (Constraint)

import GHC.TypeNats

--------------------------------------------------------------------------------
-- * Region annotation.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- ** Example language based on 'D'.

type D :: Signature (A.Put Nat) * -> *
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
type B a = Beta @(A.Put Nat) (D :&: TR) ('None) ('Const a)

smartD ::
    forall
       (es  :: Exists    (A.Put Nat))
       (sub :: Signature (A.Put Nat) * -> *)
       (sig :: Signature (A.Put Nat) *)
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

type LR :: * -> *
data LR a where
    LInt :: AW.N r -> LR Int
    LTup :: AW.N r -> LR a -> LR b -> LR (a, b)

-- int : () -> Int^a
-- neg : Int^a -> Int^b
-- add : Int^a, Int^b -> Int^c
-- let : Int^a, (Int^a -> Int^b) -> Int^b
-- ...
instance A.Lbl D where
    type Label D = LR
    
    label (Num _) n (A.Nil) = LInt n
    label (Neg) n (_ A.:* A.Nil) = LInt n
    label (Add) n (_ A.:* _ A.:* A.Nil) = LInt n
    label (Let) n (_ A.:* _ A.:* A.Nil) = LInt n
    label (Tup) n (a A.:* b A.:* A.Nil) = LTup n a b
    label (Fst) _ ((LTup _ a _) A.:* A.Nil) = a
    label (Snd) _ ((LTup _ _ b) A.:* A.Nil) = b

    free _ (LInt (n :: AW.NatRep r))
      = A.E (AW.withKnownNat n (QualPred (Proxy @r) QualNone))
    free p (LTup (n :: AW.NatRep r) a b)
      | A.E aq <- A.free p a
      , A.E bq <- A.free p b
      = A.E (AW.withKnownNat n (QualPred (Proxy @r) (union aq bq)))

type E :: * -> *
type E a = A.Beta2 @(A.Put Nat) (((D :&: TR) :+: A.Rgn) :&: LR) ((A.>=) 'None) ('Const a)

ann :: B Int -> E Int
ann = A.annotate

pr :: E Int -> String
pr (A.B2 b _) = show b

--------------------------------------------------------------------------------
-- Fin.
