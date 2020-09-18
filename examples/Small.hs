-- {-# OPTIONS_GHC -Wall #-}

module Small where

import Language.Diorite
import Language.Diorite.Region

import Data.List (partition)
import Data.Proxy (Proxy(..))
import Data.Typeable (Typeable, eqT)
import Data.Type.Equality ((:~:)(..), TestEquality(..))
import Data.Constraint (Dict(..))

import Control.Monad.State (State)
import qualified Control.Monad.State as S (get, put, evalState)

--------------------------------------------------------------------------------
-- * Source language.
--------------------------------------------------------------------------------

-- | Source language.
data SExp a where
    SInt :: Int -> SExp ('Const Int)
    SAdd :: SExp ('Const Int ':-> 'Const Int ':-> 'Const Int)
    SLet :: SExp ('Const Int ':-> ('Const Int ':-> 'Const Int) ':-> 'Const Int)

instance Render SExp where
    renderSym (SInt i) = "i" ++ show i
    renderSym (SAdd)   = "(+)"
    renderSym (SLet)   = "let"

instance Sym SExp where
    symbol (SInt _) = signature
    symbol (SAdd)   = signature
    symbol (SLet)   = signature

intS :: Int -> Beta SExp ('Const Int)
intS = smartSym' . SInt

addS :: Beta SExp ('Const Int) -> Beta SExp ('Const Int) -> Beta SExp ('Const Int)
addS = smartSym' SAdd

letS :: Beta SExp ('Const Int)
     -> (Beta SExp ('Const Int) -> Beta SExp ('Const Int))
     -> Beta SExp ('Const Int)
letS = smartSym' SLet

--------------------------------------------------------------------------------
-- ** Small examples.

one :: Beta SExp ('Const Int)
one = intS 1

test_add :: Beta SExp ('Const Int)
test_add = one `addS` (one `addS` one)

test_share :: Beta SExp ('Const Int)
test_share = letS one (\v -> one `addS` v)

--------------------------------------------------------------------------------
-- * Target language.
--------------------------------------------------------------------------------

-- | Target language.
data TExp a where
    TInt :: Int -> TExp ('Put ':=> 'Const Int)
    TAdd :: TExp ('Put ':=> 'Const Int ':-> 'Const Int ':-> 'Const Int)
    TLet :: TExp
        (    'Put
        ':=> ('Put ':=> 'Const Int)
        ':-> ('Const Int ':-> 'Const Int)
        ':-> 'Const Int
        )
    TLoc :: Typeable a => Place -> TExp ('Const a ':-> 'Const a)
  -- todo: The number of 'Put':s in 'TLet' really depend on its shared value.

instance Render TExp where
    renderSym (TInt i) = renderSym (SInt i)
    renderSym (TAdd)   = renderSym (SAdd)
    renderSym (TLet)   = renderSym (SLet)
    renderSym (TLoc p) = "rgn " ++ ('r':show p) ++ " in"

instance Sym TExp where
    symbol (TInt _) = signature
    symbol (TAdd)   = signature
    symbol (TLet)   = signature
    symbol (TLoc _) = signature

--------------------------------------------------------------------------------

data P a where
    PInt :: Region -> P Int

instance TestEquality P where
    testEquality (PInt _) (PInt _) = Just Refl

instance Representable P Int where
    represent = PInt 0

instance Free P where
    free (PInt r) = [r]

instance Substitute P where
    sub s (PInt r) = PInt (subR s r)

instance Fresh P where
    fresh (PInt _) = PInt <$> newName

--------------------------------------------------------------------------------

type LExp = TExp :+: Local

instance InferSym SExp LExp where
    type Prim LExp = P
    inferSym = inferSym'

-- | ...
inferSym' :: forall sig a . (a ~ Result sig)
    => Store P -> SExp sig -> Args (Eta SExp) sig
    -> M (Sub, Context, P a, Beta LExp ('Const a))
inferSym' env (SInt i) (Nil) = do
    p <- newName
    r <- newName
    return $ ( []
             , [(p, r)]
             , PInt r
             , inj (TInt i) :# p)
inferSym' env (SAdd) (Spine a :* Spine b :* Nil) = do
    (sa, ca, ta, a') <- inferM env a
    (sb, cb, tb, b') <- inferM (subS sa env) b
    p <- newName
    r <- newName
    return $ ( sb @@ sa
             , (p, r) : subC sb ca ++ cb
             , PInt r
             , inj TAdd :# p :$ Spine a' :$ Spine b')
inferSym' env (SLet) (Spine a :* (v :\ Spine f) :* Nil) = do
    (sa, ca, ta, a') <- inferM env a
    let (ca_p,ca_y) = freeL ca env ta
    let (x, rho) = case ca_y of
          [(x, y)] -> (x, (v, Ex (TypePred y (TypeConst ta)))) -- todo.
    (sf, cf, tf, f') <- inferM (rho : subS sa env) f
    p <- newName
    r <- newName
    return $ ( sf @@ sa
             , subC sf ((p,r) : ca_p) ++ cf
             , tf
             , inj TLet :# p :$ (x :\\ Spine a') :$ (v :\ Spine f'))

inferTExp :: Typeable a => ASTF SExp a -> ASTF LExp a
inferTExp = infer

--------------------------------------------------------------------------------
-- Fin.
