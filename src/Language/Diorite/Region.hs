--{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE ConstraintKinds #-}

module Language.Diorite.Region
    (
    -- * Valid primitive types.
      Erasure(..)
    , (:~~:)(..)
    -- * ...
    , Local(..)
    -- * ...
    , Representable(..)
    , TypeRep(..)
    -- * Region inference.
    , Infer(..)
    , infer
    , inferM
    --
    , M
    , Store
    , Context
    , Sub
    , Free(..)
    , Substitute(..)
    , Fresh(..)
    , newName
    , newNames
    , store
    , freeS
    , freeL
    , subR
    , subS
    , subC
    , (@@)
    ) where

import Language.Diorite.Syntax
import Language.Diorite.Decoration
import Language.Diorite.Interpretation (Render(..))
import Language.Diorite.Traversal (Args(..), Result(..), constMatch)

import Data.Maybe (fromJust)
import Data.Constraint (Constraint, Dict(..), withDict)
import Data.Proxy (Proxy(..))
import Data.Type.Equality ((:~:)(..), TestEquality(..))
import Data.Typeable (Typeable, eqT)
import qualified Data.List as L (partition)

import Control.Monad.State (State)
import qualified Control.Monad.State as S (get, put, evalState)

import Prelude hiding (lookup)
import qualified Prelude as P (lookup)

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

-- | Local region-bindings.
data Local sig where
    Local :: Typeable a => Place -> Local ('Const a ':-> 'Const a)

instance Render Local where
    renderSym (Local p) = "local " ++ show p

instance Sym Local where
    symbol (Local _) = signature

local :: (Typeable a, Local :<: sym) => Place -> ASTF sym a -> ASTF sym a
local = smartSym . Local

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

-- | Erasure of any "Put" predicates of a symbol's signature.
type family Erasure a where
    Erasure ('Const a)    = 'Const a
    Erasure (a ':-> b)    = Erasure a ':-> Erasure b
    Erasure ('Put ':=> a) = Erasure a

-- | Witness of equality under "Erasure" of second signature.
newtype sig :~~: sig' = Erased (sig :~: Erasure sig')

infixr :~~:

-- | Extract a witness of equality of a type and its erasure.
eqET :: SigRep sig -> SigRep rsig -> Maybe (sig :~~: rsig)
eqET (SigConst :: SigRep a) (SigConst :: SigRep b) = do
    (Refl :: a :~: b) <- eqT
    return (Erased Refl)
eqET (SigPart a b) (SigPart c d) = do
    (Erased Refl) <- eqET a c
    (Erased Refl) <- eqET b d
    return (Erased Refl)
eqET sig (SigPred a) = do
    (Erased Refl) <- eqET sig a
    return (Erased Refl)
eqET _ _ = Nothing

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

class (TestEquality rep, Typeable a) => Representable rep (a :: *) where
    represent :: rep a

data TypeRep (rep :: * -> *) (sig :: Signature *) where
    TypeConst :: Representable rep a => rep a -> TypeRep rep ('Const a)
    TypePart  :: TypeRep rep a -> TypeRep rep sig -> TypeRep rep (a ':-> sig)
    TypePred  :: Region -> TypeRep rep sig -> TypeRep rep ('Put ':=> sig)
  -- todo: Annotate lambdas with regions.

instance Sym (TypeRep r) where
    symbol (TypeConst _)  = SigConst
    symbol (TypePart a b) = SigPart (symbol a) (symbol b)
    symbol (TypePred _ a) = SigPred (symbol a)

witType :: TypeRep r sig -> Dict (Sig sig)
witType = witSig . symbol

--------------------------------------------------------------------------------
-- * Region inference.
--------------------------------------------------------------------------------

-- | ...
class Infer sub sup where
    type Prim sup :: * -> *
    -- | ...
    inferSym :: forall sig a . (a ~ Result sig)
        => Store (Prim sup)
        -> sub sig
        -> Args (Eta sub) sig
        -> M (Sub, Context, Prim sup a, ASTF sup a)

infer :: forall sub sup a
    .  ( Infer sub sup
       , Local :<: sup
       , Free (Prim sup)
       , Substitute (Prim sup)
       , Fresh (Prim sup)
       , Typeable a
       )
    => ASTF sub a -> ASTF sup a
infer = err . runM . inferM []
  where
    err :: (Sub, Context, Prim sup a, ASTF sup a) -> ASTF sup a
    err (_, _, _, b) = b
  -- todo: Do not throw away the type.

inferM :: forall sub sup a
    .  ( Infer sub sup
       , Local :<: sup
       , Free (Prim sup)
       , Substitute (Prim sup)
       , Fresh (Prim sup)
       , Typeable a
       )
    => Store (Prim sup)
    -> ASTF sub a
    -> M (Sub, Context, Prim sup a, ASTF sup a)
inferM env = constMatch annotate instantiate
  where
    annotate :: forall sig . a ~ Result sig
        => sub sig -> Args (Eta sub) sig
        -> M (Sub, Context, Prim sup a, Beta sup ('Const a))
    annotate sym as = do
        (s, c, t, b) <- inferSym env sym as
        let (pi, q) = freeL c env t
        return (s, q, t, foldr local b (map fst pi))

    instantiate :: forall sig . (a ~ Result sig, Sig sig)
        => Name -> Args (Eta sub) sig
        -> M (Sub, Context, Prim sup a, Beta sup ('Const a))
    instantiate name as = fromJust $ do
        (Ex t)        <- P.lookup name env
        (Erased Refl) <- eqET (signature :: SigRep sig) (symbol t)
        return $ withDict (witType t) $
            reduceBeta env (Var name) t as

--------------------------------------------------------------------------------

reduceBeta :: forall sub sup s r a
  .  ( a ~ Result s
     , s ~ Erasure r
     , Infer sub sup
     , Local :<: sup
     , Free (Prim sup)
     , Fresh (Prim sup)
     , Substitute (Prim sup)
     )
  => Store (Prim sup) -> Beta sup r -> TypeRep (Prim sup) r
  -> Args (Eta sub) s
  -> M (Sub, Context, Prim sup a, Beta sup ('Const a))
reduceBeta env beta (TypeConst t) (Nil) = do
  t' <- fresh t
  return ([], [], t', beta)
reduceBeta env beta (TypePart a b) (eta :* as) = do
  (s1, c1, _,  e) <- reduceEta env eta a
  (s2, c2, t2, b) <- reduceBeta (subS s1 env) (beta :$ e) b as
  return (s2 @@ s1, c2 ++ subC s2 c1, t2, b)
reduceBeta env beta (TypePred _ a) as = do
  r <- newName
  p <- newName
  (s, c, t, b) <- reduceBeta env (beta :# p) a as
  return (s, (p, r) : c, t, b)

reduceEta :: forall sub sup s r a
  .  ( a ~ Result s
     , s ~ Erasure r
     , Infer sub sup
     , Local :<: sup
     , Free (Prim sup)
     , Fresh (Prim sup)
     , Substitute (Prim sup)
     )
  => Store (Prim sup) -> Eta sub s -> TypeRep (Prim sup) r
  -> M (Sub, Context, TypeRep (Prim sup) r, Eta sup r)
reduceEta env (Spine beta) (TypeConst _) = do
  (s, c, p, b) <- inferM env beta
  return (s, c, TypeConst p, Spine b)
reduceEta env (v :\ eta) (TypePart a b) = do
  (s, c, t, e) <- reduceEta (store v a env) eta b
  withDict (witType a) $
    return (s, c, TypePart (sub s a) t, v :\ e)
reduceEta env eta (TypePred _ a) = do
  r <- newName
  p <- newName
  (s, c, t, e) <- reduceEta env eta a
  return (s, (p, r) : c, TypePred r t, p :\\ e)
  -- todo: 'sig ~ Erasure rsig' means that we cannot have ':~' in the args.
  -- todo: Could interleave with reg. inference for tighter binds.

--------------------------------------------------------------------------------
-- ** ...
--------------------------------------------------------------------------------

type Store r = [(Name, Ex (TypeRep r))] -- Variable store.
type Context = [(Place, Region)]        -- Region store.
type Sub     = [(Region,Region)]        -- Substitutions.
type M a     = State Name a             -- Name supply.

runM :: M a -> a
runM = flip S.evalState 0

newName :: M Name
newName = do n <- S.get; S.put (n+1); return n

newNames :: (Enum a, Num a) => a -> M [Name]
newNames n = mapM (const newName) [1..n]

store :: Name -> TypeRep r a -> Store r -> Store r
store name c = (:) (name, Ex c)

class Free f where
    free :: f a -> [Region]

instance Free r => Free (TypeRep r) where
    free (TypeConst p)  = free p
    free (TypePart a b) = free a ++ free b
    free (TypePred r a) = r : free a

freeS :: Free r => Store r -> [Region]
freeS = concatMap (liftE free . snd)

freeL :: Free r => Context -> Store r -> r a -> (Context, Context)
freeL ctxt s p = let rs = freeS s ++ free p in
    L.partition (not . flip elem rs . snd) ctxt

class Substitute f where
    sub :: Sub -> f a -> f a

instance Substitute r => Substitute (TypeRep r) where
    sub s (TypeConst p)  = TypeConst (sub s p)
    sub s (TypePart a b) = TypePart  (sub s a)  (sub s b)
    sub s (TypePred r a) = TypePred  (subR s r) (sub s a)

subR :: Sub -> Region -> Region
subR s r | Just r' <- P.lookup r s = r'
         | otherwise = r

subS :: Substitute r => Sub -> Store r -> Store r
subS s = map (fmap (liftE (Ex . sub s)))

subC :: Sub -> Context -> Context
subC s = map (fmap (subR s))

(@@) :: Sub -> Sub -> Sub
(@@) new old = [(u, subR new t) | (u, t) <- old] ++ new

class Fresh f where
    fresh :: f a -> M (f a)

class Unify f where
    unify :: f a -> f a -> Sub

instance Unify r => Unify (TypeRep r) where
    unify (TypeConst p)  (TypeConst q)  = unify  p q
    unify (TypePart a b) (TypePart c d) = unify  a c ++ unify b d
    unify (TypePred i a) (TypePred j b) = unifyR i j ++ unify a b

unifyR :: Region -> Region -> Sub
unifyR p q | p == q    = []
           | otherwise = [(p, q)]
           
--------------------------------------------------------------------------------
-- Fin.
