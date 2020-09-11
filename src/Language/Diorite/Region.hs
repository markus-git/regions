{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE ConstraintKinds #-}

module Language.Diorite.Region
    (
    -- * Valid primitive types.
      Primitive(..)
    , Erasure(..)
    , (:~~:)(..)
    -- * ...
    , Local(..)
    ) where

import Language.Diorite.Syntax
import Language.Diorite.Interpretation (Render(..))
import Language.Diorite.Traversal (Args(..), Result(..), constMatch)

import qualified Data.List as L (partition)
import Data.Constraint (Dict(..))
import Data.Proxy (Proxy(..))
import Data.Type.Equality ((:~:)(..), TestEquality)
import Data.Typeable (Typeable, eqT)

import Control.Monad.State (State)
import qualified Control.Monad.State as S (get, put, evalState)

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
eqET (SigConst :: SigRep a) (SigConst :: SigRep b)
    | Just (Refl :: a :~: b) <- eqT
    = Just (Erased Refl)
eqET (SigPart a b) (SigPart c d)
    | Just (Erased Refl) <- eqET a c
    , Just (Erased Refl) <- eqET b d
    = Just (Erased Refl)
eqET sig (SigPred a)
    | Just (Erased Refl) <- eqET sig a
    = Just (Erased Refl)
eqET _ _ = Nothing

--------------------------------------------------------------------------------

-- | ...
class Primitive a where
    type Prim a :: *
    reify :: a -> Prim a

-- | ...
data TypeRep (r :: * -> *) (sig :: Signature *) where
    TypeConst :: Typeable a => r a -> TypeRep r ('Const a)
    TypePart  :: Region -> TypeRep r a -> TypeRep r sig -> TypeRep r (a ':-> sig)
    TypePred  :: Region -> TypeRep r sig -> TypeRep r ('Put ':=> sig)

instance Sym (TypeRep r) where
    symbol (TypeConst _)    = SigConst
    symbol (TypePart _ a b) = SigPart (symbol a) (symbol b)
    symbol (TypePred _ a)   = SigPred (symbol a)

witSigT :: TypeRep r a -> Dict (Sig a)
witSigT = witSig . symbol

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
-- * Region inference.
--------------------------------------------------------------------------------

-- | ... instantiate/apply.
reduceBeta :: forall sup sub sig rsig r a
    .  ( a ~ Result sig
       , sig ~ Erasure rsig
       , Substitute r)
    => Store r
    -> Beta sup rsig
    -> TypeRep r rsig
    -> Args (Eta sub) sig
    -> M (Sub, Context, r a, Beta sup ('Const a))
reduceBeta env beta (TypeConst t) (Nil) = do
    return ([], [], t, beta)
reduceBeta env beta (TypePart r a b) (eta :* as) = do
    (s,  c,     eta')  <- reduceEta env eta a
    (s', c', t, beta') <- reduceBeta (subS s env) (beta :$ eta') b as
    return (s' @@ s, c' ++ subC s' c, t, beta')
reduceBeta env beta (TypePred r a) as = do
    p <- newName
    (s, c, t, beta') <- reduceBeta env (beta :# p) a as
    return (s, (p, r) : c, t, beta')

-- | ... recurse/abstract.
reduceEta :: forall sup sub sig rsig r a
    .  (sig ~ Erasure rsig)
    => Store r
    -> Eta sub sig
    -> TypeRep r rsig
    -> M (Sub, Context, Eta sup rsig)
reduceEta env (Spine beta) (TypeConst t) = do
    undefined
reduceEta env (v :\ eta) (TypePart r a b) | Dict <- witSigT a = do
    (s, c, eta') <- reduceEta env eta b
    return (s, c, v :\ eta')
reduceEta env eta (TypePred r a) = do
    p <- newName
    (s, c, eta') <- reduceEta env eta a
    return (s, (p, r) : c, p :\\ eta')
  -- todo: Allocate regions for functions in 'TypePart' case.
  -- todo: The 'sig ~ Erasure rsig' means that we cannot have ':~' in the args.

-- | ...
inferVar :: forall sup sub sig r a
    .  (a ~ Result sig, Sig sig, Substitute r)
    => Store r
    -> Name
    -> Args (Eta sub) sig
    -> M (Sub, Context, r a, Beta sup ('Const a))
inferVar env name as = case lookup name env of
    Nothing -> error ("Variable " ++ show name ++ " not found.")
    Just (Ex t) -> case eqET (signature :: SigRep sig) (symbol t) of
      Nothing -> error ("Variable " ++ show name ++ " type mismatch.")
      Just (Erased Refl) -> case witSigT t of
        Dict -> reduceBeta env (Var name) t as

--------------------------------------------------------------------------------

-- | ...
class Infer sup sub r where
    inferSym :: forall sig a
        .  (a ~ Result sig, Local :<: sup)
        => Store r
        -> sub sig
        -> Args (Eta sub) sig
        -> M (Sub, Context, r a, ASTF sup a)

-- | ...
inferRgn :: forall sup sub sig r a
    .  ( a ~ Result sig
       , Infer sup sub r
       , Local :<: sup
       , Free r
       , Typeable a
       )
    => Store r
    -> sub sig
    -> Args (Eta sub) sig
    -> M (Sub, Context, r a, Beta sup ('Const a))
inferRgn env sym as = do
    (s,c,t,e') <- inferSym env sym as
    let (pi,q) = freeL c env t
    return (s, q, t, foldr local e' (map fst pi))

--------------------------------------------------------------------------------

inferM :: forall sup sub r a
    .  ( Infer sup sub r
       , Local :<: sup
       , Substitute r
       , Free r
       , Typeable a
       )
    => Store r
    -> ASTF sub a
    -> M (Sub, Context, r a, ASTF sup a)
inferM env = constMatch (inferRgn env) (inferVar env)

--------------------------------------------------------------------------------

infer :: forall sup sub r a
    .  ( Infer sub sub r
       , Local :<: sup
       , Substitute r
       , Free r
       , Typeable a
       )
    => ASTF sub a -> ASTF sup a
infer = undefined

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
    free (TypeConst p)    = free p
    free (TypePart r a b) = r : free a ++ free b
    free (TypePred r a)   = r : free a

freeS :: Free r => Store r -> [Region]
freeS = concatMap (liftE free . snd)

freeL :: Free r => Context -> Store r -> r a -> (Context, Context)
freeL ctxt s p = let rs = freeS s ++ free p in
    L.partition (not . flip elem rs . snd) ctxt

class Substitute f where
    sub :: Sub -> f a -> f a

instance Substitute r => Substitute (TypeRep r) where
    sub s (TypeConst p)    = TypeConst (sub s p)
    sub s (TypePart r a b) = TypePart (subR s r) (sub s a) (sub s b)
    sub s (TypePred r a)   = TypePred (subR s r) (sub s a)

subR :: Sub -> Region -> Region
subR s r | Just r' <- lookup r s = r'
         | otherwise = r

subS :: Substitute r => Sub -> Store r -> Store r
subS s = map (fmap (liftE (Ex . sub s)))

subC :: Sub -> Context -> Context
subC s = map (fmap (subR s))

(@@) :: Sub -> Sub -> Sub
(@@) new old = [(u, subR new t) | (u, t) <- old] ++ new

--------------------------------------------------------------------------------
-- Fin.
