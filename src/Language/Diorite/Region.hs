--{-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE ConstraintKinds #-}

module Language.Diorite.Region
    (
    -- * Valid primitive types.
      Erasure(..)
    , (:~~:)(..)
    -- * ...
    , Local(..)
    ) where

import Language.Diorite.Syntax
import Language.Diorite.Decoration
import Language.Diorite.Interpretation (Render(..))
import Language.Diorite.Traversal (Args(..), Result(..), constMatch)

import Data.Maybe (fromMaybe)
import Data.Constraint (Constraint, Dict(..), withDict)
import Data.Proxy (Proxy(..))
import Data.Type.Equality ((:~:)(..))
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

-- | ...
data TypeRep (r :: * -> *) (sig :: Signature *) where
    TypeConst :: Typeable a => r a -> TypeRep r ('Const a)
    TypePart  :: TypeRep r a -> TypeRep r sig -> TypeRep r (a ':-> sig)
    TypePred  :: Region -> TypeRep r sig -> TypeRep r ('Put ':=> sig)
  -- todo: Annotate lambdas with regions.

instance Sym (TypeRep r) where
    symbol (TypeConst _)  = SigConst
    symbol (TypePart a b) = SigPart (symbol a) (symbol b)
    symbol (TypePred _ a) = SigPred (symbol a)

witSigT :: TypeRep r a -> Dict (Sig a)
witSigT = witSig . symbol

--------------------------------------------------------------------------------
-- * Region inference.
--------------------------------------------------------------------------------

instantiate :: forall sup sub sig r a
    .  ( a ~ Result sig
       , Sig sig
       , Fresh (Prim sup)
       , Substitute (Prim sup)
       )
    => Store (Prim sup)
    -> Name
    -> Args (Eta sub) sig
    -> M (Sub, Context, Prim sup a, Beta sup ('Const a))
instantiate env name as = withType (\t -> undefined)
  where
    withType :: forall r
        .  (forall rig . sig ~ Erasure rig
                => TypeRep (Prim sup) rig -> M r
           )
        -> M r
    withType f = fromMaybe (error $ "Variable " ++ show name ++ " not found.") $
      do (Ex t)        <- P.lookup name env
         (Erased Refl) <- eqET (signature :: SigRep sig) (symbol t)
         withDict (witSigT t) (return $ fresh t >>= f)

    reduce :: forall s r . (a ~ Result s, s ~ Erasure r)
        => Store (Prim sup)
        -> Beta sup r
        -> TypeRep (Prim sup) r
        -> Args (Eta sub) s
        -> M (Sub, Context, Prim sup a, Beta sup ('Const a))
    reduce env beta (TypeConst p) (Nil) = do
        return ([], [], p, beta)
    reduce env beta (TypePart a b) (eta :* as) = do
        undefined

--------------------------------------------------------------------------------

reduceBeta :: forall sup sub sig rsig r a
    .  ( a   ~ Result sig
       , sig ~ Erasure rsig
       , Substitute (Prim sup)
       )
    => Store (Prim sup)
    -> Beta sup rsig
    -> TypeRep (Prim sup) rsig
    -> Args (Eta sub) sig
    -> M (Sub, Context, Prim sup a, Beta sup ('Const a))
reduceBeta env beta (TypeConst t) (Nil) = do
    return ([], [], t, beta)
reduceBeta env beta (TypePart a b) (eta :* as) = do
    (s,  c,     eta')  <- reduceEta env eta a
    (s', c', t, beta') <- reduceBeta (subS s env) (beta :$ eta') b as
    return (s' @@ s, c' ++ subC s' c, t, beta')
reduceBeta env beta (TypePred r a) as = do
    p <- newName
    (s, c, t, beta') <- reduceBeta env (beta :# p) a as
    return (s, (p, r) : c, t, beta')

reduceEta :: forall sup sub sig rsig a
    .  (sig ~ Erasure rsig)
    => Store (Prim sup)
    -> Eta sub sig
    -> TypeRep (Prim sup) rsig
    -> M (Sub, Context, Eta sup rsig)
reduceEta env (Spine beta) (TypeConst t) = do
    undefined
reduceEta env (v :\ eta) (TypePart a b) | Dict <- witSigT a = do
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
    .  ( a ~ Result sig
       , Sig sig
       , Substitute (Prim sup)
       )
    => Store (Prim sup)
    -> Name
    -> Args (Eta sub) sig
    -> M (Sub, Context, Prim sup a, Beta sup ('Const a))
inferVar env name as = case P.lookup name env of
    Nothing -> error ("Variable " ++ show name ++ " not found.")
    Just (Ex t) -> case eqET (signature :: SigRep sig) (symbol t) of
      Nothing -> error ("Variable " ++ show name ++ " type mismatch.")
      Just (Erased Refl) -> case witSigT t of
        Dict -> reduceBeta env (Var name) t as

--------------------------------------------------------------------------------

-- | ...
class Infer sub sup where
    type Prim sup :: * -> *
    -- | ...
    inferSym :: forall sig a
        .  ( a ~ Result sig
           , Local :<: sup
           , Free (Prim sup)
           , Substitute (Prim sup)
           )
        => Store (Prim sup)
        -> sub sig
        -> Args (Eta sub) sig
        -> M (Sub, Context, Prim sup a, ASTF sup a)

-- | ...
inferRgn :: forall sup sub sig a
    .  ( a ~ Result sig
       , Infer sub sup
       , Local :<: sup
       , Free (Prim sup)
       , Substitute (Prim sup)
       , Typeable a
       )
    => Store (Prim sup)
    -> sub sig
    -> Args (Eta sub) sig
    -> M (Sub, Context, Prim sup a, Beta sup ('Const a))
inferRgn env sym as = do
    (s,c,t,e') <- inferSym env sym as
    let (pi,q) = freeL c env t
    return (s, q, t, foldr local e' (map fst pi))

--------------------------------------------------------------------------------

inferM :: forall sup sub a
    .  ( Infer sub sup
       , Local :<: sup
       , Free (Prim sup)
       , Substitute (Prim sup)
       , Typeable a
       )
    => Store (Prim sup)
    -> ASTF sub a
    -> M (Sub, Context, Prim sup a, ASTF sup a)
inferM env = constMatch (inferRgn env) (inferVar env)

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

class Fresh f where
    fresh :: f a -> M (f a)

instance Fresh r => Fresh (TypeRep r) where
    fresh (TypeConst p)  = TypeConst <$> fresh p
    fresh (TypePart a b) = TypePart  <$> fresh a <*> fresh b
    fresh (TypePred _ a) = TypePred  <$> newName <*> fresh a

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

--------------------------------------------------------------------------------
-- Fin.
