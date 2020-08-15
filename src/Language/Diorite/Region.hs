module Language.Diorite.Region
    ( (:&:)(..), Erasure, (:~~:)(..), Annotate(..)
    --
    , infer
    ) where

import Language.Diorite.Syntax
    ( Put(..), Signature(..), Name, Place, Beta(..), Eta(..), SigRep(..)
    , Sym(..), Render(..), Region)
import Language.Diorite.Traversal (Result, Arg(..), Args(..), transMatch)

import Data.Type.Equality ((:~:)(..))

import Data.IntMap (IntMap)
import qualified Data.IntMap as Map (insert,lookup,union,map,empty,fromList)

import Control.Monad.State (State)
import qualified Control.Monad.State as S

--------------------------------------------------------------------------------
-- * Region inference.
--------------------------------------------------------------------------------

-- | Local region-bindings.
data Local sig where
    Local :: Place -> Local (a ':-> a)

instance Render Local where
    renderSym (Local p) = "local " ++ show p

--------------------------------------------------------------------------------

-- | Decorated symbol.
data (sym :&: info) sig where
    (:&:) :: { decor_sym  :: sym sig
             , decor_info :: info sig }
          -> (sym :&: info) sig

instance Render sym => Render (sym :&: info) where
    renderSym       = renderSym . decor_sym
    renderArgs args = renderArgs args . decor_sym

-- | Erasure of any \"Put\" predicates of a symbol's signature.
type family Erasure a where
    Erasure ('Const a)    = 'Const a
    Erasure (a ':-> b)    = Erasure a ':-> Erasure b
    Erasure ('Put ':=> a) = Erasure a

-- | Witness of equality under \"Erasure\" of second signature.
newtype sig :~~: sig' = Erased (sig :~: Erasure sig')
--    W :: sig ~ Erasure sig' => Wit sig sig'

infixr :~~:

-- | Annotate a symbol with regions, leaving original signature 'intact'.
class Annotate sym rgn where
    annotate :: sym sig -> (rgn :&: (:~~:) sig) ann

--------------------------------------------------------------------------------

-- | Get the highest place bound for \"Eta\" node.
maxPlaceEta :: Eta sym a -> Place
maxPlaceEta (Lam _ e)  = maxPlaceEta e
maxPlaceEta (ELam p _) = p
maxPlaceEta (Spine b)  = maxPlaceBeta b

-- | Get the highest place bound for \"Beta\" node.
maxPlaceBeta :: Beta sym a -> Place
maxPlaceBeta (b :$ e) = maxPlaceBeta b `Prelude.max` maxPlaceEta e
maxPlaceBeta (_ :# p) = p
maxPlaceBeta _        = 0
  -- todo: hmm..

-- | Predicate context.
type P = [(Place,Region)]

-- | Region substitutions.
type S = IntMap Region

-- | ...
data Ann sym where
    A :: sig :~~: sig' -> SigRep sig -> rgn sig' -> Ann sym

-- | Variable assignments.
type A sym = IntMap (Ann sym)

-- | ...
infer :: forall sym rgn a . (Sym rgn, Annotate sym rgn)
    => Beta sym ('Const a) -> M (Beta rgn ('Const a))
infer = transMatch inferSym inferVar
  where
    inferSym :: forall sig . (a ~ Result sig)
        => sym sig -> Args (Beta sym) sig
        -> M (Beta rgn ('Const a))
    inferSym sym as = case (annotate sym :: (rgn :&: (:~~:) sig) ann) of
        (rgn :&: Erased Refl) -> do
            sig <- return (symbol rgn) -- error!
            saturate sig as (Sym rgn)

    inferVar :: forall sig . (a ~ Result sig)
        => Name -> Args (Beta sym) sig
        -> M (Beta rgn ('Const a))
    inferVar = undefined
{-        
    inferVar var _ = case Map.lookup var undefined of
        Nothing -> error ("unknown variable " ++ show var)
        Just (A (Erased Refl) sig _) -> case eqST (undefined :: SigRep sig) sig of
          Nothing -> error ("type mismatch")
          Just Refl -> do
              ann <- symbol rgn
              saturate ann as (Sym rgn)
-}
    saturate :: forall sig ann . (a ~ Result sig, sig ~ Erasure ann)
        => SigRep ann -> Args (Beta sym) sig -> Beta rgn ann
        -> M (Beta rgn ('Const a))
    saturate (SigConst) (Nil) s = do
        return s
    saturate (SigPart _ arg sig) (a :* as) s = do
        a' <- qualify arg a
        saturate sig as (s :$ a')
    saturate (SigPred r sig) as s = do
        saturate sig as (s :# r) -- error!

    qualify :: forall sig ann . (sig ~ Erasure ann)
        => SigRep ann -> Arg (Beta sym) sig
        -> M (Eta rgn ann)
    qualify (SigConst) (ASym s) = do
        sym <- infer s
        return (Spine sym)
    qualify (SigPart _ _ sig) (AVar v arg) = do
        eta <- qualify sig arg
        return (Lam v eta)
    qualify (SigPred r sig) arg = do
        eta <- qualify sig arg
        return (ELam r eta) -- error!

--------------------------------------------------------------------------------
-- *** ...

-- | Name supply monad.
type M a = State Name a

runM :: M a -> a
runM = flip S.evalState 0

newName :: M Name
newName = do n <- S.get; S.put (n+1); return n

newNames :: (Enum a, Num a) => a -> M [Name]
newNames n = mapM (const newName) [1..n]

--------------------------------------------------------------------------------
-- *** ...

emptySub :: S
emptySub = Map.empty

newSub :: [(Place,Name)] -> S
newSub = Map.fromList

-- | ...
(+@) :: (Place,Name) -> S -> S
(+@) (p,r) s = Map.insert p r s

-- | Left-biased union of two substitutions.
(@@) :: S -> S -> S
(@@) a b = Map.union a (Map.map update b)
  where
    update :: Region -> Region
    update r = case Map.lookup r a of
      Nothing -> r
      Just r' -> r'

--------------------------------------------------------------------------------
-- Fin.
