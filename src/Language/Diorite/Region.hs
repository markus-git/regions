{-# OPTIONS_GHC -Wall #-}

module Language.Diorite.Region
    ( Erasure, (:~~:)(..)
    --
--    , infer
    ) where

import Language.Diorite.Syntax --(Put(..), Signature(..), Place, Beta(..), Eta(..), SigRep(..), Sym(..), Render(..))
--import Language.Diorite.Traversal

import Data.Type.Equality ((:~:)(..))

--import Data.IntMap (IntMap)
--import qualified Data.IntMap as Map (insert, lookup, union, map, empty, fromList)

--import Control.Monad.Reader (ReaderT)
--import qualified Control.Monad.Reader as R (ask, runReaderT)
--import Control.Monad.State (State)
--import qualified Control.Monad.State as S (get, put, evalState)

--------------------------------------------------------------------------------
-- * Region inference.
--------------------------------------------------------------------------------

-- | Local region-bindings.
data Local sig where
    Local :: Place -> Local sig

instance Render Local where
    renderSym (Local p) = "local " ++ show p

--------------------------------------------------------------------------------

-- | Erasure of any \"Put\" predicates of a symbol's signature.
type family Erasure a where
    Erasure ('Const a)    = 'Const a
    Erasure (a ':-> b)    = Erasure a ':-> Erasure b
    Erasure ('Put ':=> a) = Erasure a

-- | Witness of equality under \"Erasure\" of second signature.
newtype sig :~~: sig' = Erased (sig :~: Erasure sig')

infixr :~~:

--------------------------------------------------------------------------------
{-
-- | ...
infer :: forall sym sym' a
    .  (forall sig . sym sig -> Int)
        -- ^ ...
    -> Beta sym ('Const a)
        -- ^ ...
    -> Beta sym' ('Const a)
infer f = match inferSym undefined
  where
    inferSym :: forall sig . (a ~ Result sig)
        => sym sig -> Args sym sig -> Beta sym' ('Const a)
    inferSym _ _ = undefined

    inferBeta :: (a ~ Result sig, sig ~ Erasure sig')
        => Beta sym' sig' -> Args sym sig -> SigRep sig' -> Beta sym' ('Const a)
    inferBeta b (Nil)     (SigConst)        = b
    inferBeta b (a :* as) (SigPart arg sig) = inferBeta (b :$ inferEta a arg) as sig
    inferBeta b as        (SigPred sig)     = inferBeta (b :# 0) as sig -- region.

    inferEta :: (sig ~ Erasure sig')
        => Eta sym sig -> SigRep sig' -> Eta sym' sig'
    inferEta (Spine b) (SigConst)      = Spine (infer f b)
    inferEta (v :\ e)  (SigPart _ sig) = v :\ inferEta e sig
    inferEta e         (SigPred sig)   = 0 :\\ inferEta e sig -- region.
-}

{-
    inferSym sym as = case (label sym :: (sig :~~: sig', sym' sig')) of
        (Erased Refl, sym') -> inferBeta (Sym sym') as (symbol sym')
-}
--------------------------------------------------------------------------------
-- ** Inference monad.
{-
-- | Assignment, ...
data A sym where A :: sig :~~: sig' -> SigRep sig -> sym sig' -> A sym

-- | Variable assignments.
type VA sym = IntMap (A sym)

-- | Predicate context.
--type P = [(Place,Region)]

-- | Region substitutions.
--type S = IntMap Region

-- | Name supply monad.
type M sym a = ReaderT (VA sym) (State Name) a

runM :: VA sym -> M sym a -> a
runM env = flip S.evalState 0 . flip R.runReaderT env

newName :: M sym Name
newName = do n <- S.get; S.put (n+1); return n

newNames :: (Enum a, Num a) => a -> M sym [Name]
newNames n = mapM (const newName) [1..n]
-}
--------------------------------------------------------------------------------
-- *** Subst.
{-
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
-}
--------------------------------------------------------------------------------
-- Old stuff
{-
-- | Labelling of primitive types.
class (Eq a, Show a, Typeable a) => Prim a

-- | Extract a witness of equality of two signatures' types, ignoring any regions.
eqSigT :: forall sig sig' . SigRep sig -> SigRep sig' -> Maybe (sig :~: sig')
eqSigT (SigConst) (SigConst)
    | Just Refl <- eqT :: Maybe (sig :~: sig') = Just Refl
eqSigT (SigPart _ a sig) (SigPart _ a' sig')
    | Just Refl <- eqSigT a a', Just Refl <- eqSigT sig sig' = Just Refl
eqSigT (SigPred _ sig) (SigPred _ sig')
    | Just Refl <- eqSigT sig sig' = Just Refl
eqSigT _ _ = Nothing

symbolBeta :: Sym sym => Beta sym sig -> SigRep sig
symbolBeta (Var v)  = undefined
symbolBeta (Sym s)  = symbol s
symbolBeta (b :$ _) = case (symbolBeta b) of (SigPart _ _ sig) -> sig
symbolBeta (b :# _) = case (symbolBeta b) of (SigPred _ sig) -> sig

-- | Get the highest place bound for \"Eta\" node.
maxPlaceEta :: Eta sym a -> Place
maxPlaceEta (_ :\ e)  = maxPlaceEta e
maxPlaceEta (p :\\ _) = p
maxPlaceEta (Spine b) = maxPlaceBeta b

-- | Get the highest place bound for \"Beta\" node.
maxPlaceBeta :: Beta sym a -> Place
maxPlaceBeta (b :$ e) = maxPlaceBeta b `Prelude.max` maxPlaceEta e
maxPlaceBeta (b :# _) = maxPlaceBeta b
maxPlaceBeta _        = 0

withSym :: forall sym sym' sig c . Annotate sym sym'
    => sym sig
    -> (forall sig' . sig ~ Erasure sig' => sym' sig' -> c)
    -> M sym' c
withSym sym f = case (annotate sym :: (sig :~~: ann, sym' ann)) of
    (Erased Refl, rgn) -> return (f rgn)

withVar :: forall sym sig c
    .  Name -> SigRep sig
    -> (forall sig' . sig ~ Erasure sig' => sym sig' -> c)
    -> M sym c
withVar v sig f = do
    va <- R.ask
    case Map.lookup v va of
        Nothing -> error ("Unknown variable " ++ show v)
        Just (A (Erased Refl) sig' sym) -> case eqSigT sig sig' of
            Nothing -> error ("Signature mismatch " ++ undefined)
            Just Refl -> return (f sym)
-}
--------------------------------------------------------------------------------
-- Fin.
