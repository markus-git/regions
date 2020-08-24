{-# OPTIONS_GHC -Wall #-}

module Small where

import Language.Diorite
import Language.Diorite.Traversal
--import Language.Diorite.Region

import Data.List (partition)
--import Data.Type.Equality ((:~:)(..))

--import Data.IntMap (IntMap)
--import qualified Data.IntMap as Map
--  (empty, insert, lookup, assocs, partition, union, map, fromList, ...)

import Control.Monad.State (State)
import qualified Control.Monad.State as S (get, put, evalState)

--------------------------------------------------------------------------------
-- * Example.
--------------------------------------------------------------------------------

-- | Source language.
data SExp a where
    SInt :: Int -> SExp ('Const Int)
    SAdd :: SExp ('Const Int ':-> 'Const Int ':-> 'Const Int)

instance Render SExp where
    renderSym (SInt i) = "i" ++ show i
    renderSym (SAdd)   = "(+)"

instance Sym SExp where
    symbol (SInt _) = signature
    symbol (SAdd)   = signature

--------------------------------------------------------------------------------

-- | Target language.
data TExp a where
    TInt :: Int -> TExp ('Put ':=> 'Const Int)
    TAdd :: TExp ('Put ':=> 'Const Int ':-> 'Const Int ':-> 'Const Int)
    -- 
    TLoc :: Place -> TExp ('Const a ':-> 'Const a)

instance Render TExp where
    renderSym (TInt i) = renderSym (SInt i)
    renderSym (TAdd)   = renderSym (SAdd)
    renderSym (TLoc p) = "letr " ++ show p ++ " in"

instance Sym TExp where
    symbol (TInt _) = signature
    symbol (TAdd)   = signature
    symbol (TLoc _) = signature

--------------------------------------------------------------------------------
-- Infer.
--------------------------------------------------------------------------------

data Label (sig :: Signature *) where
    LblConst :: Region -> Label ('Const a)
    LblPart  :: Label a -> Label sig -> Label (a ':-> sig) -- !
    LblPred  :: Label sig -> Label ('Put ':=> sig)         -- !

labels :: Label sig -> [Region]
labels (LblConst r)    = [r]
labels (LblPart a sig) = labels a ++ labels sig
labels (LblPred sig)   = labels sig

--------------------------------------------------------------------------------

inferM :: forall a
    .  Beta SExp ('Const a)
    -> M ( P
         , Label ('Const a)
         , Beta TExp ('Const a)
         )
inferM = constMatch inferRgn ()
  where
    inferSym :: forall sig . a ~ Result sig
        => SExp sig
        -> Args SExp sig
        -> M ( P
             , Label ('Const a)
             , Beta TExp ('Const a)
             )
    inferSym (SInt i) (Nil) = do
        p <- newName
        r <- newName
        return $ ([(p,r)], LblConst r, Sym (TInt i) :# p)
    inferSym (SAdd) (Spine a :* Spine b :* Nil) = do
        (pa, _, a') <- inferM a
        (pb, _, b') <- inferM b
        p <- newName
        r <- newName
        return $ ( (p,r) : pa ++ pb
                 , LblConst r
                 , Sym TAdd :# p :$ Spine a' :$ Spine b'
                 )

    inferRgn :: forall sig . a ~ Result sig
        => SExp sig
        -> Args SExp sig
        -> M ( P
             , Label ('Const a)
             , Beta TExp ('Const a)
             )
    inferRgn e as = do
        (p,t,e') <- inferSym e as
        let (f,b) = partR (not . flip elem (labels t)) p
        return $ ( b
                 , t
                 , foldr extend e' (places f)
                 )
      where
        extend :: Place -> Beta TExp ('Const a) -> Beta TExp ('Const a)
        extend p s = Sym (TLoc p) :$ (Spine s)

infer :: Beta SExp ('Const a) -> Beta TExp ('Const a)
infer e = let (_,_,b) = runM (inferM e) in b

--------------------------------------------------------------------------------
-- Small examples.
--------------------------------------------------------------------------------

var :: Name -> Beta SExp a
var a = Var a

one :: Beta SExp ('Const Int)
one = Sym (SInt 1)

add :: Eta SExp ('Const Int) -> Eta SExp ('Const Int) -> Beta SExp ('Const Int)
add a b = Sym SAdd :$ a :$ b  

--------------------------------------------------------------------------------

test_add :: Beta SExp ('Const Int)
test_add =
    (add (Spine one) (Spine (add (Spine one) (Spine one))))

test_lam :: Eta SExp ('Const Int ':-> 'Const Int)
test_lam =
    (1 :\ (Spine (add (Spine one) (Spine (var 1)))))

--------------------------------------------------------------------------------
-- Extra stuff needed for inference.
--------------------------------------------------------------------------------

type M a = State Name a

runM :: M a -> a
runM = flip S.evalState 0

newName :: M Name
newName = do n <- S.get; S.put (n+1); return n

newNames :: (Enum a, Num a) => a -> M [Name]
newNames n = mapM (const newName) [1..n]

--------------------------------------------------------------------------------

type P = [(Place,Region)]

places :: P -> [Place]
places = map fst

findR :: Place -> P -> Region
findR p m = case lookup p m of
    Nothing -> error $ show p ++ " has no assoc. region."
    Just r  -> r

partR :: (Region -> Bool) -> P -> (P, P)
partR f = partition (f . snd)

--------------------------------------------------------------------------------
-- Fin.
