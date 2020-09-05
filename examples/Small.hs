-- {-# OPTIONS_GHC -Wall #-}

module Small where

import Language.Diorite
import Language.Diorite.Region

import Data.List (partition)
--import Data.Dynamic (Dynamic, toDyn, fromDynamic)
import Data.Proxy (Proxy(..))
import Data.Typeable (Typeable, eqT)
import Data.Type.Equality ((:~:)(..))
import Data.Constraint (Dict(..))

--import Control.Monad.Reader (ReaderT)
import Control.Monad.State (State)
--import qualified Control.Monad.Reader as R (ask, local, runReaderT)
import qualified Control.Monad.State as S (get, put, evalState)

--------------------------------------------------------------------------------
-- * Example.
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

--------------------------------------------------------------------------------

-- | Target language.
data TExp a where
    TInt :: Int -> TExp ('Put ':=> 'Const Int)
    TAdd :: TExp ('Put ':=> 'Const Int ':-> 'Const Int ':-> 'Const Int)
    TLet :: TExp ('Put ':=> ('Put ':=> 'Const Int) ':-> ('Const Int ':-> 'Const Int) ':-> 'Const Int)
  -- todo: Second 'a' should maybe be wrapped in a 'Put' as well.
    TLoc :: Typeable a => Place -> TExp ('Const a ':-> 'Const a)

instance Render TExp where
    renderSym (TInt i) = renderSym (SInt i)
    renderSym (TAdd)   = renderSym (SAdd)
    renderSym (TLet)   = renderSym (SLet)
    renderSym (TLoc p) = "letr " ++ show p ++ " in"

instance Sym TExp where
    symbol (TInt _) = signature
    symbol (TAdd)   = signature
    symbol (TLet)   = signature
    symbol (TLoc _) = signature

--------------------------------------------------------------------------------
-- Infer.
--------------------------------------------------------------------------------

data Prim a where
    PInt :: Region -> Prim Int

primEq :: Prim a -> Prim b -> Maybe (a :~: b)
primEq (PInt _) (PInt _) = Just Refl

primTyp :: Prim a -> Dict (Typeable a)
primTyp (PInt _) = Dict

primTEq :: Typeable a => Proxy a -> Prim b -> Maybe (a :~: b)
primTEq _ p | Dict <- primTyp p = eqT

data TypeRep (sig :: Signature *) where
    TypeConst :: Prim a -> TypeRep ('Const a)
    TypePart  :: Region -> TypeRep a -> TypeRep sig -> TypeRep (a ':-> sig)
    TypePred  :: Region -> TypeRep sig -> TypeRep ('Put ':=> sig)

instance Sym TypeRep where
    symbol (TypeConst p) | Dict <- primTyp p = SigConst
    symbol (TypePart _ a b) = SigPart (symbol a) (symbol b)
    symbol (TypePred _ a) = SigPred (symbol a)

result :: a ~ Result sig => TypeRep sig -> Prim a
result (TypeConst p) = p
result (TypePart _ _ a) = result a
result (TypePred _ a) = result a

--------------------------------------------------------------------------------

-- instantiate/apply.
reduceBeta :: forall sig rsig a . (a ~ Result sig, sig ~ Erasure rsig)
    => Env -> Beta TExp rsig -> TypeRep rsig -> Args (Eta SExp) sig
    -> M (Sub, Context, Prim a, Beta TExp ('Const a))
reduceBeta env beta (TypeConst p) (Nil) =
    return ([], [], p, beta)
reduceBeta env beta (TypePart r a sig) (eta :* as) = do
    (s, c, eta') <- reduceEta env eta a
    (s', c', t, beta') <- reduceBeta (sub s env) (beta :$ eta') sig as
    return (s' @@ s, c' ++ sub s' c, t, beta')
reduceBeta env beta (TypePred r sig) as = do
    p <- newName
    (s, c, t, beta') <- reduceBeta env (beta :# p) sig as
    return (s, (p, r) : c, t, beta')
  -- todo: 'sig ~ Erasure rsig' means that we cannot have ':~' in the args.

-- instantiate/abstract.
reduceEta :: forall sig rsig a . (sig ~ Erasure rsig)
    => Env -> Eta SExp sig -> TypeRep rsig
    -> M (Sub, Context, Eta TExp rsig)
reduceEta env (Spine beta) (TypeConst p) | Dict <- primTyp p = do
    (s, c, _, beta') <- inferM env beta
    return (s, c, Spine beta')
reduceEta env (v :\ eta) (TypePart r a sig) | Dict <- witSig sig = do
    (s, c, eta') <- reduceEta env eta sig
    return (s, c, v :\ eta')
reduceEta env eta (TypePred r sig) = do
    p <- newName
    (s, c, eta') <- reduceEta env eta sig
    return (s, (p, r) : c, p :\\ eta')
  -- todo: same "erasure" issue as 'reduceBeta'.

--------------------------------------------------------------------------------

inferVar :: forall sig a . (a ~ Result sig, Sig sig)
    => Env -> Name -> Args (Eta SExp) sig
    -> M (Sub, Context, Prim a, Beta TExp ('Const a))
inferVar env name as = case lookup name env of
    Nothing -> error "E1"
    Just (Ex t) -> case witErased t (signature :: SigRep sig) of
        Nothing -> error "E2"
        Just (Erased Refl) | Dict <- witSig t ->
            reduceBeta env (Var name) t as

witErased :: forall sig rsig
    .  TypeRep rsig -> SigRep sig -> Maybe (sig :~~: rsig)
witErased (TypeConst p) sig@(SigConst)
    | Just Refl <- primTEq (proxyConst sig) p
    = Just (Erased Refl)
  where proxyConst :: c ('Const a) -> Proxy a
        proxyConst _ = Proxy
witErased (TypePart _ a b) (SigPart c d)
    | Just (Erased Refl) <- witErased a c
    , Just (Erased Refl) <- witErased b d
    = Just (Erased Refl)
witErased (TypePred _ a) sig
    | Just (Erased Refl) <- witErased a sig
    = Just (Erased Refl)
witErased _ _ = Nothing

witSig :: forall sig . TypeRep sig -> Dict (Sig sig)
witSig (TypeConst p) | Dict <- primTyp p = Dict
witSig (TypePart _ a b) | Dict <- witSig a, Dict <- witSig b = Dict
witSig (TypePred _ a) | Dict <- witSig a = Dict

--------------------------------------------------------------------------------

-- | ...
inferSym :: forall sig a . (a ~ Result sig)
    => Env -> SExp sig -> Args (Eta SExp) sig
    -> M (Sub, Context, Prim a, Beta TExp ('Const a))
inferSym env (SInt i) (Nil) = do
    p <- newName
    r <- newName
    return $ ( []
             , [(p, r)]
             , PInt r
             , Sym (TInt i) :# p)
inferSym env (SAdd) (Spine a :* Spine b :* Nil) = do
    (sa, ca, ta, a') <- inferM env a
    (sb, cb, tb, b') <- inferM (sub sa env) b
    p <- newName
    r <- newName
    return $ ( sb @@ sa
             , (p, r) : sub sb ca ++ cb
             , PInt r
             , Sym TAdd :# p :$ Spine a' :$ Spine b')
inferSym env (SLet) (Spine a :* (v :\ Spine f) :* Nil) = do
    (sa, ca, _, a') <- inferM env a
    (sf, cf, t, f') <- inferM env f
    p <- newName
    r <- newName
    return $ ( []
             , []
             , t
             , Sym TLet :# p :$ (undefined :\\ Spine a') :$ undefined)

--------------------------------------------------------------------------------

inferRgn :: forall sig a . (a ~ Result sig)
    => Env -> SExp sig -> Args (Eta SExp) sig
    -> M (Sub, Context, Prim a, Beta TExp ('Const a))
inferRgn env sym as = do
    (s,c,t,e') <- inferSym env sym as
    let (pi,q) = partitionFree c env t
    case primTyp t of
      Dict -> return (s, q, t, foldr extend e' (map fst pi))
  where
    extend :: Typeable a => Place -> Beta TExp ('Const a) -> Beta TExp ('Const a)
    extend p s = Sym (TLoc p) :$ (Spine s)

--------------------------------------------------------------------------------

-- | ...
inferM :: forall a . Env -> Beta SExp ('Const a)
    -> M (Sub, Context, Prim a, Beta TExp ('Const a))
inferM env = constMatch (inferRgn env) (inferVar env)

infer :: Beta SExp ('Const a) -> Beta TExp ('Const a)
infer e = let (_,_,_,b) = runM (inferM [] e) in b
  -- todo: Don't discard P.

--------------------------------------------------------------------------------
-- Small examples.
--------------------------------------------------------------------------------

var :: Sig a => Name -> Beta SExp a
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

type Env = [(Name, Ex TypeRep)]

localSym :: Name -> TypeRep sig -> Env -> Env
localSym n t env = (n, Ex t) : env

findSym :: forall sig . Name -> Args (Eta SExp) sig -> Env -> TypeRep sig
findSym v as env = case lookup v env of
    Nothing -> error ("Variable " ++ show v ++ " not found")
    Just (Ex d) -> undefined

--------------------------------------------------------------------------------

type Context = [(Place,Region)]

class Free a where
    free :: a -> [Region]

instance Free (Prim a) where
    free (PInt r) = [r]

instance Free Env where
    free = concatMap (free . snd)

instance Free (Ex TypeRep) where
    free (Ex e) = free e

instance Free (TypeRep sig) where
    free _ = []
  -- todo: bound regions.

partitionFree :: Context -> Env -> Prim a -> (Context, Context)
partitionFree ctxt env p =
  let rs = free p ++ free env
   in partition (not . flip elem rs . snd) ctxt

--------------------------------------------------------------------------------

type Sub = [(Region,Region)]

class Substitute a where
    sub :: Sub -> a -> a

instance Substitute Region where
    sub s r = case lookup r s of
        Nothing -> r
        Just r' -> r'

instance Substitute (Prim a) where
    sub s (PInt r) = PInt (sub s r)

instance Substitute (TypeRep a) where
    sub s (TypeConst p)    = TypeConst (sub s p)
    sub s (TypePart r a b) = TypePart (sub s r) (sub s a) (sub s b)
    sub s (TypePred r a)   = TypePred (sub s r) (sub s a)

instance Substitute Env where
    sub s = map (fmap (sub s))

instance Substitute (Ex TypeRep) where
    sub s (Ex t) = Ex (sub s t)

instance Substitute Context where
    sub s = map (fmap (sub s))

(@@) :: Sub -> Sub -> Sub
(@@) new old = [(u, sub new t) | (u, t) <- old] ++ new

--------------------------------------------------------------------------------
-- Fin.
