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
    TLoc :: Place -> TExp ('Const a ':-> 'Const a)

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

eqPrim :: Prim a -> Prim b -> Maybe (a :~: b)
eqPrim (PInt _) (PInt _) = Just Refl

witType :: Prim a -> Dict (Typeable a)
witType (PInt _) = Dict

witProxy :: Typeable a => Proxy a -> Prim b -> Maybe (a :~: b)
witProxy _ p | Dict <- witType p = eqT

--------------------------------------------------------------------------------

data TypeRep a where
    TypeConst :: Prim a -> TypeRep ('Const a)
    TypePart  :: Region -> TypeRep a -> TypeRep sig -> TypeRep (a ':-> sig)
    TypePred  :: Region -> TypeRep sig -> TypeRep ('Put ':=> sig)

eqType :: TypeRep a -> TypeRep b -> Maybe (a :~: b)
eqType (TypeConst a)  (TypeConst b)
    | Just Refl <- eqPrim a b = Just Refl
eqType (TypePart _ a b) (TypePart _ c d)
    | Just Refl <- eqType a c, Just Refl <- eqType b d = Just Refl
eqType (TypePred _ a) (TypePred _ b)
    | Just Refl <- eqType a b = Just Refl
eqType _ _ = Nothing

--------------------------------------------------------------------------------

-- instantiate/apply.
reduceBeta :: forall sig rsig a . (a ~ Result sig, sig ~ Erasure rsig)
    => Env -> Beta TExp rsig -> TypeRep rsig -> Args (Eta SExp) sig
    -> M (Sub, Context, Beta TExp ('Const a))
reduceBeta env beta (TypeConst p) (Nil) =
    return ([], [], beta)
reduceBeta env beta (TypePart r a sig) (eta :* as) = do
    (s, c, eta') <- reduceEta env eta a
    (s', c', beta') <- reduceBeta env (beta :$ eta') sig as
    return ([], [], beta')
reduceBeta env beta (TypePred r sig) as = do
    p <- newName
    (s, c, beta') <- reduceBeta env (beta :# p) sig as
    return ([], [], beta')
  -- todo: 'sig ~ Erasure rsig' means that we cannot have ':~' in the args.

-- instantiate/abstract.
reduceEta :: forall sig rsig a . (sig ~ Erasure rsig)
    => Env -> Eta SExp sig -> TypeRep rsig
    -> M (Sub, Context, Eta TExp rsig)
reduceEta env (Spine beta) (TypeConst p) | Dict <- witType p = do
    (s, c, _, beta') <- inferM env beta
    return (s, c, Spine beta')
reduceEta env (v :\ eta) (TypePart r a sig) = do
    (s, c, eta') <- reduceEta env eta sig
    return (s, c, v :\ eta')
reduceEta env eta (TypePred r sig) = do
    p <- newName
    (s, c, eta') <- reduceEta env eta sig
    return (s, c, p :\\ eta')
  -- todo: same "erasure" issue as 'reduceBeta'.

--------------------------------------------------------------------------------

inferVar :: forall sig a . (a ~ Result sig)
  => Env -> Name -> Args (Eta SExp) sig
  -> M (Sub, Context, Prim a, Beta TExp ('Const a))
inferVar env name as = case lookup name env of
    Nothing     -> error "E1"
    Just (Ex t) -> case witness as t of
      Nothing            -> error "E2"
      Just (Erased Refl) -> do
        (s, c, beta') <- reduceBeta env (Var name) t as
        return (s, c, undefined, beta')

witness :: forall sig rsig c . Args c sig -> TypeRep rsig -> Maybe (sig :~~: rsig)
witness a@(Nil) (TypeConst p)
  | Just Refl <- witProxy (proxy a) p
  = Just (Erased Refl)
  where proxy :: Args c ('Const a) -> Proxy a
        proxy _ = Proxy
witness (c :* as) (TypePart r a sig)
  | Just (Erased Refl) <- witness2 c a
  , Just (Erased Refl) <- witness as sig
  = undefined
witness as (TypePred r sig)
  | Just (Erased Refl) <- witness as sig
  = Just (Erased Refl)
witness _ _ = Nothing

witness2 :: c sig -> TypeRep rsig -> Maybe (sig :~~: rsig)
witness2 = undefined

--------------------------------------------------------------------------------

-- | ...
inferSym :: forall sig a . (a ~ Result sig)
    => Env -> SExp sig -> Args (Eta SExp) sig
    -> M (Sub, Context, Prim a, Beta TExp ('Const a))
inferSym env (SInt i) (Nil) = do
    p <- newName
    r <- newName
    return $ ([], [], PInt r,
        Sym (TInt i) :# p)
inferSym env (SAdd) (Spine a :* Spine b :* Nil) = do
    (sa, _, _, a') <- inferM env a
    (sb, _, _, b') <- inferM env b
    p <- newName
    r <- newName
    return $ ([], [], PInt r,
        Sym TAdd :# p :$ Spine a' :$ Spine b')
inferSym env (SLet) (Spine a :* (v :\ Spine f) :* Nil) = do
    (_, _, _, a') <- inferM env a
    (_, _, t, f') <- inferM env f
    p <- newName
    r <- newName
    return $ ([], [], t,
        Sym TLet :# p :$ (undefined :\\ Spine a') :$ undefined)

--------------------------------------------------------------------------------

inferRgn :: forall sig a . (a ~ Result sig)
    => Env -> SExp sig -> Args (Eta SExp) sig
    -> M (Sub, Context, Prim a, Beta TExp ('Const a))
inferRgn e sym as = inferSym e sym as
--        (p,t,e') <- inferSym env e as
--        let (f,b) = partCxt (not . flip elem (rgnPrim t)) p
--        return $ (b, t, foldr extend e' (map fst f))
  where
    extend :: Place -> Beta TExp ('Const a) -> Beta TExp ('Const a)
    extend p s = Sym (TLoc p) :$ (Spine s)

--------------------------------------------------------------------------------

-- | ...
inferM :: forall a . Typeable a
    => Env
    -> Beta SExp ('Const a)
    -> M (Sub, Context, Prim a, Beta TExp ('Const a))
inferM env = constMatch (inferRgn env) (inferVar env)

--infer :: Beta SExp ('Const a) -> Beta TExp ('Const a)
--infer e = let (_,_,b) = runM (inferM [] e) in b
  -- todo: Don't discard P.

--------------------------------------------------------------------------------
-- Small examples.
--------------------------------------------------------------------------------

var :: Typeable a => Name -> Beta SExp a
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

partCxt :: (Region -> Bool) -> Context -> (Context, Context)
partCxt f = partition (f . snd)

findRgn :: Place -> Context -> Region
findRgn p m = case lookup p m of
    Nothing -> error ("Place " ++ show p ++ " has no assoc. region.")
    Just r  -> r

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

(@@) :: Sub -> Sub -> Sub
(@@) new old = [(u, sub new t) | (u, t) <- old] ++ new

--------------------------------------------------------------------------------
-- Fin.
