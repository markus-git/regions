{-# language TypeSynonymInstances #-}
{-# language FlexibleInstances #-}

module Regions where

import Data.List (nub,nubBy,partition,intersperse,zip3,unzip3,zipWith3)
import Data.Maybe (fromMaybe,isNothing)
import Data.Function (on)
import Control.Arrow ((***))
import Control.Monad (liftM,ap,unless,when)
import Control.Monad.State (lift,StateT)
import qualified Control.Monad.State as S
import qualified Debug.Trace as D

import Prelude hiding (print,(<>))

--------------------------------------------------------------------------------
-- * Source Language.

type Var  = String
type Con  = Var

data SExp  = SEVar Var
           | SELam Var SExp
           | SEApp SExp SExp
           | SELet [SBind] SExp
           | SECon Con [SExp]
           | SECase SExp [SAlt]
           deriving (Eq,Show)

data SAlt  = SAVar Var SExp
           | SACon Con [Var] SExp
           deriving (Eq,Show)

type SBind = (Var,SExp)

--------------------------------------------------------------------------------
-- * Target Language.

type Rgn   = Type
type Place = Var

data Type  = TVar Var
           | TApp Type Type
           | TFun Type Rgn Type
           | TCon Con [Type]
           deriving (Eq, Show)

data Qual  = Put Type
           deriving (Eq,Show)

data Exp   = EVar Var [Place]
           | ELam Var Place Exp
           | EApp Exp Exp
           | ELet [Bind] Exp
           | ECon Con [Place] [Exp]
           | ECase Exp [Alt]
           | ERgn [Place] Exp
           --
           | EEv Place Exp
           deriving (Eq,Show)

data Alt   = AVar Var Exp
           | ACon Con [Place] [Var] Exp
           deriving (Eq,Show)

type Bind  = (Var,Place,Exp)

--------------------------------------------------------------------------------
-- * Inference environment types.

type Scheme  = ([Var],[Qual],Maybe Rgn,Type)
type Env     = [(Var,Scheme)]
type Context = [(Var,Qual)]

scheme :: Type -> Scheme
scheme = (,,,) [] [] Nothing

--------------------------------------------------------------------------------
-- * Substitutions and free variables.

type TSub = [(Var,Type)]

class Sub a where 
  sub :: TSub -> a -> a

instance Sub a => Sub [a] where
  sub s xs = map (sub s) xs

instance Sub Type where
  sub s (TVar v)     = fromMaybe (TVar v) $ lookup v s
  sub s (TApp t1 t2) = TApp (sub s t1) (sub s t2)
  sub s (TCon c ts)  = TCon c (sub s ts)
  sub s (TFun t1 r t2) = TFun (sub s t1) (sub s r) (sub s t2)

instance Sub Qual where
  sub s (Put t) = Put (sub s t)

instance Sub Scheme where
  sub s (vs,qs,r,t) = (vs,sub s' qs,r,sub s' t)
     where s' = filter ((`notElem` (free r ++ vs)) . fst) s
  -- Note: no alpha-conversion is done, thus we rely on (range s) always
  --       being 'fresh' and distinct from vs.

instance Sub (Var,Scheme) where
  sub s (v,sc) = (v,sub s sc)

instance Sub (Var,Qual) where
  sub s (v,q) = (v,sub s q)

--------------------------------------------------------------------------------

class Free a where
  free :: a -> [Var]

instance Free a => Free [a] where
  free xs = concatMap free xs

instance Free a => Free (Maybe a) where
  free x = maybe [] free x

instance Free Type where
  free (TVar v)       = [v]
  free (TApp t1 t2)   = free t1 ++ free t2
  free (TFun t1 r t2) = free t1 ++ free r ++ free t2
  free (TCon c ts)    = free ts

instance Free Qual where
  free (Put t) = free t

instance Free Scheme where
  free (vs,qs,r,t) = (free qs ++ free t) `except` (free r ++ vs)

instance Free (Var,Scheme) where
  free (_,sc) = free sc

instance Free (Var,Qual) where
  free (_,q) = free q

--------------------------------------------------------------------------------
-- * Unification.

type Equal = (Type,Type)

instance Sub Equal where
  sub s (t1,t2) = (sub s t1,sub s t2)

instance Free Equal where
  free (t1,t2) = free t1 ++ free t2

(@@) :: TSub -> TSub -> TSub
(@@) s1 s2 = [(u,sub s1 t) | (u,t) <- s2] ++ s1

match :: [Equal] -> TSub
match     = match' []
match' vs = merge . matchH vs []

matchH :: [Var] -> TSub -> [Equal] -> TSub
matchH vs s [] = s
matchH vs s ((TVar v,t):eqs)
  | t == TVar v        = matchH vs s eqs
  | v `notElem` free t
  , v `notElem` vs     = let s' = [(v,t)] in matchH vs (s' @@ s) (sub s eqs)
matchH vs s ((TApp t1 t2,TApp t1' t2'):eqs)
  = matchH vs s ((t1,t1'):(t2,t2'):eqs)
matchH vs s ((TCon c ts,TCon c' ts'):eqs)
  | c == c' = matchH vs s ((ts `zip` ts') ++ eqs)
matchH vs s ((TFun t1 r t2,TFun t1' r' t2'):eqs)
  = matchH vs s ((t1,t1'):(r,r'):(t2,t2'):eqs)
matchH _ _ ((t,t'):_) =
  error ("cannot match " ++ show t ++ " with " ++ show t' ++ "\n")

unify :: [Equal] -> TSub
unify     = unify' []
unify' vs = merge . unifyH vs []

unifyH :: [Var] -> TSub -> [Equal] -> TSub
unifyH vs s [] = s
unifyH vs s ((TVar v,t):eqs)
  | t == TVar v        = unifyH vs s eqs
  | v `notElem` free t
  , v `notElem` vs     = let s' = [(v,t)] in unifyH vs (s' @@ s) (sub s eqs)
unifyH vs s ((t,TVar v):eqs)
  = unifyH vs s ((TVar v,t):eqs)
unifyH vs s ((TApp t1 t2,TApp t1' t2'):eqs)
  = unifyH vs s ((t1,t1'):(t2,t2'):eqs)
unifyH vs s ((TCon c ts,TCon c' ts'):eqs)
  | c == c' = unifyH vs s ((ts `zip` ts') ++ eqs)
unifyH vs s ((TFun t1 r t2,TFun t1' r' t2'):eqs)
  = unifyH vs s ((t1,t1'):(r,r'):(t2,t2'):eqs)
unifyH _ _ ((t,t'):_) =
  error ("cannot unify " ++ show t ++ " and " ++ show t' ++ "\n")

merge :: TSub -> TSub
merge = mergeTS . map matchTS . merge'
  where
    matchTS :: (Var,[Type]) -> (TSub,[(Var,Type)])
    matchTS (v,t:[]) = ([],[(v,t)])
    matchTS (v,t:ts) =
      let (u,t') = foldr matchT ([],t) ts in (u,(v,t') : u)

    matchT :: Type -> (TSub,Type) -> (TSub,Type)
    matchT t' (s,t) =
      let u = unify [(t,t')] in (u @@ s, sub u t)

    mergeTS :: [(TSub,[(Var,Type)])] -> [(Var,Type)]
    mergeTS ss =
      let (u,s) = (***) concat concat (unzip ss) in [(v,sub u t) | (v,t) <- s]

--------------------------------------------------------------------------------
-- * Region inference.

reginfer :: Env -> SExp -> M (TSub,Context,Type,Exp)
reginfer env e = do
  aenv       <- abstract env
  (s,q,t,e') <- infer aenv e
  let vs       = free t ++ free (sub s aenv)
      (pi,q')  = partition (outside vs) q
      (u,uenv) = unifyEnv env (sub s aenv)
      m        = matchEnv env uenv
  return $ if null pi || higherorder t
    then (m,sub u q ,sub u t,                  e')
    else (m,sub u q',sub u t,ERgn (map fst pi) e')

infer :: Env -> SExp -> M (TSub,Context,Type,Exp)
infer env (SEVar x) = do
  (q,t,ws) <- instantiate env x
  return ([],q,t,EVar x ws)
infer env (SELam x e) = do
  t <- newType
  v <- newVar
  r <- newRegion
  (s,q,t',e') <- reginfer ((x,scheme t):env) e
  return (s,(v,Put r):q,TFun (sub s t) r t',ELam x v e')
infer env (SEApp e1 e2) = do
  (s1,q1,t1,e1') <- reginfer env e1
  (s2,q2,t2,e2') <- reginfer (sub s1 env) e2
  t <- newType
  r <- newRegion
  let st = unify [(sub s2 t1, TFun t2 r t)]
      s' = st @@ s2
  return (s' @@ s1,q2 ++ sub s' q1,sub st t,EApp e1' e2')
infer env (SELet bs e) = do
  let (xs,es) = unzip bs
  vs <- newVars    (length xs)
  rs <- newRegions (length xs)
  (ss,qs,ts,es') <- inferL env es
  let env'    = sub ss env
      (ys,ps) = unzip (map (partition (outside (free env'))) qs)
      schemes = zipWith3 (\y r -> gen (free env') (quals y) (Just r))
                  ys rs (sub ss ts)
      env''   = xs `zip` schemes ++ env'
      qs'     = zip vs (map Put rs)
  (s,q,t,e') <- reginfer env'' e
  return (s @@ ss,(sub s (qs' ++ concat ps)) ++ q,t,ELet (zip3 xs vs es') e')
infer env (SECon c es) = do
  (q,t,ws)      <- instantiate env c
  (s,q',ts,es') <- inferL env es
  t'  <- newType
  rs  <- newRegions (length ts)
  let s' = unify [(t,foldr2 TFun t' ts rs)]
  return (s' @@ s,sub s' q ++ concat q',sub s' t',ECon c ws es')
infer env (SECase e as) = do
  (s,q,t,e')     <- reginfer env e
  (sa,qa,ta,as') <- inferA (sub s env) as
  tc <- newType
  rc <- newRegion
  let sc = unify (repeat (TFun (sub sa t) rc tc) `zip` ta)
      qc = sub sc (sub sa (q ++ qa))
  return (sc @@ sa @@ s,qc,sub sc tc,ECase e' as')

--------------------------------------------------------------------------------
-- ** Inference utils.

instantiate :: Env -> Var -> M (Context,Type,[Place])
instantiate env x = case lookup x env of
  Nothing          -> error ("unknown identifier: " ++ x ++ "\n")
  Just (vs,qs,_,t) -> do
    ts <- newTypes (length vs)
    xs <- newVars (length qs)
    let s = vs `zip` ts
    return (xs `zip` sub s qs, sub s t, xs)

inferL :: Env -> [SExp] -> M (TSub,[Context],[Type],[Exp])
inferL _   []     = return ([],[],[],[])
inferL env (e:es) = do
  (s, q, t, e')  <- reginfer env e
  (ss,qs,ts,es') <- inferL (sub s env) es
  return (ss @@ s,sub ss q:qs,sub ss t:ts,e':es')

inferA :: Env -> [SAlt] -> M (TSub,Context,[Type],[Alt])
inferA _   []     = return ([],[],[],[])
inferA env (a:as) = do
  (s,q,t,a')    <- inferAlt a
  (ss,qs,ts,es) <- inferA (sub s env) as
  return (ss @@ s,qs ++ sub ss q,sub ss t : ts,a' : es)
  where
    inferAlt :: SAlt -> M (TSub,Context,Type,Alt)
    inferAlt (SAVar x e) = do
      t <- newType
      r <- newRegion
      (s,q,t',e') <- reginfer ((x,scheme t):env) e
      return (s,q,TFun t r t',AVar x e')
    inferAlt (SACon c xs e) = do
      ts <- newTypes   (length xs)
      rs <- newRegions (length xs)
      tc <- newType
      rc <- newRegion
      (q,t,_)      <- instantiate env c
      (s,q',t',e') <- reginfer (xs `zip` map scheme ts ++ env) e
      let s' = unify [(t, foldr2 TFun tc (sub s ts) (sub s rs))]
          ta = TFun (sub s' tc) rc (sub s' t')
          vs = fst (unzip (sub s' q))
      return (s' @@ s,sub s' q',ta,ACon c vs xs e')

--------------------------------------------------------------------------------
-- ** Region annotations.

typecheck :: SExp -> Env -> IO ()
typecheck exp env = do
  (_,q,t,_) <- runM (reginfer env exp)
  let (_,qs) = unzip q
  print $ pretty $ gen (free env) qs Nothing t

translate :: SExp -> Env -> IO ()
translate exp env = do
  (s,q,t,e) <- runM (reginfer env exp)
  let (vs,qs) = unzip q
  print $ pretty $ qual vs e

--------------------------------------------------------------------------------
-- ** Annotation utils.

-- Generate the most general type scheme.
gen :: [Var] -> [Qual] -> Maybe Rgn -> Type -> Scheme
gen vs qs r t = (vs',qs,r,t)
  where vs' = nub ((free qs ++ free t) `except` (free r ++ vs))

-- Translate unresolved region constraints into lambda functions.
qual :: [Var] -> Exp -> Exp
qual vs e = foldr EEv e vs
-- Todo: Bake these not-special "special" lambdas into the rules instead.

-- Check if a type is "higher-order".
higherorder :: Type -> Bool
higherorder (TVar _)     = False
higherorder (TApp t1 t2) = higherorder t1 || higherorder t2
higherorder (TCon _ ts)  = any higherorder ts
higherorder (TFun _ _ _) = True

-- Check if a type is "first-order".
firstorder :: Type -> Bool
firstorder = not . higherorder

type TSub' = [(Type,Type)]

-- Try and get the principal type abstraction.
abstract :: Env -> M Env
abstract = mapM (\(v,s) -> (,) v <$> absS s) 
  where
    absS :: Scheme -> M Scheme
    absS (vs,qs,r,t) = (,,,) vs qs r <$> absT vs t

    absT :: [Var] -> Type -> M Type
    absT vs t | all (`notElem` vs) (free t) = newType
    absT vs (TVar v)       = pure $ TVar v
    absT vs (TApp t1 t2)   = TApp <$> absT vs t1 <*> absT vs t2
    absT vs (TFun t1 r t2) = TFun <$> absT vs t1 <*> pure r <*> absT vs t2
    absT vs (TCon c ts)    = TCon c <$> mapM (absT vs) ts

-- While I use a list of schemes in types, in practice it is only two.
unifyEnv :: [(Var,Scheme)] -> [(Var,Scheme)] -> (TSub,[(Var,Scheme)])
unifyEnv env1 env2 =
  let menv      = merge2' env1 env2
      (us,uenv) = unzip (map unifyVS menv)
  in (merge (concat us),uenv)
  where
    unifyVS :: (Var,[Scheme]) -> (TSub,(Var,Scheme))
    unifyVS (v,s:sc) =
      let (u,sc') = foldr unifyS ([],s) sc in (u,(v,sc'))

    unifyS :: Scheme -> (TSub,Scheme) -> (TSub,Scheme)
    unifyS (_,_,_,t') (s,sc@(vs,_,_,t)) =
      let u = unify' vs [(t,t')] in (u @@ s,sub u sc)    

-- Simplified as `merge'` preserves ordering of schemes relative to eachother.
matchEnv :: [(Var,Scheme)] -> [(Var,Scheme)] -> TSub
matchEnv env1 env2 =
  let menv    = merge2' env1 env2
      ms      = map matchVS menv
  in merge (concat ms)
  where
    matchVS :: (Var,[Scheme]) -> TSub
    matchVS (v,s:sc) =
      let (m,_) = foldr matchS ([],s) sc in m

    matchS :: Scheme -> (TSub,Scheme) -> (TSub,Scheme)
    matchS (_,_,_,t') (s,sc@(vs,_,_,t)) =
      let m = match' vs [(t,t')] in (m @@ s,sub m sc)

--------------------------------------------------------------------------------
-- * Testing/Examples.

env0 :: Env
env0 = [scOne,scTuple,scFst,scSnd]

scOne,scTuple,scFst,scSnd :: (Var,Scheme)
scOne   = ("1",([],[],Nothing,TCon "Int" []))
scTuple = ("(,)",
  (["r0","r1","r2","a","b"]
  ,[Put (TVar "r0"),Put (TVar "r1"),Put (TVar "r2")]
  ,Nothing
  ,TFun (TVar "a") (TVar "r1") (TFun (TVar "b") (TVar "r2") (TCon "(,)" [TVar "r0",TVar "a",TVar "b"]))))
scFst   = ("fst",
  (["r0","r1","a","b"]
  ,[Put (TVar "r0")]
  ,Nothing
  ,TFun (TCon "(,)" [TVar "r0",TVar "a",TVar "b"]) (TVar "r1") (TVar "a")))
scSnd   = ("snd",
  (["r0","r1","a","b"]
  ,[Put (TVar "r0")]
  ,Nothing
  ,TFun (TCon "(,)" [TVar "r0",TVar "a",TVar "b"]) (TVar "r1") (TVar "b")))

--------------------------------------------------------------------------------

-- Con.
test0 = flip translate [scTuple,scOne]
  (SECon "(,)" [SECon "1" [], SECon "1" []])

-- Lam/App.
test1 = flip translate [scOne]
  (SEApp (SELam "x" (SEVar "x")) (SECon "1" []))

-- Var/Let.
test2 = flip translate [scOne]
  (SELet [("x",(SECon "1" []))] (SEVar "x"))

-- Con with Tuple.
test3 = flip translate [scOne,scTuple,scFst]
  (SEApp
    (SELam "x" (SECon "fst" [SEVar "x"]))
    (SECon "(,)" [SECon "1" [], SECon "1" []]))

-- Con/Case.
test4 = flip translate [scOne]
  (SEApp
    (SELam "x"
      (SECase (SEVar "x") [SACon "1" [] (SECon "1" [])]))
    (SECon "1" []))

-- Case with Tuple.
test5 = flip translate [scOne,scTuple]
  (SECase
    (SECon "(,)" [SECon "1" [], SECon "1" []])
    [SACon "(,)" ["a","b"] (SEVar "a")])

-- Con/Case with Var/Tuple.
test6 = flip translate [scOne,scTuple]
  (SEApp
    (SELam "x"
      (SECase (SEVar "x") [SACon "(,)" ["a","b"] (SEVar "a")]))
    (SECon "(,)" [SECon "1" [], SECon "1" []]))

--------------------------------------------------------------------------------
-- * Name-supply monad and utils.

type M a = StateT Int IO a

runM :: M a -> IO a
runM = flip S.evalStateT 0

newName :: String -> M String
newName x = do
  n <- S.get
  S.put (n+1)
  return (x ++ "_" ++ show n)

newVar :: M String
newVar = newName "v"

newVars :: (Enum a, Num a) => a -> M [String]
newVars k = mapM (const newVar) [1..k]

newType :: M Type
newType = TVar <$> newName "t"

newTypes :: (Enum a, Num a) => a -> M [Type]
newTypes k = mapM (const newType) [1..k]

newRegion :: M Type
newRegion = TVar <$> newName "r"

newRegions :: (Enum a, Num a) => a -> M [Type]
newRegions k = mapM (const newRegion) [1..k]

--------------------------------------------------------------------------------
-- * Generic utils.

quals :: [(a, Qual)] -> [Qual]
quals xs = snd (unzip xs)

vars :: [(Var, a)] -> [Place]
vars xs = fst (unzip xs)

outside :: Free a => [Var] -> a -> Bool
outside vs q = all (`notElem` vs) (free q)

foldr2 :: (a -> b -> c -> c) -> c -> [a] -> [b] -> c
foldr2 f c as bs = foldr (uncurry f) c (as `zip` bs)

except :: Eq a => [a] -> [a] -> [a]
except xs ys = filter (`notElem` ys) xs

merge' :: Eq a => [(a,b)] -> [(a,[b])]
merge' xs = let ys = group' ((==) `on` fst) xs in map one ys
  where
    one :: [(a,b)] -> (a,[b])
    one ((a,b):xs) = (a,b:map snd xs)

merge2' :: Eq a => [(a,b)] -> [(a,b)] -> [(a,[b])]
merge2' xs ys = merge' (xs++ys)

group' :: (a -> a -> Bool) -> [a] -> [[a]]
group' p [] = []
group' p (x:xs) = let (ys,zs) = span' (p x) xs in (x:ys):group' p zs

span' :: (a -> Bool) -> [a] -> ([a],[a])
span' p [] = ([],[])
span' p (x:xs)
  | p x       = let (ys,zs) = span' p xs in (x:ys,zs)
  | otherwise = let (ys,zs) = span' p xs in (ys,x:zs)

--------------------------------------------------------------------------------
-- * Pretty printing.

class Pretty a where
  pretty :: a -> String
    
instance Pretty String  where pretty = id
instance Pretty Exp     where pretty = prettyExp
instance Pretty Alt     where pretty = prettyAlt
instance Pretty Bind    where pretty = prettyBind
instance Pretty Type    where pretty = prettyType
instance Pretty Qual    where pretty = prettyQual
instance Pretty Scheme  where pretty = prettyScheme
instance Pretty Context where pretty = prettyContext
instance Pretty TSub    where pretty = prettyTSub

instance Pretty (Var,Scheme) where
  pretty (v,sc) = v <+> ":" <+> pretty sc

prettyExp :: Exp -> String
prettyExp (EVar x vs)    = x <> angles (commas vs)
prettyExp (ELam x v e)   = "\\" <+> x <+> "." <+> parens (prettyExp e) <+> label v
prettyExp (EApp f e)     = parens (prettyExp f) <+> parens (prettyExp e)
prettyExp (ELet xs e)  = "let" <+> brackets (commas (map prettyBind xs)) <+> "in" <+> parens (prettyExp e)
prettyExp (ECon c vs es) = c <+> angles (commas vs) <+> brackets (commas (map prettyExp es))
prettyExp (ECase e as)   = "case" <+> prettyExp e <+> "of" <+> braces (commas (map prettyAlt as))
prettyExp (ERgn r e)     = "letregion" <+> brackets (commas r) <+> parens (prettyExp e)
prettyExp (EEv v e)      = "\\" <+> v <+> "." <+> parens (prettyExp e)

prettyAlt :: Alt -> String
prettyAlt (AVar x e)       = x <+> "->" <+> prettyExp e
prettyAlt (ACon c vs es e) = c <+> angles (commas vs) <+> brackets (commas es) <+> "->" <+> prettyExp e

prettyBind :: Bind -> String
prettyBind (x,v,e) = x <+> ":=" <+> prettyExp e <+> label v

prettyType :: Type -> String
prettyType (TVar v)     = v
prettyType (TApp f t)   = parens (prettyType f) <+> parens (prettyType t)
prettyType (TCon c ts)  = c <+> brackets (commas (map prettyType ts))
prettyType (TFun a r b) = prettyType a <+> "-" <> angles (prettyType r) <> "->" <+> prettyType b

prettyQual :: Qual -> String
prettyQual (Put t) = "Put" <+> prettyType t

prettyScheme :: Scheme -> String
prettyScheme ([],[],Nothing,t) = prettyType t
prettyScheme (vs,[],Nothing,t) = "forall" <+> commas vs <+> "." <+> prettyType t
prettyScheme (vs,qs,Nothing,t) = "forall" <+> commas vs <+> "." <+> commas (free qs) <+> "=>" <+> prettyType t
prettyScheme (vs,qs,Just r,t)  = "forall" <+> commas vs <+> "." <+> commas (free qs) <+> "=" <> angles (prettyType r) <> "=>" <+> prettyType t

prettyContext :: Context -> String
prettyContext xs = braces (commas (map go xs))
  where
    go :: (Var, Qual) -> String
    go (v, q) = v <+> ":" <+> prettyQual q

prettyTSub :: TSub -> String
prettyTSub xs = commas (map go xs)
  where
    go :: (Var, Type) -> String
    go (v, t) = v <+> "=" <+> prettyType t

(<+>) :: String -> String -> String
(<+>) "" b = b
(<+>) a "" = a
(<+>) a  b = a ++ " " ++ b

infixr 5 <+>

(<>) :: String -> String -> String
(<>) "" b = b
(<>) a "" = a
(<>) a b  = a ++ b
  
parens :: String -> String
parens "" = ""
parens s  = "(" ++ s ++ ")"

brackets :: String -> String
brackets "" = ""
brackets s  = "[" ++ s ++ "]"

braces :: String -> String
braces "" = ""
braces s  = "{" ++ s ++ "}"

angles :: String -> String
angles "" = ""
angles s  = "<" ++ s ++ ">"

raise :: String -> String
raise "" = ""
raise s  = "^" ++ s

commas  :: [String] -> String
commas []     = ""
commas (x:[]) = x
commas (x:xs) = x ++ "," ++ commas xs

label :: String -> String
label s = "at" <+> s

labels :: [String] -> String
labels = label . commas

--------------------------------------------------------------------------------
-- * Debug utils.

debug :: Bool
debug = False

trace :: String -> Bool
trace m = D.trace (m++"\n") debug

print :: Pretty a => a -> IO ()
print a = putStrLn $ pretty a

printM :: Pretty a => a -> M ()
printM a = lift $ print a

printEnv e env (s,q,t,e') = do
  printM $ "+++ inferred from (" ++ show e ++ "):"
  printM $ "Env:  " ++ prettyEnv env
  printM $ "Exp:  " ++ pretty e'
  printM $ "Type: " ++ pretty t
  printM $ "Sub:  " ++ pretty s
  printM $ "Ctx:  " ++ pretty q

printNew v env (q,t,ws) = do
  printM $ "=== instantiated variable (" ++ show v ++ "):"
  printM $ "Env:  " ++ prettyEnv env
  printM $ "Type: " ++ pretty t
  printM $ "Reg:  " ++ concat (intersperse "," (map pretty ws))
  printM $ "Ctx:  " ++ pretty q

printReg e env aenv t s u m = when debug $ do
  printM $ "+++ reginfer for " ++ show e
  printM $ "Init. Env : " ++ prettyEnv env
  printM $ "Abst. Env : " ++ prettyEnv aenv
  printM $ "Inf. Type : " ++ pretty t
  printM $ "Inf. Sub  : " ++ pretty s
  printM $ "Uni. Sub  : " ++ pretty u
  printM $ "Type : " ++ pretty (sub u t)
  printM $ "Sub  : " ++ pretty m

prettyEnv :: [(Var,Scheme)] -> String
prettyEnv = commas . map go
  where go :: (Var,Scheme) -> String
        go ("(,)",_) = "..."
        go sc        = pretty sc

--------------------------------------------------------------------------------
