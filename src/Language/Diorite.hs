{-# OPTIONS_GHC -Wall #-}

-- Related stuff:
--   https://github.com/Feldspar/feldspar-language
--   https://github.com/emilaxelsson/syntactic
--   https://github.com/emilaxelsson/lambda-edsl

module Language.Diorite where

import Data.Type.Equality ((:~:)(..))
import Data.Typeable (Typeable, eqT)
import Data.IntMap (IntMap)
import qualified Data.IntMap as Map (insert,lookup,union,map,empty,fromList)

--import Control.Arrow (first)
import qualified Control.Applicative as A
import Control.Monad.State (State)
import qualified Control.Monad.State as S

--------------------------------------------------------------------------------
-- * Abstract syntax tree.
--------------------------------------------------------------------------------

-- | \"Put\" predicate, asserts that a region is allocated.
data Put = Put

-- | Signature of a symbol.
data Signature a = Const a | Signature a :-> Signature a | Put :=> Signature a

infixr :->, :=>

-- | Variable names.
type Name = Int

-- | Place names.
type Place = Name
  
-- | Generic abstact syntax tree with beta-eta long normal form.
data Beta sym (sig :: Signature *) where
    Var  :: Name -> Beta sym sig
    Sym  :: sym sig -> Beta sym sig
    (:$) :: Beta sym (sig ':-> a) -> Eta sym sig -> Beta sym a
    (:#) :: Beta sym ('Put ':=> sig) -> Place -> Beta sym sig

data Eta sym (sig :: Signature *) where
    Lam   :: Name -> Eta sym a -> Eta sym (sig ':-> a)
    ELam  :: Place -> Eta sym sig -> Eta sym ('Put ':=> sig)
    Spine :: Beta sym ('Const sig) -> Eta sym ('Const sig)

infixl 1 :$, :#

-- | Generic AST, parameterized by a symbol domain.
type AST sym sig = Beta sym sig

-- | Fully applied AST (constant value).
type ASTF sym sig = Beta sym ('Const sig)

--------------------------------------------------------------------------------
-- ** Syntactic sugaring.
--------------------------------------------------------------------------------

-- | Syntactic sugaring for AST embeddings.
class Syntactic a where
    type Domain a   :: Signature * -> *
    type Internal a :: Signature *
    sugar   :: Beta (Domain a) (Internal a) -> a
    desugar :: a -> Eta (Domain a) (Internal a)

-- | Syntactic type casting.
resugar ::
    ( Syntactic a
    , Syntactic b
    , Domain a ~ Domain b
    , Internal a ~ Internal b
    , Internal a ~ 'Const a
    )
    => a -> b
resugar = sugar . tail' . desugar
  where
    tail' :: Eta (Domain a) ('Const a) -> Beta (Domain a) ('Const a)
    tail' (Spine b) = b

instance Syntactic (Beta sym ('Const a)) where
    type Domain   (Beta sym ('Const a)) = sym
    type Internal (Beta sym ('Const a)) = 'Const a
    sugar   = id
    desugar = Spine

instance Syntactic (Eta sym ('Const a)) where
    type Domain   (Eta sym ('Const a)) = sym
    type Internal (Eta sym ('Const a)) = 'Const a
    sugar   = Spine
    desugar = id

-- | Get the highest name bound for \"Eta\" node.
maxLamEta :: Eta sym a -> Name
maxLamEta (Lam n _)   = n
maxLamEta (ELam _ e)  = maxLamEta e
maxLamEta (Spine b)   = maxLamBeta b

-- | Get the highest name bound for \"Beta\" node.
maxLamBeta :: Beta sym a -> Name
maxLamBeta (b :$ e) = maxLamBeta b `Prelude.max` maxLamEta e
maxLamBeta (b :# _) = maxLamBeta b
maxLamBeta _        = 0

-- | Interface for variable binding.
lam :: (Beta sym a -> Eta sym b) -> Eta sym (a ':-> b)
lam f = Lam v body
  where
    v    = maxLamEta body + 1
    body = f $ Var v

-- | Syntactic functions.
instance
    ( Syntactic a
    , Syntactic b
    , Domain a ~ Domain b
    )
    => Syntactic (a -> b)
  where
    type Domain (a -> b)   = Domain a
    type Internal (a -> b) = Internal a ':-> Internal b
    sugar   f = sugar . (f :$) . desugar
    desugar f = lam (desugar . f . sugar)

-- | Sugared symbol application.
sugarSym :: Syntactic a => Domain a (Internal a) -> a
sugarSym = sugar . Sym

--------------------------------------------------------------------------------
-- ** Evaluation.
--------------------------------------------------------------------------------

type family Denotation sig where
    Denotation ('Const a)    = a
    Denotation (a ':-> b)    = Denotation a -> Denotation b
    -- ...

-- todo.

--------------------------------------------------------------------------------
-- ** Rendering.
--------------------------------------------------------------------------------

-- | Render a symbol as concrete syntax.
class Render sym where
    renderSym  :: sym sig -> String
    renderArgs :: [String] -> sym sig -> String
    renderArgs []   s = renderSym s
    renderArgs args s = "(" ++ unwords (renderSym s : args) ++ ")"

-- | Render a \"Beta\" tree as concrete syntax.
renderBeta :: Render sym => [String] -> Beta sym a -> String
renderBeta _    (Var n)  = show n
renderBeta args (Sym s)  = renderArgs args s
renderBeta args (s :$ e) = renderBeta (renderEta e : args) s
renderBeta args (s :# p) = renderBeta (("<" ++ show p ++ ">") : args) s

-- | Render an \"Eta\" spine as concrete syntax.
renderEta :: Render sym => Eta sym a -> String
renderEta (Lam n e)  = "(\\" ++ show n ++ ". " ++ renderEta e ++ ")"
renderEta (ELam p e) = "(/\\" ++ show p ++ ". " ++ renderEta e ++ ")"
renderEta (Spine b)  = renderBeta [] b

instance Render sym => Show (Beta sym a) where
    show = renderBeta []

instance Render sym => Show (Eta sym a) where
    show = renderEta

--------------------------------------------------------------------------------
-- ** Traversal.
--------------------------------------------------------------------------------

-- | Denotational result of a symbol's signature.
type family Result sig where
    Result ('Const a)    = a
    Result (a ':-> b)    = Result b
    Result ('Put ':=> a) = Result a

-- | Argument parameterized on variables and places.
data Arg c (sig :: Signature *) where
    AVar   :: Name -> Arg c a -> Arg c (sig ':-> a)
    APlace :: Place -> Arg c a -> Arg c ('Put ':=> a)
    ASym   :: c ('Const a) -> Arg c ('Const a)

-- | List of symbol arguments.
data Args c (sig :: Signature *) where
    Nil  :: Args c ('Const a)
    (:*) :: Arg c a -> Args c sig -> Args c (a ':-> sig)
    (:~) :: Place -> Args c sig -> Args c ('Put ':=> sig)

infixr :*, :~

-- | \"Pattern match\" on a fully applied AST using a function that gets direct
--   access to the top-most symbol and its sub-trees given as \"Args\".
match :: forall sym a c
    .  (forall sig . (a ~ Result sig)
           => sym sig -> Args (Beta sym) sig -> c ('Const a))
    -> (forall sig . (a ~ Result sig)
           => Name    -> Args (Beta sym) sig -> c ('Const a))
    -> Beta sym ('Const a)
    -> c ('Const a)
match f g = flip matchBeta Nil
  where
    matchBeta :: forall sig . (a ~ Result sig)
        => Beta sym sig -> Args (Beta sym) sig -> c ('Const a)
    matchBeta (Var v)  as = g v as
    matchBeta (Sym s)  as = f s as
    matchBeta (b :$ e) as = matchBeta b (matchEta e :* as)
    matchBeta (b :# p) as = matchBeta b (p :~ as)

    matchEta :: Eta sym sig -> Arg (Beta sym) sig
    matchEta (Lam v e)  = AVar v (matchEta e)
    matchEta (ELam p e) = APlace p (matchEta e)
    matchEta (Spine b)  = ASym b
  -- todo: users can probably use their 'f' in the definition of 'g' but I feel
  -- like I should be able to define that myself somehow, like 'f (g ..) as'

-- | A version of \"match\" with a simpler, constant result type.
constMatch :: forall sym a b
    .  (forall sig . (a ~ Result sig)
           => sym sig -> Args (Beta sym) sig -> b)
    -> (forall sig . (a ~ Result sig)
           => Name    -> Args (Beta sym) sig -> b)
    -> ASTF sym a -> b
constMatch f g = A.getConst . match (\s -> A.Const . f s) (\v -> A.Const . g v)

newtype WrapBeta c sym sig = WrapBeta { unWrapBeta :: c (Beta sym sig) }
  -- Only used in the definition of 'transMatch'

-- | A version of \"match\" where the result is a transformed syntax tree,
--   wrapped in some type constructor.
transMatch :: forall sym sym' c a
    .  (forall sig . (a ~ Result sig)
           => sym sig -> Args (Beta sym) sig -> c (Beta sym' ('Const a)))
    -> (forall sig . (a ~ Result sig)
           => Name    -> Args (Beta sym) sig -> c (Beta sym' ('Const a)))
    -> ASTF sym a
    -> c (ASTF sym' a)
transMatch f g = unWrapBeta . match (\s -> WrapBeta . f s) (\v -> WrapBeta . g v)

--------------------------------------------------------------------------------
-- ** Type/Signature witness.
--------------------------------------------------------------------------------

-- | Labelling of primitive types.
class (Eq a, Show a, Typeable a) => Prim a where
    primitive :: TR a

-- | Name of a region, associated with one or more places.
type Region = Name

-- | Witness of a symbol signature.
data SigRep (sig :: Signature *) where
    SigConst :: Prim a => SigRep ('Const a)
    SigPart  :: Region -> SigRep a -> SigRep sig -> SigRep (a ':-> sig)
    SigPred  :: Region -> SigRep sig -> SigRep ('Put ':=> sig)
  -- todo: added 'SigRep a' to 'SigPart' since arguments can be extended with
  -- evidence as well, might be a smarter way of doing it.

-- | Extract a witness of equality of two signatures' types.
eqST :: forall sig sig' . SigRep sig -> SigRep sig' -> Maybe (sig :~: sig')
eqST (SigConst) (SigConst)
    | Just Refl <- eqT :: Maybe (sig :~: sig') = Just Refl
eqST (SigPart _ a sig) (SigPart _ a' sig')
    | Just Refl <- eqST a a', Just Refl <- eqST sig sig' = Just Refl
eqST (SigPred _ sig) (SigPred _ sig')
    | Just Refl <- eqST sig sig' = Just Refl
eqST _ _ = Nothing

-- | Valid symbol signatures.
class Sig sig where
    represent :: M (SigRep sig)
  -- todo: added 'M' for now, not sure if actually needed.

instance Prim a => Sig ('Const a) where
    represent = return SigConst

instance (Sig a, Sig sig) => Sig (a ':-> sig) where
    represent = SigPart <$> newName <*> represent <*> represent

instance Sig sig => Sig ('Put ':=> sig) where
    represent = SigPred <$> newName <*> represent

-- | Symbol with a valid signature.
class Sym sym where
    symbol :: sym sig -> M (SigRep sig)

-- | ...
argS :: forall sym sig . Sym sym => Arg sym sig -> M (SigRep sig)
argS (AVar _ arg)   = SigPart <$> newName <*> undefined <*> argS arg
argS (APlace _ arg) = SigPred <$> newName <*> argS arg
argS (ASym s)       = symbol s

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
            sig <- symbol rgn
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

-- | Existential quantification.
data Ex e where
    Ex :: e a -> Ex e

liftE :: (forall a . e a -> b) -> Ex e -> b
liftE f (Ex a) = f a

--------------------------------------------------------------------------------
-- * Example.
--------------------------------------------------------------------------------

-- | Source language.
data SExp a where
    SInt :: Int -> SExp ('Const Int)
    SAdd :: SExp ('Const Int ':-> 'Const Int ':-> 'Const Int)

data TR a where
    TRInt :: TR Int

instance Prim Int where
    primitive = TRInt

instance Render SExp where
    renderSym (SInt i) = "i" ++ show i
    renderSym (SAdd)   = "(+)"

instance Sym SExp where
    symbol (SInt _) = represent
    symbol (SAdd)   = represent

--------------------------------------------------------------------------------

-- | Target language.
data TExp a where
    TInt :: Int -> TExp ('Put ':=> 'Const Int)
    TAdd :: TExp ('Put ':=> 'Const Int ':-> 'Const Int ':-> 'Const Int)
    --
    TLocal :: Place -> TExp (a ':-> a) -- todo: open symbol domains.
    TAt    :: Place -> TExp (a ':-> a) -- todo: ???

instance Render TExp where
    renderSym (TInt i)   = renderSym (SInt i)
    renderSym (TAdd)     = renderSym (SAdd)
    renderSym (TLocal p) = "local " ++ show p
    renderSym (TAt p)    = "at " ++ show p

--------------------------------------------------------------------------------

test_add :: Eta SExp ('Const Int ':-> 'Const Int)
test_add =
    (Lam 1
      (Spine ((Sym SAdd)
        :$ (Spine (Sym (SInt 0)))
        :$ (Spine (Var 1)))))

test_add' :: Eta TExp ('Put ':=> 'Const Int ':-> 'Const Int)
test_add' =
    (ELam 2 (Lam 1
      (Spine ((Sym (TLocal 3))
        :$ (Spine ((Sym TAdd)
             :# 2
             :$ (Spine ((Sym (TInt 0)) :# 3))
             :$ (Spine (Var 1))))))))

--------------------------------------------------------------------------------
-- Fin.
