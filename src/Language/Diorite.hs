{-# OPTIONS_GHC -Wall #-}

-- Related stuff:
--   https://github.com/Feldspar/feldspar-language
--   https://github.com/emilaxelsson/syntactic
--   https://github.com/emilaxelsson/lambda-edsl

module Language.Diorite where

import Data.Typeable (Typeable)

--import Data.List (intersperse)
--import Data.IntMap (IntMap)
--import qualified Data.IntMap as Map (lookup,union,map,fromList)

--import Control.Arrow (first)
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
  
-- | Generic abstact sytnax tree with beta-eta long normal form.
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

-- | Render an 'ASTF' as concrete syntax.
render :: Render sym => ASTF sym a -> String
render = renderBeta []

--------------------------------------------------------------------------------
-- ** Type/Signature witness.
--------------------------------------------------------------------------------

-- | Labelling of primitive types.
class (Eq a, Show a, Typeable a) => Prim a
--    data Type a :: *
--    represent :: Type a

-- | Name of a region, associated with one or more places.
type Region = Name

-- | Witness of a symbol signature.
data SigRep sig where
    SigConst :: SigRep ('Const a)
    SigPart  :: Region -> SigRep sig -> SigRep (a ':-> sig)
    SigPred  :: Region -> SigRep sig -> SigRep ('Put ':=> sig)

-- | Valid symbol signatures.
class Sig sig where
    represent :: SigRep sig

instance Sig ('Const a) where
    represent = SigConst

instance Sig sig => Sig (a ':-> sig) where
    represent = SigPart 0 represent

instance Sig sig => Sig ('Put ':=> sig) where
    represent = SigPred 0 represent

-- | Symbol with a valid signature.
class Sym sym where
    symbol :: sym sig -> SigRep sig

--------------------------------------------------------------------------------
-- ** Decoration.
--------------------------------------------------------------------------------

-- | Denotational result of a symbol's signature.
type family Result sig where
    Result ('Const a) = a
    Result (a ':-> b) = Result b

-- | Decorated symbol.
data (sym :&: info) sig where
    (:&:) :: { decor_sym  :: sym sig
             , decor_info :: info (Result sig)
             }
          -> (sym :&: info) sig

instance Render sym => Render (sym :&: info) where
    renderSym       = renderSym . decor_sym
    renderArgs args = renderArgs args . decor_sym

--------------------------------------------------------------------------------
-- *** Type casting (todo).

-- | \"Typed\" symbol.
data Typed sym sig where
    Typed :: Typeable (Result sig) => sym sig -> Typed sym sig

instance Render sym => Render (Typed sym) where
    renderSym (Typed s) = renderSym s

--------------------------------------------------------------------------------
-- *** Local regions.

-- | Local region-bindings and region-annotations.
data Local sig where
    Local :: Place -> Local (a ':-> a)

instance Render Local where
    renderSym (Local p) = "local " ++ show p

--------------------------------------------------------------------------------
-- * Region inference.
--------------------------------------------------------------------------------

-- | Erase any \"Put\" predicates in a signature.
type family Erasure a where
    Erasure ('Const a)    = 'Const a
    Erasure (a ':-> b)    = Erasure a ':-> Erasure b
    Erasure ('Put ':=> a) = Erasure a

-- | ...
class Infer source target where
    inferSym :: (sig ~ Erasure sig') => source sig -> Beta target sig'

--------------------------------------------------------------------------------

-- | A \"Place\" associated with the region of a \"Put\" predicate.
type Pred = (Place,Region)

-- | ...
inferBeta :: Infer source target => Beta source sig -> M (Beta target sig)
inferBeta (Var _)  = undefined
inferBeta (Sym _)  = undefined
inferBeta (_ :$ _) = undefined
inferBeta (_ :# _) = error "inferred."

{-
-- | ...
type Env sym = IntMap ([Place],E QualType)

inferEta :: Env sym -> Eta sym sig -> M (Eta sym sig)
inferEta _   (Lam _ _)  = undefined
inferEta _   (Spine _)  = undefined
inferEta _   (ELam _ _) = error "inferred."

-- | ...
instantiate :: forall sym sig
    .  Env sym
    -> Beta sym sig
    -> M (Subst, QualType sig, Beta sym sig)
instantiate env b@(Var v) = case Map.lookup v env of
    Nothing       -> error ("Unknown identifier: " ++ show v ++ "\n")
    Just (ps,E t) -> do
        ps' <- newNames (length ps)
        let s = newSub (zip ps ps')
        return (s, undefined, foldr (flip (:#)) b ps')
instantiate _ _ = error "Instantiate not called on variable."
-}

--------------------------------------------------------------------------------
-- ** Utils.
--------------------------------------------------------------------------------

-- | Name supply monad.
type M a = State Name a

runM :: M a -> a
runM = flip S.evalState 0

newName :: M Name
newName = do n <- S.get; S.put (n+1); return n

newNames :: (Enum a, Num a) => a -> M [Name]
newNames n = mapM (const newName) [1..n]

--------------------------------------------------------------------------------
{-
-- | Region-substitution.
type Subst = IntMap Region

newSub :: [(Place,Place)] -> Subst
newSub = Map.fromList

-- | Left-biased union of two substitutions.
(@@) :: Subst -> Subst -> Subst
(@@) a b = Map.union a (Map.map update b)
  where
    update :: Region -> Region
    update r = case Map.lookup r a of
      Nothing -> r
      Just r' -> r'
-}
--------------------------------------------------------------------------------
{-
-- | Existential quantification.
data E e where
    E :: e a -> E e

liftE :: (forall a . e a -> b) -> E e -> b
liftE f (E a) = f a
-}
--------------------------------------------------------------------------------
{-
-- | ...
data P e a where
    P :: e -> P e a
-}
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

--------------------------------------------------------------------------------

-- | Target language.
data TExp a where
    TInt :: Int -> TExp ('Put ':=> 'Const Int)
    TAdd :: TExp ('Put ':=> 'Const Int ':-> 'Const Int ':-> 'Const Int)
    -- todo: add via open symbol domains instead.
    TLocal :: Place -> TExp (a ':-> a)

instance Render TExp where
    renderSym (TInt i)   = renderSym (SInt i)
    renderSym (TAdd)     = renderSym (SAdd)
    renderSym (TLocal p) = "local " ++ show p

--------------------------------------------------------------------------------

test_add :: Eta SExp ('Const Int ':-> 'Const Int)
test_add =
    (Lam 1
      (Spine ((Sym SAdd)
          :$ (Spine (Sym (SInt 0)))
          :$ (Spine (Var 1)))))

test_add' :: Beta TExp ('Const Int)
test_add' = undefined

--------------------------------------------------------------------------------
-- Old Code.
--------------------------------------------------------------------------------

{-
labelSym :: Label (Result sig) => sym sig -> M ((sym :&: Type) sig, [Qualifier])
labelSym sym = (first (sym :&:)) <$> label

substSym :: Label (Result sig) => Subst -> (sym :&: Type) sig -> (sym :&: Type) sig
substSym s (sym :&: t) = sym :&: (subst s t)
-}

--------------------------------------------------------------------------------
-- fin.
