--{-# OPTIONS_GHC -Wall #-}

module Language.Diorite.Region.Label
    (
    -- * ...
      Rgn(..)
    , local
    , at
    ) where

import Language.Diorite.Signatures (Result, SigRep(..))
import Language.Diorite.Qualifiers (Qualifier(..), Difference, QualRep(..))
import Language.Diorite.Syntax (Name, Ev(..), Beta(..), Eta(..), AST, ASTF, elam, (:+:), (:<:)(..))
import Language.Diorite.Traversal (Args(..), constMatch)
import Language.Diorite.Region.Labels (Put(..), Label(..), (:~~:)(..), Strip(..), LblRep)
import qualified Language.Diorite.Signatures as S (Signature(..))

import Data.Type.Equality ((:~:)(..))

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------
--
-- > What I (sorta) have:
--
-- beta :: B [] ('C Int -> 'C Int -> 'C Int)
-- beta = \x. \y. x + y
--
-- > What I (sorta) want:
--
-- beta :: B .. ('C^1 Int ->^2 'C^3 Int ->^4 'C^5 Int)
-- beta = (\x . (\y . (x + y) at 5) at 4) at 2
--   ~alternatively~
-- beta = \x .^2 \y .^4 (x + y)^5
--
-- > note: the evaluation rules match on "const a at r" and "\x . e at r"
--   instead of just "const a" and "\x . e" with a rule for "e at r".
--
-- > So I need symbols which I can label terms with:
--
-- local r in E
-- E at r
--
-- > But Beta/Eta operates on signatures, not labelled signatures, so their
--   "smart" constructors need to take a "labelled" Beta/Eta that takes a
--   labelled signature instead.
--

type Labelled :: (S.Signature (Put *) * -> *) -> Label * * -> *
data Labelled ast lsig = forall sig . Labelled
    { _ast :: ast sig
    , _lbl :: sig :~~: lsig
    }

type LAST  sym qs lsig = Labelled (Beta sym qs) lsig
type LASTF sym qs a    = LAST sym qs ('Const a)

--
-- > The symbols can then be implemented as usual but with smart constructors
--   modify these labels as well:
--

type Place :: * -> *
type Place r = Ev ('Put r)

type Rgn :: S.Signature (Put *) * -> *
data Rgn sig where
    Local :: Rgn (('Put r 'S.:=> a) 'S.:-> a)
    At    :: Rgn (sig 'S.:-> sig)

local :: forall sym r qs a lsig . (Rgn :<: sym, Strip lsig ~ 'S.Const a) => LAST sym ('Put r ':. qs) lsig -> Place r -> LAST sym qs lsig
local (Labelled b (Stripped Refl)) p = Labelled (ast b) (Stripped Refl)
  where
    ast :: ASTF sym ('Put r ':. qs) a -> ASTF sym qs a
    ast b = local' :$ (p :\\ (Spine b))
    
    local' :: AST sym 'None (('Put r 'S.:=> 'S.Const a) 'S.:-> 'S.Const a)
    local' = inj Local

at :: forall sym qs r lsig . Rgn :<: sym => LAST sym qs lsig -> Place r -> LAST sym qs (lsig :^ r)
at (Labelled b (Stripped Refl)) p = Labelled undefined (Stripped Refl)
  where
    ast :: AST sym qs sig -> AST sym qs sig
    ast b = at' :$ undefined
    
    at' :: AST sym 'None (sig 'S.:-> sig)
    at' = inj At

--
-- > Region annotation is automatic, so we should write a function like:
--
-- annotate :: sig ~ Unlabel lsig => B [] sig -> LB .. lsig
--

annotate :: forall sym qs ps a lbl . AST sym qs ('S.Const a) -> LAST (sym :+: Rgn) ps lbl
annotate = constMatch annotateSym instantiateVar
  where
    annotateSym :: forall sig . a ~ Result sig => sym sig -> Args sym 'None sig -> LAST (sym :+: Rgn) ps lbl
    annotateSym = undefined

    instantiateVar :: forall rs sig . a ~ Result sig => Name -> Args sym rs sig -> LAST (sym :+: Rgn) ps lbl
    instantiateVar = undefined


--------------------------------------------------------------------------------
-- ** ...

-- Store [(Name, AST sig)]
type VarStore = ()

-- Context = [(Name, Ev r)]
type EvStore = ()

partitionFree :: LblRep sig -> VarStore -> EvStore -> (Name, Name)
partitionFree label vars evs = undefined

--------------------------------------------------------------------------------

-- ...

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------

reduceBeta :: Beta sym qs a -> Args sym qs a -> Beta (sym :+: Rgn) qs a
reduceBeta b = undefined

reduceEta :: Eta sym qs a -> SigRep a -> Eta (sym :+: Rgn) qs a
reduceEta (Spine b) (SigConst) = Spine $ undefined b

--------------------------------------------------------------------------------
-- Fin.
