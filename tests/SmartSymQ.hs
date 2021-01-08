{-# OPTIONS_GHC -Wall #-}

module SmartSymQ where

import Language.Diorite.Syntax
import Language.Diorite.Interpretation

--------------------------------------------------------------------------------
-- * A puzzle for Nick!
--------------------------------------------------------------------------------
--
-- What I have: Symbols like S below.
-- What I want: Convert a symbol like X into its constructor function.
--
-- That is, I want a function like 'smartSym':
--
--   type A q a = AST S q ('Const a)
--
--   smartSym (X :: S ('Const Int ':-> 'Const Int ':-> 'Const Int))
--       = f :: forall s1 s2 . A s1 Int -> A s2 Int -> A (Union s1 s2) Int
--
-- What you need to know ("Name(line#)" refer to "Syntax.hs" file):
--
--   The 'a' used above is a type captured by 'Signature'(69):
--
--     data Signature p a = Const a | Signature p a :-> Signature p a
--
--   and can be reified with the 'Sig'(92) class into its 'SigRep'(86):
--
--     data SigRep (sig :: Signature p *) where
--       SigConst :: SigRep ('Const a)
--       SigPart  :: SigRep a -> SigRep sig -> SigRep (a ':-> sig)
--
--   Same goes for qualifiers, as in we have a 'Qualifier'(140) type:
--
--     data Qualifier p = None | p :. Qualifier p
--
--   and a class 'Qual'(179) and corresponding reified type 'QualRep'(174):
--
--     data QualRep (qs :: Qualifier p) where
--       QualNone  :: QualRep ('None)
--       QualPred  :: Proxy q -> QualRep qs -> QualRep (q ':. qs)
--
--   The AST themselves are given by 'Beta'(236) and 'Eta'(246):
--
--     data Beta sym (qs :: Qualifier p) (sig :: Signature p *) where
--       Var   :: Sig sig => Name -> Beta sym qs sig                                     -- ^ Variable.
--       Sym   :: sym sig -> Beta sym 'None sig                                          -- ^ Symbol.
--       (:$)  :: Beta sym qs (a ':-> sig) -> Eta sym ps a -> Beta sym (Union qs ps) sig -- ^ Application.
--
--     data Eta sym (qs :: Qualifier p) (sig :: Signature p *) where
--       Spine :: Beta sym qs ('Const a) -> Eta sym qs ('Const a)                        -- ^ Body.
--       (:\)  :: Sig a => Name -> Eta sym qs sig -> Eta sym qs (a ':-> sig)             -- ^ Abstraction.
--
--   And that's a summary of what you basically need to know. The function that
--   actually implements this (for no qualifiers) is 'smartSym''(343) and the
--   type families it uses are right above it. The rest you shouldn't have to
--   look at.
--
--   'S' and 'B' below gives you a small example to work with.
--
--------------------------------------------------------------------------------

data Put a

data S a where
    X :: S ('Const Int ':-> 'Const Int ':-> 'Const Int)

instance Render S where
    renderSym (X) = "X"

type B q a = Beta S (q :: Qualifier (Put *)) ('Const a)

--------------------------------------------------------------------------------

x, xs :: forall q1 q2 . B q1 Int -> B q2 Int -> B (Union q1 q2) Int
x  = undefined
xs = \a -> \b -> Sym X :$ Spine a :$ Spine b

--------------------------------------------------------------------------------
-- Fin.
