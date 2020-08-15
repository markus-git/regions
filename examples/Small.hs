module Small where

import Language.Diorite

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

