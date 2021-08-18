{-# OPTIONS_GHC -Wall #-}

module Wit where

--import Language.Diorite.Signatures
import Language.Diorite.Qualifiers
import Language.Diorite.Qualifiers.Witness

import Data.Proxy (Proxy(..))
import Data.Type.Equality ((:~:)(..))
--import Data.Typeable (Typeable)

--------------------------------------------------------------------------------
-- * ...
--------------------------------------------------------------------------------

p :: P Int
p = Proxy

q :: P Bool
q = Proxy

r :: P Double
r = Proxy

a :: Q (Int ':. Bool ':. Double ':. 'None)
a = qualifier

b :: Q (Int ':. Bool ':. 'None)
b = qualifier

c :: Q (Bool ':. Double ':. 'None)
c = qualifier

d :: Q (Bool ':. 'None)
d = qualifier

--------------------------------------------------------------------------------

wit1 :: String
wit1 | Refl <- witEqRefl p q
     = "OK"
     | otherwise = "BAD!"

wit2 :: String
wit2 | Refl <- witRemOrd p q a
     , Refl <- witRemDist p a b
     = "OK"
     | otherwise = "BAD!"

wit3 :: String
wit3 | Refl <- witUniIdent a
     , Refl <- witUniAssoc a b c
     = "OK"
     | otherwise = "BAD!"

wit4 :: String
wit4 | Refl <- witElemAdd p q a Refl
     , Refl <- witElemRemove p q c Refl
     , Refl <- witElemShrink p q c Refl
     , Refl <- witElemCons p a b
     , Refl <- witElemUniRemove p q a b Refl
     , Refl <- witElemUniCons p q a b Refl
     , Refl <- witElemUni p a c Refl
     , Refl <- witElemUniRefl p a c
     = "OK"
     | otherwise = "BAD!"

wit5 :: String
wit5 | Refl <- witSubElem p a a Refl
     , Refl <- witSubRem p a a Refl
     , Refl <- witSubAdd r b a Refl
     , Refl <- witSubRemove p a a Refl
     , Refl <- witSubRemove' p c a Refl
     , Refl <- witSubShrink p b a Refl Refl
     , Refl <- witSubIn p b a Refl Refl
     , Refl <- witSubNotIn p b c Refl Refl
     , Refl <- witSubCons p b a Refl
     , Refl <- witSubRefl a
     , Refl <- witSubUni a b
     , Refl <- witSubTrans b a a Refl Refl
     = "OK"
     | otherwise = "BAD!"

wit6 :: String
wit6 | Refl <- witExtRefl a
     , Refl <- witExtNotIn p b c Refl Refl
     , Refl <- witExtSub b a Refl
     , Refl <- witExtElem p d a Refl
     , Refl <- witExtAdd r b a Refl
     , Refl <- witExtRem r b a Refl
     , Refl <- witExtCons p b a Refl
     , Refl <- witExtShrink p b a Refl
     , Refl <- witExtIn p b a Refl Refl
     = "OK"
     | otherwise = "BAD!"

wit7 :: String
wit7 | Refl <- witEURefl b a d
     , Refl <- witEUBoth b a d c Refl Refl
     = "OK"
     | otherwise = "BAD!"

--------------------------------------------------------------------------------

wit :: IO ()
wit = do
  putStrLn wit1
  putStrLn wit2
  putStrLn wit3
  putStrLn wit4
  putStrLn wit5
  putStrLn wit6
  --putStrLn wit7

--------------------------------------------------------------------------------
-- Fin.
