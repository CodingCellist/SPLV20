-- Idris 2

import Decidable.Equality

-- This is the (simplified) definition of names in Core.TT
data Name : Type where
     UN : String -> Name -- user written name
     MN : String -> Int -> Name -- machine generated name

-- 1. Write an Eq instance for Name
-- (sorry, it's not derivable yet!)
Eq Name where
  (UN x) == (UN y)      = x == y
  (MN x i) == (MN y j)  = x == y && i == j
  _ == _                = False

-- 2. Sometimes, we need to compare names for equality and use a proof that
-- they're equal. So, implement the following 
nameEq : (x : Name) -> (y : Name) -> Maybe (x = y)
nameEq (UN x) (UN y) with (decEq x y)
  nameEq (UN y) (UN y) | (Yes Refl) = Just Refl
  nameEq (UN x) (UN y) | (No _) = Nothing
nameEq (MN x i) (MN y j) with (decEq x y)
  nameEq (MN x i) (MN y j) | (No _) = Nothing
  nameEq (MN y i) (MN y j) | (Yes Refl) with (decEq i j)
    nameEq (MN y i) (MN y i) | (Yes Refl) | (Yes Refl) = Just Refl
    nameEq (MN y i) (MN y j) | (Yes Refl) | (No _) = Nothing
nameEq _ _ = Nothing


unContraHelper : (x = y -> Void) -> UN x = UN y -> Void

-- 3. (Optional, since we don't need this in Idris 2, but it's a good
-- exercise to see if you can do it!) Implement decidable equality, so you
-- also have a proof if names are *not* equal.
DecEq Name where
  decEq (UN x) (UN y) with (decEq x y)
    decEq (UN x) (UN x) | Yes Refl = Yes Refl
    decEq (UN x) (UN y) | No xyContra = No (unContraHelper xyContra)
  decEq (MN x z) (MN y w) with (decEq x y)
    decEq (MN x i) (MN y j) | (No xyContra) = No ?hole1
    decEq (MN y i) (MN y j) | (Yes Refl) with (decEq i j)
      decEq (MN y i) (MN y i) | (Yes Refl) | (Yes Refl) = Yes Refl
      decEq (MN y i) (MN y j) | (Yes Refl) | (No ijContra) = No ?hole2
  decEq _ _ = No ?decEq_rhs_7
