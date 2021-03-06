-- Idris 2

data Name : Type where
     UN : String -> Name -- user written name
     MN : String -> Int -> Name -- machine generated name

-- In the term representation, we represent local variables as an index into
-- a list of bound names:
data IsVar : Name -> Nat -> List Name -> Type where
     First : IsVar n Z (n :: ns)
     Later : IsVar n i ns -> IsVar n (S i) (m :: ns)

-- And, sometimes, it's convenient to manipulate variables separately.
-- Note the erasure properties of the following definition (it is just a Nat
-- at run time)
data Var : List Name -> Type where
     MkVar : {i : Nat} -> (0 p : IsVar n i vars) -> Var vars

-- 1. Remove all references to the most recently bound variable
dropFirst : List (Var (v :: vs)) -> List (Var vs)
dropFirst [] = []
dropFirst (x :: xs)
    = do x' <- ?something
         xs' <- dropFirst xs
         ?idkMan

--dropFirst (x :: xs) = case x of
--                           (MkVar First) => ?dropfirst_rhs1_2
--                           (MkVar (Later y)) => ?dropfirst_rhs1_3
--dropFirst ((MkVar First) :: xs) = ?dropFirst_rhs_4
--dropFirst ((MkVar (Later x)) :: xs) = ?dropFirst_rhs_5


-- 2. Add a reference to a variable in the middle of a scope - we'll need 
-- something like this later.
-- Note: The type here isn't quite right, you'll need to modify it slightly.
insertName : {outer, inner : List Name} -> Var (outer ++ inner) -> Var (outer ++ n :: inner)
insertName {outer = []} {inner = []} (MkVar p) = MkVar First  -- not convinced this is right...
insertName {outer = []} {inner = is} (MkVar p) = ?insertName_rhs_2
insertName {outer = os} {inner = []} (MkVar p) = ?insertName_rhs_3
insertName {outer = os} {inner = is} (MkVar p) = ?insertName_rhs_4

-- what I want to do:
--insertName {outer = []} {inner = is} (MkVar p) = (MkVar First) :: is
--insertName {outer = os} {inner = []} (MkVar p) = os :: (MkVar First)
--insertName {outer = os} {inner = is} (MkVar p) = ?vodoo

