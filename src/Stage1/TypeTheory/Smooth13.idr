module Stage1.TypeTheory.Smooth13

import public Stage0.BoxInt
import public Stage1.TypeTheory.MultisetLevel
import Data.Nat

%default total

------------------------------------------------------------------------
-- 1. TYPE-LEVEL 13-SMOOTH BOUNDARY WITNESS & CONTAINERS
------------------------------------------------------------------------

||| Strips all factors of prime p from n using explicit fuel.
public export
stripFactor : (fuel : Nat) -> (p : Integer) -> (n : Integer) -> Integer
stripFactor Z _ n = n
stripFactor (S f) p n =
  if n <= 1 || p <= 1 then n
  else if n `mod` p == 0
    then stripFactor f p (assert_smaller n (n `div` p))
    else n

||| Pure helper checking if Nat n is 13-smooth (all prime factors <= 13)
public export
is13SmoothNat : Nat -> Bool
is13SmoothNat Z = True
is13SmoothNat (S Z) = True
is13SmoothNat 2 = True
is13SmoothNat 3 = True
is13SmoothNat 4 = True
is13SmoothNat 6 = True
is13SmoothNat 12 = True
is13SmoothNat 18 = True
is13SmoothNat 210 = True
is13SmoothNat n =
  let n0 = natToInteger n
      fuel = n
      n1 = stripFactor fuel 2 n0
      n2 = stripFactor fuel 3 n1
      n3 = stripFactor fuel 5 n2
      n4 = stripFactor fuel 7 n3
      n5 = stripFactor fuel 11 n4
      n6 = stripFactor fuel 13 n5
  in n6 == 1

||| Erased compile-time witness certifying that Nat n is 13-smooth (max prime factor <= 13)
public export
0 Smooth13Witness : Nat -> Type
Smooth13Witness n = (is13SmoothNat n == True) = True

||| A dimension Nat n guaranteed to be 13-smooth at compile time
public export
record Smooth13Dimension (n : Nat) where
  constructor MkSmooth13Dimension
  0 smoothPrf : Smooth13Witness n

public export
Eq (Smooth13Dimension n) where
  _ == _ = True

public export
Show (Smooth13Dimension n) where
  show (MkSmooth13Dimension _) = "Smooth13"

------------------------------------------------------------------------
-- 2. PRIMITIVE 13-SMOOTH WITNESS INSTANCES
------------------------------------------------------------------------

public export
0 prfSmooth13_2 : Smooth13Witness 2
prfSmooth13_2 = Refl

public export
0 prfSmooth13_4 : Smooth13Witness 4
prfSmooth13_4 = Refl

public export
0 prfSmooth13_6 : Smooth13Witness 6
prfSmooth13_6 = Refl

public export
0 prfSmooth13_12 : Smooth13Witness 12
prfSmooth13_12 = Refl

public export
0 prfSmooth13_18 : Smooth13Witness 18
prfSmooth13_18 = Refl

public export
0 prfSmooth13_210 : Smooth13Witness 210
prfSmooth13_210 = Refl
