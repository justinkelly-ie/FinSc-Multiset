module Stage0.BoxNat

import Data.Nat
import Data.Linear
import Data.Fuel
import Stage0.Interfaces
import public Stage0.Multiset
import public Stage0.BoxInt

%default total

------------------------------------------------------------------------
-- 1. BOXNAT UNBOXED SCALAR RECORD
------------------------------------------------------------------------

||| A Box Natural represents discrete non-negative counts, particle numbers,
||| and structural dimensions in Wildberger's Box Arithmetic.
public export
record BoxNat where
  constructor MkBoxNat
  value : Nat

||| Extracts raw underlying Nat term from boxed representation in O(1) time.
%inline public export
unwrapBoxNat : BoxNat -> Nat
unwrapBoxNat (MkBoxNat v) = v

||| O(1) projection to Nat.
%inline public export
boxNatToNat : BoxNat -> Nat
boxNatToNat (MkBoxNat v) = v

||| O(1) constructor lifting Nat into BoxNat.
%inline public export
natToBoxNat : Nat -> BoxNat
natToBoxNat n = MkBoxNat n

||| Converts a BoxNat to a signed BoxInt.
%inline public export
boxNatToBoxInt : BoxNat -> BoxInt
boxNatToBoxInt (MkBoxNat n) = natToBoxInt n

||| Converts a non-negative BoxInt to a BoxNat.
public export
boxIntToBoxNat : BoxInt -> BoxNat
boxIntToBoxNat (MkBoxInt v) =
  if v <= 0 then MkBoxNat 0 else MkBoxNat (integerToNat v)

||| Converts a BoxNat directly to structural evaluation Fuel.
%inline public export
boxNatToFuel : BoxNat -> Fuel
boxNatToFuel (MkBoxNat n) = limit n

------------------------------------------------------------------------
-- 2. EXACT MONOMORPHIC ARITHMETIC OPERATORS
------------------------------------------------------------------------

%inline public export
boxNatAdd : BoxNat -> BoxNat -> BoxNat
boxNatAdd (MkBoxNat a) (MkBoxNat b) = MkBoxNat (a + b)

public export
boxNatAddLinear : (1 a : BoxNat) -> (1 b : BoxNat) -> BoxNat
boxNatAddLinear (MkBoxNat a) (MkBoxNat b) = MkBoxNat (a + b)

%inline public export
boxNatSub : BoxNat -> BoxNat -> BoxNat
boxNatSub (MkBoxNat a) (MkBoxNat b) = MkBoxNat (minus a b)

%inline public export
boxNatMul : BoxNat -> BoxNat -> BoxNat
boxNatMul (MkBoxNat a) (MkBoxNat b) = MkBoxNat (a * b)

%inline public export
normalizeBoxNat : BoxNat -> BoxNat
normalizeBoxNat bn = bn

public export
Eq BoxNat where
  (MkBoxNat a) == (MkBoxNat b) = a == b

public export
Ord BoxNat where
  compare (MkBoxNat a) (MkBoxNat b) = compare a b

public export
Show BoxNat where
  show (MkBoxNat n) = "BoxNat(" ++ show n ++ ")"

||| Computes exact integer halving (n / 2) and parity (n % 2 == 1) simultaneously
||| in a single pass of structural recursion on Nat.
||| Eliminates all GMP BigInt conversions in binary exponentiation.
public export
natHalfAndOdd : Nat -> (Nat, Bool)
natHalfAndOdd Z = (Z, False)
natHalfAndOdd (S Z) = (Z, True)
natHalfAndOdd (S (S n)) =
  let (h, odd) = natHalfAndOdd n
  in (S h, odd)

||| Constructive Euclidean division and remainder on Nat with structural fuel.
||| Returns (quotient, remainder) such that n = q * d + r with r < d.
||| When d = 0, returns (0, 0) by constructive convention.
public export
natDivMod : Nat -> Nat -> (Nat, Nat)
natDivMod _ Z = (Z, Z)
natDivMod n d = go n n Z
  where
    go : (fuel : Nat) -> Nat -> Nat -> (Nat, Nat)
    go Z rem q = (q, rem)
    go (S f) rem q =
      if rem < d
        then (q, rem)
        else go f (minus rem d) (S q)

||| BoxNat division and remainder.
public export
boxNatDivMod : BoxNat -> BoxNat -> (BoxNat, BoxNat)
boxNatDivMod (MkBoxNat n) (MkBoxNat d) =
  let (q, r) = natDivMod n d
  in (MkBoxNat q, MkBoxNat r)

||| BoxNat halving and parity.
public export
boxNatHalfAndOdd : BoxNat -> (BoxNat, Bool)
boxNatHalfAndOdd (MkBoxNat n) =
  let (h, odd) = natHalfAndOdd n
  in (MkBoxNat h, odd)

------------------------------------------------------------------------
-- 3. QTT 0 ERASED PROOFS & DEFINITIONAL INVARIANTS
------------------------------------------------------------------------

||| Zero is the left identity for BoxNat addition (reduces definitionally via Refl).
public export
0 prfBoxNatAddZeroLeft : (b : BoxNat) -> boxNatAdd (MkBoxNat 0) b = b
prfBoxNatAddZeroLeft (MkBoxNat n) = Refl

||| Zero produces 0 Nat tally.
public export
0 prfNatToBoxNatZero : boxNatToNat (natToBoxNat 0) = 0
prfNatToBoxNatZero = Refl

||| Round-trip conversion preserves Nat values definitionally without induction!
public export
0 prfBoxNatRoundTrip : (n : Nat) -> boxNatToNat (natToBoxNat n) = n
prfBoxNatRoundTrip n = Refl

------------------------------------------------------------------------
-- 4. LINEAR INSTANCES
------------------------------------------------------------------------

public export
implementation LConsumable BoxNat where
  lconsume (MkBoxNat _) = ()

public export
implementation LComonoid BoxNat where
  lcomult (MkBoxNat n) = Builtin.(#) (MkBoxNat n) (MkBoxNat n)

