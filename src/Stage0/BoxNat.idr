module Stage0.BoxNat

import Data.Nat
import Data.Linear
import Data.Fuel
import Stage0.Interfaces
import public Stage0.Multiset
import public Stage0.BoxInt

%default total

------------------------------------------------------------------------
-- 1. BOXNAT RLE TALLY MULTISET
------------------------------------------------------------------------

||| A Box Arithmetic Natural Multiset (BoxNat)
||| Parameterized over discrete Nat counts with unit element ()
public export
BoxNat : Type
BoxNat = Multiset Nat ()

||| Computes the total Nat tally of a BoxNat.
public export
boxNatToNat : BoxNat -> Nat
boxNatToNat ZeroM = 0
boxNatToNat (AddM () c xs) = c + boxNatToNat xs

||| Creates a BoxNat from a Nat.
public export
natToBoxNat : Nat -> BoxNat
natToBoxNat Z = ZeroM
natToBoxNat n = AddM () n ZeroM

||| Converts a BoxNat to a signed BoxInt.
public export
boxNatToBoxInt : BoxNat -> BoxInt
boxNatToBoxInt bn = natToBoxInt (boxNatToNat bn)

||| Converts a non-negative BoxInt to a BoxNat.
public export
boxIntToBoxNat : BoxInt -> BoxNat
boxIntToBoxNat (MkBoxInt v) =
  if v <= 0 then ZeroM else natToBoxNat (integerToNat v)

||| Converts a BoxNat tally into structural evaluation Fuel.
public export
boxNatToFuel : BoxNat -> Fuel
boxNatToFuel bn = limit (boxNatToNat bn)

------------------------------------------------------------------------
-- 2. EXACT CONSTRUCTIVE ARITHMETIC OPERATORS
------------------------------------------------------------------------

||| Adds two BoxNat multisets (lazy structural merge).
public export
boxNatAdd : BoxNat -> BoxNat -> BoxNat
boxNatAdd xs ys = addMultiset xs ys

||| Linear BoxNat addition preserving QTT multiplicity.
public export
boxNatAddLinear : (1 a : BoxNat) -> (1 b : BoxNat) -> BoxNat
boxNatAddLinear a b = laddMultiset a b

||| Subtraction of BoxNat with truncation at zero.
public export
boxNatSub : BoxNat -> BoxNat -> BoxNat
boxNatSub a b =
  let na = boxNatToNat a
      nb = boxNatToNat b
  in natToBoxNat (minus na nb)

||| Multiplication of BoxNat values.
public export
boxNatMul : BoxNat -> BoxNat -> BoxNat
boxNatMul a b =
  let na = boxNatToNat a
      nb = boxNatToNat b
  in natToBoxNat (na * nb)

||| Normalizes a BoxNat by coalescing duplicate () counts into a single RLE node.
public export
normalizeBoxNat : BoxNat -> BoxNat
normalizeBoxNat xs =
  let totalCount = boxNatToNat xs
  in natToBoxNat totalCount

public export
Eq BoxNat where
  xs == ys = boxNatToNat xs == boxNatToNat ys

public export
Ord BoxNat where
  compare xs ys = compare (boxNatToNat xs) (boxNatToNat ys)

public export
Show BoxNat where
  show xs = "BoxNat(" ++ show (boxNatToNat xs) ++ ")"

------------------------------------------------------------------------
-- 3. QTT 0 ERASED PROOFS & INVARIANTS
------------------------------------------------------------------------

||| Zero is the left identity for BoxNat addition.
public export
0 prfBoxNatAddZeroLeft : (b : BoxNat) -> boxNatAdd ZeroM b = b
prfBoxNatAddZeroLeft _ = Refl

||| Zero produces 0 Nat tally.
public export
0 prfNatToBoxNatZero : boxNatToNat (natToBoxNat 0) = 0
prfNatToBoxNatZero = Refl

||| Round-trip conversion preserves Nat values.
public export
0 prfBoxNatRoundTrip : (n : Nat) -> boxNatToNat (natToBoxNat n) = n
prfBoxNatRoundTrip Z = Refl
prfBoxNatRoundTrip (S k) = plusZeroRightNeutral (S k)

-----------------------------------------------------------------------
-- 4. LINEAR INSTANCES
-----------------------------------------------------------------------

||| Linear BoxNat Consumption
public export
implementation LConsumable BoxNat where
  lconsume = consumeMultiset

||| Linear BoxNat Duplication
public export
implementation LComonoid BoxNat where
  lcomult ZeroM = Builtin.(#) ZeroM ZeroM
  lcomult (AddM () c rest) =
    let Builtin.(#) r1 r2 = lcomult rest
    in Builtin.(#) (AddM () c r1) (AddM () c r2)
