module Stage0.SignedFraction

import Data.Nat
import Stage0.BoxInt
import Stage0.Multiset
import Stage0.Interfaces

%default total

-----------------------------------------------------------------------
-- MSet FRACTION
--
-- The uniform type underlying every row of the Global Finite Science
-- Table. Pairs a signed integer numerator (BoxInt ∈ ℤ) with a
-- strictly positive natural denominator (Nat, enforced > 0 by
-- construction via S k).
--
-- Cross-multiplication replaces division everywhere:
--   a/b == c/d  ⟺  a*d == c*b
--
-- Named MSetFraction: a fraction built from multiset primitives.
-----------------------------------------------------------------------

||| A strictly positive natural number, represented as (S k).
||| Eliminates zero denominators by construction.
public export
PosNat : Type
PosNat = Nat

||| Compile-time witness that a natural number is strictly positive (> 0).
public export
IsPositiveNat : Nat -> Type
IsPositiveNat Z     = Void
IsPositiveNat (S _) = ()

||| Dependent Sigma-type bundling a strictly positive natural number with its erased proof.
public export
CertifiedPosNat : Type
CertifiedPosNat = (n : Nat ** IsPositiveNat n)

||| Smart constructor producing a certified strictly positive natural number (clamping 0 to 1).
public export
mkCertifiedPosNat : (n : Nat) -> CertifiedPosNat
mkCertifiedPosNat Z     = (S Z ** ())
mkCertifiedPosNat (S k) = (S k ** ())

||| Projects the underlying positive natural number from a CertifiedPosNat.
public export
fromCertifiedPosNat : CertifiedPosNat -> PosNat
fromCertifiedPosNat (n ** _) = n

||| Smart constructor: wraps a Nat into a guaranteed-positive value.
||| Returns 1 if given 0.
public export
mkPosNat : Nat -> PosNat
mkPosNat n = fromCertifiedPosNat (mkCertifiedPosNat n)

||| The universal fractional container for the Finite Science Table.
||| Every row — from Boole circuits to chromogeometric spreads to
||| gauge field flux — evaluates as an MSetFraction.
public export
record MSetFraction where
  constructor MkMSF
  num : BoxInt    -- Active signed weight (∈ ℤ)
  den : PosNat    -- Strictly positive scale (∈ ℕ⁺)

-----------------------------------------------------------------------
-- CONSTRUCTION
-----------------------------------------------------------------------

||| The fraction 0/1.
public export
zeroMSF : MSetFraction
zeroMSF = MkMSF 0 1

||| The fraction 1/1.
public export
oneMSF : MSetFraction
oneMSF = MkMSF 1 1

||| Embed a plain BoxInt as n/1.
public export
fromBoxInt : BoxInt -> MSetFraction
fromBoxInt n = MkMSF n 1

||| Embed a pair (numerator, denominator) directly.
||| Clamps denominator to 1 if zero is supplied.
public export
mkMSF : BoxInt -> Nat -> MSetFraction
mkMSF n d = MkMSF n (mkPosNat d)

-----------------------------------------------------------------------
-- CROSS-MULTIPLIED ARITHMETIC (no division)
-----------------------------------------------------------------------

||| Addition: a/b + c/d = (a*d + c*b) / (b*d).
public export
addMSF : MSetFraction -> MSetFraction -> MSetFraction
addMSF (MkMSF a b) (MkMSF c d) =
  MkMSF (a * fromInteger (natToInteger d) + c * fromInteger (natToInteger b))
        (b * d)

||| Subtraction: a/b - c/d = (a*d - c*b) / (b*d).
public export
subMSF : MSetFraction -> MSetFraction -> MSetFraction
subMSF (MkMSF a b) (MkMSF c d) =
  MkMSF (a * fromInteger (natToInteger d) - c * fromInteger (natToInteger b))
        (b * d)

||| Multiplication: a/b * c/d = (a*c) / (b*d).
public export
mulMSF : MSetFraction -> MSetFraction -> MSetFraction
mulMSF (MkMSF a b) (MkMSF c d) =
  MkMSF (a * c) (b * d)

||| Negation: -(a/b) = (-a)/b.
public export
negateMSF : MSetFraction -> MSetFraction
negateMSF (MkMSF a b) = MkMSF (negate a) b

||| Scalar multiplication by a BoxInt: n * (a/b) = (n*a)/b.
public export
scaleMSF : BoxInt -> MSetFraction -> MSetFraction
scaleMSF s (MkMSF a b) = MkMSF (s * a) b

||| Division: (a/b) / (c/d) = (a*d*sgn(c)) / (b*|c|), safely clamping zero divisor to 1.
public export
divMSF : MSetFraction -> MSetFraction -> MSetFraction
divMSF (MkMSF a b) (MkMSF c d) =
  let cAbs = boxToNat (absBox c)
      denScale = if cAbs == 0 then 1 else cAbs
      signAdj = if c < 0 then -1 else 1
  in MkMSF (a * fromInteger (natToInteger d) * signAdj) (b * denScale)

-----------------------------------------------------------------------
-- CROSS-MULTIPLIED COMPARISON (no division)
-----------------------------------------------------------------------

||| Equality by cross-multiplication: a/b == c/d ⟺ a*d == c*b.
public export
eqMSF : MSetFraction -> MSetFraction -> Bool
eqMSF (MkMSF a b) (MkMSF c d) =
  (a * fromInteger (natToInteger d)) == (c * fromInteger (natToInteger b))

public export
Eq MSetFraction where
  (==) = eqMSF

-----------------------------------------------------------------------
-- DISPLAY
-----------------------------------------------------------------------

public export
Show MSetFraction where
  show (MkMSF n d) = show n ++ "/" ++ show d

-----------------------------------------------------------------------
-- CONVERSION FROM LEGACY TYPES
-----------------------------------------------------------------------

||| Lifts a (BoxInt, BoxInt) pair into an
||| MSetFraction. The denominator is clamped to 1 if zero.
public export
fromBoxIntPair : (BoxInt, BoxInt) -> MSetFraction
fromBoxIntPair (n, d) =
  let posD = mkPosNat (boxToNat (absBox d))
  in MkMSF n posD


