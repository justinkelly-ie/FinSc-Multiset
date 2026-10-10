module Stage0.StreamPolynumber

import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.StructuralFuel
import Stage0.OnSeq.FusedStream
import Data.Nat
import Data.List

%default total

------------------------------------------------------------------------
-- 1. SPARSE STREAMING POLYNUMBER TYPES & CONSTRUCTORS
------------------------------------------------------------------------

||| A Sparse Streaming Polynumber is a deforested stream of (degree, coefficient) pairs.
||| Isomorphic to a 1D sparse Multiset: P(x) = sum_{k in Supp(P)} c_k * x^k.
||| Emits only active non-zero monomial terms, executing in O(1) registers even for degrees 137^38.
public export
0 StreamPolynumber : Type
StreamPolynumber = FusedStream (Nat, BoxInt)

||| Empty zero polynomial.
public export
streamPolyZero : StreamPolynumber
streamPolyZero = stream []

||| Constant polynomial: c * x^0.
public export
streamPolyConstant : BoxInt -> StreamPolynumber
streamPolyConstant c =
  if unwrapBox c == 0
     then stream []
     else stream [(0, c)]

||| Sparse monomial: c * x^k.
public export
streamPolyMonomial : Nat -> BoxInt -> StreamPolynumber
streamPolyMonomial deg c =
  if unwrapBox c == 0
     then stream []
     else stream [(deg, c)]

||| Builds a StreamPolynumber from a list of sparse (degree, coefficient) terms.
public export
streamPolyFromList : List (Nat, BoxInt) -> StreamPolynumber
streamPolyFromList terms =
  filterMapStream (\(d, c) => if unwrapBox c == 0 then Nothing else Just (d, c)) (stream terms)

||| Unfolds a StreamPolynumber into a list of sparse terms under structural fuel bounds.
public export
streamPolyToList : Fuel -> StreamPolynumber -> List (Nat, BoxInt)
streamPolyToList f p = runFueledStream f p

------------------------------------------------------------------------
-- 2. WILDBERGER SUPPORT STREAM EXTRACTION (RULE 04 SECTION 8)
------------------------------------------------------------------------

||| Extracts the finite active support of a sparse StreamPolynumber:
||| Supp(P) = { k in Nat | c_k /= 0 }.
||| Executes deforested in O(1) auxiliary registers without intermediate heap allocation.
public export
supportStreamPoly : StreamPolynumber -> FusedStream Nat
supportStreamPoly =
  filterMapStream (\(d, c) => if unwrapBox c == 0 then Nothing else Just d)

------------------------------------------------------------------------
-- 3. SPARSE STREAMING POLYNOMIAL ALGEBRA
------------------------------------------------------------------------

||| Scalar multiplication: alpha * P(x) = sum (alpha * c_k) x^k.
public export
streamPolyScale : BoxInt -> StreamPolynumber -> StreamPolynumber
streamPolyScale s strm =
  if unwrapBox s == 0
     then stream []
     else filterMapStream (\(d, c) =>
            let sc = mulBox s c
            in if unwrapBox sc == 0 then Nothing else Just (d, sc)) strm

||| Polynomial addition via deforested stream concatenation.
||| Monomials of like degree consolidate under evaluation or conversion.
public export
streamPolyAdd : StreamPolynumber -> StreamPolynumber -> StreamPolynumber
streamPolyAdd = appendStream

||| Standard Cauchy multiplication (convolution of monomial terms):
||| (c_a * x^a) * (c_b * x^b) = (c_a * c_b) * x^(a + b).
public export
streamPolyCauchyMul : StreamPolynumber -> StreamPolynumber -> StreamPolynumber
streamPolyCauchyMul p1 p2 =
  flatMapStream (\(d1, c1) =>
    mapStream (\(d2, c2) => (d1 + d2, mulBox c1 c2)) p2) p1

||| Wildberger Caret multiplication (multiplicative exponent algebra):
||| (c_a * x^a) ^ (c_b * x^b) = (c_a * c_b) * x^(a * b).
public export
streamPolyCaret : StreamPolynumber -> StreamPolynumber -> StreamPolynumber
streamPolyCaret p1 p2 =
  flatMapStream (\(d1, c1) =>
    mapStream (\(d2, c2) => (d1 * d2, mulBox c1 c2)) p2) p1

||| Formal discrete derivative of a sparse StreamPolynumber:
||| d/dx (sum c_k x^k) = sum_{k >= 1} (k * c_k) x^(k - 1).
||| Degree 0 constant terms drop automatically.
public export
streamPolyDeriv : StreamPolynumber -> StreamPolynumber
streamPolyDeriv = filterMapStream stepDeriv
  where
    stepDeriv : (Nat, BoxInt) -> Maybe (Nat, BoxInt)
    stepDeriv (Z, _) = Nothing
    stepDeriv (S k, c) =
      let nBox = natToBoxInt (S k)
          newCoeff = mulBox nBox c
      in if unwrapBox newCoeff == 0 then Nothing else Just (k, newCoeff)

------------------------------------------------------------------------
-- 4. DEFORESTED POLYNOMIAL EVALUATION
------------------------------------------------------------------------

||| Natural power of a BoxInt scalar.
public export
boxIntPower : BoxInt -> Nat -> BoxInt
boxIntPower _ Z = MkBoxInt 1
boxIntPower x (S k) = mulBox x (boxIntPower x k)

||| Direct deforested evaluation of a StreamPolynumber at a target coordinate x in BoxInt.
||| Evaluates P(x) = sum c_k x^k with O(1) auxiliary registers.
public export
evalStreamPolyNat : (fuel : Nat) -> BoxInt -> StreamPolynumber -> BoxInt
evalStreamPolyNat fuel x strm =
  foldStreamNat fuel (\acc, (d, c) => addBox acc (mulBox c (boxIntPower x d))) (MkBoxInt 0) strm

||| Evaluates a StreamPolynumber with explicit Fuel bound.
public export
evalStreamPolyFuel : Fuel -> BoxInt -> StreamPolynumber -> BoxInt
evalStreamPolyFuel fuel x strm =
  foldStreamFuel fuel (\acc, (d, c) => addBox acc (mulBox c (boxIntPower x d))) (MkBoxInt 0) strm

||| Evaluates a StreamPolynumber bounded by Master Substrate Primorial 210 Goh capacity.
public export
evalStreamPolyGoh : BoxInt -> StreamPolynumber -> BoxInt
evalStreamPolyGoh x strm =
  evalStreamPolyNat (boxNatToNat masterSubstrateGohFuel) x strm

------------------------------------------------------------------------
-- 5. COMPILE-TIME INVARIANT AUDITS (RULE 01)
------------------------------------------------------------------------

||| Verifies formal discrete derivative: d/dx (3 x^2 + 5 x + 7) = 6 x + 5.
public export
auditStreamPolyDerivProof : Bool
auditStreamPolyDerivProof =
  let p = streamPolyFromList [(2, MkBoxInt 3), (1, MkBoxInt 5), (0, MkBoxInt 7)]
      dp = streamPolyDeriv p
      res = streamPolyToList (limit 10) dp
  in res == [(1, MkBoxInt 6), (0, MkBoxInt 5)]

||| Verifies Wildberger Caret algebra: (x^2) ^ (x^3) = x^6.
public export
auditStreamPolyCaretProof : Bool
auditStreamPolyCaretProof =
  let p1 = streamPolyMonomial 2 (MkBoxInt 1)
      p2 = streamPolyMonomial 3 (MkBoxInt 1)
      pCaret = streamPolyCaret p1 p2
      res = streamPolyToList (limit 5) pCaret
  in res == [(6, MkBoxInt 1)]

||| Verifies Cauchy convolution and evaluation: (x + 2) * (x + 3) evaluated at x = 4 is 42.
public export
auditStreamPolyCauchyProof : Bool
auditStreamPolyCauchyProof =
  let p1 = streamPolyFromList [(1, MkBoxInt 1), (0, MkBoxInt 2)]
      p2 = streamPolyFromList [(1, MkBoxInt 1), (0, MkBoxInt 3)]
      prod = streamPolyCauchyMul p1 p2
      val = evalStreamPolyGoh (MkBoxInt 4) prod
  in boxEq val (MkBoxInt 42)

||| Verifies sparse representation at Eddington Observer Epoch degree k = 38:
||| M_38 = x^38, support is {38}, derivative has support {37} and coeff 38,
||| executing in O(1) registers without allocating 38 zero coefficients.
public export
auditStreamPolyEddingtonScaleProof : Bool
auditStreamPolyEddingtonScaleProof =
  let m38 = streamPolyMonomial 38 (MkBoxInt 1)
      supp = runFueledStream (limit 5) (supportStreamPoly m38)
      dm38 = streamPolyDeriv m38
      dTerms = streamPolyToList (limit 5) dm38
  in supp == [38] && dTerms == [(37, MkBoxInt 38)]
