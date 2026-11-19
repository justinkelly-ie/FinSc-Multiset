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
  if boxIsZero c
     then stream []
     else stream [(0, c)]

||| Sparse monomial: c * x^k.
public export
streamPolyMonomial : Nat -> BoxInt -> StreamPolynumber
streamPolyMonomial deg c =
  if boxIsZero c
     then stream []
     else stream [(deg, c)]

||| Builds a StreamPolynumber from a list of sparse (degree, coefficient) terms.
public export
streamPolyFromList : List (Nat, BoxInt) -> StreamPolynumber
streamPolyFromList terms =
  filterMapStream (\(d, c) => if boxIsZero c then Nothing else Just (d, c)) (stream terms)

||| Unfolds a StreamPolynumber into a list of sparse terms with Nat fuel.
public export
streamPolyToListNat : (fuel : Nat) -> StreamPolynumber -> List (Nat, BoxInt)
streamPolyToListNat fuel p = runFueledStreamNat fuel p

||| Unfolds a StreamPolynumber into a list of sparse terms with model-indexed GohFuel.
public export
streamPolyToListFuelModel : GohFuel cap -> StreamPolynumber -> List (Nat, BoxInt)
streamPolyToListFuelModel fuel = streamPolyToListNat (gohSteps fuel)

------------------------------------------------------------------------
-- 2. WILDBERGER SUPPORT STREAM EXTRACTION (RULE 04 SECTION 8)
------------------------------------------------------------------------

||| Extracts the finite active support of a sparse StreamPolynumber:
||| Supp(P) = { k in Nat | c_k /= 0 }.
||| Executes deforested in O(1) auxiliary registers without intermediate heap allocation.
public export
supportStreamPoly : StreamPolynumber -> FusedStream Nat
supportStreamPoly =
  filterMapStream (\(d, c) => if boxIsZero c then Nothing else Just d)

------------------------------------------------------------------------
-- 3. SPARSE STREAMING POLYNOMIAL ALGEBRA
------------------------------------------------------------------------

||| Scalar multiplication: alpha * P(x) = sum (alpha * c_k) x^k.
public export
streamPolyScale : BoxInt -> StreamPolynumber -> StreamPolynumber
streamPolyScale s strm =
  if boxIsZero s
     then stream []
     else filterMapStream (\(d, c) =>
            let sc = mulBox s c
            in if boxIsZero sc then Nothing else Just (d, sc)) strm

||| Polynomial addition via deforested stream concatenation.
||| Monomials of like degree consolidate under evaluation or conversion.
public export
streamPolyAdd : StreamPolynumber -> StreamPolynumber -> StreamPolynumber
streamPolyAdd = appendStream

||| Polynomial subtraction via deforested scaled stream concatenation: P1 - P2 = P1 + (-1) * P2.
public export
streamPolySub : StreamPolynumber -> StreamPolynumber -> StreamPolynumber
streamPolySub p1 p2 = streamPolyAdd p1 (streamPolyScale (intToBoxInt (-1)) p2)

||| Deforested monomial degree shift: x^k * P(x) = sum c_i * x^(i + k).
||| Executes in O(1) auxiliary registers without allocating polynomial terms.
public export
streamPolyShiftDegree : (shift : Nat) -> StreamPolynumber -> StreamPolynumber
streamPolyShiftDegree Z p = p
streamPolyShiftDegree k p = mapStream (\(d, c) => (d + k, c)) p

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
      in if boxIsZero newCoeff then Nothing else Just (k, newCoeff)

------------------------------------------------------------------------
-- 4. DEFORESTED POLYNOMIAL EVALUATION
------------------------------------------------------------------------

||| Natural power of a BoxInt scalar.
public export
boxIntPower : BoxInt -> Nat -> BoxInt
boxIntPower _ Z = MkBoxInt 1
boxIntPower x (S k) = mulBox x (boxIntPower x k)

||| Fast O(log d) binary exponentiation of a BoxInt scalar with structural fuel (Rule 04 §2).
public export
fastBoxIntPowerFuel : (fuel : Nat) -> BoxInt -> Nat -> BoxInt
fastBoxIntPowerFuel Z _ _ = MkBoxInt 1
fastBoxIntPowerFuel (S _) _ Z = MkBoxInt 1
fastBoxIntPowerFuel (S _) x (S Z) = x
fastBoxIntPowerFuel (S f) x d =
  let (half, isOdd) = natHalfAndOdd d
      halfPow = fastBoxIntPowerFuel f x half
      sqPow   = mulBox halfPow halfPow
  in if isOdd then mulBox x sqPow else sqPow

||| Fast O(log d) binary exponentiation of a BoxInt scalar bounded by model-derived Goh fuel.
public export
fastBoxIntPower : BoxInt -> Nat -> BoxInt
fastBoxIntPower x d = fastBoxIntPowerFuel (gohSteps (gohFuelForCapacity d)) x d

||| Direct deforested evaluation of a StreamPolynumber at a target coordinate x in BoxInt.
||| Evaluates P(x) = sum c_k x^k with O(1) auxiliary registers and degree 0/1 fast paths.
public export
evalStreamPolyNat : (fuel : Nat) -> BoxInt -> StreamPolynumber -> BoxInt
evalStreamPolyNat fuel x strm =
  foldStreamNat fuel
    (\acc, (d, c) =>
      case d of
        Z     => acc + c
        (S Z) => acc + (c * x)
        _     => acc + (c * fastBoxIntPower x d))
    (MkBoxInt 0)
    strm

||| Evaluates a StreamPolynumber bounded by Master Substrate Primorial 210 Goh capacity.
public export
evalStreamPolyGoh : BoxInt -> StreamPolynumber -> BoxInt
evalStreamPolyGoh x strm =
  evalStreamPolyNat (boxNatToNat masterSubstrateGohFuel) x strm

------------------------------------------------------------------------
-- 4B. BIVARIATE STREAMING INTEGER POLYNUMBER & GOH FUEL EXTRACTION
------------------------------------------------------------------------

||| A Deforested Bivariate Streaming Integer Polynumber:
||| P(alpha, beta) = sum_{(i, j) in Supp(P)} c_{i,j} * alpha^i * beta^j.
||| Streams active ((alphaDeg, betaDeg), coeff) terms in O(1) auxiliary registers without List-backed RLE.
public export
0 StreamIntPolynumber : Type
StreamIntPolynumber = FusedStream ((Nat, Nat), BoxInt)

||| Empty zero bivariate StreamIntPolynumber.
public export
streamIntPolyZero : StreamIntPolynumber
streamIntPolyZero = stream []

||| Constant bivariate StreamIntPolynumber: c * alpha^0 * beta^0.
public export
streamIntPolyConstant : BoxInt -> StreamIntPolynumber
streamIntPolyConstant c =
  if boxIsZero c then stream [] else stream [((0, 0), c)]

||| Sparse bivariate monomial: c * alpha^i * beta^j.
public export
streamIntPolyMonomial : Nat -> Nat -> BoxInt -> StreamIntPolynumber
streamIntPolyMonomial da db c =
  if boxIsZero c then stream [] else stream [((da, db), c)]

||| Builds a StreamIntPolynumber from a sparse list of ((degAlpha, degBeta), coeff) terms.
public export
streamIntPolyFromList : List ((Nat, Nat), BoxInt) -> StreamIntPolynumber
streamIntPolyFromList terms =
  filterMapStream (\t@(_, c) => if boxIsZero c then Nothing else Just t) (stream terms)

||| Extracts the active exponent-pair support { (i, j) | c_{i,j} /= 0 } as a FusedStream.
public export
supportStreamIntPoly : StreamIntPolynumber -> FusedStream (Nat, Nat)
supportStreamIntPoly =
  filterMapStream (\(degs, c) => if boxIsZero c then Nothing else Just degs)

||| Scales a StreamIntPolynumber by a BoxInt scalar in O(1) registers.
public export
streamIntPolyScale : BoxInt -> StreamIntPolynumber -> StreamIntPolynumber
streamIntPolyScale s strm =
  if boxIsZero s
     then stream []
     else filterMapStream (\(degs, c) =>
            let sc = s * c
            in if boxIsZero sc then Nothing else Just (degs, sc)) strm

||| Addition of bivariate StreamIntPolynumbers via deforested stream concatenation.
public export
streamIntPolyAdd : StreamIntPolynumber -> StreamIntPolynumber -> StreamIntPolynumber
streamIntPolyAdd = appendStream

||| Subtraction of bivariate StreamIntPolynumbers: P1 - P2 = P1 + (-1) * P2.
public export
streamIntPolySub : StreamIntPolynumber -> StreamIntPolynumber -> StreamIntPolynumber
streamIntPolySub p1 p2 = streamIntPolyAdd p1 (streamIntPolyScale (intToBoxInt (-1)) p2)

||| Cauchy convolution multiplication of two bivariate StreamIntPolynumbers.
public export
streamIntPolyCauchyMul : StreamIntPolynumber -> StreamIntPolynumber -> StreamIntPolynumber
streamIntPolyCauchyMul p1 p2 =
  flatMapStream (\((a1, b1), c1) =>
    mapStream (\((a2, b2), c2) => ((a1 + a2, b1 + b2), c1 * c2)) p2) p1

||| Direct deforested evaluation of P(alpha, beta) bounded by Nat fuel.
public export
evalStreamIntPolyNat : (fuel : Nat) -> BoxInt -> BoxInt -> StreamIntPolynumber -> BoxInt
evalStreamIntPolyNat fuel alpha beta strm =
  foldStreamNat fuel
    (\acc, ((da, db), c) =>
      let pa = case da of { Z => MkBoxInt 1; (S Z) => alpha; _ => fastBoxIntPower alpha da }
          pb = case db of { Z => MkBoxInt 1; (S Z) => beta;  _ => fastBoxIntPower beta db }
      in acc + (c * pa * pb))
    (MkBoxInt 0)
    strm

||| Evaluates a StreamIntPolynumber bounded by Master Substrate Primorial 210 GohFuel.
public export
evalStreamIntPolyGoh : BoxInt -> BoxInt -> StreamIntPolynumber -> BoxInt
evalStreamIntPolyGoh alpha beta = evalStreamIntPolyNat (gohSteps masterSubstrateGohFuelModel) alpha beta

||| Summary invariants extracted in a single deforested fold over a streaming integer polynumber:
||| - `supportCardinality`: active non-zero term count `P_supp(1)`
||| - `totalAbsMass`: sum of absolute multiplicities `sum |c|`
||| - `maxDegree`: maximum total exponent (`d` univariate, `d_a + d_b` bivariate)
||| - `maxAxisIndex`: maximum single-axis index (`max d` or `max d_a d_b`)
public export
record PolySupportSummary where
  constructor MkPolySupportSummary
  supportCardinality : Nat
  totalAbsMass       : Nat
  maxDegree          : Nat
  maxAxisIndex       : Nat

public export
Eq PolySupportSummary where
  s1 == s2 =
    s1.supportCardinality == s2.supportCardinality &&
    s1.totalAbsMass == s2.totalAbsMass &&
    s1.maxDegree == s2.maxDegree &&
    s1.maxAxisIndex == s2.maxAxisIndex

public export
Show PolySupportSummary where
  show s = "PolySupportSummary(supp=" ++ show s.supportCardinality ++
           ", mass=" ++ show s.totalAbsMass ++
           ", maxDeg=" ++ show s.maxDegree ++
           ", maxAxis=" ++ show s.maxAxisIndex ++ ")"

||| Single-pass deforested invariant summary of a univariate StreamPolynumber.
public export
summarizeStreamPolyNat : (stepBound : Nat) -> StreamPolynumber -> PolySupportSummary
summarizeStreamPolyNat stepBound =
  foldStreamNat stepBound
    (\acc, (d, c) =>
      if boxIsZero c then acc
      else MkPolySupportSummary
             (S acc.supportCardinality)
             (acc.totalAbsMass + boxToNat (absBox c))
             (fuelMax d acc.maxDegree)
             (fuelMax d acc.maxAxisIndex))
    (MkPolySupportSummary Z Z Z Z)

||| Single-pass deforested invariant summary of a bivariate StreamIntPolynumber.
public export
summarizeStreamIntPolyNat : (stepBound : Nat) -> StreamIntPolynumber -> PolySupportSummary
summarizeStreamIntPolyNat stepBound =
  foldStreamNat stepBound
    (\acc, ((da, db), c) =>
      if boxIsZero c then acc
      else MkPolySupportSummary
             (S acc.supportCardinality)
             (acc.totalAbsMass + boxToNat (absBox c))
             (fuelMax (da + db) acc.maxDegree)
             (fuelMax (fuelMax da db) acc.maxAxisIndex))
    (MkPolySupportSummary Z Z Z Z)

||| Derives existential `GohFuel` capacity from a univariate StreamPolynumber's support cardinality.
public export
streamPolyToGohFuel : (stepBound : Nat) -> StreamPolynumber -> AnyGohFuel
streamPolyToGohFuel stepBound p =
  anyGohFuel (summarizeStreamPolyNat stepBound p).supportCardinality

||| Derives existential `GohFuel` capacity from a bivariate StreamIntPolynumber's support cardinality.
public export
streamIntPolyToGohFuel : (stepBound : Nat) -> StreamIntPolynumber -> AnyGohFuel
streamIntPolyToGohFuel stepBound p =
  anyGohFuel (summarizeStreamIntPolyNat stepBound p).supportCardinality

||| Derives existential `GohFuel` for dense/NTT finite span `(S maxDegree)` from a StreamIntPolynumber.
public export
streamIntPolySpanGohFuel : (stepBound : Nat) -> StreamIntPolynumber -> AnyGohFuel
streamIntPolySpanGohFuel stepBound p =
  let summ = summarizeStreamIntPolyNat stepBound p
  in if summ.supportCardinality == Z
        then anyGohFuel Z
        else anyGohFuel (S summ.maxDegree)

||| Packages a StreamPolynumber together with its derived GohFuel capacity and Skip headroom
||| into an AnyFueledFiniteStream ready for Skip-safe fueled finite stream folds.
public export
streamPolyToFueledFinite : (srcStepBound : Nat) -> StreamPolynumber -> AnyFueledFiniteStream (Nat, BoxInt)
streamPolyToFueledFinite srcStepBound strm =
  let summ  = summarizeStreamPolyNat srcStepBound strm
      cap   = summ.supportCardinality
      slack = if srcStepBound > cap then minus srcStepBound cap else 2
  in MkAnyFueledFiniteStream cap (mkFueledFiniteStreamWithSkips (gohFuelForCapacity cap) slack strm)

||| Packages a bivariate StreamIntPolynumber with its derived GohFuel capacity and Skip headroom.
public export
streamIntPolyToFueledFinite : (srcStepBound : Nat) -> StreamIntPolynumber -> AnyFueledFiniteStream ((Nat, Nat), BoxInt)
streamIntPolyToFueledFinite srcStepBound strm =
  let summ  = summarizeStreamIntPolyNat srcStepBound strm
      cap   = summ.supportCardinality
      slack = if srcStepBound > cap then minus srcStepBound cap else 2
  in MkAnyFueledFiniteStream cap (mkFueledFiniteStreamWithSkips (gohFuelForCapacity cap) slack strm)

------------------------------------------------------------------------
-- 5. COMPILE-TIME INVARIANT AUDITS (RULE 01)
------------------------------------------------------------------------

||| Verifies formal discrete derivative: d/dx (3 x^2 + 5 x + 7) = 6 x + 5.
public export
auditStreamPolyDerivProof : Bool
auditStreamPolyDerivProof =
  let p = streamPolyFromList [(2, MkBoxInt 3), (1, MkBoxInt 5), (0, MkBoxInt 7)]
      dp = streamPolyDeriv p
      res = streamPolyToListNat 10 dp
  in res == [(1, MkBoxInt 6), (0, MkBoxInt 5)]

||| Verifies Wildberger Caret algebra: (x^2) ^ (x^3) = x^6.
public export
auditStreamPolyCaretProof : Bool
auditStreamPolyCaretProof =
  let p1 = streamPolyMonomial 2 (MkBoxInt 1)
      p2 = streamPolyMonomial 3 (MkBoxInt 1)
      pCaret = streamPolyCaret p1 p2
      res = streamPolyToListNat 5 pCaret
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
      supp = runFueledStreamNat 5 (supportStreamPoly m38)
      dm38 = streamPolyDeriv m38
      dTerms = streamPolyToListNat 5 dm38
  in supp == [38] && dTerms == [(37, MkBoxInt 38)]

||| Verifies deforested monomial degree shift: (3 x^2 + 5 x + 7) * x = 3 x^3 + 5 x^2 + 7 x.
public export
auditStreamPolyShiftDegreeProof : Bool
auditStreamPolyShiftDegreeProof =
  let p = streamPolyFromList [(2, MkBoxInt 3), (1, MkBoxInt 5), (0, MkBoxInt 7)]
      pShifted = streamPolyShiftDegree 1 p
      res = streamPolyToListNat 10 pShifted
  in res == [(3, MkBoxInt 3), (2, MkBoxInt 5), (1, MkBoxInt 7)]
