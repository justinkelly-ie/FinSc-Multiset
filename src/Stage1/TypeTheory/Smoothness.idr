module Stage1.TypeTheory.Smoothness

import public Stage0.BoxInt
import public Stage0.PrimeMultiset
import public Stage0.OnSeq.FusedStream
import public Stage1.TypeTheory.MultisetLevel
import Data.Nat
import Data.List

%default total

------------------------------------------------------------------------
-- 1. CONSTRUCTIVE PRIME GENERATION UNDER BOUND
------------------------------------------------------------------------

||| Deterministic primality trial candidate with explicit fuel.
public export
isPrimeCandidate : (fuel : Nat) -> (d : Integer) -> (n : Integer) -> Bool
isPrimeCandidate Z _ _ = False
isPrimeCandidate (S f) d n =
  if d * d > n then True
  else if n `mod` d == 0 then False
  else isPrimeCandidate f (d + 1) n

||| Generates primes up to a given limit using structural fuel.
public export
primesUpToCandidate : (fuel : Nat) -> (curr : Integer) -> (limit : Integer) -> List Integer
primesUpToCandidate Z _ _ = []
primesUpToCandidate (S f) curr limit =
  if curr > limit then []
  else if isPrimeCandidate (integerToNat limit) 2 curr
       then curr :: primesUpToCandidate f (curr + 1) limit
       else primesUpToCandidate f (curr + 1) limit

||| Dynamic constructivist primes strictly bounded by natural bound.
public export
primesUnderBound : (bound : Nat) -> List Integer
primesUnderBound bound =
  let lim = cast {to = Integer} bound
  in primesUpToCandidate (S bound) 2 lim

------------------------------------------------------------------------
-- 1B. DEFORESTED STREAMING OF PRIMES (Zero Intermediate Heap Allocations)
------------------------------------------------------------------------

||| Generates a deforested stream of natural numbers in range [start, limit].
public export
streamRange : (start : Nat) -> (limit : Nat) -> FusedStream Nat
streamRange start limit = unfoldStream next start
  where
    next : Nat -> Step Nat Nat
    next curr =
      if curr > limit then Done
      else Yield curr (S curr)

||| Generates primes up to a given bound as a deforested stream without intermediate List allocation.
public export
streamPrimesUnderBound : (bound : Nat) -> FusedStream Nat
streamPrimesUnderBound bound =
  filterStream (\p => isPrimeCandidate bound 2 (cast {to = Integer} p)) (streamRange 2 bound)

------------------------------------------------------------------------
-- 2. GENERIC SMOOTHNESS TRANSFORMATION & WITNESSES
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

||| Strips a list of prime factors sequentially from n.
public export
stripPrimeFactors : (fuel : Nat) -> List Integer -> Integer -> Integer
stripPrimeFactors _ [] n = n
stripPrimeFactors fuel (p :: ps) n =
  stripPrimeFactors fuel ps (stripFactor fuel p n)

||| Generic smoothness predicate parameterized by upper prime bound.
public export
isSmoothNat : (bound : Nat) -> (n : Nat) -> Bool
isSmoothNat _ Z = True
isSmoothNat _ (S Z) = True
isSmoothNat bound n =
  let n0 = natToInteger n
      fuel = n
      remVal = stripPrimeFactors fuel (primesUnderBound bound) n0
  in remVal == 1

||| Type-level witness certifying that Nat n is smooth up to prime bound.
public export
SmoothWitness : (bound : Nat) -> (n : Nat) -> Type
SmoothWitness bound n = (isSmoothNat bound n == True) = True

||| Indexed smooth dimension witness record for types indexed by dimension n.
public export
record SmoothDimensionWitness (bound : Nat) (n : Nat) where
  constructor MkSmoothDimensionWitness
  0 smoothPrf : SmoothWitness bound n

public export
{bound, n : Nat} -> Eq (SmoothDimensionWitness bound n) where
  _ == _ = True

public export
{bound, n : Nat} -> Show (SmoothDimensionWitness bound n) where
  show (MkSmoothDimensionWitness _) = "SmoothDimensionWitness(" ++ show bound ++ ", " ++ show n ++ ")"

||| Validated smooth dimension as a dependent pair (Sigma-type).
||| Guarantees at compile-time that any dimension element carries its correctness certificate.
public export
SmoothDimension : (bound : Nat) -> Type
SmoothDimension bound = (n : Nat ** SmoothWitness bound n)

public export
{bound : Nat} -> Eq (SmoothDimension bound) where
  (n1 ** _) == (n2 ** _) = n1 == n2

public export
{bound : Nat} -> Show (SmoothDimension bound) where
  show (n ** _) = "SmoothDimension(" ++ show n ++ ")"

||| Constructive prime multiset carrier bundling a dimension with its verified prime decomposition.
public export
record SmoothCarrier (bound : Nat) where
  constructor MkSmoothCarrier
  carrierDimension : Nat
  primeFactors     : PrimeMultiset
  0 smoothWitness  : SmoothWitness bound carrierDimension

------------------------------------------------------------------------
-- 3. CANONICAL PHYSICAL HORIZON & PRIMITIVE WITNESSES
------------------------------------------------------------------------

||| The fundamental cosmological 13-smooth horizon (Law of Coherent Matter).
public export
CosmicSmoothHorizon : Nat
CosmicSmoothHorizon = 13

||| Cosmological smooth dimension carrier (Sigma-pair).
public export
CosmicSmoothDimension : Type
CosmicSmoothDimension = SmoothDimension CosmicSmoothHorizon

||| Cosmological indexed smooth dimension witness.
public export
CosmicSmoothDimensionWitness : (n : Nat) -> Type
CosmicSmoothDimensionWitness n = SmoothDimensionWitness CosmicSmoothHorizon n

||| Canonical 13-smooth witness for dimension 2.
public export
prfSmooth2 : SmoothWitness CosmicSmoothHorizon 2
prfSmooth2 = Refl

||| Canonical 13-smooth witness for dimension 4.
public export
prfSmooth4 : SmoothWitness CosmicSmoothHorizon 4
prfSmooth4 = Refl

||| Canonical 13-smooth witness for dimension 6.
public export
prfSmooth6 : SmoothWitness CosmicSmoothHorizon 6
prfSmooth6 = Refl

||| Canonical 13-smooth witness for dimension 12.
public export
prfSmooth12 : SmoothWitness CosmicSmoothHorizon 12
prfSmooth12 = Refl

||| Canonical 13-smooth witness for dimension 18.
public export
prfSmooth18 : SmoothWitness CosmicSmoothHorizon 18
prfSmooth18 = Refl

||| Canonical 13-smooth witness for observer scale dimension 39 (3 * 13).
public export
prfSmooth39 : SmoothWitness CosmicSmoothHorizon 39
prfSmooth39 = Refl

||| Canonical 13-smooth witness for Primorial 210 ground state (2 * 3 * 5 * 7).
public export
prfSmooth210 : SmoothWitness CosmicSmoothHorizon 210
prfSmooth210 = Refl

||| Canonical proof certifying that 137 (Fine-Structure Constant / Grid Wall) is decoherent.
public export
prfDecoherent137 : isSmoothNat CosmicSmoothHorizon 137 = False
prfDecoherent137 = Refl

||| Canonical validated observer epoch dimension (Sigma-pair).
public export
dimObserver : CosmicSmoothDimension
dimObserver = (the Nat 39 ** Refl)

||| Canonical validated Primorial 210 cosmic ground state dimension (Sigma-pair).
public export
dimPrimorial210 : CosmicSmoothDimension
dimPrimorial210 = (the Nat 210 ** Refl)

------------------------------------------------------------------------
-- 4. BACKWARD-COMPATIBILITY ALIASES (Transition Bridge)
------------------------------------------------------------------------

||| Backward-compatible alias for 13-smooth predicate.
public export
is13SmoothNat : Nat -> Bool
is13SmoothNat = isSmoothNat CosmicSmoothHorizon

||| Backward-compatible alias for 13-smooth type-level witness.
public export
Smooth13Witness : Nat -> Type
Smooth13Witness = SmoothWitness CosmicSmoothHorizon

||| Backward-compatible alias for indexed 13-smooth dimension record.
public export
Smooth13Dimension : Nat -> Type
Smooth13Dimension = SmoothDimensionWitness CosmicSmoothHorizon

||| Backward-compatible constructor alias for indexed 13-smooth dimension.
public export
mkSmooth13Dimension : {n : Nat} -> Smooth13Witness n -> Smooth13Dimension n
mkSmooth13Dimension prf = MkSmoothDimensionWitness prf

||| Backward-compatible projection to CosmicSmoothDimension Sigma-pair.
public export
0 toSmoothDimension13 : Smooth13Dimension n -> CosmicSmoothDimension
toSmoothDimension13 (MkSmoothDimensionWitness prf) = (n ** prf)

||| Backward-compatible primitive witness instances.
public export
0 prfSmooth13_2 : Smooth13Witness 2
prfSmooth13_2 = prfSmooth2

public export
0 prfSmooth13_4 : Smooth13Witness 4
prfSmooth13_4 = prfSmooth4

public export
0 prfSmooth13_6 : Smooth13Witness 6
prfSmooth13_6 = prfSmooth6

public export
0 prfSmooth13_12 : Smooth13Witness 12
prfSmooth13_12 = prfSmooth12

public export
0 prfSmooth13_18 : Smooth13Witness 18
prfSmooth13_18 = prfSmooth18

public export
0 prfSmooth13_210 : Smooth13Witness 210
prfSmooth13_210 = prfSmooth210
