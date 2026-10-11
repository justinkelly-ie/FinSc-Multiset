module Stage1.TypeTheory.Smoothness

import public Stage0.BoxInt
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

||| Validated smooth dimension as a dependent pair (Sigma-type).
||| Guarantees at compile-time that any dimension element carries its correctness certificate.
public export
SmoothDimension : (bound : Nat) -> Type
SmoothDimension bound = (n : Nat ** SmoothWitness bound n)

public export
Eq (SmoothDimension bound) where
  (n1 ** _) == (n2 ** _) = n1 == n2

public export
Show (SmoothDimension bound) where
  show (n ** _) = "SmoothDimension(" ++ show n ++ ")"

------------------------------------------------------------------------
-- 3. CANONICAL PHYSICAL HORIZON & PRIMITIVE WITNESSES
------------------------------------------------------------------------

||| The fundamental cosmological 13-smooth horizon (Law of Coherent Matter).
public export
CosmicSmoothHorizon : Nat
CosmicSmoothHorizon = 13

||| Cosmological smooth dimension carrier.
public export
CosmicSmoothDimension : Type
CosmicSmoothDimension = SmoothDimension CosmicSmoothHorizon

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
