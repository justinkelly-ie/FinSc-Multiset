module Stage1.TypeTheory.Smoothness

import public Stage0.BoxInt
import public Stage0.PrimeMultiset
import public Stage0.OnSeq.FusedStream
import public Stage1.TypeTheory.MultisetLevel
import Data.Nat
import Data.List
import Data.Maybe

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

||| Indexed dimension witness record for types indexed by dimension n.
public export
record DimensionWitness (bound : Nat) (n : Nat) where
  constructor MkDimensionWitness
  0 smoothPrf : SmoothWitness bound n

public export
{bound, n : Nat} -> Eq (DimensionWitness bound n) where
  _ == _ = True

public export
{bound, n : Nat} -> Show (DimensionWitness bound n) where
  show (MkDimensionWitness _) = "DimensionWitness(" ++ show bound ++ ", " ++ show n ++ ")"

||| Validated dimension as a dependent pair (Sigma-type).
||| Guarantees at compile-time that any dimension element carries its correctness certificate.
public export
Dimension : (bound : Nat) -> Type
Dimension bound = (n : Nat ** SmoothWitness bound n)

public export
{bound : Nat} -> Eq (Dimension bound) where
  (n1 ** _) == (n2 ** _) = n1 == n2

public export
{bound : Nat} -> Show (Dimension bound) where
  show (n ** _) = "Dimension(" ++ show n ++ ")"

||| Constructive prime multiset carrier bundling a dimension with its verified prime decomposition.
public export
record DimensionCarrier (bound : Nat) where
  constructor MkDimensionCarrier
  carrierDimension : Nat
  primeFactors     : GohPrimeMultiset
  0 smoothWitness  : SmoothWitness bound carrierDimension

||| Constructive decidability of the smoothness property under prime bound.
public export
decideSmoothness : (bound : Nat) -> (n : Nat) -> Dec (SmoothWitness bound n)
decideSmoothness bound n with (isSmoothNat bound n == True)
  decideSmoothness bound n | True  = Yes Refl
  decideSmoothness bound n | False = No (\p => case p of Refl impossible)

||| Safely lifts a raw Nat to a certified Dimension Sigma-pair if smooth.
public export
toDimension : (bound : Nat) -> (n : Nat) -> Maybe (Dimension bound)
toDimension bound n with (decideSmoothness bound n)
  toDimension bound n | Yes prf = Just (n ** prf)
  toDimension bound n | No _    = Nothing

||| Inductive coherence classification of a scale step n under prime bound.
||| - GatePure:   n is certified smooth under prime bound, preserving quantum coherence.
||| - Decoherent: n contains prime factors > bound, draining into thermal dispersion.
public export
data CoherenceStatus : (bound : Nat) -> (n : Nat) -> Type where
  GatePure   : SmoothWitness bound n -> CoherenceStatus bound n
  Decoherent : (SmoothWitness bound n -> Void) -> CoherenceStatus bound n

public export
{bound, n : Nat} -> Show (CoherenceStatus bound n) where
  show (GatePure _)   = "GatePure(" ++ show n ++ ")"
  show (Decoherent _) = "Decoherent(" ++ show n ++ ")"

||| Evaluates and returns the constructive coherence status witness.
public export
decideCoherence : (bound : Nat) -> (n : Nat) -> CoherenceStatus bound n
decideCoherence bound n with (decideSmoothness bound n)
  decideCoherence bound n | Yes prf   = GatePure prf
  decideCoherence bound n | No contra = Decoherent contra

||| Extracts the certified Dimension from a GatePure status.
public export
statusToDimension : {bound, n : Nat} -> CoherenceStatus bound n -> Maybe (Dimension bound)
statusToDimension (GatePure prf) = Just (n ** prf)
statusToDimension (Decoherent _) = Nothing

||| Boolean projection of coherence status.
public export
isStatusGatePure : {bound, n : Nat} -> CoherenceStatus bound n -> Bool
isStatusGatePure (GatePure _)   = True
isStatusGatePure (Decoherent _) = False

------------------------------------------------------------------------
-- 3. CANONICAL PHYSICAL HORIZON & PRIMITIVE WITNESSES
------------------------------------------------------------------------

||| The fundamental cosmological 13-smooth horizon (Law of Coherent Matter).
public export
CosmicSmoothHorizon : Nat
CosmicSmoothHorizon = 13

||| Cosmological smooth dimension carrier (Sigma-pair).
public export
CosmicDimension : Type
CosmicDimension = Dimension CosmicSmoothHorizon

||| Cosmological indexed dimension witness.
public export
CosmicDimensionWitness : (n : Nat) -> Type
CosmicDimensionWitness n = DimensionWitness CosmicSmoothHorizon n

||| Canonical 13-smooth witness for dimension 2.
public export
prfSmooth2 : SmoothWitness CosmicSmoothHorizon 2
prfSmooth2 = Refl

||| Canonical 13-smooth witness for manifest spatial dimension L = 3.
public export
prfSmooth3 : SmoothWitness CosmicSmoothHorizon 3
prfSmooth3 = Refl

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

||| Canonical 13-smooth witness for elliptic lattice capacity 27 (3^3).
public export
prfSmooth27 : SmoothWitness CosmicSmoothHorizon 27
prfSmooth27 = Refl

||| Canonical 13-smooth witness for observer scale dimension 39 (3 * 13).
public export
prfSmooth39 : SmoothWitness CosmicSmoothHorizon 39
prfSmooth39 = Refl

||| Canonical 13-smooth witness for holographic boundary surface area 54 (6 * 3^2).
public export
prfSmooth54 : SmoothWitness CosmicSmoothHorizon 54
prfSmooth54 = Refl

||| Canonical 13-smooth witness for parabolic residue dimension 55 (T_10 = 55).
public export
prfSmooth55 : SmoothWitness CosmicSmoothHorizon 55
prfSmooth55 = Refl

||| Canonical 13-smooth witness for hyperbolic ROM capacity 128 (2^7).
public export
prfSmooth128 : SmoothWitness CosmicSmoothHorizon 128
prfSmooth128 = Refl

||| Canonical 13-smooth witness for Primorial 210 ground state (2 * 3 * 5 * 7).
public export
prfSmooth210 : SmoothWitness CosmicSmoothHorizon 210
prfSmooth210 = Refl

||| Canonical 13-smooth witness for multi-sector holographic capacity 216 (4 * 54).
public export
prfSmooth216 : SmoothWitness CosmicSmoothHorizon 216
prfSmooth216 = Refl

||| Canonical proof certifying that 137 (Fine-Structure Constant / Grid Wall) is decoherent.
public export
prfDecoherent137 : isSmoothNat CosmicSmoothHorizon 137 = False
prfDecoherent137 = Refl

||| Canonical refutation witness that 137 is smooth.
public export
contraSmooth137 : SmoothWitness CosmicSmoothHorizon 137 -> Void
contraSmooth137 p = case p of Refl impossible

||| Canonical validated manifest spatial dimension L = 3 (Sigma-pair).
public export
dimManifest3 : CosmicDimension
dimManifest3 = (the Nat 3 ** Refl)

||| Canonical validated elliptic lattice capacity dimension 27 (Sigma-pair).
public export
dimElliptic27 : CosmicDimension
dimElliptic27 = (the Nat 27 ** Refl)

||| Canonical validated observer epoch dimension 39 (Sigma-pair).
public export
dimObserver : CosmicDimension
dimObserver = (the Nat 39 ** Refl)

||| Canonical validated holographic boundary surface area dimension 54 (Sigma-pair).
public export
dimHolographic54 : CosmicDimension
dimHolographic54 = (the Nat 54 ** Refl)

||| Canonical validated parabolic dissipation sink dimension 55 (Sigma-pair).
public export
dimParabolic55 : CosmicDimension
dimParabolic55 = (the Nat 55 ** Refl)

||| Canonical validated hyperbolic ROM capacity dimension 128 (Sigma-pair).
public export
dimHyperbolic128 : CosmicDimension
dimHyperbolic128 = (the Nat 128 ** Refl)

||| Canonical validated Primorial 210 cosmic ground state dimension (Sigma-pair).
public export
dimPrimorial210 : CosmicDimension
dimPrimorial210 = (the Nat 210 ** Refl)

||| Canonical validated multi-sector holographic capacity dimension 216 (Sigma-pair).
public export
dimHolographic216 : CosmicDimension
dimHolographic216 = (the Nat 216 ** Refl)

||| Safely lifts a validated Dimension to a DimensionCarrier if 13-smooth.
public export
toDimensionCarrier : Dimension CosmicSmoothHorizon -> Maybe (DimensionCarrier CosmicSmoothHorizon)
toDimensionCarrier (n ** prf) =
  case factorizeGohSmooth n of
    Just factors => Just (MkDimensionCarrier n factors prf)
    Nothing      => Nothing

||| Constructive mapping from any constructivist Goh prime to its 13-smooth certificate.
public export
gohPrimeWitness : GohPrime p -> SmoothWitness CosmicSmoothHorizon p
gohPrimeWitness Prime2  = prfSmooth2
gohPrimeWitness Prime3  = Refl
gohPrimeWitness Prime5  = Refl
gohPrimeWitness Prime7  = Refl
gohPrimeWitness Prime11 = Refl
gohPrimeWitness Prime13 = Refl

||| Certified dimension corresponding directly to a Goh prime.
public export
gohPrimeDimension : {p : Nat} -> GohPrime p -> CosmicDimension
gohPrimeDimension prf = (p ** gohPrimeWitness prf)

||| Certified dimension corresponding directly to an existential AnyGohPrime pair.
public export
anyGohPrimeDimension : AnyGohPrime -> CosmicDimension
anyGohPrimeDimension (p ** prf) = (p ** gohPrimeWitness prf)

------------------------------------------------------------------------
-- 4. DEPENDENT DIMENSION-DERIVED STRUCTURAL GOH FUEL & INVARIANT PROOFS
------------------------------------------------------------------------

||| Derives structural Goh fuel directly from a certified CosmicDimension Sigma-pair.
public export
dimensionGohFuel : CosmicDimension -> BoxNat
dimensionGohFuel (dim ** _) = gohFuel dim

||| Derives structural Nat fuel directly from a certified CosmicDimension Sigma-pair.
public export
dimensionNatFuel : CosmicDimension -> Nat
dimensionNatFuel (dim ** _) = boxNatToNat (gohFuel dim)

||| Static compile-time witness: Elliptic lattice fuel derived from dimElliptic27
||| definitionally equals ellipticGohFuel (Rule 01, Rule 03, Rule 04).
public export
0 prfEllipticFuelEquiv :
  dimensionGohFuel Stage1.TypeTheory.Smoothness.dimElliptic27 = Stage0.StructuralFuel.ellipticGohFuel
prfEllipticFuelEquiv = Refl

||| Static compile-time witness: Hyperbolic spectral fuel derived from dimHyperbolic128
||| definitionally equals hyperbolicGohFuel.
public export
0 prfHyperbolicFuelEquiv :
  dimensionGohFuel Stage1.TypeTheory.Smoothness.dimHyperbolic128 = Stage0.StructuralFuel.hyperbolicGohFuel
prfHyperbolicFuelEquiv = Refl

||| Static compile-time witness: Parabolic dissipation fuel derived from dimParabolic55
||| definitionally equals parabolicGohFuel.
public export
0 prfParabolicFuelEquiv :
  dimensionGohFuel Stage1.TypeTheory.Smoothness.dimParabolic55 = Stage0.StructuralFuel.parabolicGohFuel
prfParabolicFuelEquiv = Refl

||| Static compile-time witness: Primorial 210 master ground fuel derived from dimPrimorial210
||| definitionally equals masterSubstrateGohFuel.
public export
0 prfPrimorialFuelEquiv :
  dimensionGohFuel Stage1.TypeTheory.Smoothness.dimPrimorial210 = Stage0.StructuralFuel.masterSubstrateGohFuel
prfPrimorialFuelEquiv = Refl

||| Static compile-time witness: Observer epoch fuel derived from dimObserver (k=38, n=39=3x13).
public export
0 prfObserverFuelMatchesProduct :
  dimensionGohFuel Stage1.TypeTheory.Smoothness.dimObserver = gohFuel 39
prfObserverFuelMatchesProduct = Refl

||| Static compile-time proofs verifying that canonical cosmic dimensions
||| factorize cleanly into certified 13-smooth GohPrimeMultisets.
public export
0 prfElliptic27Carrier : isJust (factorizeGohSmooth 27) = True
prfElliptic27Carrier = Refl

public export
0 prfHyperbolic128Carrier : isJust (factorizeGohSmooth 128) = True
prfHyperbolic128Carrier = Refl

public export
0 prfParabolic55Carrier : isJust (factorizeGohSmooth 55) = True
prfParabolic55Carrier = Refl

public export
0 prfPrimorial210Carrier : isJust (factorizeGohSmooth 210) = True
prfPrimorial210Carrier = Refl

public export
0 prfObserver39Carrier : isJust (factorizeGohSmooth 39) = True
prfObserver39Carrier = Refl


