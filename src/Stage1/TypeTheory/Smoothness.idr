module Stage1.TypeTheory.Smoothness

import public Stage0.BoxInt
import public Stage0.PrimeMultiset
import public Stage0.StructuralFuel
import public Stage0.OnSeq.FusedStream
import Data.Nat
import Data.List
import Data.Maybe
import public Data.DPair

%default total

------------------------------------------------------------------------
-- 1. CONSTRUCTIVE PRIME GENERATION UNDER BOUND
------------------------------------------------------------------------

||| Deterministic primality trial candidate using native constructivist Nat and BoxInt arithmetic.
public export
isPrimeCandidate : (fuel : Nat) -> (d : Nat) -> (n : Nat) -> Bool
isPrimeCandidate Z _ _ = False
isPrimeCandidate (S f) d n =
  if (d * d) > n then True
  else if boxEq (modBox (natToBoxInt n) (natToBoxInt d)) (intToBoxInt 0) then False
  else isPrimeCandidate f (S d) n

||| Generates primes up to a given limit using structural Nat fuel.
public export
primesUpToCandidate : (fuel : Nat) -> (curr : Nat) -> (limit : Nat) -> List Nat
primesUpToCandidate Z _ _ = []
primesUpToCandidate (S f) curr limit =
  if curr > limit then []
  else if isPrimeCandidate limit 2 curr
       then curr :: primesUpToCandidate f (S curr) limit
       else primesUpToCandidate f (S curr) limit

||| Dynamic constructivist primes strictly bounded by natural bound.
||| Definitional fast-path for CosmicSmoothHorizon = 13 ensures instantaneous compile-time proof reduction (Rule 01, Item 3).
public export
primesUnderBound : (bound : Nat) -> List BoxInt
primesUnderBound 13 = [intToBoxInt 2, intToBoxInt 3, intToBoxInt 5, intToBoxInt 7, intToBoxInt 11, intToBoxInt 13]
primesUnderBound bound =
  map natToBoxInt (primesUpToCandidate (S bound) 2 bound)

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
  filterStream (\p => isPrimeCandidate bound 2 p) (streamRange 2 bound)

||| Generates primes up to bound as a list from deforested prime stream using model-indexed GohFuel.
public export
primesUnderBoundStream : (bound : Nat) -> List BoxInt
primesUnderBoundStream 13 = [intToBoxInt 2, intToBoxInt 3, intToBoxInt 5, intToBoxInt 7, intToBoxInt 11, intToBoxInt 13]
primesUnderBoundStream bound =
  map natToBoxInt (runFueledStreamFuelModel (gohFuelForCapacity bound) (streamPrimesUnderBound bound))

------------------------------------------------------------------------
-- 2. GENERIC SMOOTHNESS TRANSFORMATION & WITNESSES
------------------------------------------------------------------------

||| Strips all factors of prime p from n using explicit fuel and monomorphic BoxInt operations.
public export
stripFactor : (fuel : Nat) -> (p : BoxInt) -> (n : BoxInt) -> BoxInt
stripFactor Z _ n = n
stripFactor (S f) p n =
  if boxLTE n (intToBoxInt 1) || boxLTE p (intToBoxInt 1) then n
  else if boxEq (modBox n p) (intToBoxInt 0)
    then stripFactor f p (divBox n p)
    else n

||| Strips all factors of prime p from n using model-indexed GohFuel.
public export
stripFactorFuelModel : GohFuel cap -> (p : BoxInt) -> (n : BoxInt) -> BoxInt
stripFactorFuelModel fuel p n = stripFactor (gohSteps fuel) p n

||| Strips a list of prime factors sequentially from n using BoxInt arithmetic.
public export
stripPrimeFactors : (fuel : Nat) -> List BoxInt -> BoxInt -> BoxInt
stripPrimeFactors _ [] n = n
stripPrimeFactors fuel (p :: ps) n =
  stripPrimeFactors fuel ps (stripFactor fuel p n)

||| Strips a list of prime factors sequentially from n using model-indexed GohFuel.
public export
stripPrimeFactorsFuelModel : GohFuel cap -> List BoxInt -> BoxInt -> BoxInt
stripPrimeFactorsFuelModel fuel primes n = stripPrimeFactors (gohSteps fuel) primes n

||| Generic smoothness predicate parameterized by upper prime bound grounded in BoxInt.
public export
isSmoothNat : (bound : Nat) -> (n : Nat) -> Bool
isSmoothNat _ Z = True
isSmoothNat _ (S Z) = True
isSmoothNat bound n =
  let n0 = natToBoxInt n
      fuel = gohFuelForCapacity n
      remVal = stripPrimeFactorsFuelModel fuel (primesUnderBound bound) n0
  in boxEq remVal (intToBoxInt 1)

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

||| Dependent Pair bundling dimension n with its smoothness certificate under prime bound (Rule 03).
public export
SmoothDimension : (bound : Nat) -> Type
SmoothDimension bound = Dimension bound

||| Certified dimension constructor: auto-dispatches compile-time smoothness proof.
public export
certifiedDimension : (bound : Nat) -> (n : Nat) -> {auto prf : SmoothWitness bound n} -> Dimension bound
certifiedDimension bound n {prf} = (n ** prf)

||| Zero-runtime-overhead subset dimension carrying QTT 0 erased smoothness evidence (Data.DPair.Subset).
public export
SubsetDimension : (bound : Nat) -> Type
SubsetDimension bound = Subset Nat (SmoothWitness bound)

||| Smart constructor for zero-runtime-overhead subset dimension with QTT 0 erased proof:
public export
elementDimension : (bound : Nat) -> (n : Nat) -> {auto 0 prf : SmoothWitness bound n} -> SubsetDimension bound
elementDimension bound n {prf} = Element n prf

------------------------------------------------------------------------
-- 2B. ALGEBRAIC AND EMERGENT DIMENSIONS (WILDBERGER SUPPORT & DEGREE)
------------------------------------------------------------------------

||| An Algebraic Dimension grounded in the finite active support Supp(M)
||| and algebraic degree of a cyclotomic or polynomial carrier.
public export
record AlgebraicDimension where
  constructor MkAlgebraicDimension
  dimValue        : Nat
  supportSize     : Nat
  0 prfSupportEq  : supportSize = dimValue

public export
Eq AlgebraicDimension where
  (MkAlgebraicDimension d1 s1 _) == (MkAlgebraicDimension d2 s2 _) = d1 == d2 && s1 == s2

public export
Show AlgebraicDimension where
  show (MkAlgebraicDimension d s _) = "AlgebraicDimension(dim=" ++ show d ++ ", supp=" ++ show s ++ ")"

||| An Emergent Dimension bundling an AlgebraicDimension with a constructive
||| SmoothWitness under prime bound (e.g. CosmicSmoothHorizon = 13).
public export
record EmergentDimension (bound : Nat) where
  constructor MkEmergentDimension
  algebraicDim  : AlgebraicDimension
  smoothWitness : SmoothWitness bound algebraicDim.dimValue

public export
{bound : Nat} -> Eq (EmergentDimension bound) where
  (MkEmergentDimension a1 _) == (MkEmergentDimension a2 _) = a1 == a2

public export
{bound : Nat} -> Show (EmergentDimension bound) where
  show (MkEmergentDimension a _) = "EmergentDimension(" ++ show bound ++ ", " ++ show a.dimValue ++ ")"

||| Smart constructor for an EmergentDimension from a verified smooth degree:
public export
emergentDimension : (bound : Nat) -> (n : Nat) ->
                    {auto prfSmooth : SmoothWitness bound n} ->
                    EmergentDimension bound
emergentDimension bound n {prfSmooth} =
  MkEmergentDimension (MkAlgebraicDimension n n Refl) prfSmooth

||| Smart constructor for an EmergentDimension directly from a cyclotomic factor index d:
public export
cyclotomicEmergentDimension : (bound : Nat) -> (d : Nat) ->
                              {auto prfSmooth : SmoothWitness bound (totientNat d)} ->
                              EmergentDimension bound
cyclotomicEmergentDimension bound d {prfSmooth} =
  MkEmergentDimension (MkAlgebraicDimension (totientNat d) (totientNat d) Refl) prfSmooth

||| Bidirectional conversion between existing Dimension (Sigma pair) and EmergentDimension:
public export
toEmergentDimension : Dimension bound -> EmergentDimension bound
toEmergentDimension (n ** prf) = MkEmergentDimension (MkAlgebraicDimension n n Refl) prf

public export
fromEmergentDimension : EmergentDimension bound -> Dimension bound
fromEmergentDimension ed = (ed.algebraicDim.dimValue ** ed.smoothWitness)

||| Zero-runtime-overhead subset dimension from EmergentDimension (Data.DPair.Subset):
public export
toSubsetDimension : EmergentDimension bound -> SubsetDimension bound
toSubsetDimension ed = Element ed.algebraicDim.dimValue ed.smoothWitness

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


||| Canonical proof certifying that 137 (Fine-Structure Constant / Grid Wall) is decoherent (QTT 0 erased).
public export
0 prfDecoherent137 : isSmoothNat CosmicSmoothHorizon 137 = False
prfDecoherent137 = Refl

||| Canonical refutation witness that 137 is smooth.
public export
contraSmooth137 : SmoothWitness CosmicSmoothHorizon 137 -> Void
contraSmooth137 p = case p of Refl impossible

||| Canonical validated manifest spatial dimension L = 3 (Sigma-pair).
public export
dimManifest3 : CosmicDimension
dimManifest3 = certifiedDimension CosmicSmoothHorizon 3

||| Canonical validated elliptic lattice capacity dimension 27 (Sigma-pair).
public export
dimElliptic27 : CosmicDimension
dimElliptic27 = certifiedDimension CosmicSmoothHorizon 27

||| Canonical validated observer epoch dimension 39 (Sigma-pair).
public export
dimObserver : CosmicDimension
dimObserver = certifiedDimension CosmicSmoothHorizon 39

||| Canonical validated holographic boundary surface area dimension 54 (Sigma-pair).
public export
dimHolographic54 : CosmicDimension
dimHolographic54 = certifiedDimension CosmicSmoothHorizon 54

||| Canonical validated parabolic dissipation sink dimension 55 (Sigma-pair).
public export
dimParabolic55 : CosmicDimension
dimParabolic55 = certifiedDimension CosmicSmoothHorizon 55

||| Canonical validated hyperbolic ROM capacity dimension 128 (Sigma-pair).
public export
dimHyperbolic128 : CosmicDimension
dimHyperbolic128 = certifiedDimension CosmicSmoothHorizon 128

||| Canonical validated Primorial 210 cosmic ground state dimension (Sigma-pair).
public export
dimPrimorial210 : CosmicDimension
dimPrimorial210 = certifiedDimension CosmicSmoothHorizon 210

||| Canonical validated multi-sector holographic capacity dimension 216 (Sigma-pair).
public export
dimHolographic216 : CosmicDimension
dimHolographic216 = certifiedDimension CosmicSmoothHorizon 216

||| Canonical Emergent Cosmic Dimension (bound = CosmicSmoothHorizon = 13).
public export
EmergentCosmicDimension : Type
EmergentCosmicDimension = EmergentDimension CosmicSmoothHorizon

||| Canonical Emergent Cosmic Dimension instances.
public export
dimEmergentManifest3 : EmergentCosmicDimension
dimEmergentManifest3 = emergentDimension CosmicSmoothHorizon 3

public export
dimEmergentElliptic27 : EmergentCosmicDimension
dimEmergentElliptic27 = emergentDimension CosmicSmoothHorizon 27

public export
dimEmergentObserver39 : EmergentCosmicDimension
dimEmergentObserver39 = emergentDimension CosmicSmoothHorizon 39

public export
dimEmergentHolographic54 : EmergentCosmicDimension
dimEmergentHolographic54 = emergentDimension CosmicSmoothHorizon 54

public export
dimEmergentParabolic55 : EmergentCosmicDimension
dimEmergentParabolic55 = emergentDimension CosmicSmoothHorizon 55

public export
dimEmergentHyperbolic128 : EmergentCosmicDimension
dimEmergentHyperbolic128 = emergentDimension CosmicSmoothHorizon 128

public export
dimEmergentPrimorial210 : EmergentCosmicDimension
dimEmergentPrimorial210 = emergentDimension CosmicSmoothHorizon 210

public export
dimEmergentHolographic216 : EmergentCosmicDimension
dimEmergentHolographic216 = emergentDimension CosmicSmoothHorizon 216

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
gohPrimeWitness Prime2  = Refl
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

||| Model-derived Goh fuel indexed directly by a certified CosmicDimension Sigma-pair:
public export
GohFuelDim : CosmicDimension -> Type
GohFuelDim (dim ** _) = GohFuel dim

||| Canonical fuel generator for a certified cosmic dimension:
%inline public export
gohFuelForDim : (dim : CosmicDimension) -> GohFuel (fst dim)
gohFuelForDim (cap ** _) = gohFuelForCapacity cap

||| Definitional compile-time reflection proofs verifying exact fuel steps across cosmic dimensions:
public export
0 prfDimEllipticGohFuel : (gohFuelForDim Stage1.TypeTheory.Smoothness.dimElliptic27).fuelSteps = 42
prfDimEllipticGohFuel = Refl

public export
0 prfDimHyperbolicGohFuel : (gohFuelForDim Stage1.TypeTheory.Smoothness.dimHyperbolic128).fuelSteps = 193
prfDimHyperbolicGohFuel = Refl

public export
0 prfDimParabolicGohFuel : (gohFuelForDim Stage1.TypeTheory.Smoothness.dimParabolic55).fuelSteps = 84
prfDimParabolicGohFuel = Refl

public export
0 prfDimPrimorialGohFuel : (gohFuelForDim Stage1.TypeTheory.Smoothness.dimPrimorial210).fuelSteps = 316
prfDimPrimorialGohFuel = Refl

public export
0 prfDimObserverGohFuel : (gohFuelForDim Stage1.TypeTheory.Smoothness.dimObserver).fuelSteps = 60
prfDimObserverGohFuel = Refl

||| Derives structural Goh fuel directly from a certified CosmicDimension Sigma-pair.
public export
dimensionGohFuel : CosmicDimension -> BoxNat
dimensionGohFuel (dim ** _) = gohFuel dim

||| Derives structural Nat fuel directly from a certified CosmicDimension Sigma-pair without multiset unwrapping.
public export
dimensionNatFuel : CosmicDimension -> Nat
dimensionNatFuel dim = (gohFuelForDim dim).fuelSteps

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


