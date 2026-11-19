module Stage0.StructuralFuel

import public Data.Fuel
import Data.Nat
import public Stage0.BoxNat
import public Stage0.BoxInt
import public Stage0.HereditaryMSet
import public Stage0.SignedBit
import public Stage0.Box

%default total

--------------------------------------------------------------------------------
-- 1. GENERATIVE MOTION ALIASES & ARITHMETIC SCALING GENERATORS
--------------------------------------------------------------------------------

||| Canonical signed exponent key helper for Stage 0 Laurent bootstrap:
||| Alias for `Stage0.HereditaryMSet.scalarKeyHMSet`.
public export
stage0SignedKey : Integer -> HereditaryMSet BoxInt
stage0SignedKey = scalarKeyHMSet

||| Relational scaling function for 3D spatial field lattice cells.
||| Grid dimension k produces k^3 active spatial slots (1 -> 1, 2 -> 8, 3 -> 27).
public export
computeVMSize : (gridDim : Nat) -> Nat
computeVMSize dim = dim * (dim * dim)

||| Relational scaling function for Dark Energy binary ROM buffer depth.
||| Binary depth b produces 2^b conserved archival capacity slots (e.g. 7 -> 128).
public export
computeDESize : (deDepth : Nat) -> Nat
computeDESize depth = fastNatPower2 depth

||| Computes triangular number T_n via structural induction without typeclass division.
public export
triangularSum : Nat -> Nat
triangularSum Z = Z
triangularSum (S k) = S k + triangularSum k

--------------------------------------------------------------------------------
-- 2. PRIMORIAL-210 CAPACITIES & COMPOSITIONAL `GohFuel` COMBINATORS
--------------------------------------------------------------------------------

||| Derived Elliptic (27), Hyperbolic (128), and Parabolic (55) sector capacities:
public export
EllipticCapacity : Nat
EllipticCapacity = computeVMSize spatialAxisCount

public export
HyperbolicCapacity : Nat
HyperbolicCapacity = computeDESize (spatialAxisCount + boundaryBracketOverhead + boundaryBracketOverhead)

public export
ParabolicCapacity : Nat
ParabolicCapacity = triangularSum (elementaryPolarityCount * (spatialAxisCount + boundaryBracketOverhead))

||| Canonical default capacity budget derived from the three geometric sectors (27 + 128 + 55 = 210):
public export
DefaultStreamCapacity : Nat
DefaultStreamCapacity = EllipticCapacity + HyperbolicCapacity + ParabolicCapacity

||| Backward-compatible lowercase alias for `DefaultStreamCapacity` (`210`).
public export
defaultStreamCapacity : Nat
defaultStreamCapacity = DefaultStreamCapacity

||| Compile-time proof that `boundaryBracketOverhead` is 2 and `DefaultStreamCapacity` is Primorial 210:
public export
0 prfBoundaryOverheadTwo : Stage0.HereditaryMSet.boundaryBracketOverhead = 2
prfBoundaryOverheadTwo = Refl

||| ToDo: Replace hardcoded values with `primorial` or `primorial210` definitions from `Data.Primorial`.
public export
0 prfDerivedCapacityEqualsPrimorial210 :
  Stage0.StructuralFuel.DefaultStreamCapacity = (2 * 3 * 5 * 7)
prfDerivedCapacityEqualsPrimorial210 = Refl

||| Canonical default GohFuel for total stream folds and equality comparisons.
public export
defaultStreamGohFuel : GohFuel DefaultStreamCapacity
defaultStreamGohFuel = gohFuelForCapacity DefaultStreamCapacity

||| Compile-time verification that default stream fuel provides 316 structural steps:
public export
0 prfDefaultStreamGohFuelSteps : Stage0.StructuralFuel.defaultStreamGohFuel.fuelSteps = 316
prfDefaultStreamGohFuelSteps = Refl

||| Additive fuel combination for sequential execution pipelines.
||| Running two sequential stages with capacities c1 and c2 requires additive fuel steps.
public export
sequentialFuel : GohFuel c1 -> GohFuel c2 -> GohFuel (c1 + c2)
sequentialFuel (MkGohFuel s1) (MkGohFuel s2) = MkGohFuel (s1 + s2)

||| Join/Envelope fuel combination for parallel or branched execution.
||| Guaranteed to provide sufficient fuel for either branch.
public export
joinFuel : GohFuel c1 -> GohFuel c2 -> GohFuel (fuelMax c1 c2)
joinFuel (MkGohFuel s1) (MkGohFuel s2) = MkGohFuel (fuelMax s1 s2)

||| Multi-stream fuel combinator computing the step budget required for flatMap/fusedConcat
||| with outer stream steps and inner stream steps.
||| Accounts for N * (M + 2) + 1 steps (Skip entering inner, inner Yields, Skip exiting inner, Done).
public export
multiStreamFuelNat : (outerSteps : Nat) -> (innerSteps : Nat) -> Nat
multiStreamFuelNat outer inner = (outer * (inner + boundaryBracketOverhead)) + S Z

||| Model-indexed multi-stream fuel combinator for nested FusedStream pipelines.
public export
multiStreamGohFuel : GohFuel cOuter -> GohFuel cInner -> Nat
multiStreamGohFuel (MkGohFuel sOuter) (MkGohFuel sInner) = multiStreamFuelNat sOuter sInner

--------------------------------------------------------------------------------
-- 3. CANONICAL FUEL WRAPPERS & BACKWARD-COMPATIBILITY ALIASES
--------------------------------------------------------------------------------

||| Backward-compatible alias for the master ground state capacity (Rule 03):
public export
masterSubstrateGohFuelModel : GohFuel DefaultStreamCapacity
masterSubstrateGohFuelModel = defaultStreamGohFuel

||| Backward-compatible alias for Elliptic capacity fuel (27 items):
public export
ellipticGohFuelModel : GohFuel 27
ellipticGohFuelModel = gohFuelForCapacity 27

||| Backward-compatible alias for Hyperbolic capacity fuel (128 items):
public export
hyperbolicGohFuelModel : GohFuel 128
hyperbolicGohFuelModel = gohFuelForCapacity 128

||| Backward-compatible alias for Parabolic capacity fuel (55 items):
public export
parabolicGohFuelModel : GohFuel 55
parabolicGohFuelModel = gohFuelForCapacity 55

||| Formal compile-time witness certifying that default fuel dominates 27 items:
public export
0 prfMasterDominatesElliptic : fuelLTE (gohSteps Stage0.StructuralFuel.ellipticGohFuelModel) (gohSteps Stage0.StructuralFuel.masterSubstrateGohFuelModel) = True
prfMasterDominatesElliptic = Refl

||| Formal compile-time witness certifying that default fuel dominates 128 items:
public export
0 prfMasterDominatesHyperbolic : fuelLTE (gohSteps Stage0.StructuralFuel.hyperbolicGohFuelModel) (gohSteps Stage0.StructuralFuel.masterSubstrateGohFuelModel) = True
prfMasterDominatesHyperbolic = Refl

||| Formal compile-time witness certifying that default fuel dominates 55 items:
public export
0 prfMasterDominatesParabolic : fuelLTE (gohSteps Stage0.StructuralFuel.parabolicGohFuelModel) (gohSteps Stage0.StructuralFuel.masterSubstrateGohFuelModel) = True
prfMasterDominatesParabolic = Refl

||| Canonical structural fuel derived from Goh factorisation as a BoxNat multiset tally.
||| Bounded by N plus divisor count and gate parity offset:
public export
gohFuel : Nat -> BoxNat
gohFuel n = natToBoxNat (gohFuelNat n)

||| Canonical structural fuel operating directly on BoxNat inputs.
public export
gohFuelBox : BoxNat -> BoxNat
gohFuelBox bn = gohFuel (boxNatToNat bn)

||| Legacy BoxNat-wrapped Elliptic Confinement Fuel (27 items).
public export
ellipticGohFuel : BoxNat
ellipticGohFuel = gohFuel 27

||| Legacy BoxNat-wrapped Hyperbolic Spectral Fuel (128 items).
public export
hyperbolicGohFuel : BoxNat
hyperbolicGohFuel = gohFuel 128

||| Legacy BoxNat-wrapped Parabolic Dissipation Drain Fuel (55 items).
public export
parabolicGohFuel : BoxNat
parabolicGohFuel = gohFuel 55

||| Legacy BoxNat-wrapped Master Substrate Ground State Fuel (210 items).
public export
masterSubstrateGohFuel : BoxNat
masterSubstrateGohFuel = gohFuel defaultStreamCapacity

--------------------------------------------------------------------------------
-- 4. LEGACY DATA.FUEL COMPATIBILITY ENVELOPES
--------------------------------------------------------------------------------

||| Elliptic Bound State Confinement Fuel (27 items).
public export
ellipticFuel : Fuel
ellipticFuel = limit 27

||| Hyperbolic Gauge Flux Fuel (128 items).
public export
hyperbolicFuel : Fuel
hyperbolicFuel = limit 128

||| Parabolic Dissipation Drain Fuel (55 items).
public export
parabolicFuel : Fuel
parabolicFuel = limit 55

||| Substrate Primorial Ground State Fuel (210 items).
public export
substrateFuel : Fuel
substrateFuel = limit defaultStreamCapacity

||| Prime 13 Gate-Purity Boundary Fuel.
public export
prime13Fuel : Fuel
prime13Fuel = limit 13

||| Intrinsic structural fuel derived from total factor count \sum m_i of a factorized multiset.
public export
gohFactorFuel : (factorCount : Nat) -> Fuel
gohFactorFuel Z = limit 1
gohFactorFuel (S k) = limit (S k)

||| Intrinsic structural fuel derived from total polynomial degree \sum d_i \cdot m_i.
public export
gohDegreeFuel : (degSum : Nat) -> Fuel
gohDegreeFuel Z = limit 1
gohDegreeFuel (S k) = limit (S k)

||| Constructivist Stern-Brocot continued fraction tree depth fuel (Rule 01).
public export
rationalFlowFuel : (p : Nat) -> (q : Nat) -> Fuel
rationalFlowFuel p q = limit (p + q + 10)

--------------------------------------------------------------------------------
-- 5. MODEL-INDEXED GOH FACTOR/DEGREE FUEL & EXISTENTIAL ENVELOPE
--------------------------------------------------------------------------------

||| Model-indexed structural fuel derived from total factor / active support count.
public export
gohFactorGohFuel : (factorCount : Nat) -> GohFuel factorCount
gohFactorGohFuel factorCount = gohFuelForCapacity factorCount

||| Model-indexed structural fuel derived from polynomial degree / span capacity.
public export
gohDegreeGohFuel : (degSum : Nat) -> GohFuel degSum
gohDegreeGohFuel degSum = gohFuelForCapacity degSum

||| Sequential additive combination over existential GohFuel envelopes.
public export
seqAnyGohFuel : AnyGohFuel -> AnyGohFuel -> AnyGohFuel
seqAnyGohFuel (MkAnyGohFuel c1 f1) (MkAnyGohFuel c2 f2) =
  MkAnyGohFuel (c1 + c2) (sequentialFuel f1 f2)

||| Parallel envelope join over existential GohFuel envelopes.
public export
joinAnyGohFuel : AnyGohFuel -> AnyGohFuel -> AnyGohFuel
joinAnyGohFuel (MkAnyGohFuel c1 f1) (MkAnyGohFuel c2 f2) =
  MkAnyGohFuel (fuelMax c1 c2) (joinFuel f1 f2)

--------------------------------------------------------------------------------
-- 6. SUPPORT-DRIVEN `GohFuel` ALIASES (`fuelOfM`, `fuelFromSupport`, `hyperOpFuelOfM`)
--------------------------------------------------------------------------------

||| Single-pass `fuelOfM` extractor (`BoxInt` specialization of `HereditaryMSet.fuelOfHMSet`).
public export
fuelOfM : (cap : Nat) -> HereditaryMSet BoxInt -> (GohFuel cap, Nat)
fuelOfM = fuelOfHMSet

||| Single-pass `GohFuel` sizer over unsigned support multisets (`HereditaryMSet MultisetBit`).
public export
fuelFromSupport : (cap : Nat) -> HereditaryMSet MultisetBit -> (GohFuel cap, Nat)
fuelFromSupport = fuelOfHMSet

||| Binary multi-stream fuel combiner (`BoxInt` specialization of `multiStreamFuelOfHMSet`).
public export
multiStreamFuelOfM : (cap : Nat) ->
                     InteractionMode ->
                     HereditaryMSet BoxInt ->
                     HereditaryMSet BoxInt ->
                     (GohFuel cap, Nat)
multiStreamFuelOfM = multiStreamFuelOfHMSet

||| Level-aware `hyperOp` fuel sizer (`BoxInt` specialization of `hyperOpFuelOfHMSet`).
public export
hyperOpFuelOfM : (level : Nat) ->
                 (cap : Nat) ->
                 HereditaryMSet BoxInt ->
                 HereditaryMSet BoxInt ->
                 (GohFuel cap, Nat)
hyperOpFuelOfM = hyperOpFuelOfHMSet
