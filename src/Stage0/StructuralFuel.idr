module Stage0.StructuralFuel

import public Data.Fuel
import Data.Nat
import public Stage0.BoxNat

%default total

--------------------------------------------------------------------------------
-- 1. ARITHMETIC SCALING GENERATORS
--------------------------------------------------------------------------------

||| Relational scaling function for 3D spatial field lattice cells.
||| Grid dimension k produces k^3 active spatial slots (1 -> 1, 2 -> 8, 3 -> 27).
public export
computeVMSize : (gridDim : Nat) -> Nat
computeVMSize dim = dim * (dim * dim)

||| Helper to calculate 2^n for Nat buffer depth.
public export
fastNatPower2 : Nat -> Nat
fastNatPower2 Z = 1
fastNatPower2 (S k) = 2 * fastNatPower2 k

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
-- 2. CONSTRUCTIVIST GOH FUEL GENERATOR & CAPACITY BOUNDS (RULE 03 & 04)
--------------------------------------------------------------------------------

||| Division by 2 via structural recursion.
public export
half : Nat -> Nat
half Z = Z
half (S Z) = Z
half (S (S k)) = S (half k)

||| Canonical Goh factorisation formula computing exact fuel steps natively in Nat:
||| Fuel(N) = N + floor(N/2) + 2
public export
gohFuelNat : Nat -> Nat
gohFuelNat Z = 1
gohFuelNat (S k) = S (S k + S (half k))

||| First-class constructivist Goh Fuel indexed directly by model capacity.
||| Guaranteed zero-allocation Peano integer carrier for recursive evaluators.
public export
record GohFuel (capacity : Nat) where
  constructor MkGohFuel
  fuelSteps : Nat

public export
Eq (GohFuel cap) where
  (MkGohFuel s1) == (MkGohFuel s2) = s1 == s2

public export
Show (GohFuel cap) where
  show (MkGohFuel s) = "GohFuel(" ++ show s ++ " steps)"

||| Canonical smart constructor generating exact fuel from capacity:
%inline public export
gohFuelForCapacity : (capacity : Nat) -> GohFuel capacity
gohFuelForCapacity cap = MkGohFuel (gohFuelNat cap)

||| Zero-cost projection to raw steps for loop pattern-matching (Z and S f):
%inline public export
gohSteps : GohFuel cap -> Nat
gohSteps f = f.fuelSteps

||| Canonical default capacity budget for constructivist stream evaluation.
||| Accommodates up to 210 discrete items (316 structural Goh fuel steps).
%inline public export
DefaultStreamCapacity : Nat
DefaultStreamCapacity = 210

public export
defaultStreamCapacity : Nat
defaultStreamCapacity = DefaultStreamCapacity

||| Canonical default GohFuel for total stream folds and equality comparisons.
%inline public export
defaultStreamGohFuel : GohFuel DefaultStreamCapacity
defaultStreamGohFuel = gohFuelForCapacity DefaultStreamCapacity

||| Compile-time verification that default stream fuel provides 316 structural steps:
public export
0 prfDefaultStreamGohFuelSteps : Stage0.StructuralFuel.defaultStreamGohFuel.fuelSteps = 316
prfDefaultStreamGohFuelSteps = Refl

--------------------------------------------------------------------------------
-- 2. GOH FUEL ALGEBRA (SEQUENTIAL, ENVELOPE JOIN & MULTI-STREAM COMPOSITION)
--------------------------------------------------------------------------------

||| Monomorphic less-than-or-equal test on inductive Peano Nat for fuel budgets.
||| Definitionally reducible in the unifier for compile-time reflection audits (Rule 01).
public export
fuelLTE : Nat -> Nat -> Bool
fuelLTE Z _ = True
fuelLTE (S _) Z = False
fuelLTE (S k) (S j) = fuelLTE k j

||| Monomorphic maximum on inductive Peano Nat for fuel envelopes.
||| Definitionally reducible in the unifier for compile-time reflection audits (Rule 01).
public export
fuelMax : Nat -> Nat -> Nat
fuelMax Z b = b
fuelMax a Z = a
fuelMax (S a) (S b) = S (fuelMax a b)

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
multiStreamFuelNat outer inner = (outer * (inner + 2)) + 1

||| Model-indexed multi-stream fuel combinator for nested FusedStream pipelines.
public export
multiStreamGohFuel : GohFuel cOuter -> GohFuel cInner -> Nat
multiStreamGohFuel (MkGohFuel sOuter) (MkGohFuel sInner) = multiStreamFuelNat sOuter sInner

--------------------------------------------------------------------------------
-- 3. CANONICAL FUEL WRAPPERS & BACKWARD-COMPATIBILITY ALIASES
--------------------------------------------------------------------------------

||| Backward-compatible alias for the master ground state capacity (Rule 03):
%inline public export
masterSubstrateGohFuelModel : GohFuel DefaultStreamCapacity
masterSubstrateGohFuelModel = defaultStreamGohFuel

||| Backward-compatible alias for Elliptic capacity fuel (27 items):
%inline public export
ellipticGohFuelModel : GohFuel 27
ellipticGohFuelModel = gohFuelForCapacity 27

||| Backward-compatible alias for Hyperbolic capacity fuel (128 items):
%inline public export
hyperbolicGohFuelModel : GohFuel 128
hyperbolicGohFuelModel = gohFuelForCapacity 128

||| Backward-compatible alias for Parabolic capacity fuel (55 items):
%inline public export
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
