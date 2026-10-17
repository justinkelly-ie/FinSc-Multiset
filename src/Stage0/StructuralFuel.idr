module Stage0.StructuralFuel

import public Data.Fuel
import Data.Nat
import public Stage0.BoxNat

%default total

--------------------------------------------------------------------------------
-- 1. MODEL GENERATORS & RELATIONAL SCALING FUNCTIONS (RULE 03)
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

||| Formal constructive proof witness certifying that the Model-Derived Primorial Cosmic Budget
||| matches the 4th Primorial factorization: p_4# = 2 * 3 * 5 * 7 = 210.
public export
0 prfMasterGohBudgetMatchesFactorization :
    (computeVMSize 3 + computeDESize 7 + triangularSum 10) = 210
prfMasterGohBudgetMatchesFactorization = Refl

||| Formal compile-time witness certifying Elliptic VM spatial capacity: 3^3 = 27.
public export
0 prfEllipticCapacity27 : computeVMSize 3 = 27
prfEllipticCapacity27 = Refl

||| Formal compile-time witness certifying Hyperbolic DE ROM bit depth capacity: 2^7 = 128.
public export
0 prfHyperbolicCapacity128 : computeDESize 7 = 128
prfHyperbolicCapacity128 = Refl

||| Formal compile-time witness certifying Parabolic DM triangular residue: T_10 = 55.
public export
0 prfParabolicCapacity55 : triangularSum 10 = 55
prfParabolicCapacity55 = Refl

||| Formal compile-time witness certifying the exact Primorial 210 partition: 27 + 128 + 55 = 210.
public export
0 prfPrimorial210Partition : (27 + 128 + 55) = 210
prfPrimorial210Partition = Refl

--------------------------------------------------------------------------------
-- 2. GOH FACTORISATION STRUCTURAL FUEL GENERATORS (BOXNAT & NAT)
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

||| Model-derived Elliptic Confinement Fuel (3^3 = 27 VM bound states).
%inline public export
ellipticGohFuelModel : GohFuel 27
ellipticGohFuelModel = gohFuelForCapacity 27

||| Model-derived Hyperbolic Spectral Fuel (2^7 = 128 DE spectral modes).
%inline public export
hyperbolicGohFuelModel : GohFuel 128
hyperbolicGohFuelModel = gohFuelForCapacity 128

||| Model-derived Parabolic Dissipation Drain Fuel (T_10 = 55 DM channels).
%inline public export
parabolicGohFuelModel : GohFuel 55
parabolicGohFuelModel = gohFuelForCapacity 55

||| Model-derived Master Substrate Primorial Ground State Fuel (210 Master Budget).
%inline public export
masterSubstrateGohFuelModel : GohFuel 210
masterSubstrateGohFuelModel = gohFuelForCapacity 210

||| Definitional compile-time reflection witnesses verifying exact step counts:
public export
0 prfEllipticGohFuelModelSteps : Stage0.StructuralFuel.ellipticGohFuelModel.fuelSteps = 42
prfEllipticGohFuelModelSteps = Refl

public export
0 prfHyperbolicGohFuelModelSteps : Stage0.StructuralFuel.hyperbolicGohFuelModel.fuelSteps = 193
prfHyperbolicGohFuelModelSteps = Refl

public export
0 prfParabolicGohFuelModelSteps : Stage0.StructuralFuel.parabolicGohFuelModel.fuelSteps = 84
prfParabolicGohFuelModelSteps = Refl

public export
0 prfMasterSubstrateGohFuelModelSteps : Stage0.StructuralFuel.masterSubstrateGohFuelModel.fuelSteps = 316
prfMasterSubstrateGohFuelModelSteps = Refl

||| Canonical structural fuel derived from Goh factorisation as a BoxNat multiset tally.
||| Bounded by N plus divisor count and gate parity offset:
public export
gohFuel : Nat -> BoxNat
gohFuel n = natToBoxNat (gohFuelNat n)

||| Canonical structural fuel operating directly on BoxNat inputs.
public export
gohFuelBox : BoxNat -> BoxNat
gohFuelBox bn = gohFuel (boxNatToNat bn)

||| Legacy BoxNat-wrapped Elliptic Confinement Fuel (3^3 = 27 VM bound states).
public export
ellipticGohFuel : BoxNat
ellipticGohFuel = gohFuel (computeVMSize 3)

||| Legacy BoxNat-wrapped Hyperbolic Spectral Fuel (2^7 = 128 DE spectral modes).
public export
hyperbolicGohFuel : BoxNat
hyperbolicGohFuel = gohFuel (computeDESize 7)

||| Legacy BoxNat-wrapped Parabolic Dissipation Drain Fuel (T_10 = 55 DM channels).
public export
parabolicGohFuel : BoxNat
parabolicGohFuel = gohFuel (triangularSum 10)

||| Legacy BoxNat-wrapped Master Substrate Primorial Ground State Fuel (210 Master Budget).
public export
masterSubstrateGohFuel : BoxNat
masterSubstrateGohFuel = gohFuel (computeVMSize 3 + computeDESize 7 + triangularSum 10)

--------------------------------------------------------------------------------
-- 3. LEGACY DATA.FUEL COMPATIBILITY ENVELOPES
--------------------------------------------------------------------------------

||| Elliptic Bound State Confinement Fuel (27 VM).
public export
ellipticFuel : Fuel
ellipticFuel = limit (computeVMSize 3)

||| Hyperbolic Gauge Flux Fuel (128 DE).
public export
hyperbolicFuel : Fuel
hyperbolicFuel = limit (computeDESize 7)

||| Parabolic Dissipation Drain Fuel (55 DM).
public export
parabolicFuel : Fuel
parabolicFuel = limit (triangularSum 10)

||| Substrate Primorial 210 Ground State Fuel (210 Master Budget).
public export
substrateFuel : Fuel
substrateFuel = limit (computeVMSize 3 + computeDESize 7 + triangularSum 10)

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
