module Stage1.Basis.Coordinate

import Data.Fin
import Data.Nat
import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.Bit
import Stage0.Token
import Stage0.StructuralFuel
import public Stage1.Basis.CoordCell
import public Stage1.Carrier.CellMultiset
import public Stage1.Carrier.Vexel
import public Stage1.Carrier.Maxel
import public Stage1.Carrier.Boxel
import public Stage1.Carrier.HyperBoxel
import public Stage1.Carrier.StagedLinear
import public Stage1.Carrier.SquareMaxel
import public Stage1.Carrier.Kronecker
import public Stage1.Carrier.ChromogeometricMetric

%default total

------------------------------------------------------------------------
-- 1. CANONICAL COORDINATE INSTANCES (07-coordinate-systems.md)
------------------------------------------------------------------------

public export
DiscreteCoord BoxNat where

public export
DiscreteCoord Bit where

public export
DiscreteCoord a => DiscreteCoord (Token a) where

public export
DiscreteCoord a => DiscreteCoord (SingRelation a) where

------------------------------------------------------------------------
-- 3. MODEL-DERIVED STRUCTURALFUEL COORDINATE UNIVERSES
--    (07-coordinate-systems.md Section 6: k <-> Stage0.StructuralFuel)
------------------------------------------------------------------------

||| Elliptic 3D spatial voxel coordinate universe (cardinality = computeVMSize 3 = 27).
public export
EllipticVoxelCoord : Type
EllipticVoxelCoord = Fin (computeVMSize 3)

||| Hyperbolic spectral ROM mode coordinate universe (cardinality = computeDESize 7 = 128).
public export
HyperbolicModeCoord : Type
HyperbolicModeCoord = Fin (computeDESize 7)

||| Parabolic triangular dissipation channel coordinate universe (cardinality = triangularSum 10 = 55).
public export
ParabolicDrainCoord : Type
ParabolicDrainCoord = Fin (triangularSum 10)

||| Master Primorial 210 substrate coordinate universe (cardinality = DefaultStreamCapacity = 210).
public export
MasterSubstrateCoord : Type
MasterSubstrateCoord = Fin DefaultStreamCapacity

||| Elliptic causal horizon window coordinate universe (cardinality = gohSteps ellipticGohFuelModel = 42).
public export
EllipticWindowCoord : Type
EllipticWindowCoord = Fin (gohSteps ellipticGohFuelModel)

||| Master substrate causal horizon window coordinate universe (cardinality = gohSteps masterSubstrateGohFuelModel = 316).
public export
MasterWindowCoord : Type
MasterWindowCoord = Fin (gohSteps masterSubstrateGohFuelModel)

||| Compile-time QTT 0 proof: EllipticVoxelCoord cardinality is 27.
public export
0 prfEllipticCoordCardinality : cardinality @{the (FiniteCoord EllipticVoxelCoord) %search} = 27
prfEllipticCoordCardinality = Refl

||| Compile-time QTT 0 proof: HyperbolicModeCoord cardinality is 128.
public export
0 prfHyperbolicCoordCardinality : cardinality @{the (FiniteCoord HyperbolicModeCoord) %search} = 128
prfHyperbolicCoordCardinality = Refl

||| Compile-time QTT 0 proof: ParabolicDrainCoord cardinality is 55.
public export
0 prfParabolicCoordCardinality : cardinality @{the (FiniteCoord ParabolicDrainCoord) %search} = 55
prfParabolicCoordCardinality = Refl

||| Compile-time QTT 0 proof: MasterSubstrateCoord cardinality equals the sum of the 3 geometric sectors (210).
public export
0 prfMasterSubstrateCoordCardinality :
  cardinality @{the (FiniteCoord MasterSubstrateCoord) %search} =
    cardinality @{the (FiniteCoord EllipticVoxelCoord) %search} +
    cardinality @{the (FiniteCoord HyperbolicModeCoord) %search} +
    cardinality @{the (FiniteCoord ParabolicDrainCoord) %search}
prfMasterSubstrateCoordCardinality = Refl

||| Compile-time QTT 0 proof: MasterWindowCoord temporal depth is 316 Goh steps.
public export
0 prfMasterWindowCoordCardinality : cardinality @{the (FiniteCoord MasterWindowCoord) %search} = 316
prfMasterWindowCoordCardinality = Refl

