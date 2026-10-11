module Stage1.TypeTheory.Smooth13

import public Stage0.BoxInt
import public Stage1.TypeTheory.MultisetLevel
import public Stage1.TypeTheory.Smoothness
import Data.Nat

%default total

------------------------------------------------------------------------
-- BACKWARD-COMPATIBILITY ALIASES (Re-exporting Stage1.TypeTheory.Smoothness)
------------------------------------------------------------------------

||| Backward-compatible alias for 13-smooth test.
public export
is13SmoothNat : Nat -> Bool
is13SmoothNat = isSmoothNat CosmicSmoothHorizon

||| Backward-compatible alias for 13-smooth type-level witness.
public export
Smooth13Witness : Nat -> Type
Smooth13Witness = SmoothWitness CosmicSmoothHorizon

||| Backward-compatible record carrier for a 13-smooth dimension.
public export
record Smooth13Dimension (n : Nat) where
  constructor MkSmooth13Dimension
  0 smoothPrf : Smooth13Witness n

public export
Eq (Smooth13Dimension n) where
  _ == _ = True

public export
Show (Smooth13Dimension n) where
  show (MkSmooth13Dimension _) = "Smooth13"

public export
0 toSmoothDimension13 : Smooth13Dimension n -> CosmicSmoothDimension
toSmoothDimension13 (MkSmooth13Dimension prf) = (n ** prf)

------------------------------------------------------------------------
-- PRIMITIVE 13-SMOOTH WITNESS INSTANCES (Backward Compatible)
------------------------------------------------------------------------

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
