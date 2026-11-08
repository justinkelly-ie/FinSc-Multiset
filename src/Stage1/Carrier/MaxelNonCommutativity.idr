module Stage1.Carrier.MaxelNonCommutativity

import Data.Nat
import Stage0.BoxInt
import Stage0.Multiset
import Stage0.Basis.GeometricPixel
import Stage0.OnSeq.FusedStream
import Stage1.Basis.CoordCell
import Stage1.Carrier.CellMultiset
import Stage1.Carrier.Maxel
import Stage1.MultisetTree
import Language.Reflection

%default total

------------------------------------------------------------------------
-- 1. PIXEL BASIS CONTRACTION THEOREMS
--    [A, B] · [C, D] = [A, D] iff B = C; 0 otherwise.
------------------------------------------------------------------------

||| Theorem 1 (Basis Propagation):
||| When the column token of the first pixel matches the row token of the second,
||| contraction propagates the outer boundary coordinates [A, C].
public export
0 prfContractionPropagation123 : mulPixel (mkPixel 1 2) (mkPixel 2 3) = Just (mkPixel 1 3)
prfContractionPropagation123 = Refl

||| Theorem 2 (Basis Annihilation):
||| When the inner tokens mismatch (B ≠ C), the contraction product vanishes identically to Nothing.
public export
0 prfContractionAnnihilation1234 : mulPixel (mkPixel 1 2) (mkPixel 3 4) = Nothing
prfContractionAnnihilation1234 = Refl

||| Theorem 3 (Fermionic / Grassmann Nilpotency):
||| Off-diagonal basis pixels square to zero: [A, B] · [A, B] = 0 when A ≠ B.
public export
0 prfGrassmannNilpotency12 : mulPixel (mkPixel 1 2) (mkPixel 1 2) = Nothing
prfGrassmannNilpotency12 = Refl

public export
0 prfGrassmannNilpotency21 : mulPixel (mkPixel 2 1) (mkPixel 2 1) = Nothing
prfGrassmannNilpotency21 = Refl

||| Theorem 4 (Idempotent Basis Projection):
||| Diagonal pixels act as idempotent projection operators: [A, A] · [A, A] = [A, A].
public export
0 prfIdempotentProjection11 : mulPixel (mkPixel 1 1) (mkPixel 1 1) = Just (mkPixel 1 1)
prfIdempotentProjection11 = Refl

public export
0 prfIdempotentProjection22 : mulPixel (mkPixel 2 2) (mkPixel 2 2) = Just (mkPixel 2 2)
prfIdempotentProjection22 = Refl

------------------------------------------------------------------------
-- 2. EMERGENCE OF NON-COMMUTATIVITY FROM COMMUTATIVE MULTISETS
------------------------------------------------------------------------

||| Elementary Maxel basis unit [1, 2] with unit weight.
public export
M12 : Maxel
M12 = singletonCell (mkPixel 1 2) (intToBoxInt 1)

||| Elementary Maxel basis unit [2, 1] with unit weight.
public export
M21 : Maxel
M21 = singletonCell (mkPixel 2 1) (intToBoxInt 1)

||| Forward contraction product: [1, 2] · [2, 1] = [1, 1].
public export
M12_M21 : Maxel
M12_M21 = mulMaxel M12 M21

||| Reverse contraction product: [2, 1] · [1, 2] = [2, 2].
public export
M21_M12 : Maxel
M21_M12 = mulMaxel M21 M12

||| Proves definitionally that the forward product contains [1, 1] with weight 1.
public export
0 prfForwardProductWeight11 : lookupCellMultiset (mkPixel 1 1) Stage1.Carrier.MaxelNonCommutativity.M12_M21 = intToBoxInt 1
prfForwardProductWeight11 = Refl

||| Proves definitionally that the forward product has zero weight at [2, 2].
public export
0 prfForwardProductWeight22 : lookupCellMultiset (mkPixel 2 2) Stage1.Carrier.MaxelNonCommutativity.M12_M21 = intToBoxInt 0
prfForwardProductWeight22 = Refl

||| Proves definitionally that the reverse product contains [2, 2] with weight 1.
public export
0 prfReverseProductWeight22 : lookupCellMultiset (mkPixel 2 2) Stage1.Carrier.MaxelNonCommutativity.M21_M12 = intToBoxInt 1
prfReverseProductWeight22 = Refl

||| Proves definitionally that the reverse product has zero weight at [1, 1].
public export
0 prfReverseProductWeight11 : lookupCellMultiset (mkPixel 1 1) Stage1.Carrier.MaxelNonCommutativity.M21_M12 = intToBoxInt 0
prfReverseProductWeight11 = Refl

||| Contrast with Multiset Addition:
||| Both M12 + M21 and M21 + M12 yield identical observable multiset weight distributions.
public export
0 prfMaxelAddWeightEquivalence12 :
  lookupCellMultiset (mkPixel 1 2) (addMaxel Stage1.Carrier.MaxelNonCommutativity.M12 Stage1.Carrier.MaxelNonCommutativity.M21) =
  lookupCellMultiset (mkPixel 1 2) (addMaxel Stage1.Carrier.MaxelNonCommutativity.M21 Stage1.Carrier.MaxelNonCommutativity.M12)
prfMaxelAddWeightEquivalence12 = Refl

public export
0 prfMaxelAddWeightEquivalence21 :
  lookupCellMultiset (mkPixel 2 1) (addMaxel Stage1.Carrier.MaxelNonCommutativity.M12 Stage1.Carrier.MaxelNonCommutativity.M21) =
  lookupCellMultiset (mkPixel 2 1) (addMaxel Stage1.Carrier.MaxelNonCommutativity.M21 Stage1.Carrier.MaxelNonCommutativity.M12)
prfMaxelAddWeightEquivalence21 = Refl

------------------------------------------------------------------------
-- 3. COMPILE-TIME ELABORATOR REFLECTION AUDIT (RULE 01)
------------------------------------------------------------------------

||| Decision boolean certifying that the forward product differs from the reverse product:
||| M12 · M21 ≠ M21 · M12, establishing that non-commutativity emerges from pixel contraction.
public export
auditMaxelNonCommutativityProofExport : Bool
auditMaxelNonCommutativityProofExport =
  let w11_fwd = lookupCellMultiset (mkPixel 1 1) M12_M21
      w22_fwd = lookupCellMultiset (mkPixel 2 2) M12_M21
      w11_rev = lookupCellMultiset (mkPixel 1 1) M21_M12
      w22_rev = lookupCellMultiset (mkPixel 2 2) M21_M12
  in boxEq w11_fwd (intToBoxInt 1) &&
     boxEq w22_fwd (intToBoxInt 0) &&
     boxEq w11_rev (intToBoxInt 0) &&
     boxEq w22_rev (intToBoxInt 1)

||| Compile-time proof witness that non-commutativity is verified at typecheck time.
public export
0 prfAuditMaxelNonCommutativity : Stage1.Carrier.MaxelNonCommutativity.auditMaxelNonCommutativityProofExport = True
prfAuditMaxelNonCommutativity = Refl

||| Elaborator reflection macro auditing the emergence of non-commutativity at compile time.
public export
%macro
auditMaxelNonCommutativity : Elab (Stage1.Carrier.MaxelNonCommutativity.auditMaxelNonCommutativityProofExport = True)
auditMaxelNonCommutativity = pure Refl
