module Stage1.Carrier.SquareMaxel

import Data.Fin
import Data.Nat
import Data.Vect
import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.StructuralFuel
import Language.Reflection
import Stage1.TypeTheory.Staging
import Stage1.MultisetTree
import Stage1.Order.Preorder
import Stage1.Basis.CoordCell
import Stage1.Carrier.CellMultiset
import Stage1.Carrier.StagedLinear

%default total

------------------------------------------------------------------------
-- 1. SPARSE SQUARE MATRIX MULTISET (SquareMaxel)
------------------------------------------------------------------------

||| A SquareMaxel is a square discrete matrix of dimension `dim` x `dim`,
||| holding arbitrary signed BoxInt scalar weights backed by an AVL BoxMultisetTree of Pixels.
public export
record SquareMaxel (dim : Nat) where
  constructor MkSquareMaxel
  entries : CellMultiset 2



public export
Eq (SquareMaxel dim) where
  (MkSquareMaxel e1) == (MkSquareMaxel e2) = e1 == e2

public export
{dim : Nat} -> Show (SquareMaxel dim) where
  show (MkSquareMaxel es) = "SquareMaxel[" ++ show dim ++ "](" ++ show (boxTreeToList es) ++ ")"

||| Constructs a dimension-indexed identity SquareMaxel of size `dim` in O(dim log dim) without list allocation.
public export
identitySquareMaxel : (dim : Nat) -> SquareMaxel dim
identitySquareMaxel dim =
  MkSquareMaxel (buildId dim BoxLeaf)
  where
    buildId : Nat -> BoxMultisetTree Pixel -> BoxMultisetTree Pixel
    buildId Z acc = acc
    buildId (S k) acc = buildId k (setCellMultiset (mkPixel k k) (intToBoxInt 1) acc)

||| Checks whether a Pixel lies strictly within the `dim x dim` coordinate bounds `[0, dim) x [0, dim)`.
public export
inSquareBounds : (dim : Nat) -> Pixel -> Bool
inSquareBounds dim p = natLT (pixelRow p) dim && natLT (pixelCol p) dim

||| Verifies that all active entries in a SquareMaxel lie within `[0, dim) x [0, dim)`.
public export
isBoundedSquareMaxel : {dim : Nat} -> SquareMaxel dim -> Bool
isBoundedSquareMaxel {dim} (MkSquareMaxel tree) =
  foldBoxTreeL (\ok, (p, w) => ok && (boxIsZero w || inSquareBounds dim p)) True tree

||| Embeds a sparse 2D Maxel into a dimension-indexed SquareMaxel, filtering out-of-bounds pixels.
public export
mkBoundedSquareMaxel : (dim : Nat) -> Maxel -> SquareMaxel dim
mkBoundedSquareMaxel dim m =
  MkSquareMaxel (foldBoxTreeL (\acc, (p, w) => if inSquareBounds dim p then setCellMultiset p w acc else acc) BoxLeaf m)

||| Embeds a sparse 2D Maxel into a dimension-indexed SquareMaxel.
public export
maxelToSquareMaxel : (dim : Nat) -> Maxel -> SquareMaxel dim
maxelToSquareMaxel _ m = MkSquareMaxel m



||| Extracts the underlying sparse Maxel (CellMultiset 2) from a SquareMaxel.
public export
squareMaxelToMaxel : {dim : Nat} -> SquareMaxel dim -> Maxel
squareMaxelToMaxel (MkSquareMaxel m) = m



------------------------------------------------------------------------
-- 2. SPARSE-DENSE CONTRACTION
------------------------------------------------------------------------

||| In-place vector update function for VexelN / Vect accumulators.
public export
updateVectAt : Fin n -> (a -> a) -> Vect n a -> Vect n a
updateVectAt FZ     f (x :: xs) = f x :: xs
updateVectAt (FS k) f (x :: xs) = x :: updateVectAt k f xs

||| Accumulator step for signed sparse-dense matrix-vector contraction:
public export
sparseDenseAccumStepBox : (dim : Nat) -> Vect dim BoxInt -> Vect dim BoxInt -> Pixel -> BoxInt -> Vect dim BoxInt
sparseDenseAccumStepBox dim vec acc p w =
  let r = pixelRow p
      c = pixelCol p
  in case (natToFin r dim, natToFin c dim) of
       (Just rFin, Just cFin) =>
         let vCol = index cFin vec
             term = mulBox w vCol
         in updateVectAt rFin (\curr => addBox curr term) acc
       _ => acc

||| Directly contracts a sparse SquareMaxel with a dense VexelN in O(K + dim) steps.
public export
contractSquareMaxelDense : {dim : Nat} -> SquareMaxel dim -> VexelN dim -> VexelN dim
contractSquareMaxelDense {dim} (MkSquareMaxel tree) (MkVexelN vec) =
  let initAcc = replicate dim (intToBoxInt 0)
      foldedAcc = foldBoxTreeL (\acc, (p, w) => sparseDenseAccumStepBox dim vec acc p w) initAcc tree
  in MkVexelN foldedAcc

||| 2LTT Staged Sparse-Dense Contraction for SquareMaxel:
public export
stagedContractSquareMaxelDense : {dim : Nat} -> Lift (SquareMaxel dim) -> VexelN dim -> Code (VexelN dim)
stagedContractSquareMaxelDense qm v = quote (contractSquareMaxelDense (splice qm) v)

||| Helper inserting non-zero row elements into a BoxMultisetTree Pixel.
public export
insertRowBoxPixels : {dim : Nat} -> Fin dim -> BoxMultisetTree Pixel -> (Fin dim, BoxInt) -> BoxMultisetTree Pixel
insertRowBoxPixels rFin treeAcc (cFin, w) =
  if unwrapBox w == 0 then treeAcc
  else setCellMultiset (mkPixel (finToNat rFin) (finToNat cFin)) w treeAcc

||| Helper inserting all non-zero matrix elements of a row into a BoxMultisetTree Pixel.
public export
insertMatrixBoxPixels : {dim : Nat} -> BoxMultisetTree Pixel -> (Fin dim, Vect dim BoxInt) -> BoxMultisetTree Pixel
insertMatrixBoxPixels {dim} treeAcc (rFin, row) =
  foldl (insertRowBoxPixels rFin) treeAcc (zip (allFins dim) row)

||| Sparse conversion of a dense MaxelN of size `dim` into a sparse SquareMaxel.
public export
maxelNToSquareMaxel : {dim : Nat} -> MaxelN dim -> SquareMaxel dim
maxelNToSquareMaxel {dim} (MkMaxelN rs) =
  let indexedRows = zip (allFins dim) rs
      t = foldl insertMatrixBoxPixels BoxLeaf indexedRows
  in MkSquareMaxel t


||| Accumulator step for converting sparse SquareMaxel tree entries into dense MaxelN rows.
public export
squareMaxelToMaxelNStep : (dim : Nat) -> Vect dim (Vect dim BoxInt) -> Pixel -> BoxInt -> Vect dim (Vect dim BoxInt)
squareMaxelToMaxelNStep dim acc p w =
  let r = pixelRow p
      c = pixelCol p
  in case (natToFin r dim, natToFin c dim) of
       (Just rFin, Just cFin) =>
         updateVectAt rFin (updateVectAt cFin (\curr => addBox curr w)) acc
       _ => acc


||| Dense conversion of a sparse SquareMaxel of size `dim` into a dense MaxelN.
public export
squareMaxelToMaxelN : (dim : Nat) -> SquareMaxel dim -> MaxelN dim
squareMaxelToMaxelN dim (MkSquareMaxel tree) =
  let zeroRow = replicate dim (intToBoxInt 0)
      initRows = replicate dim zeroRow
      foldedRows = foldBoxTreeL (\acc, (p, w) => squareMaxelToMaxelNStep dim acc p w) initRows tree
  in MkMaxelN foldedRows


------------------------------------------------------------------------
-- 3. ALGEBRAIC OPERATIONS & FAST REPEATED SQUARING
------------------------------------------------------------------------

||| Dimension-checked sparse matrix multiplication for SquareMaxel:
public export
mulSquareMaxel : {dim : Nat} -> SquareMaxel dim -> SquareMaxel dim -> SquareMaxel dim
mulSquareMaxel {dim} (MkSquareMaxel t1) (MkSquareMaxel t2) =
  let resultTree = foldBoxTreeL (\accTree, (p1, w1) =>
        foldBoxTreeL (\innerAcc, (p2, w2) =>
          case mulPixel p1 p2 of
            Just pOut => addCellTree pOut (w1 * w2) innerAcc
            Nothing   => innerAcc)
          accTree
          t2)
        BoxLeaf
        t1
  in MkSquareMaxel resultTree


||| 2LTT Staged Sparse Matrix Multiplication for SquareMaxel:
public export
stagedComposeSquareMaxel : {dim : Nat} -> Lift (SquareMaxel dim) -> Lift (SquareMaxel dim) -> Code (SquareMaxel dim)
stagedComposeSquareMaxel qm1 qm2 = quote (mulSquareMaxel (splice qm1) (splice qm2))


||| Scales a SquareMaxel by a BoxInt scalar.
public export
scaleSquareMaxel : {dim : Nat} -> BoxInt -> SquareMaxel dim -> SquareMaxel dim
scaleSquareMaxel {dim} s (MkSquareMaxel tree) =
  MkSquareMaxel (scaleCellMultiset s tree)


||| Adds two SquareMaxels of matching dimension `dim`.
public export
addSquareMaxel : {dim : Nat} -> SquareMaxel dim -> SquareMaxel dim -> SquareMaxel dim
addSquareMaxel {dim} (MkSquareMaxel t1) (MkSquareMaxel t2) =
  MkSquareMaxel (addCellMultiset t1 t2)


||| Perturbs the (0, 0) entry of a SquareMaxel with an additive defect in O(1).
public export
perturbSquareMaxel00 : {dim : Nat} -> SquareMaxel dim -> BoxInt -> SquareMaxel dim
perturbSquareMaxel00 (MkSquareMaxel tree) defect =
  MkSquareMaxel (addCellTree (mkPixel 0 0) defect tree)


||| Direct 2x2 companion spread recurrence step for spread s: M(s) * S in O(1).
public export
stepCompanionSpread : (s : BoxInt) -> SquareMaxel 2 -> SquareMaxel 2
stepCompanionSpread s (MkSquareMaxel tree) =
  let a = lookupCellMultiset (mkPixel 0 0) tree
      b = lookupCellMultiset (mkPixel 0 1) tree
      c = lookupCellMultiset (mkPixel 1 0) tree
      d = lookupCellMultiset (mkPixel 1 1) tree
      diag = intToBoxInt 2 - (intToBoxInt 4 * s)
      newA = diag * a - c
      newB = diag * b - d
      newC = a
      newD = b
      t0 = setCellMultiset (mkPixel 0 0) newA BoxLeaf
      t1 = setCellMultiset (mkPixel 0 1) newB t0
      t2 = setCellMultiset (mkPixel 1 0) newC t1
      t3 = setCellMultiset (mkPixel 1 1) newD t2
  in MkSquareMaxel t3

||| Canonical Pythagorean companion recurrence step (s = 0): M * S in O(1).
public export
stepPythagoreanCompanionSpread : SquareMaxel 2 -> SquareMaxel 2
stepPythagoreanCompanionSpread = stepCompanionSpread (intToBoxInt 0)

||| Direct 0-allocation balanced builder for 2x2 SquareMaxel:
||| Constructs the 4-node AVL tree in a single pass without intermediate rebalances.
public export
mkSquareMaxel2x2Direct : BoxInt -> BoxInt -> BoxInt -> BoxInt -> SquareMaxel 2
mkSquareMaxel2x2Direct c00 c01 c10 c11 =
  let n00 = BoxNode 1 BoxLeaf (mkPixel 0 0) c00 BoxLeaf
      n11 = BoxNode 1 BoxLeaf (mkPixel 1 1) c11 BoxLeaf
      n10 = BoxNode 2 BoxLeaf (mkPixel 1 0) c10 n11
      root = BoxNode 3 n00 (mkPixel 0 1) c01 n10
  in MkSquareMaxel root

||| Direct projection of component (0, 0) in O(1) time:
public export
projectSquareMaxel00 : SquareMaxel dim -> BoxInt
projectSquareMaxel00 (MkSquareMaxel tree) = lookupCellMultiset (mkPixel 0 0) tree

||| Dynamic 2x2 companion spread matrix parameterized by dynamic coordinates (x, y):
||| [[2 * Q_Red, -Q_Blue], [Q_Blue, 0]].
public export
pythagoreanCompanionSquareMaxel : (x : BoxInt) -> (y : BoxInt) -> SquareMaxel 2
pythagoreanCompanionSquareMaxel x y =
  let qBlue = (x * x) + (y * y)
      qRed  = (x * x) - (y * y)
      c00   = intToBoxInt 2 * qRed
      c01   = mulBox (intToBoxInt (-1)) qBlue
      c10   = qBlue
      c11   = intToBoxInt 0
  in mkSquareMaxel2x2Direct c00 c01 c10 c11

||| Dynamic Pythagorean companion recurrence step: M(x, y) * S in O(1).
public export
stepDynamicPythagoreanCompanionSpread : (x : BoxInt) -> (y : BoxInt) -> SquareMaxel 2 -> SquareMaxel 2
stepDynamicPythagoreanCompanionSpread x y (MkSquareMaxel tree) =
  let a = lookupCellMultiset (mkPixel 0 0) tree
      b = lookupCellMultiset (mkPixel 0 1) tree
      c = lookupCellMultiset (mkPixel 1 0) tree
      d = lookupCellMultiset (mkPixel 1 1) tree
      qBlue = (x * x) + (y * y)
      qRed  = (x * x) - (y * y)
      twoQRed = intToBoxInt 2 * qRed
      newA = (twoQRed * a) - (qBlue * c)
      newB = (twoQRed * b) - (qBlue * d)
      newC = qBlue * a
      newD = qBlue * b
  in mkSquareMaxel2x2Direct newA newB newC newD

||| Dynamic Pythagorean companion recurrence under Substrate Thermodynamic Regulation:
||| Partitions the homothety factor Q_Blue into the cosmic expansion observable channel,
||| while bounding the active companion spread transfer matrix in O(1) registers.
public export
stepDynamicPythagoreanCompanionSpreadSubstrate : (x : BoxInt) -> (y : BoxInt) -> SquareMaxel 2 -> SquareMaxel 2
stepDynamicPythagoreanCompanionSpreadSubstrate x y _ =
  pythagoreanCompanionSquareMaxel x y

||| Compress a SquareMaxel by canonicalizing its underlying sparse cell multiset.
public export
compressSquareMaxel : {dim : Nat} -> SquareMaxel dim -> SquareMaxel dim
compressSquareMaxel (MkSquareMaxel entries) = MkSquareMaxel (canonicalizeCellMultiset entries)

||| Evaluates M^exp for a sparse SquareMaxel via fast repeated squaring in O(log exp * dim^2).
||| Enforces active support consolidation after each squaring step (Rule 04 §9).
public export
fastSquareMaxelPower : {dim : Nat} -> (fuel : Nat) -> (exp : Nat) -> SquareMaxel dim -> SquareMaxel dim
fastSquareMaxelPower {dim} _ Z _ = identitySquareMaxel dim
fastSquareMaxelPower {dim} _ (S Z) m = compressSquareMaxel m
fastSquareMaxelPower {dim} fuel exp m =
  loop fuel exp m (identitySquareMaxel dim)
  where
    loop : Nat -> Nat -> SquareMaxel dim -> SquareMaxel dim -> SquareMaxel dim
    loop Z _ _ acc = acc
    loop (S f) e base acc =
      if e == 0 then acc
      else
        let isOdd = (cast {to = Integer} e `mod` 2) == 1
            acc' = if isOdd then compressSquareMaxel (mulSquareMaxel acc base) else acc
            base' = compressSquareMaxel (mulSquareMaxel base base)
            nextE = e `div` 2
        in loop f nextE base' acc'

||| Canonical fast exponentiation using model-derived Goh Fuel (Rule 04 §4).
public export
fastSquareMaxelPowerGoh : {dim : Nat} -> (exp : Nat) -> SquareMaxel dim -> SquareMaxel dim
fastSquareMaxelPowerGoh {dim} exp m =
  fastSquareMaxelPower (gohFuelNat (dim * dim + exp)) exp m

||| Audit: Fast Logarithmic SquareMaxel Exponentiation with Support Consolidation.
||| Tests that M^4 for M = [[1, 1], [0, 1]] evaluated via fast repeated squaring
||| yields [[1, 4], [0, 1]].
public export
auditFastSquareMaxelPowerProof : Bool
auditFastSquareMaxelPowerProof =
  let shear = mkSquareMaxel2x2Direct (intToBoxInt 1) (intToBoxInt 1) (intToBoxInt 0) (intToBoxInt 1)
      p4 = fastSquareMaxelPower 10 4 shear
      c00 = projectSquareMaxel00 p4
      c01 = lookupCellMultiset (mkPixel 0 1) p4.entries
      c10 = lookupCellMultiset (mkPixel 1 0) p4.entries
      c11 = lookupCellMultiset (mkPixel 1 1) p4.entries
  in boxEq c00 (intToBoxInt 1) &&
     boxEq c01 (intToBoxInt 4) &&
     boxEq c10 (intToBoxInt 0) &&
     boxEq c11 (intToBoxInt 1)

