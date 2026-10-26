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

||| Backward-compatibility alias for BoxSquareMaxel.
public export
BoxSquareMaxel : (dim : Nat) -> Type
BoxSquareMaxel = SquareMaxel

||| Backward-compatibility constructor alias.
public export
MkBoxSquareMaxel : {dim : Nat} -> CellMultiset 2 -> SquareMaxel dim
MkBoxSquareMaxel = MkSquareMaxel

public export
Eq (SquareMaxel dim) where
  (MkSquareMaxel e1) == (MkSquareMaxel e2) =
    boxTreeToList e1 == boxTreeToList e2

public export
{dim : Nat} -> Show (SquareMaxel dim) where
  show (MkSquareMaxel es) = "SquareMaxel[" ++ show dim ++ "](" ++ show (boxTreeToList es) ++ ")"

||| Constructs a dimension-indexed identity SquareMaxel of size `dim` in O(dim log dim).
public export
identitySquareMaxel : (dim : Nat) -> SquareMaxel dim
identitySquareMaxel dim =
  case dim of
    Z => MkSquareMaxel BoxLeaf
    _ => let pxs = [mkPixel i i | i <- [0..pred dim]]
             t   = foldl (\tree, p => setBoxTree p (intToBoxInt 1) tree) BoxLeaf pxs
         in MkSquareMaxel t

||| Backward-compatibility alias.
public export
identityBoxSquareMaxel : (dim : Nat) -> SquareMaxel dim
identityBoxSquareMaxel = identitySquareMaxel

||| Embeds a sparse 2D Maxel into a dimension-indexed SquareMaxel.
public export
maxelToSquareMaxel : (dim : Nat) -> Maxel -> SquareMaxel dim
maxelToSquareMaxel _ m = MkSquareMaxel m

||| Backward-compatibility alias.
public export
maxelToBoxSquareMaxel : (dim : Nat) -> Maxel -> SquareMaxel dim
maxelToBoxSquareMaxel = maxelToSquareMaxel

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

||| Backward-compatibility alias.
public export
contractBoxSquareDense : {dim : Nat} -> SquareMaxel dim -> VexelN dim -> VexelN dim
contractBoxSquareDense = contractSquareMaxelDense

||| 2LTT Staged Sparse-Dense Contraction for SquareMaxel:
public export
stagedContractSquareMaxelDense : {dim : Nat} -> Lift (SquareMaxel dim) -> VexelN dim -> Code (VexelN dim)
stagedContractSquareMaxelDense qm v = quote (contractSquareMaxelDense (splice qm) v)

||| Backward-compatibility alias.
public export
stagedContractBoxSquareDense : {dim : Nat} -> Lift (SquareMaxel dim) -> VexelN dim -> Code (VexelN dim)
stagedContractBoxSquareDense = stagedContractSquareMaxelDense

||| Helper inserting non-zero row elements into a BoxMultisetTree Pixel.
public export
insertRowBoxPixels : {dim : Nat} -> Fin dim -> BoxMultisetTree Pixel -> (Fin dim, BoxInt) -> BoxMultisetTree Pixel
insertRowBoxPixels rFin treeAcc (cFin, w) =
  if unwrapBox w == 0 then treeAcc
  else setBoxTree (mkPixel (finToNat rFin) (finToNat cFin)) w treeAcc

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

||| Backward-compatibility alias.
public export
maxelNToBoxSquareMaxel : {dim : Nat} -> MaxelN dim -> SquareMaxel dim
maxelNToBoxSquareMaxel = maxelNToSquareMaxel

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

public export
boxSquareMaxelToMaxelNStep : (dim : Nat) -> Vect dim (Vect dim BoxInt) -> Pixel -> BoxInt -> Vect dim (Vect dim BoxInt)
boxSquareMaxelToMaxelNStep = squareMaxelToMaxelNStep

||| Dense conversion of a sparse SquareMaxel of size `dim` into a dense MaxelN.
public export
squareMaxelToMaxelN : (dim : Nat) -> SquareMaxel dim -> MaxelN dim
squareMaxelToMaxelN dim (MkSquareMaxel tree) =
  let zeroRow = replicate dim (intToBoxInt 0)
      initRows = replicate dim zeroRow
      foldedRows = foldBoxTreeL (\acc, (p, w) => squareMaxelToMaxelNStep dim acc p w) initRows tree
  in MkMaxelN foldedRows

public export
boxSquareMaxelToMaxelN : (dim : Nat) -> SquareMaxel dim -> MaxelN dim
boxSquareMaxelToMaxelN = squareMaxelToMaxelN

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
            Just pOut =>
              let wOut = w1 * w2
                  cur = lookupBoxTree pOut innerAcc
                  newW = cur + wOut
              in if unwrapBox newW == 0
                   then innerAcc
                   else setBoxTree pOut newW innerAcc
            Nothing => innerAcc)
          accTree
          t2)
        BoxLeaf
        t1
  in MkSquareMaxel resultTree

public export
mulBoxSquareMaxel : {dim : Nat} -> SquareMaxel dim -> SquareMaxel dim -> SquareMaxel dim
mulBoxSquareMaxel = mulSquareMaxel

||| 2LTT Staged Sparse Matrix Multiplication for SquareMaxel:
public export
stagedComposeSquareMaxel : {dim : Nat} -> Lift (SquareMaxel dim) -> Lift (SquareMaxel dim) -> Code (SquareMaxel dim)
stagedComposeSquareMaxel qm1 qm2 = quote (mulSquareMaxel (splice qm1) (splice qm2))

public export
stagedComposeBoxSquareMaxel : {dim : Nat} -> Lift (SquareMaxel dim) -> Lift (SquareMaxel dim) -> Code (SquareMaxel dim)
stagedComposeBoxSquareMaxel = stagedComposeSquareMaxel

||| Scales a SquareMaxel by a BoxInt scalar.
public export
scaleSquareMaxel : {dim : Nat} -> BoxInt -> SquareMaxel dim -> SquareMaxel dim
scaleSquareMaxel {dim} s (MkSquareMaxel tree) =
  if boxIsZero s
    then MkSquareMaxel BoxLeaf
    else let scaled = foldBoxTreeL (\acc, (p, w) => setBoxTree p (s * w) acc) BoxLeaf tree
         in MkSquareMaxel scaled

public export
scaleBoxSquareMaxel : {dim : Nat} -> BoxInt -> SquareMaxel dim -> SquareMaxel dim
scaleBoxSquareMaxel = scaleSquareMaxel

||| Adds two SquareMaxels of matching dimension `dim`.
public export
addSquareMaxel : {dim : Nat} -> SquareMaxel dim -> SquareMaxel dim -> SquareMaxel dim
addSquareMaxel {dim} (MkSquareMaxel t1) (MkSquareMaxel t2) =
  let step : BoxMultisetTree Pixel -> (Pixel, BoxInt) -> BoxMultisetTree Pixel
      step acc (p, w) =
        let cur = lookupBoxTree p acc
            newW = cur + w
        in if boxIsZero newW
             then setBoxTree p (intToBoxInt 0) acc
             else setBoxTree p newW acc
      sumTree = foldBoxTreeL step t1 t2
  in MkSquareMaxel sumTree

public export
addBoxSquareMaxel : {dim : Nat} -> SquareMaxel dim -> SquareMaxel dim -> SquareMaxel dim
addBoxSquareMaxel = addSquareMaxel

||| Evaluates M^exp for a sparse SquareMaxel via fast repeated squaring in O(log exp * dim^2).
public export
fastSquareMaxelPower : {dim : Nat} -> (fuel : Nat) -> (exp : Nat) -> SquareMaxel dim -> SquareMaxel dim
fastSquareMaxelPower {dim} _ Z _ = identitySquareMaxel dim
fastSquareMaxelPower {dim} _ (S Z) m = m
fastSquareMaxelPower {dim} fuel exp m =
  loop fuel exp m (identitySquareMaxel dim)
  where
    loop : Nat -> Nat -> SquareMaxel dim -> SquareMaxel dim -> SquareMaxel dim
    loop Z _ _ acc = acc
    loop (S f) e base acc =
      if e == 0 then acc
      else
        let isOdd = (cast {to = Integer} e `mod` 2) == 1
            acc' = if isOdd then mulSquareMaxel acc base else acc
            base' = mulSquareMaxel base base
            nextE = e `div` 2
        in loop f nextE base' acc'

public export
fastBoxSquareMaxelPower : {dim : Nat} -> (fuel : Nat) -> (exp : Nat) -> SquareMaxel dim -> SquareMaxel dim
fastBoxSquareMaxelPower = fastSquareMaxelPower
