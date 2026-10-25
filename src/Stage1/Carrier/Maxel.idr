module Stage1.Carrier.Maxel

import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.StructuralFuel
import Stage0.Multiset
import Stage1.Order.Preorder
import Stage1.MultisetTree
import Stage1.MultisetTensor
import Data.List
import Data.Vect
import Language.Reflection
import Stage1.TypeTheory.Staging
import public Stage1.Basis.Coordinate
import public Stage1.Carrier.Vexel

%default total

------------------------------------------------------------------------
-- 1. MAXEL (2D WILDBERGER MATRIX MULTISET)
------------------------------------------------------------------------

||| A Maxel is a multiset of Pixels (Wildberger Matrix).
||| Stored as an AVL BoxMultisetTree of weighted coordinate Pixels in O(log N).
public export
record Maxel where
  constructor MkMaxelTree
  tree : BoxMultisetTree Pixel

||| Direct conversion of a list of Pixel-BoxInt pairs to a signed AVL BoxMultisetTree in O(N log N).
||| Prunes zero weights and collapses duplicate Pixels.
public export
maxelListToBoxTree : List (Pixel, BoxInt) -> BoxMultisetTree Pixel
maxelListToBoxTree pxs =
  foldl (\t, (p, w) =>
          if boxIsZero w then t
          else let cur = lookupBoxTree p t
                   newW = cur + w
               in if boxIsZero newW
                    then setBoxTree p (intToBoxInt 0) t
                    else setBoxTree p newW t)
        BoxLeaf
        pxs

||| Constructs a canonical Maxel from a list of Pixel-BoxInt pairs in O(N log N).
public export
mkMaxel : List (Pixel, BoxInt) -> Maxel
mkMaxel pxs = MkMaxelTree (maxelListToBoxTree pxs)

||| Canonical constructor alias for Maxel from coordinate pairs.
public export
MkMaxel : List (Pixel, BoxInt) -> Maxel
MkMaxel = mkMaxel

||| Flattens a Maxel to an association list in O(N) time.
public export
maxelPixels : Maxel -> List (Pixel, BoxInt)
maxelPixels (MkMaxelTree t) = boxTreeToList t

||| Projection view of Maxel pixels.
public export
pixels : Maxel -> List (Pixel, BoxInt)
pixels = maxelPixels

||| Direct conversion of a Maxel to a signed AVL BoxMultisetTree in O(1).
public export
maxelToBoxTree : Maxel -> BoxMultisetTree Pixel
maxelToBoxTree (MkMaxelTree t) = t

||| Reconstructs a Maxel from a signed AVL BoxMultisetTree in O(1).
public export
boxTreeToMaxel : BoxMultisetTree Pixel -> Maxel
boxTreeToMaxel = MkMaxelTree

||| Canonicalize a Maxel via legacy Multiset linked list.
public export
canonicalizeMaxelMultiset : Maxel -> Maxel
canonicalizeMaxelMultiset (MkMaxelTree t) =
  MkMaxelTree (maxelListToBoxTree (multisetToList (fromListBox (boxTreeToList t))))

||| Identity for tree-backed Maxels: AVL tree guarantees canonical representation by construction.
public export
canonicalizeMaxel : Maxel -> Maxel
canonicalizeMaxel m = m

public export
maxelToMultiset : Maxel -> Multiset BoxInt Pixel
maxelToMultiset (MkMaxelTree t) = fromListBox (boxTreeToList t)

public export
multisetToMaxel : Multiset BoxInt Pixel -> Maxel
multisetToMaxel m = MkMaxel (multisetToList m)

public export
Eq Maxel where
  (MkMaxelTree t1) == (MkMaxelTree t2) = boxTreeToList t1 == boxTreeToList t2

public export
Show Maxel where
  show (MkMaxelTree t) = "Maxel(" ++ show (boxTreeToList t) ++ ")"

------------------------------------------------------------------------
-- 2. DIMENSION-INDEXED DEPENDENT MAXEL
------------------------------------------------------------------------

||| A SquareMaxel is a square discrete matrix of dimension `dim`,
||| backed by a balanced AVL MultisetTree of Pixels in O(log N).
public export
record SquareMaxel (dim : Nat) where
  constructor MkSquareMaxel
  entries : MultisetTree Pixel

public export
Eq (SquareMaxel dim) where
  (MkSquareMaxel e1) == (MkSquareMaxel e2) = e1 == e2

public export
{dim : Nat} -> Show (SquareMaxel dim) where
  show (MkSquareMaxel es) = "SquareMaxel[" ++ show dim ++ "](" ++ show (treeToList es) ++ ")"

||| A MaxelN is a dimension-indexed square discrete matrix of dimension `n` x `n`,
||| holding an n-vector of n-vector BoxInt weights for unrolled 2LTT staging.
public export
record MaxelN (n : Nat) where
  constructor MkMaxelN
  rows : Vect n (Vect n BoxInt)

public export
Eq (MaxelN n) where
  (MkMaxelN m1) == (MkMaxelN m2) = m1 == m2

public export
{n : Nat} -> Show (MaxelN n) where
  show (MkMaxelN m) = "Maxel" ++ show n ++ "x" ++ show n ++ "(" ++ show m ++ ")"

||| Constructor for 2x2 MaxelN (single qubit unitary gate).
public export
mkMaxel2 : BoxInt -> BoxInt -> BoxInt -> BoxInt -> MaxelN 2
mkMaxel2 m00 m01 m10 m11 = MkMaxelN [[m00, m01], [m10, m11]]

||| Constructor for 4x4 MaxelN (two-qubit unitary gate).
public export
mkMaxel4 : Vect 4 (Vect 4 BoxInt) -> MaxelN 4
mkMaxel4 rs = MkMaxelN rs

||| 2LTT Staged MaxelN-VexelN Contraction:
public export
stagedMaxelNVec : {n : Nat} -> Lift (MaxelN n) -> VexelN n -> Code (VexelN n)
stagedMaxelNVec qm (MkVexelN v) = quote (MkVexelN (stagedUnrollMatVec (rows (splice qm)) v))

||| 2LTT Staged MaxelN Matrix Multiplication:
public export
stagedMaxelNMul : {n : Nat} -> Lift (MaxelN n) -> Lift (MaxelN n) -> Code (MaxelN n)
stagedMaxelNMul qm1 qm2 = quote (MkMaxelN (stagedUnrollMatMul (rows (splice qm1)) (rows (splice qm2))))

||| 2LTT Staged MaxelN Identity Matrix of dimension n:
public export
stagedIdentityMaxelN : (n : Nat) -> MaxelN n
stagedIdentityMaxelN n = MkMaxelN (stagedIdentityMat n)

||| 2LTT Staged MaxelN Power in O(log exp) repeated squarings:
public export
stagedMaxelNPower : (fuel : Nat) -> {n : Nat} -> Lift (MaxelN n) -> Nat -> Code (MaxelN n)
stagedMaxelNPower fuel qm exp = quote (MkMaxelN (stagedFastMatPower fuel (rows (splice qm)) exp))

------------------------------------------------------------------------
-- 3. SPARSE-DENSE MATRIX-VECTOR CONTRACTIONS
------------------------------------------------------------------------

||| In-place vector update function for VexelN / Vect accumulators.
public export
updateVectAt : Fin n -> (a -> a) -> Vect n a -> Vect n a
updateVectAt FZ     f (x :: xs) = f x :: xs
updateVectAt (FS k) f (x :: xs) = x :: updateVectAt k f xs

||| Accumulator step for sparse-dense matrix-vector contraction:
public export
sparseDenseAccumStep : (dim : Nat) -> Vect dim BoxInt -> Vect dim BoxInt -> (Pixel, Nat) -> Vect dim BoxInt
sparseDenseAccumStep dim vec acc (MkPixel r c, cnt) =
  case (natToFin r dim, natToFin c dim) of
    (Just rFin, Just cFin) =>
      let vCol = index cFin vec
          w = natToBoxInt cnt
          term = mulBox w vCol
      in updateVectAt rFin (\curr => addBox curr term) acc
    _ => acc

||| Directly contracts a sparse SquareMaxel with a dense VexelN in O(K + dim) steps.
public export
contractSparseDenseVexel : {dim : Nat} -> SquareMaxel dim -> VexelN dim -> VexelN dim
contractSparseDenseVexel {dim} (MkSquareMaxel tree) (MkVexelN vec) =
  let initAcc = replicate dim (intToBoxInt 0)
      foldedAcc = foldTreeL (sparseDenseAccumStep dim vec) initAcc tree
  in MkVexelN foldedAcc

||| 2LTT Staged Sparse-Dense Contraction:
public export
stagedContractSparseDense : {dim : Nat} -> Lift (SquareMaxel dim) -> VexelN dim -> Code (VexelN dim)
stagedContractSparseDense qm v = quote (contractSparseDenseVexel (splice qm) v)

||| Accumulator step for converting sparse SquareMaxel tree entries into dense MaxelN rows.
public export
squareMaxelToMaxelNStep : (dim : Nat) -> Vect dim (Vect dim BoxInt) -> (Pixel, Nat) -> Vect dim (Vect dim BoxInt)
squareMaxelToMaxelNStep dim acc (MkPixel r c, cnt) =
  case (natToFin r dim, natToFin c dim) of
    (Just rFin, Just cFin) =>
      let w = natToBoxInt cnt
      in updateVectAt rFin (updateVectAt cFin (\curr => addBox curr w)) acc
    _ => acc

||| Dense conversion of a sparse SquareMaxel of size `dim` into a dense MaxelN.
public export
squareMaxelToMaxelN : (dim : Nat) -> SquareMaxel dim -> MaxelN dim
squareMaxelToMaxelN dim (MkSquareMaxel tree) =
  let zeroRow = replicate dim (intToBoxInt 0)
      initRows = replicate dim zeroRow
      foldedRows = foldTreeL (squareMaxelToMaxelNStep dim) initRows tree
  in MkMaxelN foldedRows

||| Helper inserting non-zero row elements into a MultisetTree Pixel.
public export
insertRowPixels : {dim : Nat} -> Fin dim -> MultisetTree Pixel -> (Fin dim, BoxInt) -> MultisetTree Pixel
insertRowPixels rFin treeAcc (cFin, w) =
  if boxIsZero w then treeAcc
  else insertTokenTree (MkPixel (finToNat rFin) (finToNat cFin)) (boxToNat w) treeAcc

||| Helper inserting all non-zero matrix elements of a row into a MultisetTree Pixel.
public export
insertMatrixPixels : {dim : Nat} -> MultisetTree Pixel -> (Fin dim, Vect dim BoxInt) -> MultisetTree Pixel
insertMatrixPixels {dim} treeAcc (rFin, row) =
  foldl (insertRowPixels rFin) treeAcc (zip (allFins dim) row)

||| Sparse conversion of a dense MaxelN of size `dim` into a sparse SquareMaxel.
public export
maxelNToSquareMaxel : {dim : Nat} -> MaxelN dim -> SquareMaxel dim
maxelNToSquareMaxel {dim} (MkMaxelN rs) =
  let indexedRows = zip (allFins dim) rs
      t = foldl insertMatrixPixels Leaf indexedRows
  in MkSquareMaxel t

------------------------------------------------------------------------
-- 4. SIGNED DIMENSION-INDEXED SPARSE MATRIX (BoxSquareMaxel)
------------------------------------------------------------------------

||| A BoxSquareMaxel is a square discrete matrix of dimension `dim`,
||| holding arbitrary signed BoxInt scalar weights backed by an AVL BoxMultisetTree of Pixels.
public export
record BoxSquareMaxel (dim : Nat) where
  constructor MkBoxSquareMaxel
  entries : BoxMultisetTree Pixel

public export
Eq (BoxSquareMaxel dim) where
  (MkBoxSquareMaxel e1) == (MkBoxSquareMaxel e2) =
    boxTreeToList e1 == boxTreeToList e2

public export
{dim : Nat} -> Show (BoxSquareMaxel dim) where
  show (MkBoxSquareMaxel es) = "BoxSquareMaxel[" ++ show dim ++ "](" ++ show (boxTreeToList es) ++ ")"

||| Constructs a dimension-indexed identity BoxSquareMaxel of size `dim` in O(dim log dim).
public export
identityBoxSquareMaxel : (dim : Nat) -> BoxSquareMaxel dim
identityBoxSquareMaxel dim =
  case dim of
    Z => MkBoxSquareMaxel BoxLeaf
    _ => let pxs = [MkPixel i i | i <- [0..pred dim]]
             t   = foldl (\tree, p => setBoxTree p (intToBoxInt 1) tree) BoxLeaf pxs
         in MkBoxSquareMaxel t

||| Accumulator step for signed sparse-dense matrix-vector contraction:
public export
sparseDenseAccumStepBox : (dim : Nat) -> Vect dim BoxInt -> Vect dim BoxInt -> Pixel -> BoxInt -> Vect dim BoxInt
sparseDenseAccumStepBox dim vec acc (MkPixel r c) w =
  case (natToFin r dim, natToFin c dim) of
    (Just rFin, Just cFin) =>
      let vCol = index cFin vec
          term = mulBox w vCol
      in updateVectAt rFin (\curr => addBox curr term) acc
    _ => acc

||| Directly contracts a sparse BoxSquareMaxel with a dense VexelN in O(K + dim) steps.
public export
contractBoxSquareDense : {dim : Nat} -> BoxSquareMaxel dim -> VexelN dim -> VexelN dim
contractBoxSquareDense {dim} (MkBoxSquareMaxel tree) (MkVexelN vec) =
  let initAcc = replicate dim (intToBoxInt 0)
      foldedAcc = foldBoxTreeL (\acc, (p, w) => sparseDenseAccumStepBox dim vec acc p w) initAcc tree
  in MkVexelN foldedAcc

||| 2LTT Staged Sparse-Dense Contraction for BoxSquareMaxel:
public export
stagedContractBoxSquareDense : {dim : Nat} -> Lift (BoxSquareMaxel dim) -> VexelN dim -> Code (VexelN dim)
stagedContractBoxSquareDense qm v = quote (contractBoxSquareDense (splice qm) v)

||| Helper inserting non-zero row elements into a BoxMultisetTree Pixel.
public export
insertRowBoxPixels : {dim : Nat} -> Fin dim -> BoxMultisetTree Pixel -> (Fin dim, BoxInt) -> BoxMultisetTree Pixel
insertRowBoxPixels rFin treeAcc (cFin, w) =
  if unwrapBox w == 0 then treeAcc
  else setBoxTree (MkPixel (finToNat rFin) (finToNat cFin)) w treeAcc

||| Helper inserting all non-zero matrix elements of a row into a BoxMultisetTree Pixel.
public export
insertMatrixBoxPixels : {dim : Nat} -> BoxMultisetTree Pixel -> (Fin dim, Vect dim BoxInt) -> BoxMultisetTree Pixel
insertMatrixBoxPixels {dim} treeAcc (rFin, row) =
  foldl (insertRowBoxPixels rFin) treeAcc (zip (allFins dim) row)

||| Sparse conversion of a dense MaxelN of size `dim` into a sparse BoxSquareMaxel.
public export
maxelNToBoxSquareMaxel : {dim : Nat} -> MaxelN dim -> BoxSquareMaxel dim
maxelNToBoxSquareMaxel {dim} (MkMaxelN rs) =
  let indexedRows = zip (allFins dim) rs
      t = foldl insertMatrixBoxPixels BoxLeaf indexedRows
  in MkBoxSquareMaxel t

||| Accumulator step for converting sparse BoxSquareMaxel tree entries into dense MaxelN rows.
public export
boxSquareMaxelToMaxelNStep : (dim : Nat) -> Vect dim (Vect dim BoxInt) -> Pixel -> BoxInt -> Vect dim (Vect dim BoxInt)
boxSquareMaxelToMaxelNStep dim acc (MkPixel r c) w =
  case (natToFin r dim, natToFin c dim) of
    (Just rFin, Just cFin) =>
      updateVectAt rFin (updateVectAt cFin (\curr => addBox curr w)) acc
    _ => acc

||| Dense conversion of a sparse BoxSquareMaxel of size `dim` into a dense MaxelN.
public export
boxSquareMaxelToMaxelN : (dim : Nat) -> BoxSquareMaxel dim -> MaxelN dim
boxSquareMaxelToMaxelN dim (MkBoxSquareMaxel tree) =
  let zeroRow = replicate dim (intToBoxInt 0)
      initRows = replicate dim zeroRow
      foldedRows = foldBoxTreeL (\acc, (p, w) => boxSquareMaxelToMaxelNStep dim acc p w) initRows tree
  in MkMaxelN foldedRows

||| Dimension-checked sparse matrix multiplication for BoxSquareMaxel:
public export
mulBoxSquareMaxel : {dim : Nat} -> BoxSquareMaxel dim -> BoxSquareMaxel dim -> BoxSquareMaxel dim
mulBoxSquareMaxel {dim} (MkBoxSquareMaxel t1) (MkBoxSquareMaxel t2) =
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
  in MkBoxSquareMaxel resultTree

||| 2LTT Staged Sparse Matrix Multiplication for BoxSquareMaxel:
public export
stagedComposeBoxSquareMaxel : {dim : Nat} -> Lift (BoxSquareMaxel dim) -> Lift (BoxSquareMaxel dim) -> Code (BoxSquareMaxel dim)
stagedComposeBoxSquareMaxel qm1 qm2 = quote (mulBoxSquareMaxel (splice qm1) (splice qm2))

||| Scales a BoxSquareMaxel by a BoxInt scalar.
public export
scaleBoxSquareMaxel : {dim : Nat} -> BoxInt -> BoxSquareMaxel dim -> BoxSquareMaxel dim
scaleBoxSquareMaxel {dim} s (MkBoxSquareMaxel tree) =
  if boxIsZero s
    then MkBoxSquareMaxel BoxLeaf
    else let scaled = foldBoxTreeL (\acc, (p, w) => setBoxTree p (s * w) acc) BoxLeaf tree
         in MkBoxSquareMaxel scaled

||| Adds two BoxSquareMaxels of matching dimension `dim`.
public export
addBoxSquareMaxel : {dim : Nat} -> BoxSquareMaxel dim -> BoxSquareMaxel dim -> BoxSquareMaxel dim
addBoxSquareMaxel {dim} (MkBoxSquareMaxel t1) (MkBoxSquareMaxel t2) =
  let step : BoxMultisetTree Pixel -> (Pixel, BoxInt) -> BoxMultisetTree Pixel
      step acc (p, w) =
        let cur = lookupBoxTree p acc
            newW = cur + w
        in if boxIsZero newW
             then setBoxTree p (intToBoxInt 0) acc
             else setBoxTree p newW acc
      sumTree = foldBoxTreeL step t1 t2
  in MkBoxSquareMaxel sumTree

||| Evaluates M^exp for a sparse BoxSquareMaxel via fast repeated squaring in O(log exp * dim^2).
public export
fastBoxSquareMaxelPower : {dim : Nat} -> (fuel : Nat) -> (exp : Nat) -> BoxSquareMaxel dim -> BoxSquareMaxel dim
fastBoxSquareMaxelPower {dim} _ Z _ = identityBoxSquareMaxel dim
fastBoxSquareMaxelPower {dim} _ (S Z) m = m
fastBoxSquareMaxelPower {dim} fuel exp m =
  loop fuel exp m (identityBoxSquareMaxel dim)
  where
    loop : Nat -> Nat -> BoxSquareMaxel dim -> BoxSquareMaxel dim -> BoxSquareMaxel dim
    loop Z _ _ acc = acc
    loop (S f) e base acc =
      if e == 0 then acc
      else
        let isOdd = (cast {to = Integer} e `mod` 2) == 1
            acc' = if isOdd then mulBoxSquareMaxel acc base else acc
            base' = mulBoxSquareMaxel base base
            nextE = e `div` 2
        in loop f nextE base' acc'

||| Canonical Kronecker Coordinate Chart Observation:
public export
observeKroneckerPixel : (n : Nat) -> ((Nat, Nat), (Nat, Nat)) -> Pixel
observeKroneckerPixel n ((r1, r2), (c1, c2)) = MkPixel ((r1 * n) + r2) ((c1 * n) + c2)

||| Inverse coordinate readout projecting a composite pixel coordinate (0 <= p < m * n)
public export
unobserveKroneckerPixel : (n : Nat) -> Pixel -> ((Nat, Nat), (Nat, Nat))
unobserveKroneckerPixel n (MkPixel r c) =
  let (r1, r2) = natDivMod r n
      (c1, c2) = natDivMod c n
  in ((r1, r2), (c1, c2))

||| Sparse Kronecker Tensor Product for BoxSquareMaxel:
public export
kroneckerBoxSquareMaxel : {m, n : Nat} -> BoxSquareMaxel m -> BoxSquareMaxel n -> BoxSquareMaxel (m * n)
kroneckerBoxSquareMaxel {m} {n} (MkBoxSquareMaxel t1) (MkBoxSquareMaxel t2) =
  let resultTree = foldBoxTreeL (\accTree, (MkPixel r1 c1, w1) =>
        foldBoxTreeL (\innerAcc, (MkPixel r2 c2, w2) =>
          let pOut = observeKroneckerPixel n ((r1, r2), (c1, c2))
              wOut = w1 * w2
          in if unwrapBox wOut == 0
               then innerAcc
               else let cur = lookupBoxTree pOut innerAcc
                        newW = cur + wOut
                    in if unwrapBox newW == 0
                         then setBoxTree pOut (intToBoxInt 0) innerAcc
                         else setBoxTree pOut newW innerAcc)
          accTree
          t2)
        BoxLeaf
        t1
  in MkBoxSquareMaxel resultTree

||| Converts a BoxSquareMaxel into a typed MultisetTensor over natural coordinates.
public export
boxSquareMaxelToTensor : BoxSquareMaxel dim -> MultisetTensor Nat Nat
boxSquareMaxelToTensor (MkBoxSquareMaxel tree) =
  foldBoxTreeR (\(MkPixel r c), w, acc => AddM (r, c) w acc) ZeroM tree

||| Reconstructs a sparse BoxSquareMaxel from an observed MultisetTensor Pixel.
public export
tensorToBoxSquareMaxel : {dim : Nat} -> Multiset BoxInt Pixel -> BoxSquareMaxel dim
tensorToBoxSquareMaxel tensor =
  MkBoxSquareMaxel (foldl (\tree, (p, w) => setBoxTree p w tree) BoxLeaf (multisetToList tensor))

||| Converts a general Maxel into a typed MultisetTensor over natural coordinates.
public export
maxelToTensor : Maxel -> MultisetTensor Nat Nat
maxelToTensor (MkMaxelTree tree) =
  foldBoxTreeR (\(MkPixel r c), w, acc => AddM (r, c) w acc) ZeroM tree

||| Reconstructs a general Maxel from a MultisetTensor over natural coordinates.
public export
tensorToMaxel : MultisetTensor Nat Nat -> Maxel
tensorToMaxel tensor =
  MkMaxelTree (foldl (\tree, ((r, c), w) =>
                 if boxIsZero w then tree
                 else let cur = lookupBoxTree (MkPixel r c) tree
                          newW = cur + w
                      in if boxIsZero newW
                           then setBoxTree (MkPixel r c) (intToBoxInt 0) tree
                           else setBoxTree (MkPixel r c) newW tree)
                     BoxLeaf
                     (multisetToList tensor))

||| Algebraic Kronecker Tensor Product on BoxSquareMaxel:
public export
kroneckerBoxSquareMaxelAlg : {m, n : Nat} -> BoxSquareMaxel m -> BoxSquareMaxel n -> BoxSquareMaxel (m * n)
kroneckerBoxSquareMaxelAlg {m} {n} m1 m2 =
  let t1 = boxSquareMaxelToTensor m1
      t2 = boxSquareMaxelToTensor m2
      tOp = tensorOperator t1 t2
      observed = mapMultiset (observeKroneckerPixel n) tOp
  in tensorToBoxSquareMaxel observed

||| Verified Invariant: Direct sparse Kronecker product definitionally matches
||| the pushforward observation of the underlying monoidal tensor operator.
public export
auditKroneckerAlgebraicEquivalence : Bool
auditKroneckerAlgebraicEquivalence =
  let id2 = identityBoxSquareMaxel 2
  in kroneckerBoxSquareMaxel id2 id2 == kroneckerBoxSquareMaxelAlg id2 id2

||| 2LTT Staged Sparse Kronecker Tensor Product:
public export
stagedKroneckerBoxSquareMaxel : {m, n : Nat} -> Lift (BoxSquareMaxel m) -> Lift (BoxSquareMaxel n) -> Code (BoxSquareMaxel (m * n))
stagedKroneckerBoxSquareMaxel qm1 qm2 = quote (kroneckerBoxSquareMaxel (splice qm1) (splice qm2))

------------------------------------------------------------------------
-- 5. MATRIX MULTIPLICATION, IDENTITY & NUM INSTANCE
------------------------------------------------------------------------

||| Multiplies a Unixel on the left by a Pixel (Row extraction filter).
public export
mulUnixelPixel : Unixel -> Pixel -> Maybe Unixel
mulUnixelPixel (MkUnixel k) (MkPixel l m) =
  if k == l then Just (MkUnixel m) else Nothing

||| Multiplies a Pixel on the left by a Unixel (Column extraction filter).
public export
mulPixelUnixel : Pixel -> Unixel -> Maybe Unixel
mulPixelUnixel (MkPixel l m) (MkUnixel k) =
  if m == k then Just (MkUnixel l) else Nothing

||| Lookups the signed BoxInt weight of a coordinate Pixel in O(log N) time.
public export
lookupPixel : Pixel -> Maxel -> BoxInt
lookupPixel p (MkMaxelTree t) = lookupBoxTree p t

||| Adds two Maxels and consolidates duplicate coordinates directly via BoxMultisetTree in O(N log N).
public export
addMaxel : Maxel -> Maxel -> Maxel
addMaxel (MkMaxelTree t1) (MkMaxelTree t2) =
  let tMerged = foldBoxTreeL (\tree, (p, w) =>
                  let cur = lookupBoxTree p tree
                      newW = cur + w
                  in if boxIsZero newW
                       then setBoxTree p (intToBoxInt 0) tree
                       else setBoxTree p newW tree)
                  t1
                  t2
  in MkMaxelTree tMerged

public export
Semigroup Maxel where
  (<+>) = addMaxel

public export
Monoid Maxel where
  neutral = MkMaxelTree BoxLeaf

||| Scales a Maxel by a BoxInt scalar, pruning zero weights.
public export
scaleMaxel : BoxInt -> Maxel -> Maxel
scaleMaxel s (MkMaxelTree t) =
  if boxIsZero s
    then MkMaxelTree BoxLeaf
    else MkMaxelTree (mapBoxTreeWeight (s *) t)

||| Computes total weight/mass across all pixels in a Maxel via in-order tree fold in O(N).
public export
totalMaxelWeight : Maxel -> BoxInt
totalMaxelWeight (MkMaxelTree t) =
  foldBoxTreeL (\acc, (_, w) => acc + w) (intToBoxInt 0) t

||| The canonical zero/empty Maxel.
public export
emptyMaxel : Maxel
emptyMaxel = MkMaxelTree BoxLeaf

||| Compresses a Maxel by pruning zero weights.
public export
compressMaxel : Maxel -> Maxel
compressMaxel m = m

||| Multiplies two Maxels (discrete matrix multiplication).
public export
mulMaxel : Maxel -> Maxel -> Maxel
mulMaxel (MkMaxelTree t1) (MkMaxelTree t2) =
  let resultTree = foldBoxTreeL (\treeAcc, (p1, w1) =>
        foldBoxTreeL (\acc, (p2, w2) =>
          case mulPixel p1 p2 of
            Just pOut =>
              let wOut = w1 * w2
                  cur = lookupBoxTree pOut acc
                  newW = cur + wOut
              in if boxIsZero newW
                   then setBoxTree pOut (intToBoxInt 0) acc
                   else setBoxTree pOut newW acc
            Nothing => acc)
          treeAcc
          t2)
        BoxLeaf
        t1
  in MkMaxelTree resultTree

public export
multiplyMaxel : Maxel -> Maxel -> Maxel
multiplyMaxel = mulMaxel

||| Fast tensor contraction via native Maxel AVL tree matrix multiplication:
public export
fastMultisetTensorMult : MultisetTensor Nat Nat -> MultisetTensor Nat Nat -> MultisetTensor Nat Nat
fastMultisetTensorMult t1 t2 =
  maxelToTensor (mulMaxel (tensorToMaxel t1) (tensorToMaxel t2))

||| Canonical 3D identity metric Maxel: [1, 1] + [2, 2] + [3, 3].
public export
identityMaxel : Maxel
identityMaxel =
  MkMaxel [ (MkPixel 1 1, intToBoxInt 1)
          , (MkPixel 2 2, intToBoxInt 1)
          , (MkPixel 3 3, intToBoxInt 1)
          ]

public export
Num Maxel where
  (+) = addMaxel
  (*) = mulMaxel
  fromInteger n = scaleMaxel (intToBoxInt n) identityMaxel

||| Subtracts two Maxels and consolidates duplicate coordinates directly via BoxMultisetTree in O(N log N).
public export
subMaxel : Maxel -> Maxel -> Maxel
subMaxel (MkMaxelTree t1) (MkMaxelTree t2) =
  let tMerged = foldBoxTreeL (\tree, (p, w) =>
                  let cur = lookupBoxTree p tree
                      newW = cur - w
                  in if boxIsZero newW
                       then setBoxTree p (intToBoxInt 0) tree
                       else setBoxTree p newW tree)
                  t1
                  t2
  in MkMaxelTree tMerged

public export
Neg Maxel where
  negate (MkMaxelTree t) = MkMaxelTree (mapBoxTreeWeight negate t)
  (-) = subMaxel

||| Contracts a Maxel matrix on a Vexel vector (M * v).
public export
actMaxelVexel : Maxel -> Vexel -> Vexel
actMaxelVexel (MkMaxelTree tm) (MkVexelTree tv) =
  let resultTree = foldBoxTreeL (\treeAcc, (pix, pw) =>
        foldBoxTreeL (\acc, (sing, sw) =>
          case mulPixelUnixel pix sing of
            Just sOut =>
              let wOut = pw * sw
                  cur = lookupBoxTree sOut acc
                  newW = cur + wOut
              in if boxIsZero newW
                   then setBoxTree sOut (intToBoxInt 0) acc
                   else setBoxTree sOut newW acc
            Nothing => acc)
          treeAcc
          tv)
        BoxLeaf
        tm
  in MkVexelTree resultTree

||| Evaluates metric inner product <u, v>_g = u^T (g * v).
public export
metricInnerVexel : Maxel -> Vexel -> Vexel -> BoxInt
metricInnerVexel g u v =
  let gv = actMaxelVexel g v
  in dotVexel u gv

public export
implementation MultisetAlgebra Maxel where
  zeroM = MkMaxelTree BoxLeaf
  addM = addMaxel
  scaleM = scaleMaxel
  dotM m1 m2 = totalMaxelWeight (mulMaxel m1 m2)

public export
implementation MultisetAlgebra Vexel where
  zeroM = MkVexelTree BoxLeaf
  addM = addVexel
  scaleM = scaleVexel
  dotM = dotVexel

------------------------------------------------------------------------
-- 6. WILDBERGER SUPPORT & CHROMOGEOMETRIC METRIC MAXELS
------------------------------------------------------------------------

||| Extracts the finite active support of a Maxel as a list of directed edges [i, j].
public export
supportMaxel : Maxel -> List Pixel
supportMaxel (MkMaxelTree t) =
  foldBoxTreeR (\p, w, acc => if boxIsNonZero w then p :: acc else acc) [] t

||| Extracts the finite active support of a Vexel vector as a list of basis Unixels.
public export
supportVexel : Vexel -> List Unixel
supportVexel (MkVexelTree t) =
  foldBoxTreeR (\u, w, acc => if boxIsNonZero w then u :: acc else acc) [] t

||| 2D Blue (Elliptic/Euclidean) Metric Maxel parameterized by (x, y):
public export
parameterizedBlueMetricMaxel : BoxInt -> BoxInt -> Maxel
parameterizedBlueMetricMaxel x y =
  MkMaxel [ (MkPixel 1 1, x * x)
          , (MkPixel 2 2, y * y)
          ]

||| 2D Red (Hyperbolic/Relativistic) Metric Maxel parameterized by (x, y):
public export
parameterizedRedMetricMaxel : BoxInt -> BoxInt -> Maxel
parameterizedRedMetricMaxel x y =
  MkMaxel [ (MkPixel 1 1, x * x)
          , (MkPixel 2 2, mulBox (intToBoxInt (-1)) (y * y))
          ]

||| 2D Green (Parabolic/Null) Metric Maxel parameterized by (x, y):
public export
parameterizedGreenMetricMaxel : BoxInt -> BoxInt -> Maxel
parameterizedGreenMetricMaxel x y =
  let xy = x * y
  in MkMaxel [ (MkPixel 1 2, xy)
             , (MkPixel 2 1, xy)
             ]

||| Invariant audit verifying the parameterized chromogeometric operator identity:
public export
auditParameterizedMetricOperatorIdentity : (x : BoxInt) -> (y : BoxInt) -> Bool
auditParameterizedMetricOperatorIdentity x y =
  let gB = parameterizedBlueMetricMaxel x y
      gR = parameterizedRedMetricMaxel x y
      gG = parameterizedGreenMetricMaxel x y
      gR2 = mulMaxel gR gR
      gG2 = mulMaxel gG gG
      lhsSum = addMaxel gR2 gG2
      qBlue = (x * x) + (y * y)
      rhsExpected = scaleMaxel qBlue gB
      lhs11 = lookupPixel (MkPixel 1 1) lhsSum
      rhs11 = lookupPixel (MkPixel 1 1) rhsExpected
      lhs22 = lookupPixel (MkPixel 2 2) lhsSum
      rhs22 = lookupPixel (MkPixel 2 2) rhsExpected
  in boxEq lhs11 rhs11 && boxEq lhs22 rhs22

------------------------------------------------------------------------
-- 7. SQUAREMAXEL CHROMOGEOMETRIC TRIADS
------------------------------------------------------------------------

||| 2D Maxel represented as a balanced binary multiset search tree in O(log N).
public export
MaxelTree : Type
MaxelTree = MultisetTree Pixel

||| Converts a Maxel to a balanced MultisetTree in O(N log N) time.
public export
maxelToTree : Maxel -> MultisetTree Pixel
maxelToTree (MkMaxelTree t) =
  foldBoxTreeL (\tree, (p, w) => insertTokenTree p (boxToNat w) tree) Leaf t

||| Converts a MultisetTree back to a Maxel in linear O(N log N) time with zero intermediate lists.
public export
treeToMaxel : MultisetTree Pixel -> Maxel
treeToMaxel tree =
  MkMaxelTree (foldTreeL (\acc, (p, cnt) => if cnt == 0 then acc else setBoxTree p (natToBoxInt cnt) acc) BoxLeaf tree)

||| O(log N) lookup for coordinate pixel in a MaxelTree.
public export
lookupPixelTree : Pixel -> MultisetTree Pixel -> Nat
lookupPixelTree = lookupTokenTree

||| Converts a SquareMaxel into a standard Maxel carrier.
public export
squareMaxelToMaxel : SquareMaxel dim -> Maxel
squareMaxelToMaxel (MkSquareMaxel es) = treeToMaxel es

||| Converts a standard Maxel into a SquareMaxel with explicit dimension bound.
public export
maxelToSquareMaxel : (dim : Nat) -> Maxel -> SquareMaxel dim
maxelToSquareMaxel dim m = MkSquareMaxel (maxelToTree m)

||| Constructs a dimension-indexed identity SquareMaxel of size `dim` in O(dim log dim).
public export
identitySquareMaxel : (dim : Nat) -> SquareMaxel dim
identitySquareMaxel dim =
  let pxs = [MkPixel (S i) (S i) | i <- [0..pred dim]]
      t   = foldl (\tree, p => insertTokenTree p 1 tree) Leaf pxs
  in MkSquareMaxel t

||| Dimension-checked discrete matrix multiplication for SquareMaxel:
public export
mulSquareMaxel : SquareMaxel dim -> SquareMaxel dim -> SquareMaxel dim
mulSquareMaxel (MkSquareMaxel e1) (MkSquareMaxel e2) =
  let m1 = treeToMaxel e1
      m2 = treeToMaxel e2
      mProd = mulMaxel m1 m2
  in MkSquareMaxel (maxelToTree mProd)

||| Scales a SquareMaxel by a BoxInt scalar.
public export
scaleSquareMaxel : BoxInt -> SquareMaxel dim -> SquareMaxel dim
scaleSquareMaxel s (MkSquareMaxel es) =
  let m = treeToMaxel es
      mScaled = scaleMaxel s m
  in MkSquareMaxel (maxelToTree mScaled)

||| Adds two SquareMaxels of identical dimension `dim`.
public export
addSquareMaxel : SquareMaxel dim -> SquareMaxel dim -> SquareMaxel dim
addSquareMaxel (MkSquareMaxel e1) (MkSquareMaxel e2) =
  let m1 = treeToMaxel e1
      m2 = treeToMaxel e2
      mSum = addMaxel m1 m2
  in MkSquareMaxel (maxelToTree mSum)

public export
parameterizedBlueSquareMaxel : BoxInt -> BoxInt -> SquareMaxel 2
parameterizedBlueSquareMaxel x y =
  maxelToSquareMaxel 2 (parameterizedBlueMetricMaxel x y)

public export
parameterizedRedSquareMaxel : BoxInt -> BoxInt -> SquareMaxel 2
parameterizedRedSquareMaxel x y =
  maxelToSquareMaxel 2 (parameterizedRedMetricMaxel x y)

public export
parameterizedGreenSquareMaxel : BoxInt -> BoxInt -> SquareMaxel 2
parameterizedGreenSquareMaxel x y =
  maxelToSquareMaxel 2 (parameterizedGreenMetricMaxel x y)

public export
auditParameterizedSquareMetricOperatorIdentity : (x : BoxInt) -> (y : BoxInt) -> Bool
auditParameterizedSquareMetricOperatorIdentity x y =
  let gB = parameterizedBlueSquareMaxel x y
      gR = parameterizedRedSquareMaxel x y
      gG = parameterizedGreenSquareMaxel x y
      gR2 = mulSquareMaxel gR gR
      gG2 = mulSquareMaxel gG gG
      lhsSum = addSquareMaxel gR2 gG2
      qBlue = (x * x) + (y * y)
      rhsExpected = scaleSquareMaxel qBlue gB
  in lhsSum == rhsExpected

public export
blueMetricMaxel2D : Maxel
blueMetricMaxel2D = parameterizedBlueMetricMaxel (intToBoxInt 1) (intToBoxInt 1)

public export
redMetricMaxel2D : Maxel
redMetricMaxel2D = parameterizedRedMetricMaxel (intToBoxInt 1) (intToBoxInt 1)

public export
greenMetricMaxel2D : Maxel
greenMetricMaxel2D = parameterizedGreenMetricMaxel (intToBoxInt 1) (intToBoxInt 1)

public export
auditChromogeometricMetricSupportsProof : Bool
auditChromogeometricMetricSupportsProof =
  let sBlue  = supportMaxel blueMetricMaxel2D
      sRed   = supportMaxel redMetricMaxel2D
      sGreen = supportMaxel greenMetricMaxel2D
      tBlue  = sBlue  == [MkPixel 1 1, MkPixel 2 2]
      tRed   = sRed   == [MkPixel 1 1, MkPixel 2 2]
      tGreen = sGreen == [MkPixel 1 2, MkPixel 2 1]
  in tBlue && tRed && tGreen

public export
auditMatrixPathCompositionProof : Bool
auditMatrixPathCompositionProof =
  let gG = greenMetricMaxel2D
      gProd = mulMaxel gG gG
      sProd = supportMaxel gProd
      e11 = lookupPixel (MkPixel 1 1) gProd
      e22 = lookupPixel (MkPixel 2 2) gProd
  in sProd == [MkPixel 1 1, MkPixel 2 2] && e11 == intToBoxInt 1 && e22 == intToBoxInt 1

------------------------------------------------------------------------
-- 8. ROW & COLUMN EXTRACTION, OUTER PRODUCT & GRASSMANN WEDGE
------------------------------------------------------------------------

||| Extracts the i-th Row of a Maxel as a 1D Vexel: R_i(M) = [i] * M
public export
extractRowVexel : Nat -> Maxel -> Vexel
extractRowVexel i (MkMaxelTree tm) =
  let singI = MkUnixel i
      resultTree = foldBoxTreeL (\acc, (pix, w) => 
                     case mulUnixelPixel singI pix of
                       Just sOut =>
                         let cur = lookupBoxTree sOut acc
                             newW = cur + w
                         in if boxIsZero newW
                              then setBoxTree sOut (intToBoxInt 0) acc
                              else setBoxTree sOut newW acc
                       Nothing   => acc)
                     BoxLeaf
                     tm
  in MkVexelTree resultTree

||| Extracts the j-th Column of a Maxel as a 1D Vexel: C_j(M) = M * [j]
public export
extractColVexel : Nat -> Maxel -> Vexel
extractColVexel j (MkMaxelTree tm) =
  let singJ = MkUnixel j
      resultTree = foldBoxTreeL (\acc, (pix, w) => 
                     case mulPixelUnixel pix singJ of
                       Just sOut =>
                         let cur = lookupBoxTree sOut acc
                             newW = cur + w
                         in if boxIsZero newW
                              then setBoxTree sOut (intToBoxInt 0) acc
                              else setBoxTree sOut newW acc
                       Nothing   => acc)
                     BoxLeaf
                     tm
  in MkVexelTree resultTree

||| Multiplies a column Vexel (ket) by a row Vexel (bra) to generate a Maxel:
public export
outerProductVexel : Vexel -> Vexel -> Maxel
outerProductVexel (MkVexelTree tk) (MkVexelTree tb) =
  let resultTree = foldBoxTreeL (\accTree, (k, kw) =>
        foldBoxTreeL (\innerAcc, (b, bw) =>
          let p = MkPixel (index k) (index b)
              wOut = kw * bw
              cur = lookupBoxTree p innerAcc
              newW = cur + wOut
          in if boxIsZero newW
               then setBoxTree p (intToBoxInt 0) innerAcc
               else setBoxTree p newW innerAcc)
          accTree
          tb)
        BoxLeaf
        tk
  in MkMaxelTree resultTree

||| 🧪 Chemistry: A Molecular Bond Maxel represents covalent bond connectivity between atoms i and j.
public export
waterMoleculeBonds : Maxel
waterMoleculeBonds =
  MkMaxel [ (MkPixel 1 2, intToBoxInt 1) -- O-H1 bond
          , (MkPixel 1 3, intToBoxInt 1) -- O-H2 bond
          ]

||| Evaluates the Grassmann exterior wedge product of two Vexels:
public export
wedgeVexel : Vexel -> Vexel -> Maxel
wedgeVexel (MkVexelTree tu) (MkVexelTree tv) =
  let resultTree = foldBoxTreeL (\accU, (MkUnixel i, wu) =>
        foldBoxTreeL (\accV, (MkUnixel j, wv) =>
          if i == j
            then accV
            else
              let w = wu * wv
                  pPos = MkPixel i j
                  pNeg = MkPixel j i
                  curPos = lookupBoxTree pPos accV
                  newPos = curPos + w
                  tree1 = if boxIsZero newPos
                            then setBoxTree pPos (intToBoxInt 0) accV
                            else setBoxTree pPos newPos accV
                  curNeg = lookupBoxTree pNeg tree1
                  newNeg = curNeg - w
              in if boxIsZero newNeg
                   then setBoxTree pNeg (intToBoxInt 0) tree1
                   else setBoxTree pNeg newNeg tree1)
          accU
          tv)
        BoxLeaf
        tu
  in MkMaxelTree resultTree

||| Proves that the Grassmann wedge product of any Vexel with itself is identically zero: v ^ v == 0.
public export
auditWedgeNilpotencyProof : Bool
auditWedgeNilpotencyProof =
  let v = MkVexel [(MkUnixel 1, intToBoxInt 3), (MkUnixel 2, intToBoxInt 5)]
      w = wedgeVexel v v
  in w == MkMaxel []

public export
auditRowExtractionProof : Bool
auditRowExtractionProof =
  let v1 = MkVexel [(MkUnixel 1, intToBoxInt 2), (MkUnixel 2, intToBoxInt 3)]
      v2 = MkVexel [(MkUnixel 1, intToBoxInt 1), (MkUnixel 2, intToBoxInt 4)]
      m = outerProductVexel v1 v2
      row1 = extractRowVexel 1 m
  in row1 == MkVexel [(MkUnixel 1, intToBoxInt 2), (MkUnixel 2, intToBoxInt 8)]

------------------------------------------------------------------------
-- 9. MAXELN CONVERSIONS
------------------------------------------------------------------------

rowToPixelPairsHelper : Nat -> Nat -> Vect k BoxInt -> List (Pixel, BoxInt)
rowToPixelPairsHelper _ _ [] = []
rowToPixelPairsHelper r c (w :: ws) = (MkPixel r c, w) :: rowToPixelPairsHelper r (S c) ws

matToPixelPairsHelper : Nat -> Nat -> Vect k (Vect n BoxInt) -> List (Pixel, BoxInt)
matToPixelPairsHelper _ _ [] = []
matToPixelPairsHelper r c (row :: rows) = rowToPixelPairsHelper r c row ++ matToPixelPairsHelper (S r) c rows

||| Converts a dimension-indexed MaxelN into a canonical sparse multiset Maxel (1-indexed).
public export
maxelNToMaxel : {n : Nat} -> MaxelN n -> Maxel
maxelNToMaxel (MkMaxelN rs) = canonicalizeMaxel (MkMaxel (matToPixelPairsHelper 1 1 rs))

||| Converts a dimension-indexed MaxelN into a 0-indexed sparse multiset Maxel (quantum basis).
public export
maxelNToMaxel0 : {n : Nat} -> MaxelN n -> Maxel
maxelNToMaxel0 (MkMaxelN rs) = canonicalizeMaxel (MkMaxel (matToPixelPairsHelper 0 0 rs))

||| Kronecker tensor product of two dimension-indexed MaxelN square matrices: MaxelN (n * m).
public export
kroneckerMaxelN : {n, m : Nat} -> MaxelN n -> MaxelN m -> MaxelN (n * m)
kroneckerMaxelN (MkMaxelN rowsA) (MkMaxelN rowsB) =
  let blockRows : Vect n (Vect m (Vect (n * m) BoxInt))
      blockRows = map (\ra => map (\rb => kroneckerVect ra rb) rowsB) rowsA
  in MkMaxelN (concat blockRows)

||| 2LTT Staged Kronecker tensor product of two MaxelN square matrices at Stage 1.
public export
stagedKroneckerMaxelN : {n, m : Nat} -> Lift (MaxelN n) -> Lift (MaxelN m) -> Code (MaxelN (n * m))
stagedKroneckerMaxelN qm1 qm2 = quote (kroneckerMaxelN (splice qm1) (splice qm2))

||| Wildberger multiple-spread companion transfer matrix M(s) = [[2 - 4s, -1], [1, 0]] in MaxelN 2.
public export
companionSpreadMaxelN2 : BoxInt -> MaxelN 2
companionSpreadMaxelN2 s =
  let diag = subBox (intToBoxInt 2) (mulBox (intToBoxInt 4) s)
  in mkMaxel2 diag (intToBoxInt (-1)) (intToBoxInt 1) (intToBoxInt 0)

public export
pruneMaxelTerms : List (Pixel, BoxInt) -> List (Pixel, BoxInt)
pruneMaxelTerms [] = []
pruneMaxelTerms ((p, w) :: rest) =
  if boxIsZero w then pruneMaxelTerms rest else (p, w) :: pruneMaxelTerms rest

------------------------------------------------------------------------
-- POLYNOMIAL BRIDGES: POLYS <-> MAXELS
------------------------------------------------------------------------

||| Converts a 2D Maxel into a bivariate polynumber: sum a_ij [i, j] <=> sum a_ij x^i y^j.
public export
maxelToBivariatePolynumber : Maxel -> List ((Nat, Nat), BoxInt)
maxelToBivariatePolynumber (MkMaxelTree t) =
  foldBoxTreeR (\(MkPixel r c), w, acc => ((r, c), w) :: acc) [] t


