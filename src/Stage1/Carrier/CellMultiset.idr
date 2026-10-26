module Stage1.Carrier.CellMultiset

import Data.Fin
import Data.Nat
import Data.Vect
import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.StructuralFuel
import Language.Reflection
import Stage1.TypeTheory.Staging
import public Stage0.OnSeq.FusedStream
import public Stage1.MultisetTree
import public Stage1.Basis.CoordCell
import public Stage1.MultisetTensor

%default total

------------------------------------------------------------------------
-- 1. CANONICAL CARRIER MULTISET (CellMultiset) & SPATIAL TRANSLATION
------------------------------------------------------------------------

||| A CellMultiset is an AVL multiset of D-dimensional coordinate basis cells.
public export
CellMultiset : (dim : Nat) -> Type
CellMultiset dim = BoxMultisetTree (CoordCell dim)

||| Empty cell multiset.
public export
emptyCellMultiset : {dim : Nat} -> CellMultiset dim
emptyCellMultiset = BoxLeaf

||| Direct O(1) singleton construction of a CellMultiset without intermediate List allocation.
public export
singletonCell : {dim : Nat} -> CoordCell dim -> BoxInt -> CellMultiset dim
singletonCell c w =
  if boxIsZero w then BoxLeaf
  else BoxNode 1 BoxLeaf c w BoxLeaf

||| Constructs a CellMultiset from a fixed-length Vect of coordinate-weight pairs
||| with compile-time known length k and structural fuel bounds.
public export
fromVectCells : {dim, k : Nat} -> Vect k (CoordCell dim, BoxInt) -> CellMultiset dim
fromVectCells xs =
  foldl (\t, (c, w) =>
          if boxIsZero w then t
          else let cur = lookupBoxTree c t
                   newW = cur + w
               in if boxIsZero newW
                    then setBoxTree c (intToBoxInt 0) t
                    else setBoxTree c newW t)
        BoxLeaf
        xs

||| Deforested zero-allocation stream extractor for the active support of a CellMultiset.
||| Emits strictly non-zero basis cells in O(1) auxiliary registers (Rule 04 §8).
public export
supportCellStream : {dim : Nat} -> CellMultiset dim -> FusedStream (CoordCell dim)
supportCellStream t =
  filterMapStream (\(c, w) => if boxIsNonZero w then Just c else Nothing) (streamBoxMultisetTree t)

||| Constructs a CellMultiset from a list of coordinate-weight pairs in O(N log N).
||| @deprecated Use singletonCell + (<+>), streamToCellMultiset, or fromVectCells. Avoid heap List materialization.
public export
mkCellMultiset : {dim : Nat} -> List (CoordCell dim, BoxInt) -> CellMultiset dim
mkCellMultiset xs =
  foldl (\t, (c, w) =>
          if boxIsZero w then t
          else let cur = lookupBoxTree c t
                   newW = cur + w
               in if boxIsZero newW
                    then setBoxTree c (intToBoxInt 0) t
                    else setBoxTree c newW t)
        BoxLeaf
        xs

||| Lookups the weight of a coordinate cell in a CellMultiset in O(log N).
public export
lookupCellMultiset : {dim : Nat} -> CoordCell dim -> CellMultiset dim -> BoxInt
lookupCellMultiset = lookupBoxTree

||| Adds two cell multisets by merging coordinate weights.
public export
addCellMultiset : {dim : Nat} -> CellMultiset dim -> CellMultiset dim -> CellMultiset dim
addCellMultiset t1 t2 =
  foldBoxTreeL (\tree, (c, w) =>
    let cur = lookupBoxTree c tree
        newW = cur + w
    in if boxIsZero newW
         then setBoxTree c (intToBoxInt 0) tree
         else setBoxTree c newW tree)
    t1
    t2

||| Scales a cell multiset by a BoxInt scalar.
public export
scaleCellMultiset : {dim : Nat} -> BoxInt -> CellMultiset dim -> CellMultiset dim
scaleCellMultiset s t =
  if boxIsZero s then BoxLeaf
  else mapBoxTreeWeight (s *) t

||| Computes total weight across all cells in a CellMultiset.
public export
totalCellMultisetWeight : {dim : Nat} -> CellMultiset dim -> BoxInt
totalCellMultisetWeight t =
  foldBoxTreeL (\acc, (_, w) => acc + w) (intToBoxInt 0) t

||| Universal spatial translation of a cell multiset by a displacement coordinate cell.
public export
translateCell : CoordCell dim -> CellMultiset dim -> CellMultiset dim
translateCell delta mset =
  foldBoxTreeL (\acc, (c, w) => setBoxTree (addCoordCell c delta) w acc) BoxLeaf mset

||| Canonical zero-cost dimension synonyms:
public export Vexel       : Type; Vexel       = CellMultiset 1
public export Maxel       : Type; Maxel       = CellMultiset 2
public export Boxel       : Type; Boxel       = CellMultiset 3
public export HyperBoxel  : Type; HyperBoxel  = CellMultiset 4

||| Lookups the signed BoxInt weight of a coordinate Pixel in O(log N) time.
public export
lookupPixel : Pixel -> Maxel -> BoxInt
lookupPixel = lookupCellMultiset

||| Lookups the signed BoxInt weight of a coordinate Unixel in O(log N) time.
public export
lookupUnixel : Unixel -> Vexel -> BoxInt
lookupUnixel = lookupCellMultiset

public export totalVexelMass : Vexel -> BoxInt; totalVexelMass = totalCellMultisetWeight
public export totalVexelWeight : Vexel -> BoxInt; totalVexelWeight = totalCellMultisetWeight
public export totalMaxelWeight : Maxel -> BoxInt; totalMaxelWeight = totalCellMultisetWeight
public export totalBoxelWeight : Boxel -> BoxInt; totalBoxelWeight = totalCellMultisetWeight

||| Universal tree field identity projection for backwards compatibility with (.tree).
public export
tree : CellMultiset dim -> CellMultiset dim
tree t = t

public export
subCellMultiset : {dim : Nat} -> CellMultiset dim -> CellMultiset dim -> CellMultiset dim
subCellMultiset t1 t2 = addCellMultiset t1 (scaleCellMultiset (intToBoxInt (-1)) t2)

||| Rebuilds a canonical CellMultiset by filtering non-zero weights and rebalancing.
public export
canonicalizeCellMultiset : {dim : Nat} -> CellMultiset dim -> CellMultiset dim
canonicalizeCellMultiset t =
  foldBoxTreeL (\acc, (c, w) => if boxIsNonZero w then setBoxTree c w acc else acc) BoxLeaf t

public export
canonicalizeCell : {dim : Nat} -> CellMultiset dim -> CellMultiset dim
canonicalizeCell = canonicalizeCellMultiset

||| Canonicalize / compress a Maxel (prunes zero weights and rebalances).
public export
compressMaxel : Maxel -> Maxel
compressMaxel = canonicalizeCellMultiset

||| Extracts the finite active support of a CellMultiset as a list.
||| @deprecated Use supportCellStream (FusedStream). Materializing support as List is forbidden by Rule 04 §8.
public export
supportCellMultiset : {dim : Nat} -> CellMultiset dim -> List (CoordCell dim)
supportCellMultiset t =
  foldBoxTreeR (\c, w, acc => if boxIsNonZero w then c :: acc else acc) [] t

public export
supportMaxel : Maxel -> List Pixel
supportMaxel = supportCellMultiset

public export
supportVexel : Vexel -> List Unixel
supportVexel = supportCellMultiset

public export
{dim : Nat} -> Semigroup (CellMultiset dim) where
  (<+>) = addCellMultiset

public export
{dim : Nat} -> Monoid (CellMultiset dim) where
  neutral = BoxLeaf

------------------------------------------------------------------------
-- 2. DISCRETE MATRIX, VECTOR & EXTERIOR ALGEBRA OPERATORS
------------------------------------------------------------------------

||| Evaluates the standard Euclidean inner product between two Vexels directly via BoxMultisetTree.
public export
dotVexel : Vexel -> Vexel -> BoxInt
dotVexel t1 v2 =
  foldBoxTreeL (\acc, (u, w1) =>
    let w2 = lookupCellMultiset u v2
    in acc + (w1 * w2))
    (intToBoxInt 0)
    t1

||| Multiplies two Maxels (discrete matrix multiplication).
public export
mulMaxel : Maxel -> Maxel -> Maxel
mulMaxel t1 t2 =
  foldBoxTreeL (\treeAcc, (p1, w1) =>
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

||| Canonical 3D identity metric Maxel: [1, 1] + [2, 2] + [3, 3].
public export
identityMaxel : Maxel
identityMaxel =
  singletonCell (mkPixel 1 1) (intToBoxInt 1) <+>
  singletonCell (mkPixel 2 2) (intToBoxInt 1) <+>
  singletonCell (mkPixel 3 3) (intToBoxInt 1)

||| Contracts a Maxel matrix on a Vexel vector (M * v).
public export
actMaxelVexel : Maxel -> Vexel -> Vexel
actMaxelVexel tm tv =
  foldBoxTreeL (\treeAcc, (pix, pw) =>
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

||| Evaluates metric inner product <u, v>_g = u^T (g * v).
public export
metricInnerVexel : Maxel -> Vexel -> Vexel -> BoxInt
metricInnerVexel g u v =
  let gv = actMaxelVexel g v
  in dotVexel u gv

||| Evaluates the Grassmann exterior wedge product of two Vexels into a 2D Maxel.
public export
wedgeVexel : Vexel -> Vexel -> Maxel
wedgeVexel tu tv =
  foldBoxTreeL (\accU, (u, wu) =>
    let i = unwrapUnixel u
    in foldBoxTreeL (\accV, (v, wv) =>
         let j = unwrapUnixel v
         in if i == j
              then accV
              else
                let w = wu * wv
                    pPos = mkPixel i j
                    pNeg = mkPixel j i
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

||| Evaluates the Grassmann exterior wedge product of a Vexel and a Maxel into a 3D Boxel.
public export
wedgeVexelMaxel : Vexel -> Maxel -> Boxel
wedgeVexelMaxel tu tm =
  let addTerm : Voxel -> BoxInt -> Boxel -> Boxel
      addTerm v tw acc =
        let cur = lookupBoxTree v acc
            nw  = cur + tw
        in if boxIsZero nw then setBoxTree v (intToBoxInt 0) acc else setBoxTree v nw acc
  in foldBoxTreeL (\accU, (u, wu) =>
       let i = unwrapUnixel u
       in foldBoxTreeL (\accM, (p, wm) =>
            let j = pixelRow p
                k = pixelCol p
            in if i == j || j == k || i == k
                 then accM
                 else let w = wu * wm
                      in addTerm (mkVoxel j k i) w
                           (addTerm (mkVoxel j i k) (-w)
                             (addTerm (mkVoxel i j k) w accM))
          ) accU tm
     ) BoxLeaf tu

||| 3D Tensor Outer Product: Vexel (1D ket) x Maxel (2D surface) -> Boxel (3D volume).
||| Evaluates directly in tree space with zero intermediate List allocations.
public export
outerProductVexelMaxel : Vexel -> Maxel -> Boxel
outerProductVexelMaxel tk tm =
  foldBoxTreeL (\accK, (s, sw) =>
    foldBoxTreeL (\accM, (p, pw) =>
      let v = mkVoxel (unwrapUnixel s) (pixelRow p) (pixelCol p)
          w = sw * pw
      in if boxIsZero w then accM
         else let cur = lookupBoxTree v accM
                  newW = cur + w
              in if boxIsZero newW
                   then setBoxTree v (intToBoxInt 0) accM
                   else setBoxTree v newW accM
    ) accK tm
  ) BoxLeaf tk

||| Extracts a 2D Maxel plane slice at a fixed Z-coordinate: Z_k(B) = { [x, y] with w | [x, y, k] in B }
public export
sliceBoxelZ : Nat -> Boxel -> Maxel
sliceBoxelZ targetZ b =
  foldBoxTreeL (\acc, (v, w) =>
    if voxelZ v == targetZ
      then let p = mkPixel (voxelX v) (voxelY v)
               cur = lookupBoxTree p acc
               newW = cur + w
           in if boxIsZero newW
                then setBoxTree p (intToBoxInt 0) acc
                else setBoxTree p newW acc
      else acc)
    BoxLeaf
    b

||| Extracts a 2D Maxel plane slice at a fixed Y-coordinate: Y_k(B) = { [x, z] with w | [x, k, z] in B }
public export
sliceBoxelY : Nat -> Boxel -> Maxel
sliceBoxelY targetY b =
  foldBoxTreeL (\acc, (v, w) =>
    if voxelY v == targetY
      then let p = mkPixel (voxelX v) (voxelZ v)
               cur = lookupBoxTree p acc
               newW = cur + w
           in if boxIsZero newW
                then setBoxTree p (intToBoxInt 0) acc
                else setBoxTree p newW acc
      else acc)
    BoxLeaf
    b

||| Extracts a 2D Maxel plane slice at a fixed X-coordinate: X_k(B) = { [y, z] with w | [k, y, z] in B }
public export
sliceBoxelX : Nat -> Boxel -> Maxel
sliceBoxelX targetX b =
  foldBoxTreeL (\acc, (v, w) =>
    if voxelX v == targetX
      then let p = mkPixel (voxelY v) (voxelZ v)
               cur = lookupBoxTree p acc
               newW = cur + w
           in if boxIsZero newW
                then setBoxTree p (intToBoxInt 0) acc
                else setBoxTree p newW acc
      else acc)
    BoxLeaf
    b

||| Slices a 4D HyperBoxel at a fixed temporal coordinate t = targetT into a 3D spatial Boxel.
public export
sliceHyperBoxelT : Nat -> HyperBoxel -> Boxel
sliceHyperBoxelT targetT h =
  foldBoxTreeL (\acc, (tess, w) =>
    if tesseractT tess == targetT
      then let v = mkVoxel (tesseractX tess) (tesseractY tess) (tesseractZ tess)
               cur = lookupBoxTree v acc
               newW = cur + w
           in if boxIsZero newW
                then setBoxTree v (intToBoxInt 0) acc
                else setBoxTree v newW acc
      else acc)
    BoxLeaf
    h

||| Outer product of a temporal Vexel and a spatial Boxel: T (x) S -> 4D HyperBoxel.
||| Evaluates directly in tree space with zero intermediate List allocations.
public export
outerProductVexelBoxel : Vexel -> Boxel -> HyperBoxel
outerProductVexelBoxel tt spaces =
  foldBoxTreeL (\accT, (u, wt) =>
    let t = unwrapUnixel u
    in foldBoxTreeL (\accS, (v, ws) =>
         let cell = mkTesseract (voxelX v) (voxelY v) (voxelZ v) t
             w    = wt * ws
         in if boxIsZero w then accS
            else let cur = lookupBoxTree cell accS
                     newW = cur + w
                 in if boxIsZero newW
                      then setBoxTree cell (intToBoxInt 0) accS
                      else setBoxTree cell newW accS
       ) accT spaces
  ) BoxLeaf tt

------------------------------------------------------------------------
-- 5. DIMENSION-INDEXED TYPED VECTORS & MATRICES (VexelN & MaxelN)
------------------------------------------------------------------------

||| A VexelN is a dimension-indexed discrete vector of dimension `n`,
||| holding `n` BoxInt scalar weights for unrolled 2LTT staging.
public export
record VexelN (n : Nat) where
  constructor MkVexelN
  components : Vect n BoxInt

public export
Eq (VexelN n) where
  (MkVexelN v1) == (MkVexelN v2) = v1 == v2

public export
{n : Nat} -> Show (VexelN n) where
  show (MkVexelN v) = "Vexel" ++ show n ++ "(" ++ show v ++ ")"

||| Constructor for 2-dimensional VexelN (single qubit state vector).
public export
mkVexel2 : BoxInt -> BoxInt -> VexelN 2
mkVexel2 v0 v1 = MkVexelN [v0, v1]

||| Constructor for 4-dimensional VexelN (two-qubit state vector).
public export
mkVexel4 : BoxInt -> BoxInt -> BoxInt -> BoxInt -> VexelN 4
mkVexel4 v0 v1 v2 v3 = MkVexelN [v0, v1, v2, v3]

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
-- 6. VEXELN CONVERSION BRIDGES
------------------------------------------------------------------------

vectToVexelHelper : Nat -> Vect k BoxInt -> Vexel -> Vexel
vectToVexelHelper _ [] acc = acc
vectToVexelHelper idx (w :: ws) acc =
  if boxIsZero w
    then vectToVexelHelper (S idx) ws acc
    else vectToVexelHelper (S idx) ws (setBoxTree (mkCell1 idx) w acc)

||| Converts a dimension-indexed VexelN into a canonical sparse multiset Vexel (1-indexed).
public export
vexelNToVexel : {n : Nat} -> VexelN n -> Vexel
vexelNToVexel (MkVexelN comps) = vectToVexelHelper 1 comps BoxLeaf

||| Converts a dimension-indexed VexelN into a 0-indexed sparse multiset Vexel (quantum basis).
public export
vexelNToVexel0 : {n : Nat} -> VexelN n -> Vexel
vexelNToVexel0 (MkVexelN comps) = vectToVexelHelper 0 comps BoxLeaf

||| Converts a sparse multiset Vexel into a dimension-indexed VexelN (0-indexed).
public export
vexelToVexelN : (n : Nat) -> Vexel -> VexelN n
vexelToVexelN n v =
  MkVexelN (generateComponents 0 n)
  where
    generateComponents : Nat -> (k : Nat) -> Vect k BoxInt
    generateComponents _ Z = []
    generateComponents idx (S rem) =
      let w = lookupBoxTree (mkCell1 idx) v
      in w :: generateComponents (S idx) rem

||| Converts a sparse multiset Vexel into a dimension-indexed VexelN (1-indexed).
public export
vexelToVexelN1 : (n : Nat) -> Vexel -> VexelN n
vexelToVexelN1 n v =
  MkVexelN (generateComponents 1 n)
  where
    generateComponents : Nat -> (k : Nat) -> Vect k BoxInt
    generateComponents _ Z = []
    generateComponents idx (S rem) =
      let w = lookupBoxTree (mkCell1 idx) v
      in w :: generateComponents (S idx) rem

vectToMaxelRowHelper : Nat -> Nat -> Vect k BoxInt -> Maxel -> Maxel
vectToMaxelRowHelper _ _ [] acc = acc
vectToMaxelRowHelper r c (w :: ws) acc =
  if boxIsZero w
    then vectToMaxelRowHelper r (S c) ws acc
    else vectToMaxelRowHelper r (S c) ws (setBoxTree (mkPixel r c) w acc)

matToMaxelHelper : Nat -> Nat -> Vect k (Vect n BoxInt) -> Maxel -> Maxel
matToMaxelHelper _ _ [] acc = acc
matToMaxelHelper r c0 (row :: rows) acc =
  let acc' = vectToMaxelRowHelper r c0 row acc
  in matToMaxelHelper (S r) c0 rows acc'

||| Converts a dimension-indexed MaxelN into a canonical sparse multiset Maxel (1-indexed).
public export
maxelNToMaxel : {n : Nat} -> MaxelN n -> Maxel
maxelNToMaxel (MkMaxelN rs) = matToMaxelHelper 1 1 rs BoxLeaf

||| Converts a dimension-indexed MaxelN into a 0-indexed sparse multiset Maxel (quantum basis).
public export
maxelNToMaxel0 : {n : Nat} -> MaxelN n -> Maxel
maxelNToMaxel0 (MkMaxelN rs) = matToMaxelHelper 0 0 rs BoxLeaf

------------------------------------------------------------------------
-- 7. SIGNED DIMENSION-INDEXED SPARSE MATRIX (BoxSquareMaxel)
------------------------------------------------------------------------

||| A BoxSquareMaxel is a square discrete matrix of dimension `dim`,
||| holding arbitrary signed BoxInt scalar weights backed by an AVL BoxMultisetTree of Pixels.
public export
record BoxSquareMaxel (dim : Nat) where
  constructor MkBoxSquareMaxel
  entries : CellMultiset 2

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
    _ => let pxs = [mkPixel i i | i <- [0..pred dim]]
             t   = foldl (\tree, p => setBoxTree p (intToBoxInt 1) tree) BoxLeaf pxs
         in MkBoxSquareMaxel t

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
  else setBoxTree (mkPixel (finToNat rFin) (finToNat cFin)) w treeAcc

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
boxSquareMaxelToMaxelNStep dim acc p w =
  let r = pixelRow p
      c = pixelCol p
  in case (natToFin r dim, natToFin c dim) of
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
observeKroneckerPixel n ((r1, r2), (c1, c2)) = mkPixel ((r1 * n) + r2) ((c1 * n) + c2)

||| Sparse Kronecker Tensor Product for BoxSquareMaxel:
public export
kroneckerBoxSquareMaxel : {m, n : Nat} -> BoxSquareMaxel m -> BoxSquareMaxel n -> BoxSquareMaxel (m * n)
kroneckerBoxSquareMaxel {m} {n} (MkBoxSquareMaxel t1) (MkBoxSquareMaxel t2) =
  let resultTree = foldBoxTreeL (\accTree, (p1, w1) =>
        foldBoxTreeL (\innerAcc, (p2, w2) =>
          let r1 = pixelRow p1
              c1 = pixelCol p1
              r2 = pixelRow p2
              c2 = pixelCol p2
              pOut = observeKroneckerPixel n ((r1, r2), (c1, c2))
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

||| 2LTT Staged Kronecker Product for BoxSquareMaxel:
public export
stagedKroneckerBoxSquareMaxel : {m, n : Nat} -> Lift (BoxSquareMaxel m) -> Lift (BoxSquareMaxel n) -> Code (BoxSquareMaxel (m * n))
stagedKroneckerBoxSquareMaxel qm1 qm2 = quote (kroneckerBoxSquareMaxel (splice qm1) (splice qm2))

||| Multiplies two Vect BoxInt vectors via Kronecker tensor product: Vect (n * m) BoxInt.
public export
kroneckerVect : {n, m : Nat} -> Vect n BoxInt -> Vect m BoxInt -> Vect (n * m) BoxInt
kroneckerVect u v = concat (map (\x => map (mulBox x) v) u)

||| Kronecker tensor product of two dimension-indexed VexelN vectors: VexelN (n * m).
public export
kroneckerVexelN : {n, m : Nat} -> VexelN n -> VexelN m -> VexelN (n * m)
kroneckerVexelN (MkVexelN u) (MkVexelN v) = MkVexelN (kroneckerVect u v)

||| 2LTT Staged Kronecker tensor product of two VexelN vectors at Stage 1.
public export
stagedKroneckerVexelN : {n, m : Nat} -> Lift (VexelN n) -> Lift (VexelN m) -> Code (VexelN (n * m))
stagedKroneckerVexelN qv1 qv2 = quote (kroneckerVexelN (splice qv1) (splice qv2))

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

||| 2D Blue (Elliptic/Euclidean) Metric Maxel parameterized by (x, y):
public export
parameterizedBlueMetricMaxel : BoxInt -> BoxInt -> Maxel
parameterizedBlueMetricMaxel x y =
  singletonCell (mkPixel 1 1) (x * x) <+>
  singletonCell (mkPixel 2 2) (y * y)

||| 2D Red (Hyperbolic/Relativistic) Metric Maxel parameterized by (x, y):
public export
parameterizedRedMetricMaxel : BoxInt -> BoxInt -> Maxel
parameterizedRedMetricMaxel x y =
  singletonCell (mkPixel 1 1) (x * x) <+>
  singletonCell (mkPixel 2 2) (mulBox (intToBoxInt (-1)) (y * y))

||| 2D Green (Parabolic/Null) Metric Maxel parameterized by (x, y):
public export
parameterizedGreenMetricMaxel : BoxInt -> BoxInt -> Maxel
parameterizedGreenMetricMaxel x y =
  let xy = x * y
  in singletonCell (mkPixel 1 2) xy <+>
     singletonCell (mkPixel 2 1) xy

public export
blueMetricMaxel2D : Maxel
blueMetricMaxel2D = parameterizedBlueMetricMaxel (intToBoxInt 1) (intToBoxInt 1)

public export
redMetricMaxel2D : Maxel
redMetricMaxel2D = parameterizedRedMetricMaxel (intToBoxInt 1) (intToBoxInt 1)

public export
greenMetricMaxel2D : Maxel
greenMetricMaxel2D = parameterizedGreenMetricMaxel (intToBoxInt 1) (intToBoxInt 1)

||| Converts a BoxSquareMaxel into a MultisetTensor over natural coordinate pairs.
public export
boxSquareMaxelToTensor : {dim : Nat} -> BoxSquareMaxel dim -> Multiset BoxInt (Nat, Nat)
boxSquareMaxelToTensor (MkBoxSquareMaxel tree) =
  foldBoxTreeR (\p, w, acc => AddM (pixelRow p, pixelCol p) w acc) ZeroM tree

||| Reconstructs a sparse BoxSquareMaxel from an observed MultisetTensor Pixel.
public export
tensorToBoxSquareMaxel : {dim : Nat} -> Multiset BoxInt Pixel -> BoxSquareMaxel dim
tensorToBoxSquareMaxel tensor =
  MkBoxSquareMaxel (foldMultiset (\p, w, tree => setBoxTree p w tree) BoxLeaf tensor)

||| Converts a general Maxel into a typed MultisetTensor over natural coordinates.
public export
maxelToTensor : Maxel -> MultisetTensor Nat Nat
maxelToTensor tree =
  foldBoxTreeR (\p, w, acc => AddM (pixelRow p, pixelCol p) w acc) ZeroM tree

||| Reconstructs a general Maxel from a MultisetTensor over natural coordinates.
public export
tensorToMaxel : MultisetTensor Nat Nat -> Maxel
tensorToMaxel tensor =
  foldMultiset (\(r, c), w, tree =>
                 if boxIsZero w then tree
                 else let p = mkPixel r c
                          cur = lookupBoxTree p tree
                          newW = cur + w
                      in if boxIsZero newW
                           then setBoxTree p (intToBoxInt 0) tree
                           else setBoxTree p newW tree)
                BoxLeaf
                tensor


