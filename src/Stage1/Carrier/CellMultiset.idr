module Stage1.Carrier.CellMultiset

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
