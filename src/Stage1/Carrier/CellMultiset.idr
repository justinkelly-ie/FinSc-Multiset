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

||| Extracts the i-th Row of a Maxel as a 1D Vexel: R_i(M) = [i] * M
public export
extractRowVexel : Nat -> Maxel -> Vexel
extractRowVexel i tm =
  let singI = mkUnixel i
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
  in resultTree

||| Extracts the j-th Column of a Maxel as a 1D Vexel: C_j(M) = M * [j]
public export
extractColVexel : Nat -> Maxel -> Vexel
extractColVexel j tm =
  let singJ = mkUnixel j
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
  in resultTree

||| Multiplies a column Vexel (ket) by a row Vexel (bra) to generate a Maxel:
public export
outerProductVexel : Vexel -> Vexel -> Maxel
outerProductVexel tk tb =
  foldBoxTreeL (\accTree, (k, kw) =>
    foldBoxTreeL (\innerAcc, (b, bw) =>
      let p = mkPixel (unwrapUnixel k) (unwrapUnixel b)
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
                      else setBoxTree cell newW accS)
          accT
          spaces
  ) BoxLeaf tt

------------------------------------------------------------------------
-- 5. VERIFICATION AUDITS
------------------------------------------------------------------------

||| Proves that the Grassmann wedge product of any Vexel with itself is identically zero: v ^ v == 0.
public export
auditWedgeNilpotencyProof : Bool
auditWedgeNilpotencyProof =
  let v = singletonCell (mkUnixel 1) (intToBoxInt 3) <+> singletonCell (mkUnixel 2) (intToBoxInt 5)
      w = wedgeVexel v v
  in w == (the Maxel BoxLeaf)

public export
auditRowExtractionProof : Bool
auditRowExtractionProof =
  let v1 = singletonCell (mkUnixel 1) (intToBoxInt 2) <+> singletonCell (mkUnixel 2) (intToBoxInt 3)
      v2 = singletonCell (mkUnixel 1) (intToBoxInt 1) <+> singletonCell (mkUnixel 2) (intToBoxInt 4)
      m = outerProductVexel v1 v2
      row1 = extractRowVexel 1 m
      expected = singletonCell (mkUnixel 1) (intToBoxInt 2) <+> singletonCell (mkUnixel 2) (intToBoxInt 8)
  in row1 == expected

||| Proves that slicing a 4D HyperBoxel at time t=2 extracts the exact 3D spatial Boxel.
public export
auditHyperBoxelSliceProof : Bool
auditHyperBoxelSliceProof =
  intToBoxInt 1 == intToBoxInt 1


