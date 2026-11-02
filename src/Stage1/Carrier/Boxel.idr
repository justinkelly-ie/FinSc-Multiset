module Stage1.Carrier.Boxel

import Data.Nat
import Data.Fin
import Stage0.BoxInt
import Stage0.OnSeq.FusedStream
import Stage1.MultisetTree
import Stage1.Basis.CoordCell
import public Stage1.Carrier.CellMultiset
import public Stage1.Carrier.Vexel
import public Stage1.Carrier.Maxel

%default total

------------------------------------------------------------------------
-- 1. PURE 3D DISCRETE VOLUME CARRIER (Boxel)
------------------------------------------------------------------------

||| Backward-compatibility constructor alias for tree-backed Boxels.
public export
MkBoxelTree : BoxMultisetTree Voxel -> Boxel
MkBoxelTree t = t



||| Canonical empty/zero Boxel.
public export
emptyBoxel : Boxel
emptyBoxel = BoxLeaf

||| Canonicalize a Boxel (prunes zero weights and rebalances).
public export
canonicalizeBoxel : Boxel -> Boxel
canonicalizeBoxel = canonicalizeCellMultiset

||| Compresses a Boxel by pruning zero weights and rebalancing.
public export
compressBoxel : Boxel -> Boxel
compressBoxel = canonicalizeCellMultiset

||| Extracts voxel-weight terms association list from a 3D Boxel.
public export
voxels : Boxel -> List (Voxel, BoxInt)
voxels = boxTreeToList

||| Lookups the signed BoxInt weight of a coordinate Voxel in O(log N) time.
public export
lookupVoxel : Voxel -> Boxel -> BoxInt
lookupVoxel = lookupCellMultiset

||| Evaluates the standard Euclidean inner product between two Boxels:
||| <b1, b2> = sum w1_i * w2_i
public export
dotProduct : Boxel -> Boxel -> BoxInt
dotProduct = dotCellMultiset {dim = 3}

||| Specialized alias for dotProduct on 3D Boxels.
public export
dotBoxel : Boxel -> Boxel -> BoxInt
dotBoxel = dotCellMultiset {dim = 3}

||| Evaluates the inner product between two Boxels via deforested stream (Rule 04 §8).
public export
dotProductStream : Boxel -> Boxel -> BoxInt
dotProductStream = dotCellMultisetStream {dim = 3}

||| Scales a Boxel by a signed BoxInt scalar.
public export
scaleBoxel : BoxInt -> Boxel -> Boxel
scaleBoxel = scaleCellMultiset {dim = 3}

||| Adds two Boxels.
public export
addBoxel : Boxel -> Boxel -> Boxel
addBoxel = addCellMultiset {dim = 3}

||| Subtracts two Boxels: b1 - b2 = b1 + (-1) * b2
public export
subBoxel : Boxel -> Boxel -> Boxel
subBoxel = subCellMultiset {dim = 3}

||| Evaluates the L1 norm of a Boxel (sum of absolute weights).
public export
normL1Boxel : Boxel -> BoxInt
normL1Boxel b =
  foldBoxTreeL (\acc, (_, w) => acc + absBox w) (intToBoxInt 0) (the (BoxMultisetTree (CoordCell 3)) b)

||| Computes total weight across all voxels in a Boxel.
public export
totalBoxelWeight : Boxel -> BoxInt
totalBoxelWeight = totalCellMultisetWeight

||| Stream representation of the finite active support of a Boxel in O(1) registers.
public export
supportBoxelStream : Boxel -> FusedStream Voxel
supportBoxelStream = supportCellStream

||| Converts a Boxel to a deforested stream of (Voxel, BoxInt) pairs in O(1) registers.
public export
streamBoxel : Boxel -> FusedStream (Voxel, BoxInt)
streamBoxel = streamCellMultiset

||| Collects a deforested stream of (Voxel, BoxInt) pairs into a canonical Boxel.
public export
streamToBoxel : FusedStream (Voxel, BoxInt) -> Boxel
streamToBoxel = streamToCellMultiset

------------------------------------------------------------------------
-- 2. TENSOR PRODUCTS & GRASSMANN EXTERIOR PRODUCTS
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- 3. PLANAR MAXEL SLICING
------------------------------------------------------------------------

||| Extracts a 2D Maxel plane slice at a fixed Z-coordinate: Z_k(B) = { [x, y] with w | [x, y, k] in B }
public export
sliceBoxelZ : Nat -> Boxel -> Maxel
sliceBoxelZ targetZ b = sliceCellMultiset (FS (FS FZ)) targetZ b

||| Extracts a 2D Maxel plane slice at a fixed Y-coordinate: Y_k(B) = { [x, z] with w | [x, k, z] in B }
public export
sliceBoxelY : Nat -> Boxel -> Maxel
sliceBoxelY targetY b = sliceCellMultiset (FS FZ) targetY b

||| Extracts a 2D Maxel plane slice at a fixed X-coordinate: X_k(B) = { [y, z] with w | [k, y, z] in B }
public export
sliceBoxelX : Nat -> Boxel -> Maxel
sliceBoxelX targetX b = sliceCellMultiset FZ targetX b

------------------------------------------------------------------------
-- 4. VERIFICATION AUDITS
------------------------------------------------------------------------

||| Audits that slicing an outerProductVexelMaxel along the vector coordinate recovers the scaled Maxel.
public export
auditBoxelSliceProof : Bool
auditBoxelSliceProof =
  let v = singletonCell (mkUnixel 2) (intToBoxInt 3)
      m = singletonCell (mkPixel 1 2) (intToBoxInt 4) <+> singletonCell (mkPixel 3 1) (intToBoxInt 5)
      b = outerProductVexelMaxel v m
      s2 = sliceBoxelX 2 b
      s1 = sliceBoxelX 1 b
  in (s2 == scaleMaxel (intToBoxInt 3) m) && (s1 == emptyMaxel)
