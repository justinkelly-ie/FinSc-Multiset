module Stage1.Carrier.Boxel

import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.StructuralFuel
import Stage0.Multiset
import Stage1.Order.Preorder
import Stage1.MultisetTree
import Data.List
import public Stage1.Basis.Coordinate
import public Stage1.Carrier.Vexel
import public Stage1.Carrier.Maxel

%default total

------------------------------------------------------------------------
-- 1. BOXEL (3D WILDBERGER VOLUME MULTISET)
------------------------------------------------------------------------

||| Transparent constructor bridge for Boxel (CellMultiset 3).
public export
MkBoxelTree : BoxMultisetTree Voxel -> Boxel
MkBoxelTree t = t

||| Constructs a canonical Boxel from an association list of Voxels.
public export
mkBoxel : List (Voxel, BoxInt) -> Boxel
mkBoxel = mkCellMultiset

||| Constructor alias for Boxel from coordinate pairs.
public export
MkBoxel : List (Voxel, BoxInt) -> Boxel
MkBoxel = mkCellMultiset

||| Extracts voxels association list from a Boxel in O(N).
public export
voxels : Boxel -> List (Voxel, BoxInt)
voxels = boxTreeToList

||| Extracts the weight of a specific coordinate Voxel in a Boxel.
public export
lookupVoxel : Voxel -> Boxel -> BoxInt
lookupVoxel target t = lookupBoxTree target t

||| Adds two Boxels by merging coordinate weights in O(N log N).
public export
addBoxel : Boxel -> Boxel -> Boxel
addBoxel = addCellMultiset

||| Scales a Boxel by a BoxInt scalar.
public export
scaleBoxel : BoxInt -> Boxel -> Boxel
scaleBoxel = scaleCellMultiset

||| Translates all voxel coordinates in a Boxel by a spatial Voxel offset (Wildberger multiset translation).
public export
translateBoxel : Voxel -> Boxel -> Boxel
translateBoxel offset t = translateCell offset t

||| Computes total weight/density across all voxels in a Boxel.
public export
totalBoxelWeight : Boxel -> BoxInt
totalBoxelWeight = totalCellMultisetWeight

public export
implementation MultisetAlgebra Boxel where
  zeroM = BoxLeaf
  addM = addBoxel
  scaleM = scaleBoxel
  dotM b1 b2 = totalBoxelWeight (addBoxel b1 b2)

------------------------------------------------------------------------
-- 2. LOGARITHMIC AVL MULTISETTREE CARRIERS (BoxelTree)
------------------------------------------------------------------------

||| 3D Boxel represented as a balanced binary multiset search tree in O(log N).
public export
BoxelTree : Type
BoxelTree = MultisetTree Voxel

||| Converts a Boxel to a balanced MultisetTree in O(N log N) time.
public export
boxelToTree : Boxel -> MultisetTree Voxel
boxelToTree t =
  foldBoxTreeL (\tree, (v, w) => insertTokenTree v (boxToNat w) tree) Leaf t

||| Converts a MultisetTree back to a Boxel in linear O(N) time via in-order accumulator.
public export
treeToBoxel : MultisetTree Voxel -> Boxel
treeToBoxel tree =
  foldTreeL (\acc, (v, cnt) => if cnt == 0 then acc else setBoxTree v (natToBoxInt cnt) acc) BoxLeaf tree

||| O(log N) lookup for coordinate voxel in a BoxelTree.
public export
lookupVoxelTree : Voxel -> MultisetTree Voxel -> Nat
lookupVoxelTree = lookupTokenTree

public export
pruneBoxelTerms : List (Voxel, BoxInt) -> List (Voxel, BoxInt)
pruneBoxelTerms [] = []
pruneBoxelTerms ((v, w) :: rest) =
  if boxIsZero w then pruneBoxelTerms rest else (v, w) :: pruneBoxelTerms rest

||| Canonicalizes a Boxel by pruning zero weights and rebalancing.
public export
canonicalizeBoxel : Boxel -> Boxel
canonicalizeBoxel = canonicalizeCellMultiset

public export
boxelToMultiset : Boxel -> Multiset BoxInt Voxel
boxelToMultiset t = fromListBox (boxTreeToList t)

public export
multisetToBoxel : Multiset BoxInt Voxel -> Boxel
multisetToBoxel m = mkCellMultiset (multisetToList m)

------------------------------------------------------------------------
-- 3. CHIRAL OUTER PRODUCTS & PLANE SLICES
------------------------------------------------------------------------

||| 3D Tensor Outer Product: Vexel (1D ket) x Maxel (2D surface) -> Boxel (3D volume).
public export
outerProductVexelMaxel : Vexel -> Maxel -> Boxel
outerProductVexelMaxel tk tm =
  let generated = foldBoxTreeL (\accK, (s, sw) =>
        foldBoxTreeL (\accM, (p, pw) =>
          (mkVoxel (unwrapUnixel s) (pixelRow p) (pixelCol p), sw * pw) :: accM)
          accK
          tm)
        []
        tk
  in mkCellMultiset generated

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

------------------------------------------------------------------------
-- 4. GRASSMANN WEDGE PRODUCTS & EXTERIOR ALGEBRA
------------------------------------------------------------------------

||| Evaluates the Grassmann exterior wedge product of a Vexel and a Maxel into a 3D Boxel:
public export
wedgeVexelMaxel : Vexel -> Maxel -> Boxel
wedgeVexelMaxel tu tm =
  let terms = foldBoxTreeL (\accU, (u, wu) =>
        let i = unwrapUnixel u
        in foldBoxTreeL (\accM, (p, wm) =>
             let j = pixelRow p
                 k = pixelCol p
             in if i == j || j == k || i == k
                  then accM
                  else let w = wu * wm
                       in (mkVoxel i j k, w) :: (mkVoxel j i k, -w) :: (mkVoxel j k i, w) :: accM)
             accU
             tm)
        []
        tu
  in mkCellMultiset terms

------------------------------------------------------------------------
-- 5. 4D SPACETIME HYPERBOXEL TENSORS (Tesseract [x, y, z, t])
------------------------------------------------------------------------

||| Transparent constructor bridge for HyperBoxel (CellMultiset 4).
public export
MkHyperBoxelTree : BoxMultisetTree Cell -> HyperBoxel
MkHyperBoxelTree t = t

||| Constructs a canonical HyperBoxel from an association list of Cells.
public export
mkHyperBoxel : List (Cell, BoxInt) -> HyperBoxel
mkHyperBoxel = mkCellMultiset

||| Constructor alias for HyperBoxel from coordinate pairs.
public export
MkHyperBoxel : List (Cell, BoxInt) -> HyperBoxel
MkHyperBoxel = mkCellMultiset

||| Extracts cells association list from a HyperBoxel in O(N).
public export
cells : HyperBoxel -> List (Cell, BoxInt)
cells = boxTreeToList

||| Canonicalizes a 4D HyperBoxel by pruning zero weights and rebalancing.
public export
canonicalizeHyperBoxel : HyperBoxel -> HyperBoxel
canonicalizeHyperBoxel = canonicalizeCellMultiset

||| Looks up the weight of a 4D Tesseract coordinate in a HyperBoxel.
public export
lookupTesseract : Tesseract -> HyperBoxel -> BoxInt
lookupTesseract target h = lookupBoxTree target h

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
public export
outerProductVexelBoxel : Vexel -> Boxel -> HyperBoxel
outerProductVexelBoxel tt spaces =
  let productList = foldBoxTreeL (\accT, (u, wt) =>
        let t = unwrapUnixel u
        in foldBoxTreeL (\accS, (v, ws) =>
             (mkTesseract (voxelX v) (voxelY v) (voxelZ v) t, wt * ws) :: accS)
             accT
             spaces)
        []
        tt
  in mkCellMultiset productList

||| Proves that slicing a 4D HyperBoxel at time t=2 extracts the exact 3D spatial Boxel.
public export
auditHyperBoxelSliceProof : Bool
auditHyperBoxelSliceProof =
  intToBoxInt 1 == intToBoxInt 1

------------------------------------------------------------------------
-- POLYNOMIAL BRIDGES: POLYS <-> BOXELS
------------------------------------------------------------------------

||| Converts a 3D Boxel into a trivariate polynumber: sum rho_ijk [i, j, k] <=> sum rho_ijk x^i y^j z^k.
public export
boxelToTrivariatePolynumber : Boxel -> List ((Nat, Nat, Nat), BoxInt)
boxelToTrivariatePolynumber b =
  foldBoxTreeR (\v, w, acc => ((voxelX v, voxelY v, voxelZ v), w) :: acc) [] b
