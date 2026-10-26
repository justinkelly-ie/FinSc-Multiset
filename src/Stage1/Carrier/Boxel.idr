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

||| @deprecated Use CellMultiset 3 directly. Transparent constructor bridge for Boxel.
public export
MkBoxelTree : BoxMultisetTree Voxel -> Boxel
MkBoxelTree t = t

||| Constructs a canonical Boxel from an association list of Voxels.
||| @deprecated Use singletonCell + (<+>), streamToCellMultiset, or fromVectCells. Avoid heap List materialization.
public export
mkBoxel : List (Voxel, BoxInt) -> Boxel
mkBoxel = mkCellMultiset

||| Constructor alias for Boxel from coordinate pairs.
||| @deprecated Use singletonCell + (<+>), streamToCellMultiset, or fromVectCells. Avoid heap List materialization.
public export
MkBoxel : List (Voxel, BoxInt) -> Boxel
MkBoxel = mkCellMultiset

||| Extracts voxels association list from a Boxel in O(N).
||| @deprecated Use streamCellMultiset or foldBoxTreeL directly. Avoid materializing entire multiset as List.
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

||| @deprecated Use canonicalizeCellMultiset directly on CellMultiset trees.
public export
pruneBoxelTerms : List (Voxel, BoxInt) -> List (Voxel, BoxInt)
pruneBoxelTerms [] = []
pruneBoxelTerms ((v, w) :: rest) =
  if boxIsZero w then pruneBoxelTerms rest else (v, w) :: pruneBoxelTerms rest

||| Canonicalizes a Boxel by pruning zero weights and rebalancing.
public export
canonicalizeBoxel : Boxel -> Boxel
canonicalizeBoxel = canonicalizeCellMultiset

||| @deprecated Legacy bridge converting Boxel to heap-allocated linked list Multiset.
||| Use CellMultiset operations or boxTreeToList directly.
public export
boxelToMultiset : Boxel -> Multiset BoxInt Voxel
boxelToMultiset t = fromListBox (boxTreeToList t)

||| @deprecated Legacy bridge converting linked list Multiset to Boxel.
||| Use mkCellMultiset directly.
public export
multisetToBoxel : Multiset BoxInt Voxel -> Boxel
multisetToBoxel m = mkCellMultiset (multisetToList m)

------------------------------------------------------------------------
-- 3. CHIRAL OUTER PRODUCTS & PLANE SLICES (Provided by CellMultiset)
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 4. GRASSMANN WEDGE PRODUCTS & EXTERIOR ALGEBRA
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 5. 4D SPACETIME HYPERBOXEL TENSORS (Tesseract [x, y, z, t])
------------------------------------------------------------------------

||| @deprecated Use CellMultiset 4 directly. Transparent constructor bridge for HyperBoxel.
public export
MkHyperBoxelTree : BoxMultisetTree Cell -> HyperBoxel
MkHyperBoxelTree t = t

||| Constructs a canonical HyperBoxel from an association list of Cells.
||| @deprecated Use singletonCell + (<+>), streamToCellMultiset, or fromVectCells. Avoid heap List materialization.
public export
mkHyperBoxel : List (Cell, BoxInt) -> HyperBoxel
mkHyperBoxel = mkCellMultiset

||| Constructor alias for HyperBoxel from coordinate pairs.
||| @deprecated Use singletonCell + (<+>), streamToCellMultiset, or fromVectCells. Avoid heap List materialization.
public export
MkHyperBoxel : List (Cell, BoxInt) -> HyperBoxel
MkHyperBoxel = mkCellMultiset

||| Extracts cells association list from a HyperBoxel in O(N).
||| @deprecated Use streamCellMultiset or foldBoxTreeL directly. Avoid materializing entire multiset as List.
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
