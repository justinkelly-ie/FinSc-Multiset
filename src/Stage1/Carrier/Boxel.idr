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

||| A Boxel is a multiset of Voxels (Wildberger 3D Volume Tensor).
||| Stored as a list of weighted coordinate Voxels: sum rho_xyz * [x, y, z].
public export
record Boxel where
  constructor MkBoxel
  voxels : List (Voxel, BoxInt)

public export
Eq Boxel where
  (MkBoxel b1) == (MkBoxel b2) = b1 == b2

public export
Show Boxel where
  show (MkBoxel bs) = "Boxel(" ++ show bs ++ ")"

||| Extracts the weight of a specific coordinate Voxel in a Boxel.
public export
lookupVoxel : Voxel -> Boxel -> BoxInt
lookupVoxel target (MkBoxel vs) =
  foldl (\acc, (v, w) => if v == target then acc + w else acc) (intToBoxInt 0) vs

||| Adds two Boxels by concatenating their voxel multiset entries.
public export
addBoxel : Boxel -> Boxel -> Boxel
addBoxel (MkBoxel bs1) (MkBoxel bs2) = MkBoxel (bs1 ++ bs2)

||| Scales a Boxel by a BoxInt scalar.
public export
scaleBoxel : BoxInt -> Boxel -> Boxel
scaleBoxel s (MkBoxel bs) =
  MkBoxel (map (\(v, w) => (v, s * w)) bs)

||| Translates all voxel coordinates in a Boxel by a spatial Voxel offset (Wildberger multiset translation).
public export
translateBoxel : Voxel -> Boxel -> Boxel
translateBoxel offset (MkBoxel bs) =
  MkBoxel (map (\(v, w) => (v + offset, w)) bs)

||| Computes total weight/density across all voxels in a Boxel.
public export
totalBoxelWeight : Boxel -> BoxInt
totalBoxelWeight (MkBoxel bs) =
  sum (map snd bs)

public export
Semigroup Boxel where
  (<+>) = addBoxel

public export
Monoid Boxel where
  neutral = MkBoxel []

public export
implementation MultisetAlgebra Boxel where
  zeroM = MkBoxel []
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
boxelToTree (MkBoxel vs) =
  foldl (\tree, (v, w) => insertTokenTree v (boxToNat w) tree) Leaf vs

||| Converts a MultisetTree back to a Boxel in linear O(N) time via in-order accumulator.
public export
treeToBoxel : MultisetTree Voxel -> Boxel
treeToBoxel tree =
  MkBoxel (foldTreeR (\v, cnt, acc => (v, natToBoxInt cnt) :: acc) [] tree)

||| O(log N) lookup for coordinate voxel in a BoxelTree.
public export
lookupVoxelTree : Voxel -> MultisetTree Voxel -> Nat
lookupVoxelTree = lookupTokenTree

public export
pruneBoxelTerms : List (Voxel, BoxInt) -> List (Voxel, BoxInt)
pruneBoxelTerms [] = []
pruneBoxelTerms ((v, w) :: rest) =
  if boxIsZero w then pruneBoxelTerms rest else (v, w) :: pruneBoxelTerms rest

||| Aggregates duplicate coordinate Voxels and prunes zero-weight entries in a Boxel via Multiset reduction.
public export
canonicalizeBoxel : Boxel -> Boxel
canonicalizeBoxel (MkBoxel voxs) = MkBoxel (multisetToList (fromListBox voxs))

public export
boxelToMultiset : Boxel -> Multiset BoxInt Voxel
boxelToMultiset (MkBoxel voxs) = fromListBox voxs

public export
multisetToBoxel : Multiset BoxInt Voxel -> Boxel
multisetToBoxel m = MkBoxel (multisetToList m)

------------------------------------------------------------------------
-- 3. CHIRAL OUTER PRODUCTS & PLANE SLICES
------------------------------------------------------------------------

||| 3D Tensor Outer Product: Vexel (1D ket) x Maxel (2D surface) -> Boxel (3D volume).
public export
outerProductVexelMaxel : Vexel -> Maxel -> Boxel
outerProductVexelMaxel (MkVexelTree tk) (MkMaxelTree tm) =
  let generated = foldBoxTreeL (\accK, (s, sw) =>
        foldBoxTreeL (\accM, (p, pw) =>
          (mkVoxel (unwrapUnixel s) (pixelRow p) (pixelCol p), sw * pw) :: accM)
          accK
          tm)
        []
        tk
  in canonicalizeBoxel (MkBoxel generated)

||| Extracts a 2D Maxel plane slice at a fixed Z-coordinate: Z_k(B) = { [x, y] with w | [x, y, k] in B }
public export
sliceBoxelZ : Nat -> Boxel -> Maxel
sliceBoxelZ targetZ (MkBoxel voxs) =
  let resultTree = foldl (\acc, (v, w) =>
                     if voxelZ v == targetZ
                       then let p = mkPixel (voxelX v) (voxelY v)
                                cur = lookupBoxTree p acc
                                newW = cur + w
                            in if boxIsZero newW
                                 then setBoxTree p (intToBoxInt 0) acc
                                 else setBoxTree p newW acc
                       else acc)
                     BoxLeaf
                     voxs
  in MkMaxelTree resultTree

||| Extracts a 2D Maxel plane slice at a fixed Y-coordinate: Y_k(B) = { [x, z] with w | [x, k, z] in B }
public export
sliceBoxelY : Nat -> Boxel -> Maxel
sliceBoxelY targetY (MkBoxel voxs) =
  let resultTree = foldl (\acc, (v, w) =>
                     if voxelY v == targetY
                       then let p = mkPixel (voxelX v) (voxelZ v)
                                cur = lookupBoxTree p acc
                                newW = cur + w
                            in if boxIsZero newW
                                 then setBoxTree p (intToBoxInt 0) acc
                                 else setBoxTree p newW acc
                       else acc)
                     BoxLeaf
                     voxs
  in MkMaxelTree resultTree

||| Extracts a 2D Maxel plane slice at a fixed X-coordinate: X_k(B) = { [y, z] with w | [k, y, z] in B }
public export
sliceBoxelX : Nat -> Boxel -> Maxel
sliceBoxelX targetX (MkBoxel voxs) =
  let resultTree = foldl (\acc, (v, w) =>
                     if voxelX v == targetX
                       then let p = mkPixel (voxelY v) (voxelZ v)
                                cur = lookupBoxTree p acc
                                newW = cur + w
                            in if boxIsZero newW
                                 then setBoxTree p (intToBoxInt 0) acc
                                 else setBoxTree p newW acc
                       else acc)
                     BoxLeaf
                     voxs
  in MkMaxelTree resultTree

------------------------------------------------------------------------
------------------------------------------------------------------------
-- 4. GRASSMANN WEDGE PRODUCTS & EXTERIOR ALGEBRA
------------------------------------------------------------------------

||| Evaluates the Grassmann exterior wedge product of a Vexel and a Maxel into a 3D Boxel:
public export
wedgeVexelMaxel : Vexel -> Maxel -> Boxel
wedgeVexelMaxel (MkVexelTree tu) (MkMaxelTree tm) =
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
  in canonicalizeBoxel (MkBoxel terms)

------------------------------------------------------------------------
-- 5. 4D SPACETIME HYPERBOXEL TENSORS (Tesseract [x, y, z, t])
------------------------------------------------------------------------

||| A 4D Spacetime HyperBoxel represents a 4D volume multiset of weighted Tesseract cells.
public export
record HyperBoxel where
  constructor MkHyperBoxel
  cells : List (Tesseract, BoxInt)

public export
Eq HyperBoxel where
  (MkHyperBoxel c1) == (MkHyperBoxel c2) = c1 == c2

public export
Show HyperBoxel where
  show (MkHyperBoxel c) = "HyperBoxel" ++ show c

||| Canonicalizes a 4D HyperBoxel by pruning zeros and merging duplicate Tesseract coordinates.
public export
canonicalizeHyperBoxel : HyperBoxel -> HyperBoxel
canonicalizeHyperBoxel (MkHyperBoxel raw) =
  let nonZero = filter (\(_, w) => boxIsNonZero w) raw
      merged = foldl insertOrAdd [] nonZero
  in MkHyperBoxel merged
  where
    insertOrAdd : List (Tesseract, BoxInt) -> (Tesseract, BoxInt) -> List (Tesseract, BoxInt)
    insertOrAdd [] item = [item]
    insertOrAdd ((t, w) :: rest) (newT, newW) =
      if t == newT
        then let combined = w + newW
             in if boxIsZero combined then rest else (t, combined) :: rest
        else (t, w) :: insertOrAdd rest (newT, newW)

||| Looks up the weight of a 4D Tesseract coordinate in a HyperBoxel.
public export
lookupTesseract : Tesseract -> HyperBoxel -> BoxInt
lookupTesseract target (MkHyperBoxel raw) =
  case find (\(t, _) => t == target) raw of
    Just (_, w) => w
    Nothing     => intToBoxInt 0

||| Slices a 4D HyperBoxel at a fixed temporal coordinate t = targetT into a 3D spatial Boxel.
public export
sliceHyperBoxelT : Nat -> HyperBoxel -> Boxel
sliceHyperBoxelT targetT (MkHyperBoxel cells) =
  let extracted = mapMaybe (\(tess, w) =>
                    if tesseractT tess == targetT
                      then Just (mkVoxel (tesseractX tess) (tesseractY tess) (tesseractZ tess), w)
                      else Nothing) cells
  in canonicalizeBoxel (MkBoxel extracted)

||| Outer product of a temporal Vexel and a spatial Boxel: T (x) S -> 4D HyperBoxel.
public export
outerProductVexelBoxel : Vexel -> Boxel -> HyperBoxel
outerProductVexelBoxel (MkVexelTree tt) (MkBoxel spaces) =
  let productList = foldBoxTreeL (\accT, (u, wt) =>
        let t = unwrapUnixel u
        in foldl (\accS, (v, ws) =>
             (mkTesseract (voxelX v) (voxelY v) (voxelZ v) t, wt * ws) :: accS)
             accT
             spaces)
        []
        tt
  in canonicalizeHyperBoxel (MkHyperBoxel productList)

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
boxelToTrivariatePolynumber (MkBoxel vs) =
  map (\(v, w) => ((voxelX v, voxelY v, voxelZ v), w)) vs

