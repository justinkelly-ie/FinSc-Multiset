module Stage1.Basis.Coordinate

import Data.Nat
import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.StructuralFuel
import public Stage0.OnSeq.FusedStream
import public Stage1.MultisetTree
import Stage1.Order.Preorder

%default total

------------------------------------------------------------------------
-- 1. CANONICAL DISCRETE DIMENSION CONSTANTS (Nat)
------------------------------------------------------------------------

||| Canonical 1-dimensional discrete dimension index.
public export
Dim1 : Nat
Dim1 = 1

||| Canonical 2-dimensional discrete dimension index.
public export
Dim2 : Nat
Dim2 = 2

||| Canonical 3-dimensional discrete dimension index.
public export
Dim3 : Nat
Dim3 = 3

||| Canonical 4-dimensional discrete dimension index.
public export
Dim4 : Nat
Dim4 = 4

||| Canonical 10-dimensional discrete dimension index.
public export
Dim10 : Nat
Dim10 = 10

------------------------------------------------------------------------
-- 2. UNIVERSAL DEPENDENT COORDINATE BASIS CELL (COORDCELL)
------------------------------------------------------------------------

||| Arbitrary D-dimensional coordinate basis cell, indexed by Peano Nat dimension.
||| Backed by a balanced AVL MultisetTree Nat mapping dimension axes to coordinates.
||| Completely eliminates Data.Vect heap allocations and vector consing conflicts.
public export
record CoordCell (dim : Nat) where
  constructor MkCoordCell
  coords : MultisetTree Nat

public export
coordCellEq : CoordCell dim -> CoordCell dim -> Bool
coordCellEq (MkCoordCell cs1) (MkCoordCell cs2) = cs1 == cs2

public export
Eq (CoordCell dim) where
  (MkCoordCell cs1) == (MkCoordCell cs2) = cs1 == cs2

public export
Ord (CoordCell dim) where
  compare (MkCoordCell cs1) (MkCoordCell cs2) =
    compare (treeToList cs1) (treeToList cs2)

public export
Show (CoordCell dim) where
  show (MkCoordCell tree) =
    let pairs = foldStream (\acc, (axis, val) => acc ++ [val]) (the (List Nat) []) (streamMultisetTreeDirect tree)
    in show pairs

||| Converts a D-dimensional coordinate cell into a zero-allocation deforested FusedStream of (axis, coord).
public export
streamCoordCell : CoordCell dim -> FusedStream (Nat, Nat)
streamCoordCell (MkCoordCell tree) = streamMultisetTreeDirect tree

||| Lookups the coordinate component along the specified axis (0 .. dim-1) in O(log D) time.
public export
coordCellAxis : Nat -> CoordCell dim -> Nat
coordCellAxis axis (MkCoordCell tree) = lookupTokenTree axis tree

||| Sets the coordinate component along the specified axis in O(log D) time.
public export
coordCellSetAxis : Nat -> Nat -> CoordCell dim -> CoordCell dim
coordCellSetAxis axis val (MkCoordCell tree) = MkCoordCell (insertTokenTree axis val tree)

------------------------------------------------------------------------
-- 3. CANONICAL DIMENSION TYPE SYNONYMS & SMART CONSTRUCTORS
------------------------------------------------------------------------

||| A Unixel is a 1D basis coordinate cell (CoordCell Dim1).
public export
Unixel : Type
Unixel = CoordCell Dim1

||| Smart constructor for 1D Unixel cell.
%inline public export
mkUnixel : Nat -> Unixel
mkUnixel i = MkCoordCell (Node 1 Leaf 0 i Leaf)

||| Canonical constructor alias for 1D Unixel cell.
%inline public export
MkUnixel : Nat -> Unixel
MkUnixel = mkUnixel

||| Unwraps the natural coordinate of a Unixel.
%inline public export
unwrapUnixel : Unixel -> Nat
unwrapUnixel (MkCoordCell (Node _ _ _ i _)) = i
unwrapUnixel _ = 0

||| Equality predicate on Unixel.
public export
unixelEq : Unixel -> Unixel -> Bool
unixelEq = coordCellEq

||| A Pixel is a 2D coordinate cell or signed difference pair (CoordCell Dim2).
public export
Pixel : Type
Pixel = CoordCell Dim2

||| Canonical unambiguous alias for discrete 2D grid matrix cells.
public export
GridPixel : Type
GridPixel = Pixel

||| Alternative alias for cell coordinate.
public export
CellPixel : Type
CellPixel = Pixel

||| Smart constructor for 2D Pixel cell.
%inline public export
mkPixel : Nat -> Nat -> Pixel
mkPixel r c = MkCoordCell (Node 2 Leaf 0 r (Node 1 Leaf 1 c Leaf))

||| Canonical constructor alias for 2D Pixel cell.
%inline public export
MkPixel : Nat -> Nat -> Pixel
MkPixel = mkPixel

||| Projections for 2D Pixel cell.
%inline public export
pixelRow : Pixel -> Nat
pixelRow (MkCoordCell (Node _ (Node _ _ 0 r _) _ _ _)) = r
pixelRow (MkCoordCell (Node _ _ 0 r _)) = r
pixelRow (MkCoordCell (Node _ _ _ r _)) = r
pixelRow _ = 0

%inline public export
pixelCol : Pixel -> Nat
pixelCol (MkCoordCell (Node _ _ 0 _ (Node _ _ 1 c _))) = c
pixelCol (MkCoordCell (Node _ _ 1 c _)) = c
pixelCol (MkCoordCell (Node _ _ _ _ (Node _ _ 1 c _))) = c
pixelCol (MkCoordCell (Node _ _ _ _ (Node _ _ _ c _))) = c
pixelCol _ = 0

||| Equality predicate on Pixel.
public export
pixelEq : Pixel -> Pixel -> Bool
pixelEq = coordCellEq

||| Multiplies a Pixel by a Pixel (discrete matrix basis multiplication).
||| [i, j] * [k, l] = [i, l] if j == k, otherwise Nothing.
%inline public export
mulPixel : Pixel -> Pixel -> Maybe Pixel
mulPixel p1 p2 =
  let r1 = pixelRow p1
      c1 = pixelCol p1
      r2 = pixelRow p2
      c2 = pixelCol p2
  in if c1 == r2 then Just (mkPixel r1 c2) else Nothing

||| A Voxel is a 3D coordinate cell or Triplet Codon / Baryon state (CoordCell Dim3).
public export
Voxel : Type
Voxel = CoordCell Dim3

||| Smart constructor for 3D Voxel cell.
%inline public export
mkVoxel : Nat -> Nat -> Nat -> Voxel
mkVoxel x y z = MkCoordCell (Node 2 (Node 1 Leaf 0 x Leaf) 1 y (Node 1 Leaf 2 z Leaf))

||| Canonical constructor alias for 3D Voxel cell.
%inline public export
MkVoxel : Nat -> Nat -> Nat -> Voxel
MkVoxel = mkVoxel

||| Projections for 3D Voxel cell.
%inline public export
voxelX : Voxel -> Nat
voxelX (MkCoordCell (Node _ (Node _ _ 0 x _) _ _ _)) = x
voxelX (MkCoordCell (Node _ _ 0 x _)) = x
voxelX (MkCoordCell (Node _ _ _ x _)) = x
voxelX _ = 0

%inline public export
voxelY : Voxel -> Nat
voxelY (MkCoordCell (Node _ _ 1 y _)) = y
voxelY (MkCoordCell (Node _ _ _ y _)) = y
voxelY _ = 0

%inline public export
voxelZ : Voxel -> Nat
voxelZ (MkCoordCell (Node _ _ _ _ (Node _ _ 2 z _))) = z
voxelZ (MkCoordCell (Node _ _ _ _ (Node _ _ _ z _))) = z
voxelZ _ = 0

||| Equality predicate on Voxel.
public export
voxelEq : Voxel -> Voxel -> Bool
voxelEq = coordCellEq

||| A 4D Spacetime coordinate cell token [x, y, z, t] (CoordCell Dim4).
public export
Tesseract : Type
Tesseract = CoordCell Dim4

||| Smart constructor for 4D Tesseract cell.
%inline public export
mkTesseract : Nat -> Nat -> Nat -> Nat -> Tesseract
mkTesseract x y z t = MkCoordCell (Node 3 (Node 1 Leaf 0 x Leaf) 1 y (Node 2 Leaf 2 z (Node 1 Leaf 3 t Leaf)))

||| Canonical constructor alias for 4D Tesseract cell.
%inline public export
MkTesseract : Nat -> Nat -> Nat -> Nat -> Tesseract
MkTesseract = mkTesseract

||| Projections for 4D Tesseract cell.
%inline public export
tesseractX : Tesseract -> Nat
tesseractX (MkCoordCell (Node _ (Node _ _ 0 x _) _ _ _)) = x
tesseractX (MkCoordCell (Node _ _ 0 x _)) = x
tesseractX (MkCoordCell (Node _ _ _ x _)) = x
tesseractX _ = 0

%inline public export
tesseractY : Tesseract -> Nat
tesseractY (MkCoordCell (Node _ _ 1 y _)) = y
tesseractY (MkCoordCell (Node _ _ _ y _)) = y
tesseractY _ = 0

%inline public export
tesseractZ : Tesseract -> Nat
tesseractZ (MkCoordCell (Node _ _ _ _ (Node _ _ 2 z _))) = z
tesseractZ (MkCoordCell (Node _ _ _ _ (Node _ _ _ z _))) = z
tesseractZ _ = 0

%inline public export
tesseractT : Tesseract -> Nat
tesseractT (MkCoordCell (Node _ _ _ _ (Node _ _ _ _ (Node _ _ 3 t _)))) = t
tesseractT (MkCoordCell (Node _ _ _ _ (Node _ _ 2 _ (Node _ _ 3 t _)))) = t
tesseractT (MkCoordCell (Node _ _ _ _ (Node _ _ _ _ (Node _ _ _ t _)))) = t
tesseractT _ = 0

||| Equality predicate on Tesseract.
public export
tesseractEq : Tesseract -> Tesseract -> Bool
tesseractEq = coordCellEq

||| Evaluates 2D symmetric matrix determinant: det([a b; b c]) = a*c - b^2.
%inline public export
detSymmetricMatrix2D : BoxInt -> BoxInt -> BoxInt -> BoxInt
detSymmetricMatrix2D a b c = subBox (a * c) (b * b)

------------------------------------------------------------------------
-- 4. UNIVERSAL COORDCELL SEMIRING ALGEBRA & WILDBERGER INVARIANTS
------------------------------------------------------------------------

||| Additive neutral zero coordinate cell 0 = (0, 0, ..., 0).
public export
zeroCoordCell : CoordCell dim
zeroCoordCell = MkCoordCell Leaf

||| Vector / componentwise addition of two coordinate cells (c1 + c2).
public export
addCoordCell : CoordCell dim -> CoordCell dim -> CoordCell dim
addCoordCell (MkCoordCell cs1) (MkCoordCell cs2) =
  MkCoordCell (mergeMultisetTrees cs1 cs2)

||| Componentwise direct product (Hadamard product) of two coordinate cells (c1 * c2).
public export
mulCoordCell : CoordCell dim -> CoordCell dim -> CoordCell dim
mulCoordCell (MkCoordCell cs1) (MkCoordCell cs2) =
  let pairs = streamMultisetTreeDirect cs1
      resTree = foldStream (\acc, (axis, v1) =>
                  let v2 = lookupTokenTree axis cs2
                      p = v1 * v2
                  in if p == 0 then acc else insertTokenTree axis p acc)
                Leaf
                pairs
  in MkCoordCell resTree

||| Scalar multiplication of a coordinate cell by a natural number (k * c).
public export
scaleCoordCell : Nat -> CoordCell dim -> CoordCell dim
scaleCoordCell Z _ = MkCoordCell Leaf
scaleCoordCell (S Z) c = c
scaleCoordCell k (MkCoordCell cs) =
  let pairs = streamMultisetTreeDirect cs
      resTree = foldStream (\acc, (axis, v) =>
                  let p = k * v
                  in if p == 0 then acc else insertTokenTree axis p acc)
                Leaf
                pairs
  in MkCoordCell resTree

||| Inner / dot product of two coordinate cells (u · v).
public export
dotCoordCell : CoordCell dim -> CoordCell dim -> Nat
dotCoordCell (MkCoordCell cs1) (MkCoordCell cs2) =
  foldStream (\acc, (axis, v1) =>
    let v2 = lookupTokenTree axis cs2
    in acc + (v1 * v2))
  0
  (streamMultisetTreeDirect cs1)

||| Wildberger Quadrance Q(c) = c · c = sum (c_i)^2.
public export
quadranceCoordCell : CoordCell dim -> Nat
quadranceCoordCell c = dotCoordCell c c

||| Semigroup implementation for CoordCell (dim : Nat).
public export
Semigroup (CoordCell dim) where
  (<+>) = addCoordCell

||| Monoid implementation for CoordCell (dim : Nat).
public export
Monoid (CoordCell dim) where
  neutral = zeroCoordCell

------------------------------------------------------------------------
-- 5. SPECIALIZED MONOMORPHIC DERIVED DIMENSION OPERATORS
------------------------------------------------------------------------

-- 1D Unixel Semiring Operators
public export zeroUnixel : Unixel; zeroUnixel = mkUnixel 0
public export oneUnixel : Unixel; oneUnixel = mkUnixel 1
public export addUnixel : Unixel -> Unixel -> Unixel; addUnixel u1 u2 = mkUnixel (unwrapUnixel u1 + unwrapUnixel u2)
public export mulUnixel : Unixel -> Unixel -> Unixel; mulUnixel u1 u2 = mkUnixel (unwrapUnixel u1 * unwrapUnixel u2)
public export scaleUnixel : Nat -> Unixel -> Unixel; scaleUnixel k u = mkUnixel (k * unwrapUnixel u)
public export dotUnixel : Unixel -> Unixel -> Nat; dotUnixel u1 u2 = unwrapUnixel u1 * unwrapUnixel u2
public export quadranceUnixel : Unixel -> Nat; quadranceUnixel u = let x = unwrapUnixel u in x * x
public export minusUnixel : Unixel -> Unixel -> Unixel; minusUnixel u1 u2 = mkUnixel (minus (unwrapUnixel u1) (unwrapUnixel u2))

public export
Num Unixel where
  (+) = addUnixel
  (*) = mulUnixel
  fromInteger n = mkUnixel (integerToNat n)

-- 2D Pixel Semiring Operators
public export zeroPixel : Pixel; zeroPixel = mkPixel 0 0
public export onePixel : Pixel; onePixel = mkPixel 1 1
public export addPixel : Pixel -> Pixel -> Pixel; addPixel p1 p2 = mkPixel (pixelRow p1 + pixelRow p2) (pixelCol p1 + pixelCol p2)
public export mulPixelCell : Pixel -> Pixel -> Pixel; mulPixelCell p1 p2 = mkPixel (pixelRow p1 * pixelRow p2) (pixelCol p1 * pixelCol p2)
public export scalePixel : Nat -> Pixel -> Pixel; scalePixel k p = mkPixel (k * pixelRow p) (k * pixelCol p)
public export dotPixel : Pixel -> Pixel -> Nat; dotPixel p1 p2 = (pixelRow p1 * pixelRow p2) + (pixelCol p1 * pixelCol p2)
public export quadrancePixel : Pixel -> Nat; quadrancePixel p = let r = pixelRow p; c = pixelCol p in (r * r) + (c * c)
public export minusPixel : Pixel -> Pixel -> Pixel; minusPixel p1 p2 = mkPixel (minus (pixelRow p1) (pixelRow p2)) (minus (pixelCol p1) (pixelCol p2))

public export
Num Pixel where
  (+) = addPixel
  (*) = mulPixelCell
  fromInteger n = let k = integerToNat n in mkPixel k k

-- 3D Voxel Semiring Operators
public export zeroVoxel : Voxel; zeroVoxel = mkVoxel 0 0 0
public export oneVoxel : Voxel; oneVoxel = mkVoxel 1 1 1
public export addVoxel : Voxel -> Voxel -> Voxel; addVoxel v1 v2 = mkVoxel (voxelX v1 + voxelX v2) (voxelY v1 + voxelY v2) (voxelZ v1 + voxelZ v2)
public export mulVoxel : Voxel -> Voxel -> Voxel; mulVoxel v1 v2 = mkVoxel (voxelX v1 * voxelX v2) (voxelY v1 * voxelY v2) (voxelZ v1 * voxelZ v2)
public export scaleVoxel : Nat -> Voxel -> Voxel; scaleVoxel k v = mkVoxel (k * voxelX v) (k * voxelY v) (k * voxelZ v)
public export dotVoxel : Voxel -> Voxel -> Nat; dotVoxel v1 v2 = (voxelX v1 * voxelX v2) + (voxelY v1 * voxelY v2) + (voxelZ v1 * voxelZ v2)
public export quadranceVoxel : Voxel -> Nat; quadranceVoxel v = let x = voxelX v; y = voxelY v; z = voxelZ v in (x * x) + (y * y) + (z * z)
public export minusVoxel : Voxel -> Voxel -> Voxel; minusVoxel v1 v2 = mkVoxel (minus (voxelX v1) (voxelX v2)) (minus (voxelY v1) (voxelY v2)) (minus (voxelZ v1) (voxelZ v2))

public export
Num Voxel where
  (+) = addVoxel
  (*) = mulVoxel
  fromInteger n = let k = integerToNat n in mkVoxel k k k

-- 4D Tesseract Semiring Operators
public export zeroTesseract : Tesseract; zeroTesseract = mkTesseract 0 0 0 0
public export oneTesseract : Tesseract; oneTesseract = mkTesseract 1 1 1 1
public export addTesseract : Tesseract -> Tesseract -> Tesseract; addTesseract t1 t2 = mkTesseract (tesseractX t1 + tesseractX t2) (tesseractY t1 + tesseractY t2) (tesseractZ t1 + tesseractZ t2) (tesseractT t1 + tesseractT t2)
public export mulTesseract : Tesseract -> Tesseract -> Tesseract; mulTesseract t1 t2 = mkTesseract (tesseractX t1 * tesseractX t2) (tesseractY t1 * tesseractY t2) (tesseractZ t1 * tesseractZ t2) (tesseractT t1 * tesseractT t2)
public export scaleTesseract : Nat -> Tesseract -> Tesseract; scaleTesseract k t = mkTesseract (k * tesseractX t) (k * tesseractY t) (k * tesseractZ t) (k * tesseractT t)
public export dotTesseract : Tesseract -> Tesseract -> Nat; dotTesseract t1 t2 = (tesseractX t1 * tesseractX t2) + (tesseractY t1 * tesseractY t2) + (tesseractZ t1 * tesseractZ t2) + (tesseractT t1 * tesseractT t2)
public export quadranceTesseract : Tesseract -> Nat; quadranceTesseract t = let x = tesseractX t; y = tesseractY t; z = tesseractZ t; w = tesseractT t in (x * x) + (y * y) + (z * z) + (w * w)
public export minusTesseract : Tesseract -> Tesseract -> Tesseract; minusTesseract t1 t2 = mkTesseract (minus (tesseractX t1) (tesseractX t2)) (minus (tesseractY t1) (tesseractY t2)) (minus (tesseractZ t1) (tesseractZ t2)) (minus (tesseractT t1) (tesseractT t2))

public export
Num Tesseract where
  (+) = addTesseract
  (*) = mulTesseract
  fromInteger n = let k = integerToNat n in mkTesseract k k k k

------------------------------------------------------------------------
-- 6. CONSTRUCTIVE COMMUTATIVE SEMIRING REWRITING LEMMAS
------------------------------------------------------------------------

-- 1D Unixel Semiring Lemmas
public export
0 prfUnixelAddZeroLeft : (i : Nat) -> addUnixel (mkUnixel 0) (mkUnixel i) = mkUnixel i
prfUnixelAddZeroLeft i = Refl

public export
0 prfUnixelAddZeroRight : (i : Nat) -> addUnixel (mkUnixel i) (mkUnixel 0) = mkUnixel i
prfUnixelAddZeroRight i = cong mkUnixel (plusZeroRightNeutral i)

public export
0 prfUnixelAddComm : (i, j : Nat) -> addUnixel (mkUnixel i) (mkUnixel j) = addUnixel (mkUnixel j) (mkUnixel i)
prfUnixelAddComm i j = cong mkUnixel (plusCommutative i j)

public export
0 prfUnixelAddAssoc : (i, j, k : Nat) -> addUnixel (addUnixel (mkUnixel i) (mkUnixel j)) (mkUnixel k) = addUnixel (mkUnixel i) (addUnixel (mkUnixel j) (mkUnixel k))
prfUnixelAddAssoc i j k = cong mkUnixel (sym (plusAssociative i j k))

public export
0 prfUnixelMulZeroLeft : (i : Nat) -> mulUnixel (mkUnixel 0) (mkUnixel i) = mkUnixel 0
prfUnixelMulZeroLeft i = Refl

public export
0 prfUnixelMulOneLeft : (i : Nat) -> mulUnixel (mkUnixel 1) (mkUnixel i) = mkUnixel i
prfUnixelMulOneLeft i = cong mkUnixel (multOneLeftNeutral i)

public export
0 prfUnixelMulComm : (i, j : Nat) -> mulUnixel (mkUnixel i) (mkUnixel j) = mulUnixel (mkUnixel j) (mkUnixel i)
prfUnixelMulComm i j = cong mkUnixel (multCommutative i j)

public export
0 prfUnixelDistributesLeft : (i, j, k : Nat) -> mulUnixel (addUnixel (mkUnixel i) (mkUnixel j)) (mkUnixel k) = addUnixel (mulUnixel (mkUnixel i) (mkUnixel k)) (mulUnixel (mkUnixel j) (mkUnixel k))
prfUnixelDistributesLeft i j k = cong mkUnixel (multDistributesOverPlusLeft i j k)

-- 2D Pixel Semiring Lemmas
public export
0 prfPixelAddZeroLeft : (r, c : Nat) -> addPixel (mkPixel 0 0) (mkPixel r c) = mkPixel r c
prfPixelAddZeroLeft r c = Refl

public export
0 prfPixelAddZeroRight : (r, c : Nat) -> addPixel (mkPixel r c) (mkPixel 0 0) = mkPixel r c
prfPixelAddZeroRight r c =
  rewrite plusZeroRightNeutral r in
  rewrite plusZeroRightNeutral c in
  Refl

public export
0 prfPixelAddComm : (r1, c1, r2, c2 : Nat) -> addPixel (mkPixel r1 c1) (mkPixel r2 c2) = addPixel (mkPixel r2 c2) (mkPixel r1 c1)
prfPixelAddComm r1 c1 r2 c2 =
  rewrite plusCommutative r1 r2 in
  rewrite plusCommutative c1 c2 in
  Refl

public export
0 prfPixelAddAssoc : (r1, c1, r2, c2, r3, c3 : Nat) -> addPixel (addPixel (mkPixel r1 c1) (mkPixel r2 c2)) (mkPixel r3 c3) = addPixel (mkPixel r1 c1) (addPixel (mkPixel r2 c2) (mkPixel r3 c3))
prfPixelAddAssoc r1 c1 r2 c2 r3 c3 =
  rewrite sym (plusAssociative r1 r2 r3) in
  rewrite sym (plusAssociative c1 c2 c3) in
  Refl

public export
0 prfPixelMulZeroLeft : (r, c : Nat) -> mulPixelCell (mkPixel 0 0) (mkPixel r c) = mkPixel 0 0
prfPixelMulZeroLeft r c = Refl

public export
0 prfPixelMulOneLeft : (r, c : Nat) -> mulPixelCell (mkPixel 1 1) (mkPixel r c) = mkPixel r c
prfPixelMulOneLeft r c =
  rewrite multOneLeftNeutral r in
  rewrite multOneLeftNeutral c in
  Refl

public export
0 prfPixelMulComm : (r1, c1, r2, c2 : Nat) -> mulPixelCell (mkPixel r1 c1) (mkPixel r2 c2) = mulPixelCell (mkPixel r2 c2) (mkPixel r1 c1)
prfPixelMulComm r1 c1 r2 c2 =
  rewrite multCommutative r1 r2 in
  rewrite multCommutative c1 c2 in
  Refl

public export
0 prfPixelDistributesLeft : (r1, c1, r2, c2, r3, c3 : Nat) -> mulPixelCell (addPixel (mkPixel r1 c1) (mkPixel r2 c2)) (mkPixel r3 c3) = addPixel (mulPixelCell (mkPixel r1 c1) (mkPixel r3 c3)) (mulPixelCell (mkPixel r2 c2) (mkPixel r3 c3))
prfPixelDistributesLeft r1 c1 r2 c2 r3 c3 =
  rewrite multDistributesOverPlusLeft r1 r2 r3 in
  rewrite multDistributesOverPlusLeft c1 c2 c3 in
  Refl

-- 3D Voxel Semiring Lemmas
public export
0 prfVoxelAddZeroLeft : (x, y, z : Nat) -> addVoxel (mkVoxel 0 0 0) (mkVoxel x y z) = mkVoxel x y z
prfVoxelAddZeroLeft x y z = Refl

public export
0 prfVoxelAddZeroRight : (x, y, z : Nat) -> addVoxel (mkVoxel x y z) (mkVoxel 0 0 0) = mkVoxel x y z
prfVoxelAddZeroRight x y z =
  rewrite plusZeroRightNeutral x in
  rewrite plusZeroRightNeutral y in
  rewrite plusZeroRightNeutral z in
  Refl

public export
0 prfVoxelAddComm : (x1, y1, z1, x2, y2, z2 : Nat) -> addVoxel (mkVoxel x1 y1 z1) (mkVoxel x2 y2 z2) = addVoxel (mkVoxel x2 y2 z2) (mkVoxel x1 y1 z1)
prfVoxelAddComm x1 y1 z1 x2 y2 z2 =
  rewrite plusCommutative x1 x2 in
  rewrite plusCommutative y1 y2 in
  rewrite plusCommutative z1 z2 in
  Refl

public export
0 prfVoxelAddAssoc : (x1, y1, z1, x2, y2, z2, x3, y3, z3 : Nat) -> addVoxel (addVoxel (mkVoxel x1 y1 z1) (mkVoxel x2 y2 z2)) (mkVoxel x3 y3 z3) = addVoxel (mkVoxel x1 y1 z1) (addVoxel (mkVoxel x2 y2 z2) (mkVoxel x3 y3 z3))
prfVoxelAddAssoc x1 y1 z1 x2 y2 z2 x3 y3 z3 =
  rewrite sym (plusAssociative x1 x2 x3) in
  rewrite sym (plusAssociative y1 y2 y3) in
  rewrite sym (plusAssociative z1 z2 z3) in
  Refl

public export
0 prfVoxelMulZeroLeft : (x, y, z : Nat) -> mulVoxel (mkVoxel 0 0 0) (mkVoxel x y z) = mkVoxel 0 0 0
prfVoxelMulZeroLeft x y z = Refl

public export
0 prfVoxelMulOneLeft : (x, y, z : Nat) -> mulVoxel (mkVoxel 1 1 1) (mkVoxel x y z) = mkVoxel x y z
prfVoxelMulOneLeft x y z =
  rewrite multOneLeftNeutral x in
  rewrite multOneLeftNeutral y in
  rewrite multOneLeftNeutral z in
  Refl

public export
0 prfVoxelMulComm : (x1, y1, z1, x2, y2, z2 : Nat) -> mulVoxel (mkVoxel x1 y1 z1) (mkVoxel x2 y2 z2) = mulVoxel (mkVoxel x2 y2 z2) (mkVoxel x1 y1 z1)
prfVoxelMulComm x1 y1 z1 x2 y2 z2 =
  rewrite multCommutative x1 x2 in
  rewrite multCommutative y1 y2 in
  rewrite multCommutative z1 z2 in
  Refl

public export
0 prfVoxelDistributesLeft : (x1, y1, z1, x2, y2, z2, x3, y3, z3 : Nat) -> mulVoxel (addVoxel (mkVoxel x1 y1 z1) (mkVoxel x2 y2 z2)) (mkVoxel x3 y3 z3) = addVoxel (mulVoxel (mkVoxel x1 y1 z1) (mkVoxel x3 y3 z3)) (mulVoxel (mkVoxel x2 y2 z2) (mkVoxel x3 y3 z3))
prfVoxelDistributesLeft x1 y1 z1 x2 y2 z2 x3 y3 z3 =
  rewrite multDistributesOverPlusLeft x1 x2 x3 in
  rewrite multDistributesOverPlusLeft y1 y2 y3 in
  rewrite multDistributesOverPlusLeft z1 z2 z3 in
  Refl

-- 4D Tesseract Semiring Lemmas
public export
0 prfTesseractAddZeroLeft : (x, y, z, t : Nat) -> addTesseract (mkTesseract 0 0 0 0) (mkTesseract x y z t) = mkTesseract x y z t
prfTesseractAddZeroLeft x y z t = Refl

public export
0 prfTesseractAddZeroRight : (x, y, z, t : Nat) -> addTesseract (mkTesseract x y z t) (mkTesseract 0 0 0 0) = mkTesseract x y z t
prfTesseractAddZeroRight x y z t =
  rewrite plusZeroRightNeutral x in
  rewrite plusZeroRightNeutral y in
  rewrite plusZeroRightNeutral z in
  rewrite plusZeroRightNeutral t in
  Refl

public export
0 prfTesseractAddComm : (x1, y1, z1, t1, x2, y2, z2, t2 : Nat) -> addTesseract (mkTesseract x1 y1 z1 t1) (mkTesseract x2 y2 z2 t2) = addTesseract (mkTesseract x2 y2 z2 t2) (mkTesseract x1 y1 z1 t1)
prfTesseractAddComm x1 y1 z1 t1 x2 y2 z2 t2 =
  rewrite plusCommutative x1 x2 in
  rewrite plusCommutative y1 y2 in
  rewrite plusCommutative z1 z2 in
  rewrite plusCommutative t1 t2 in
  Refl

------------------------------------------------------------------------
-- 7. SIGNED BOXINT <-> PIXEL DIFFERENCE PAIR ISOMORPHISM
------------------------------------------------------------------------

||| Encodes a signed difference pair (pos, neg) as a 2D coordinate Pixel [pos, neg].
public export
boxIntToPixelPair : Nat -> Nat -> Pixel
boxIntToPixelPair p n = mkPixel p n

||| Evaluates the signed BoxInt integer value of a difference pair Pixel [pos, neg]: (pos - neg).
public export
pixelToSignedBoxInt : Pixel -> BoxInt
pixelToSignedBoxInt p = intToBoxInt (cast (pixelRow p) - cast (pixelCol p))

------------------------------------------------------------------------
-- 8. CANONICAL IDENTITY LENSES & ROUND-TRIP WITNESSES
------------------------------------------------------------------------

-- 1D: Unixel <-> CoordCell Dim1
public export
unixelToCell : Unixel -> CoordCell Dim1
unixelToCell = id

public export
cellToUnixel : CoordCell Dim1 -> Unixel
cellToUnixel = id

public export
prfUnixelRoundTrip : (u : Unixel) -> cellToUnixel (unixelToCell u) = u
prfUnixelRoundTrip _ = Refl

public export
prfCellToUnixelRoundTrip : (c : CoordCell Dim1) -> unixelToCell (cellToUnixel c) = c
prfCellToUnixelRoundTrip _ = Refl

-- 2D: Pixel <-> CoordCell Dim2
public export
pixelToCell : Pixel -> CoordCell Dim2
pixelToCell = id

public export
cellToPixel : CoordCell Dim2 -> Pixel
cellToPixel = id

public export
prfPixelRoundTrip : (p : Pixel) -> cellToPixel (pixelToCell p) = p
prfPixelRoundTrip _ = Refl

public export
prfCellToPixelRoundTrip : (c : CoordCell Dim2) -> pixelToCell (cellToPixel c) = c
prfCellToPixelRoundTrip _ = Refl

-- 3D: Voxel <-> CoordCell Dim3
public export
voxelToCell : Voxel -> CoordCell Dim3
voxelToCell = id

public export
cellToVoxel : CoordCell Dim3 -> Voxel
cellToVoxel = id

public export
prfVoxelRoundTrip : (v : Voxel) -> cellToVoxel (voxelToCell v) = v
prfVoxelRoundTrip _ = Refl

public export
prfCellToVoxelRoundTrip : (c : CoordCell Dim3) -> voxelToCell (cellToVoxel c) = c
prfCellToVoxelRoundTrip _ = Refl

-- 4D: Tesseract <-> CoordCell Dim4
public export
tesseractToCell : Tesseract -> CoordCell Dim4
tesseractToCell = id

public export
cellToTesseract : CoordCell Dim4 -> Tesseract
cellToTesseract = id

public export
prfTesseractRoundTrip : (t : Tesseract) -> cellToTesseract (tesseractToCell t) = t
prfTesseractRoundTrip _ = Refl

public export
prfCellToTesseractRoundTrip : (c : CoordCell Dim4) -> tesseractToCell (cellToTesseract c) = c
prfCellToTesseractRoundTrip _ = Refl
