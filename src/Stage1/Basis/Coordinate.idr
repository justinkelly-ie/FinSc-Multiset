module Stage1.Basis.Coordinate

import Data.Vect
import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.StructuralFuel
import Stage1.Order.Preorder

%default total

------------------------------------------------------------------------
-- 1. WILDBERGER'S BASIS COORDINATE CELLS (UNIXELS, PIXELS, VOXELS)
------------------------------------------------------------------------

||| A Unixel is a 1-list from Nat [n], representing a 1D basis coordinate cell.
public export
record Unixel where
  constructor MkUnixel
  index : Nat

public export
unixelEq : Unixel -> Unixel -> Bool
unixelEq (MkUnixel i1) (MkUnixel i2) = natEq i1 i2

public export
Eq Unixel where
  (MkUnixel i1) == (MkUnixel i2) = unixelEq (MkUnixel i1) (MkUnixel i2)

public export
Ord Unixel where
  compare (MkUnixel i1) (MkUnixel i2) = compare i1 i2

public export
Show Unixel where
  show (MkUnixel i) = "[" ++ show i ++ "]"

||| Unwraps the natural coordinate of a Unixel.
public export
unwrapUnixel : Unixel -> Nat
unwrapUnixel (MkUnixel i) = i

||| A Pixel is a 2-list from Nat [i, j], representing a 2D coordinate cell or signed difference pair [pos, neg].
public export
record Pixel where
  constructor MkPixel
  row : Nat
  col : Nat

||| Canonical unambiguous alias for discrete 2D grid matrix cells.
public export
GridPixel : Type
GridPixel = Pixel

||| Alternative alias for cell coordinate.
public export
CellPixel : Type
CellPixel = Pixel

public export
pixelEq : Pixel -> Pixel -> Bool
pixelEq (MkPixel r1 c1) (MkPixel r2 c2) = if natEq r1 r2 then natEq c1 c2 else False

public export
Eq Pixel where
  (MkPixel r1 c1) == (MkPixel r2 c2) = pixelEq (MkPixel r1 c1) (MkPixel r2 c2)

public export
Ord Pixel where
  compare (MkPixel r1 c1) (MkPixel r2 c2) =
    case compare r1 r2 of
      EQ => compare c1 c2
      res => res

public export
Show Pixel where
  show (MkPixel r c) = "[" ++ show r ++ ", " ++ show c ++ "]"

||| Multiplies a Pixel by a Pixel (discrete matrix basis multiplication).
||| [i, j] * [k, l] = [i, l] if j == k, otherwise Nothing.
public export
mulPixel : Pixel -> Pixel -> Maybe Pixel
mulPixel (MkPixel i j) (MkPixel k l) =
  if j == k then Just (MkPixel i l) else Nothing

||| A Voxel is a 3-list from Nat [x, y, z], representing a 3D coordinate cell or Triplet Codon / Baryon state.
public export
record Voxel where
  constructor MkVoxel
  axisX : Nat
  axisY : Nat
  axisZ : Nat

public export
voxelEq : Voxel -> Voxel -> Bool
voxelEq (MkVoxel x1 y1 z1) (MkVoxel x2 y2 z2) = natEq x1 x2 && natEq y1 y2 && natEq z1 z2

public export
Eq Voxel where
  (MkVoxel x1 y1 z1) == (MkVoxel x2 y2 z2) = voxelEq (MkVoxel x1 y1 z1) (MkVoxel x2 y2 z2)

public export
Ord Voxel where
  compare (MkVoxel x1 y1 z1) (MkVoxel x2 y2 z2) =
    case compare x1 x2 of
      EQ => case compare y1 y2 of
        EQ => compare z1 z2
        resY => resY
      resX => resX

public export
Show Voxel where
  show (MkVoxel x y z) = "[" ++ show x ++ ", " ++ show y ++ ", " ++ show z ++ "]"

||| Evaluates 2D symmetric matrix determinant: det([a b; b c]) = a*c - b^2.
%inline public export
detSymmetricMatrix2D : BoxInt -> BoxInt -> BoxInt -> BoxInt
detSymmetricMatrix2D a b c = subBox (a * c) (b * b)

------------------------------------------------------------------------
-- 2. SIGNED BOXINT <-> PIXEL DIFFERENCE PAIR ISOMORPHISM
------------------------------------------------------------------------

||| Encodes a signed difference pair (pos, neg) as a 2D coordinate Pixel [pos, neg].
public export
boxIntToPixelPair : Nat -> Nat -> Pixel
boxIntToPixelPair p n = MkPixel p n

||| Evaluates the signed BoxInt integer value of a difference pair Pixel [pos, neg]: (pos - neg).
public export
pixelToSignedBoxInt : Pixel -> BoxInt
pixelToSignedBoxInt (MkPixel p n) = intToBoxInt (cast p - cast n)

------------------------------------------------------------------------
-- 3. 4D SPACETIME BASIS COORDINATE CELLS (TESSERACT)
------------------------------------------------------------------------

||| A 4D Spacetime coordinate cell token [x, y, z, t].
public export
record Tesseract where
  constructor MkTesseract
  x : Nat
  y : Nat
  z : Nat
  t : Nat

public export
tesseractEq : Tesseract -> Tesseract -> Bool
tesseractEq (MkTesseract x1 y1 z1 t1) (MkTesseract x2 y2 z2 t2) =
  natEq x1 x2 && natEq y1 y2 && natEq z1 z2 && natEq t1 t2

public export
Eq Tesseract where
  (MkTesseract x1 y1 z1 t1) == (MkTesseract x2 y2 z2 t2) =
    tesseractEq (MkTesseract x1 y1 z1 t1) (MkTesseract x2 y2 z2 t2)

public export
Ord Tesseract where
  compare (MkTesseract x1 y1 z1 t1) (MkTesseract x2 y2 z2 t2) =
    case compare x1 x2 of
      EQ => case compare y1 y2 of
        EQ => case compare z1 z2 of
          EQ => compare t1 t2
          resZ => resZ
        resY => resY
      resX => resX

public export
Show Tesseract where
  show (MkTesseract x y z t) = "[" ++ show x ++ ", " ++ show y ++ ", " ++ show z ++ ", " ++ show t ++ "]"

------------------------------------------------------------------------
-- 4. DEPENDENT DIMENSION-INDEXED COORDINATE CELLS (COORDCELL)
------------------------------------------------------------------------

||| Canonical 1-dimensional discrete dimension index.
public export
Dim1 : BoxNat
Dim1 = MkBoxNat 1

||| Canonical 2-dimensional discrete dimension index.
public export
Dim2 : BoxNat
Dim2 = MkBoxNat 2

||| Canonical 3-dimensional discrete dimension index.
public export
Dim3 : BoxNat
Dim3 = MkBoxNat 3

||| Canonical 4-dimensional discrete dimension index.
public export
Dim4 : BoxNat
Dim4 = MkBoxNat 4

||| Canonical 10-dimensional discrete dimension index.
public export
Dim10 : BoxNat
Dim10 = MkBoxNat 10

||| Arbitrary D-dimensional coordinate basis cell, indexed by BoxNat dimension.
||| Guarantees definitional reduction: for any concrete Dim, `Vect (unwrapBoxNat Dim) Nat`
||| normalizes directly to `Vect d Nat`.
public export
record CoordCell (dim : BoxNat) where
  constructor MkCoordCell
  coords : Vect (unwrapBoxNat dim) Nat

public export
coordCellEq : CoordCell dim -> CoordCell dim -> Bool
coordCellEq (MkCoordCell cs1) (MkCoordCell cs2) = cs1 == cs2

public export
Eq (CoordCell dim) where
  (MkCoordCell cs1) == (MkCoordCell cs2) = cs1 == cs2

public export
Ord (CoordCell dim) where
  compare (MkCoordCell cs1) (MkCoordCell cs2) = compare cs1 cs2

public export
Show (CoordCell dim) where
  show (MkCoordCell cs) = show cs

------------------------------------------------------------------------
-- 5. BIDIRECTIONAL CANONICAL LENSES & ROUND-TRIP WITNESSES
------------------------------------------------------------------------

-- 1D: Unixel <-> CoordCell Dim1
public export
unixelToCell : Unixel -> CoordCell Dim1
unixelToCell (MkUnixel i) = MkCoordCell [i]

public export
cellToUnixel : CoordCell Dim1 -> Unixel
cellToUnixel (MkCoordCell [i]) = MkUnixel i

public export
prfUnixelRoundTrip : (u : Unixel) -> cellToUnixel (unixelToCell u) = u
prfUnixelRoundTrip (MkUnixel i) = Refl

public export
prfCellToUnixelRoundTrip : (c : CoordCell Dim1) -> unixelToCell (cellToUnixel c) = c
prfCellToUnixelRoundTrip (MkCoordCell [i]) = Refl

-- 2D: Pixel <-> CoordCell Dim2
public export
pixelToCell : Pixel -> CoordCell Dim2
pixelToCell (MkPixel r c) = MkCoordCell [r, c]

public export
cellToPixel : CoordCell Dim2 -> Pixel
cellToPixel (MkCoordCell [r, c]) = MkPixel r c

public export
prfPixelRoundTrip : (p : Pixel) -> cellToPixel (pixelToCell p) = p
prfPixelRoundTrip (MkPixel r c) = Refl

public export
prfCellToPixelRoundTrip : (c : CoordCell Dim2) -> pixelToCell (cellToPixel c) = c
prfCellToPixelRoundTrip (MkCoordCell [r, c]) = Refl

-- 3D: Voxel <-> CoordCell Dim3
public export
voxelToCell : Voxel -> CoordCell Dim3
voxelToCell (MkVoxel x y z) = MkCoordCell [x, y, z]

public export
cellToVoxel : CoordCell Dim3 -> Voxel
cellToVoxel (MkCoordCell [x, y, z]) = MkVoxel x y z

public export
prfVoxelRoundTrip : (v : Voxel) -> cellToVoxel (voxelToCell v) = v
prfVoxelRoundTrip (MkVoxel x y z) = Refl

public export
prfCellToVoxelRoundTrip : (c : CoordCell Dim3) -> voxelToCell (cellToVoxel c) = c
prfCellToVoxelRoundTrip (MkCoordCell [x, y, z]) = Refl

-- 4D: Tesseract <-> CoordCell Dim4
public export
tesseractToCell : Tesseract -> CoordCell Dim4
tesseractToCell (MkTesseract x y z t) = MkCoordCell [x, y, z, t]

public export
cellToTesseract : CoordCell Dim4 -> Tesseract
cellToTesseract (MkCoordCell [x, y, z, t]) = MkTesseract x y z t

public export
prfTesseractRoundTrip : (t : Tesseract) -> cellToTesseract (tesseractToCell t) = t
prfTesseractRoundTrip (MkTesseract x y z t) = Refl

public export
prfCellToTesseractRoundTrip : (c : CoordCell Dim4) -> tesseractToCell (cellToTesseract c) = c
prfCellToTesseractRoundTrip (MkCoordCell [x, y, z, t]) = Refl
