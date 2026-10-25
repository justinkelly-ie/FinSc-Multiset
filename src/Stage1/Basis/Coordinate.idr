module Stage1.Basis.Coordinate

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
