module Stage1.Basis.Coordinate

import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.StructuralFuel
import public Stage0.OnSeq.FusedStream
import public Stage1.MultisetTree
import Stage1.Order.Preorder

%default total

------------------------------------------------------------------------
-- 1. CANONICAL DISCRETE DIMENSION CONSTANTS (BoxNat)
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

------------------------------------------------------------------------
-- 2. UNIVERSAL DEPENDENT COORDINATE BASIS CELL (COORDCELL)
------------------------------------------------------------------------

||| Arbitrary D-dimensional coordinate basis cell, indexed by BoxNat dimension.
||| Backed by a balanced AVL MultisetTree Nat mapping dimension axes to coordinates.
||| Completely eliminates Data.Vect heap allocations and vector consing conflicts.
public export
record CoordCell (dim : BoxNat) where
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
-- 4. SIGNED BOXINT <-> PIXEL DIFFERENCE PAIR ISOMORPHISM
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
-- 5. CANONICAL IDENTITY LENSES & ROUND-TRIP WITNESSES
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
