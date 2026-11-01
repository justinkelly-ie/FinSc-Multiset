module Stage1.Basis.CoordCell

import Data.Nat
import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.Token
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
||| Directly formed by an inductive sequence of atomic coordinate tokens (Token Nat).
||| Dimension is definitionally the token cardinality of the cell (|C| = dim).
||| Completely eliminates intermediate AVL tree balancing, list flattening, and heap consing.
public export
data CoordCell : Nat -> Type where
  ZeroCell : CoordCell 0
  ConsCell : Token Nat -> CoordCell dim -> CoordCell (S dim)

public export
coordCellEq : CoordCell dim -> CoordCell dim -> Bool
coordCellEq ZeroCell ZeroCell = True
coordCellEq (ConsCell (MkToken x) xs) (ConsCell (MkToken y) ys) =
  x == y && coordCellEq xs ys

public export
Eq (CoordCell dim) where
  (==) = coordCellEq

public export
Ord (CoordCell dim) where
  compare ZeroCell ZeroCell = EQ
  compare (ConsCell (MkToken x) xs) (ConsCell (MkToken y) ys) =
    case compare x y of
      EQ => compare xs ys
      other => other

public export
cellToList : CoordCell dim -> List Nat
cellToList ZeroCell = []
cellToList (ConsCell (MkToken x) rest) = x :: cellToList rest

public export
Show (CoordCell dim) where
  show c = show (cellToList c)

||| Converts a D-dimensional coordinate cell into a zero-allocation deforested FusedStream of (axis, coord).
public export
streamCoordCell : CoordCell dim -> FusedStream (Nat, Nat)
streamCoordCell c =
  let pairs = let go : Nat -> List Nat -> List (Nat, Nat)
                  go _ [] = []
                  go n (x :: xs) = (n, x) :: go (S n) xs
              in go 0 (cellToList c)
  in stream pairs

||| Lookups the coordinate component along any specified dimension axis (0 .. dim-1).
public export
coordAxis : Nat -> CoordCell dim -> Nat
coordAxis _ ZeroCell = 0
coordAxis Z (ConsCell (MkToken x) _) = x
coordAxis (S k) (ConsCell _ rest) = coordAxis k rest

||| Canonical alias for coordAxis.
public export
coordCellAxis : Nat -> CoordCell dim -> Nat
coordCellAxis = coordAxis

||| Sets the coordinate component along the specified axis.
public export
coordCellSetAxis : Nat -> Nat -> CoordCell dim -> CoordCell dim
coordCellSetAxis _ _ ZeroCell = ZeroCell
coordCellSetAxis Z v (ConsCell _ rest) = ConsCell (MkToken v) rest
coordCellSetAxis (S k) v (ConsCell tok rest) = ConsCell tok (coordCellSetAxis k v rest)

------------------------------------------------------------------------
-- 3. UNIFIED CONSTRUCTORS, TYPE SYNONYMS & DIMENSION PROJECTIONS
------------------------------------------------------------------------

||| Builds a CoordCell from a list of natural numbers up to dimension dim.
public export
mkCoordCellFromList : (dim : Nat) -> List Nat -> CoordCell dim
mkCoordCellFromList Z _ = ZeroCell
mkCoordCellFromList (S k) [] = ConsCell (MkToken 0) (mkCoordCellFromList k [])
mkCoordCellFromList (S k) (x :: xs) = ConsCell (MkToken x) (mkCoordCellFromList k xs)

||| Curried dimension-indexed constructors.
public export
mkCell1 : Nat -> CoordCell Dim1
mkCell1 i = ConsCell (MkToken i) ZeroCell

public export
mkCell2 : Nat -> Nat -> CoordCell Dim2
mkCell2 r c = ConsCell (MkToken r) (ConsCell (MkToken c) ZeroCell)

public export
mkCell3 : Nat -> Nat -> Nat -> CoordCell Dim3
mkCell3 x y z = ConsCell (MkToken x) (ConsCell (MkToken y) (ConsCell (MkToken z) ZeroCell))

public export
mkCell4 : Nat -> Nat -> Nat -> Nat -> CoordCell Dim4
mkCell4 x y z t = ConsCell (MkToken x) (ConsCell (MkToken y) (ConsCell (MkToken z) (ConsCell (MkToken t) ZeroCell)))

-- 1D Unixel
public export
Unixel : Type
Unixel = CoordCell Dim1

%inline public export
mkUnixel : Nat -> Unixel
mkUnixel = mkCell1

%inline public export
MkUnixel : Nat -> Unixel
MkUnixel = mkUnixel

%inline public export
mkUnixelToken : Token Nat -> Unixel
mkUnixelToken tok = ConsCell tok ZeroCell

%inline public export
unixelToken : Unixel -> Token Nat
unixelToken (ConsCell tok ZeroCell) = tok

%inline public export
unwrapUnixel : Unixel -> Nat
unwrapUnixel (ConsCell (MkToken x) ZeroCell) = x

public export
unixelEq : Unixel -> Unixel -> Bool
unixelEq = coordCellEq

-- 2D Pixel
public export
Pixel : Type
Pixel = CoordCell Dim2

public export
GridPixel : Type
GridPixel = Pixel

public export
CellPixel : Type
CellPixel = Pixel

%inline public export
mkPixel : Nat -> Nat -> Pixel
mkPixel = mkCell2

%inline public export
MkPixel : Nat -> Nat -> Pixel
MkPixel = mkPixel

%inline public export
mkPixelTokens : Token Nat -> Token Nat -> Pixel
mkPixelTokens tokR tokC = ConsCell tokR (ConsCell tokC ZeroCell)

%inline public export
pixelRowToken : Pixel -> Token Nat
pixelRowToken (ConsCell tokR _) = tokR

%inline public export
pixelColToken : Pixel -> Token Nat
pixelColToken (ConsCell _ (ConsCell tokC _)) = tokC

%inline public export
pixelTokens : Pixel -> (Token Nat, Token Nat)
pixelTokens p = (pixelRowToken p, pixelColToken p)

%inline public export
pixelRow : Pixel -> Nat
pixelRow (ConsCell (MkToken r) (ConsCell _ ZeroCell)) = r

%inline public export
pixelCol : Pixel -> Nat
pixelCol (ConsCell _ (ConsCell (MkToken c) ZeroCell)) = c

public export
pixelEq : Pixel -> Pixel -> Bool
pixelEq = coordCellEq

------------------------------------------------------------------------
-- POLARIZED MATRIX TOKENS & STOICHIOMETRIC MULTI-TOKEN ANNIHILATION
------------------------------------------------------------------------

||| Polarity of an internal matrix basis token (Rule 03 §6).
public export
data Polarity = In | Out

public export
Eq Polarity where
  In == In = True
  Out == Out = True
  _ == _ = False

public export
Show Polarity where
  show In = "In"
  show Out = "Out"

||| A polarized matrix basis token carrying an index and orientation.
public export
record DirPixelToken where
  constructor MkDirPixelToken
  index    : Nat
  polarity : Polarity

public export
Eq DirPixelToken where
  (MkDirPixelToken i1 p1) == (MkDirPixelToken i2 p2) = i1 == i2 && p1 == p2

public export
Show DirPixelToken where
  show (MkDirPixelToken i p) = show p ++ "(" ++ show i ++ ")"

||| Decomposes a discrete Pixel into its pair of polarized basis tokens: {Out(row), In(col)}.
public export
pixelToDirTokens : Pixel -> (Token DirPixelToken, Token DirPixelToken)
pixelToDirTokens (ConsCell (MkToken r) (ConsCell (MkToken c) ZeroCell)) =
  (MkToken (MkDirPixelToken r Out), MkToken (MkDirPixelToken c In))

||| Reconstructs a discrete Pixel from a pair of polarized basis tokens.
public export
dirTokensToPixel : Token DirPixelToken -> Token DirPixelToken -> Maybe Pixel
dirTokensToPixel (MkToken (MkDirPixelToken r Out)) (MkToken (MkDirPixelToken c In)) =
  Just (mkPixel r c)
dirTokensToPixel _ _ = Nothing

||| Multiplies two Pixels via stoichiometric annihilation of internal conjugate tokens:
||| {Out(i), In(j)} + {Out(j), In(k)} -> {Out(i), In(k)} iff target == source.
public export
mulPixelMultiToken : Pixel -> Pixel -> Maybe Pixel
mulPixelMultiToken p1 p2 =
  let (out1, in1) = pixelToDirTokens p1
      (out2, in2) = pixelToDirTokens p2
  in if (fromToken in1).index == (fromToken out2).index
       then dirTokensToPixel out1 in2
       else Nothing

||| Canonical discrete matrix basis multiplication:
||| [i, j] * [k, l] = [i, l] if j == k, otherwise Nothing.
%inline public export
mulPixel : Pixel -> Pixel -> Maybe Pixel
mulPixel = mulPixelMultiToken

||| Multiplies a Pixel on the left by a Unixel: [i, j] * [j] = [i] (matrix-vector contraction).
%inline public export
mulPixelUnixel : Pixel -> Unixel -> Maybe Unixel
mulPixelUnixel p u =
  let l = pixelRow p
      m = pixelCol p
      k = unwrapUnixel u
  in if m == k then Just (mkUnixel l) else Nothing

||| Multiplies a Unixel on the left by a Pixel: [i] * [i, j] = [j] (covector-matrix contraction).
%inline public export
mulUnixelPixel : Unixel -> Pixel -> Maybe Unixel
mulUnixelPixel u p =
  let k = unwrapUnixel u
      l = pixelRow p
      m = pixelCol p
  in if k == l then Just (mkUnixel m) else Nothing

-- 3D Voxel
public export
Voxel : Type
Voxel = CoordCell Dim3

%inline public export
mkVoxel : Nat -> Nat -> Nat -> Voxel
mkVoxel = mkCell3

%inline public export
MkVoxel : Nat -> Nat -> Nat -> Voxel
MkVoxel = mkVoxel

%inline public export
voxelX : Voxel -> Nat
voxelX (ConsCell (MkToken x) _) = x

%inline public export
voxelY : Voxel -> Nat
voxelY (ConsCell _ (ConsCell (MkToken y) _)) = y

%inline public export
voxelZ : Voxel -> Nat
voxelZ (ConsCell _ (ConsCell _ (ConsCell (MkToken z) _))) = z

public export
voxelEq : Voxel -> Voxel -> Bool
voxelEq = coordCellEq

-- 4D Tesseract
public export
Tesseract : Type
Tesseract = CoordCell Dim4

public export
Cell : Type
Cell = Tesseract

%inline public export
mkTesseract : Nat -> Nat -> Nat -> Nat -> Tesseract
mkTesseract = mkCell4

%inline public export
MkTesseract : Nat -> Nat -> Nat -> Nat -> Tesseract
MkTesseract = mkTesseract

%inline public export
tesseractX : Tesseract -> Nat
tesseractX (ConsCell (MkToken x) _) = x

%inline public export
tesseractY : Tesseract -> Nat
tesseractY (ConsCell _ (ConsCell (MkToken y) _)) = y

%inline public export
tesseractZ : Tesseract -> Nat
tesseractZ (ConsCell _ (ConsCell _ (ConsCell (MkToken z) _))) = z

%inline public export
tesseractT : Tesseract -> Nat
tesseractT (ConsCell _ (ConsCell _ (ConsCell _ (ConsCell (MkToken t) _)))) = t

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
zeroCoordCell : {dim : Nat} -> CoordCell dim
zeroCoordCell {dim = Z} = ZeroCell
zeroCoordCell {dim = S k} = ConsCell (MkToken 0) zeroCoordCell

||| Vector / componentwise addition of two coordinate cells (c1 + c2).
public export
addCoordCell : CoordCell dim -> CoordCell dim -> CoordCell dim
addCoordCell ZeroCell ZeroCell = ZeroCell
addCoordCell (ConsCell (MkToken x) xs) (ConsCell (MkToken y) ys) =
  ConsCell (MkToken (x + y)) (addCoordCell xs ys)

||| Componentwise direct product (Hadamard product) of two coordinate cells (c1 * c2).
public export
mulCoordCell : CoordCell dim -> CoordCell dim -> CoordCell dim
mulCoordCell ZeroCell ZeroCell = ZeroCell
mulCoordCell (ConsCell (MkToken x) xs) (ConsCell (MkToken y) ys) =
  ConsCell (MkToken (x * y)) (mulCoordCell xs ys)

||| Scalar multiplication of a coordinate cell by a natural number (k * c).
public export
scaleCoordCell : Nat -> CoordCell dim -> CoordCell dim
scaleCoordCell _ ZeroCell = ZeroCell
scaleCoordCell k (ConsCell (MkToken x) xs) =
  ConsCell (MkToken (k * x)) (scaleCoordCell k xs)

||| Inner / dot product of two coordinate cells (u · v).
public export
dotCoordCell : CoordCell dim -> CoordCell dim -> Nat
dotCoordCell ZeroCell ZeroCell = 0
dotCoordCell (ConsCell (MkToken x) xs) (ConsCell (MkToken y) ys) =
  (x * y) + dotCoordCell xs ys

||| Wildberger Quadrance Q(c) = c · c = sum (c_i)^2.
public export
quadranceCoordCell : CoordCell dim -> Nat
quadranceCoordCell c = dotCoordCell c c

||| Componentwise subtraction / bounded natural difference of two coordinate cells.
public export
minusCoordCell : CoordCell dim -> CoordCell dim -> CoordCell dim
minusCoordCell ZeroCell ZeroCell = ZeroCell
minusCoordCell (ConsCell (MkToken x) xs) (ConsCell (MkToken y) ys) =
  ConsCell (MkToken (minus x y)) (minusCoordCell xs ys)

||| Populates a coordinate cell of dimension dim with a constant coordinate k across all axes.
public export
constCoordCell : (dim : Nat) -> Nat -> CoordCell dim
constCoordCell Z _ = ZeroCell
constCoordCell (S k) n = ConsCell (MkToken n) (constCoordCell k n)

||| Canonical 1-vector of ones: 1 = (1, 1, ..., 1).
public export
oneCoordCell : (dim : Nat) -> CoordCell dim
oneCoordCell dim = constCoordCell dim 1

||| Semigroup implementation for CoordCell (dim : Nat).
public export
Semigroup (CoordCell dim) where
  (<+>) = addCoordCell

||| Monoid implementation for CoordCell (dim : Nat).
public export
{dim : Nat} -> Monoid (CoordCell dim) where
  neutral = zeroCoordCell

||| Universal Num instance for CoordCell of any dimension.
public export
{dim : Nat} -> Num (CoordCell dim) where
  (+) = addCoordCell
  (*) = mulCoordCell
  fromInteger n = constCoordCell dim (integerToNat n)

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

-- 2D Pixel Semiring Operators
public export zeroPixel : Pixel; zeroPixel = mkPixel 0 0
public export onePixel : Pixel; onePixel = mkPixel 1 1
public export addPixel : Pixel -> Pixel -> Pixel; addPixel p1 p2 = mkPixel (pixelRow p1 + pixelRow p2) (pixelCol p1 + pixelCol p2)
public export mulPixelCell : Pixel -> Pixel -> Pixel; mulPixelCell p1 p2 = mkPixel (pixelRow p1 * pixelRow p2) (pixelCol p1 * pixelCol p2)
public export scalePixel : Nat -> Pixel -> Pixel; scalePixel k p = mkPixel (k * pixelRow p) (k * pixelCol p)
public export dotPixel : Pixel -> Pixel -> Nat; dotPixel p1 p2 = (pixelRow p1 * pixelRow p2) + (pixelCol p1 * pixelCol p2)
public export quadrancePixel : Pixel -> Nat; quadrancePixel p = let r = pixelRow p; c = pixelCol p in (r * r) + (c * c)
public export minusPixel : Pixel -> Pixel -> Pixel; minusPixel p1 p2 = mkPixel (minus (pixelRow p1) (pixelRow p2)) (minus (pixelCol p1) (pixelCol p2))

-- 3D Voxel Semiring Operators
public export zeroVoxel : Voxel; zeroVoxel = mkVoxel 0 0 0
public export oneVoxel : Voxel; oneVoxel = mkVoxel 1 1 1
public export addVoxel : Voxel -> Voxel -> Voxel; addVoxel v1 v2 = mkVoxel (voxelX v1 + voxelX v2) (voxelY v1 + voxelY v2) (voxelZ v1 + voxelZ v2)
public export mulVoxel : Voxel -> Voxel -> Voxel; mulVoxel v1 v2 = mkVoxel (voxelX v1 * voxelX v2) (voxelY v1 * voxelY v2) (voxelZ v1 * voxelZ v2)
public export scaleVoxel : Nat -> Voxel -> Voxel; scaleVoxel k v = mkVoxel (k * voxelX v) (k * voxelY v) (k * voxelZ v)
public export dotVoxel : Voxel -> Voxel -> Nat; dotVoxel v1 v2 = (voxelX v1 * voxelX v2) + (voxelY v1 * voxelY v2) + (voxelZ v1 * voxelZ v2)
public export quadranceVoxel : Voxel -> Nat; quadranceVoxel v = let x = voxelX v; y = voxelY v; z = voxelZ v in (x * x) + (y * y) + (z * z)
public export minusVoxel : Voxel -> Voxel -> Voxel; minusVoxel v1 v2 = mkVoxel (minus (voxelX v1) (voxelX v2)) (minus (voxelY v1) (voxelY v2)) (minus (voxelZ v1) (voxelZ v2))

-- 4D Tesseract Semiring Operators
public export zeroTesseract : Tesseract; zeroTesseract = mkTesseract 0 0 0 0
public export oneTesseract : Tesseract; oneTesseract = mkTesseract 1 1 1 1
public export addTesseract : Tesseract -> Tesseract -> Tesseract; addTesseract t1 t2 = mkTesseract (tesseractX t1 + tesseractX t2) (tesseractY t1 + tesseractY t2) (tesseractZ t1 + tesseractZ t2) (tesseractT t1 + tesseractT t2)
public export mulTesseract : Tesseract -> Tesseract -> Tesseract; mulTesseract t1 t2 = mkTesseract (tesseractX t1 * tesseractX t2) (tesseractY t1 * tesseractY t2) (tesseractZ t1 * tesseractZ t2) (tesseractT t1 * tesseractT t2)
public export scaleTesseract : Nat -> Tesseract -> Tesseract; scaleTesseract k t = mkTesseract (k * tesseractX t) (k * tesseractY t) (k * tesseractZ t) (k * tesseractT t)
public export dotTesseract : Tesseract -> Tesseract -> Nat; dotTesseract t1 t2 = (tesseractX t1 * tesseractX t2) + (tesseractY t1 * tesseractY t2) + (tesseractZ t1 * tesseractZ t2) + (tesseractT t1 * tesseractT t2)
public export quadranceTesseract : Tesseract -> Nat; quadranceTesseract t = let x = tesseractX t; y = tesseractY t; z = tesseractZ t; w = tesseractT t in (x * x) + (y * y) + (z * z) + (w * w)
public export minusTesseract : Tesseract -> Tesseract -> Tesseract; minusTesseract t1 t2 = mkTesseract (minus (tesseractX t1) (tesseractX t2)) (minus (tesseractY t1) (tesseractY t2)) (minus (tesseractZ t1) (tesseractZ t2)) (minus (tesseractT t1) (tesseractT t2))

------------------------------------------------------------------------
-- 6. CONSTRUCTIVE COMMUTATIVE SEMIRING REWRITING LEMMAS
------------------------------------------------------------------------

-- 1D Unixel Semiring Lemmas
public export
0 prfUnixelAddZeroLeft : (i : Nat) -> addUnixel (mkUnixel 0) (mkUnixel i) = mkUnixel i
prfUnixelAddZeroLeft i = Refl

public export
0 prfUnixelAddZeroRight : (i : Nat) -> addUnixel (mkUnixel i) (mkUnixel 0) = mkUnixel i
prfUnixelAddZeroRight i = cong (\x => ConsCell (MkToken x) ZeroCell) (plusZeroRightNeutral i)

public export
0 prfUnixelAddComm : (i, j : Nat) -> addUnixel (mkUnixel i) (mkUnixel j) = addUnixel (mkUnixel j) (mkUnixel i)
prfUnixelAddComm i j = cong (\x => ConsCell (MkToken x) ZeroCell) (plusCommutative i j)

public export
0 prfUnixelAddAssoc : (i, j, k : Nat) -> addUnixel (addUnixel (mkUnixel i) (mkUnixel j)) (mkUnixel k) = addUnixel (mkUnixel i) (addUnixel (mkUnixel j) (mkUnixel k))
prfUnixelAddAssoc i j k = cong (\x => ConsCell (MkToken x) ZeroCell) (sym (plusAssociative i j k))

public export
0 prfUnixelMulZeroLeft : (i : Nat) -> mulUnixel (mkUnixel 0) (mkUnixel i) = mkUnixel 0
prfUnixelMulZeroLeft i = Refl

public export
0 prfUnixelMulOneLeft : (i : Nat) -> mulUnixel (mkUnixel 1) (mkUnixel i) = mkUnixel i
prfUnixelMulOneLeft i = cong (\x => ConsCell (MkToken x) ZeroCell) (multOneLeftNeutral i)

public export
0 prfUnixelMulComm : (i, j : Nat) -> mulUnixel (mkUnixel i) (mkUnixel j) = mulUnixel (mkUnixel j) (mkUnixel i)
prfUnixelMulComm i j = cong (\x => ConsCell (MkToken x) ZeroCell) (multCommutative i j)

public export
0 prfUnixelDistributesLeft : (i, j, k : Nat) -> mulUnixel (addUnixel (mkUnixel i) (mkUnixel j)) (mkUnixel k) = addUnixel (mulUnixel (mkUnixel i) (mkUnixel k)) (mulUnixel (mkUnixel j) (mkUnixel k))
prfUnixelDistributesLeft i j k = cong (\x => ConsCell (MkToken x) ZeroCell) (multDistributesOverPlusLeft i j k)

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
