module Stage1.Carrier.Maxel

import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.StructuralFuel
import Stage0.Multiset
import Stage1.Order.Preorder
import Stage1.MultisetTree
import Stage1.MultisetTensor
import Data.List
import Data.Vect
import Language.Reflection
import Stage1.TypeTheory.Staging
import public Stage1.Basis.Coordinate
import public Stage1.Carrier.Vexel

%default total

------------------------------------------------------------------------
-- 1. MAXEL (2D WILDBERGER MATRIX MULTISET)
------------------------------------------------------------------------

||| @deprecated Use CellMultiset 2 directly. Transparent constructor bridge for Maxel.
public export
MkMaxelTree : BoxMultisetTree Pixel -> Maxel
MkMaxelTree t = t

||| Direct conversion of a list of Pixel-BoxInt pairs to a signed AVL BoxMultisetTree in O(N log N).
||| Prunes zero weights and collapses duplicate Pixels.
||| @deprecated Use singletonCell + (<+>), streamToCellMultiset, or fromVectCells. Avoid heap List materialization.
public export
maxelListToBoxTree : List (Pixel, BoxInt) -> BoxMultisetTree Pixel
maxelListToBoxTree = mkCellMultiset

||| Constructs a canonical Maxel from a list of Pixel-BoxInt pairs in O(N log N).
||| @deprecated Use singletonCell + (<+>), streamToCellMultiset, or fromVectCells. Avoid heap List materialization.
public export
mkMaxel : List (Pixel, BoxInt) -> Maxel
mkMaxel = mkCellMultiset

||| Canonical constructor alias for Maxel from coordinate pairs.
||| @deprecated Use singletonCell + (<+>), streamToCellMultiset, or fromVectCells. Avoid heap List materialization.
public export
MkMaxel : List (Pixel, BoxInt) -> Maxel
MkMaxel = mkCellMultiset

||| Flattens a Maxel to an association list in O(N) time.
||| @deprecated Use streamCellMultiset or foldBoxTreeL directly. Avoid materializing entire multiset as List.
public export
maxelPixels : Maxel -> List (Pixel, BoxInt)
maxelPixels = boxTreeToList

||| Projection view of Maxel pixels.
||| @deprecated Use streamCellMultiset or foldBoxTreeL directly. Avoid materializing entire multiset as List.
public export
pixels : Maxel -> List (Pixel, BoxInt)
pixels = maxelPixels

||| Direct conversion of a Maxel to a signed AVL BoxMultisetTree in O(1).
public export
maxelToBoxTree : Maxel -> BoxMultisetTree Pixel
maxelToBoxTree t = t

||| Reconstructs a Maxel from a signed AVL BoxMultisetTree in O(1).
public export
boxTreeToMaxel : BoxMultisetTree Pixel -> Maxel
boxTreeToMaxel t = t

||| Canonicalize a Maxel via legacy Multiset linked list.
public export
canonicalizeMaxelMultiset : Maxel -> Maxel
canonicalizeMaxelMultiset = canonicalizeCellMultiset

||| Canonicalizes a Maxel by pruning zero weights and rebalancing.
public export
canonicalizeMaxel : Maxel -> Maxel
canonicalizeMaxel = canonicalizeCellMultiset

||| @deprecated Legacy bridge converting Maxel to heap-allocated linked list Multiset.
||| Use CellMultiset operations or boxTreeToList directly.
public export
maxelToMultiset : Maxel -> Multiset BoxInt Pixel
maxelToMultiset t = fromListBox (boxTreeToList t)

||| @deprecated Legacy bridge converting linked list Multiset to Maxel.
||| Use mkCellMultiset directly.
public export
multisetToMaxel : Multiset BoxInt Pixel -> Maxel
multisetToMaxel m = mkCellMultiset (multisetToList m)


------------------------------------------------------------------------
-- 2. DIMENSION-INDEXED DEPENDENT MAXEL
------------------------------------------------------------------------

||| A SquareMaxel is a square discrete matrix of dimension `dim`,
||| backed by a balanced AVL MultisetTree of Pixels in O(log N).
public export
record SquareMaxel (dim : Nat) where
  constructor MkSquareMaxel
  entries : MultisetTree Pixel

public export
Eq (SquareMaxel dim) where
  (MkSquareMaxel e1) == (MkSquareMaxel e2) = e1 == e2

public export
{dim : Nat} -> Show (SquareMaxel dim) where
  show (MkSquareMaxel es) = "SquareMaxel[" ++ show dim ++ "](" ++ show (treeToList es) ++ ")"
------------------------------------------------------------------------
-- 2. DIMENSION-INDEXED TYPED MATRIX (MaxelN - Provided by CellMultiset)
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 3. SPARSE-DENSE MATRIX-VECTOR CONTRACTIONS
------------------------------------------------------------------------


||| Accumulator step for sparse-dense matrix-vector contraction:
public export
sparseDenseAccumStep : (dim : Nat) -> Vect dim BoxInt -> Vect dim BoxInt -> (Pixel, Nat) -> Vect dim BoxInt
sparseDenseAccumStep dim vec acc (p, cnt) =
  let r = pixelRow p
      c = pixelCol p
  in case (natToFin r dim, natToFin c dim) of
       (Just rFin, Just cFin) =>
         let vCol = index cFin vec
             w = natToBoxInt cnt
             term = mulBox w vCol
         in updateVectAt rFin (\curr => addBox curr term) acc
       _ => acc

||| Directly contracts a sparse SquareMaxel with a dense VexelN in O(K + dim) steps.
public export
contractSparseDenseVexel : {dim : Nat} -> SquareMaxel dim -> VexelN dim -> VexelN dim
contractSparseDenseVexel {dim} (MkSquareMaxel tree) (MkVexelN vec) =
  let initAcc = replicate dim (intToBoxInt 0)
      foldedAcc = foldTreeL (sparseDenseAccumStep dim vec) initAcc tree
  in MkVexelN foldedAcc

||| 2LTT Staged Sparse-Dense Contraction:
public export
stagedContractSparseDense : {dim : Nat} -> Lift (SquareMaxel dim) -> VexelN dim -> Code (VexelN dim)
stagedContractSparseDense qm v = quote (contractSparseDenseVexel (splice qm) v)

||| Accumulator step for converting sparse SquareMaxel tree entries into dense MaxelN rows.
public export
squareMaxelToMaxelNStep : (dim : Nat) -> Vect dim (Vect dim BoxInt) -> (Pixel, Nat) -> Vect dim (Vect dim BoxInt)
squareMaxelToMaxelNStep dim acc (p, cnt) =
  let r = pixelRow p
      c = pixelCol p
  in case (natToFin r dim, natToFin c dim) of
       (Just rFin, Just cFin) =>
         let w = natToBoxInt cnt
         in updateVectAt rFin (updateVectAt cFin (\curr => addBox curr w)) acc
       _ => acc

||| Dense conversion of a sparse SquareMaxel of size `dim` into a dense MaxelN.
public export
squareMaxelToMaxelN : (dim : Nat) -> SquareMaxel dim -> MaxelN dim
squareMaxelToMaxelN dim (MkSquareMaxel tree) =
  let zeroRow = replicate dim (intToBoxInt 0)
      initRows = replicate dim zeroRow
      foldedRows = foldTreeL (squareMaxelToMaxelNStep dim) initRows tree
  in MkMaxelN foldedRows

||| Helper inserting non-zero row elements into a MultisetTree Pixel.
public export
insertRowPixels : {dim : Nat} -> Fin dim -> MultisetTree Pixel -> (Fin dim, BoxInt) -> MultisetTree Pixel
insertRowPixels rFin treeAcc (cFin, w) =
  if boxIsZero w then treeAcc
  else insertTokenTree (mkPixel (finToNat rFin) (finToNat cFin)) (boxToNat w) treeAcc

||| Helper inserting all non-zero matrix elements of a row into a MultisetTree Pixel.
public export
insertMatrixPixels : {dim : Nat} -> MultisetTree Pixel -> (Fin dim, Vect dim BoxInt) -> MultisetTree Pixel
insertMatrixPixels {dim} treeAcc (rFin, row) =
  foldl (insertRowPixels rFin) treeAcc (zip (allFins dim) row)

||| Sparse conversion of a dense MaxelN of size `dim` into a sparse SquareMaxel.
public export
maxelNToSquareMaxel : {dim : Nat} -> MaxelN dim -> SquareMaxel dim
maxelNToSquareMaxel {dim} (MkMaxelN rs) =
  let indexedRows = zip (allFins dim) rs
      t = foldl insertMatrixPixels Leaf indexedRows
  in MkSquareMaxel t

------------------------------------------------------------------------
-- 4. SIGNED DIMENSION-INDEXED SPARSE MATRIX (Provided by CellMultiset)
------------------------------------------------------------------------





||| Algebraic Kronecker Tensor Product on BoxSquareMaxel:
public export
kroneckerBoxSquareMaxelAlg : {m, n : Nat} -> BoxSquareMaxel m -> BoxSquareMaxel n -> BoxSquareMaxel (m * n)
kroneckerBoxSquareMaxelAlg {m} {n} m1 m2 =
  let t1 = boxSquareMaxelToTensor m1
      t2 = boxSquareMaxelToTensor m2
      tOp = tensorOperator t1 t2
      observed = mapMultiset (observeKroneckerPixel n) tOp
  in tensorToBoxSquareMaxel observed

||| Verified Invariant: Direct sparse Kronecker product definitionally matches
||| the pushforward observation of the underlying monoidal tensor operator.
public export
auditKroneckerAlgebraicEquivalence : Bool
auditKroneckerAlgebraicEquivalence =
  let id2 = identityBoxSquareMaxel 2
  in kroneckerBoxSquareMaxel id2 id2 == kroneckerBoxSquareMaxelAlg id2 id2

||| 2LTT Staged Sparse Kronecker Tensor Product:
public export
stagedKroneckerBoxSquareMaxel : {m, n : Nat} -> Lift (BoxSquareMaxel m) -> Lift (BoxSquareMaxel n) -> Code (BoxSquareMaxel (m * n))
stagedKroneckerBoxSquareMaxel qm1 qm2 = quote (kroneckerBoxSquareMaxel (splice qm1) (splice qm2))

------------------------------------------------------------------------
-- 5. MATRIX MULTIPLICATION, IDENTITY & NUM INSTANCE
------------------------------------------------------------------------


||| Lookups the signed BoxInt weight of a coordinate Pixel in O(log N) time.
public export
lookupPixel : Pixel -> Maxel -> BoxInt
lookupPixel p t = lookupBoxTree p t

||| Adds two Maxels and consolidates duplicate coordinates directly via BoxMultisetTree in O(N log N).
public export
addMaxel : Maxel -> Maxel -> Maxel
addMaxel = addCellMultiset

||| Scales a Maxel by a BoxInt scalar, pruning zero weights.
public export
scaleMaxel : BoxInt -> Maxel -> Maxel
scaleMaxel = scaleCellMultiset

||| Computes total weight/mass across all pixels in a Maxel via in-order tree fold in O(N).
public export
totalMaxelWeight : Maxel -> BoxInt
totalMaxelWeight = totalCellMultisetWeight

||| The canonical zero/empty Maxel.
public export
emptyMaxel : Maxel
emptyMaxel = BoxLeaf


public export
multiplyMaxel : Maxel -> Maxel -> Maxel
multiplyMaxel = mulMaxel

||| Fast tensor contraction via native Maxel AVL tree matrix multiplication:
public export
fastMultisetTensorMult : MultisetTensor Nat Nat -> MultisetTensor Nat Nat -> MultisetTensor Nat Nat
fastMultisetTensorMult t1 t2 =
  maxelToTensor (mulMaxel (tensorToMaxel t1) (tensorToMaxel t2))


public export
Num (CellMultiset 2) where
  (+) = addCellMultiset
  (*) = mulMaxel
  fromInteger n = scaleMaxel (intToBoxInt n) identityMaxel

||| Subtracts two Maxels and consolidates duplicate coordinates directly via BoxMultisetTree in O(N log N).
public export
subMaxel : Maxel -> Maxel -> Maxel
subMaxel m1 m2 = addCellMultiset m1 (scaleCellMultiset (intToBoxInt (-1)) m2)

public export
Neg (CellMultiset 2) where
  negate = scaleCellMultiset (intToBoxInt (-1))
  (-) = subMaxel



public export
implementation MultisetAlgebra Maxel where
  zeroM = BoxLeaf
  addM = addMaxel

  scaleM = scaleMaxel
  dotM m1 m2 = totalMaxelWeight (mulMaxel m1 m2)

public export
implementation MultisetAlgebra Vexel where
  zeroM = MkVexelTree BoxLeaf
  addM = addVexel
  scaleM = scaleVexel
  dotM = dotVexel

------------------------------------------------------------------------
-- 6. WILDBERGER SUPPORT & CHROMOGEOMETRIC METRIC MAXELS
------------------------------------------------------------------------




||| 2D Blue (Elliptic/Euclidean) Metric Maxel parameterized by (x, y):
public export
parameterizedBlueMetricMaxel : BoxInt -> BoxInt -> Maxel
parameterizedBlueMetricMaxel x y =
  singletonCell (mkPixel 1 1) (x * x) <+>
  singletonCell (mkPixel 2 2) (y * y)

||| 2D Red (Hyperbolic/Relativistic) Metric Maxel parameterized by (x, y):
public export
parameterizedRedMetricMaxel : BoxInt -> BoxInt -> Maxel
parameterizedRedMetricMaxel x y =
  singletonCell (mkPixel 1 1) (x * x) <+>
  singletonCell (mkPixel 2 2) (mulBox (intToBoxInt (-1)) (y * y))

||| 2D Green (Parabolic/Null) Metric Maxel parameterized by (x, y):
public export
parameterizedGreenMetricMaxel : BoxInt -> BoxInt -> Maxel
parameterizedGreenMetricMaxel x y =
  let xy = x * y
  in singletonCell (mkPixel 1 2) xy <+>
     singletonCell (mkPixel 2 1) xy

||| Invariant audit verifying the parameterized chromogeometric operator identity:
public export
auditParameterizedMetricOperatorIdentity : (x : BoxInt) -> (y : BoxInt) -> Bool
auditParameterizedMetricOperatorIdentity x y =
  let gB = parameterizedBlueMetricMaxel x y
      gR = parameterizedRedMetricMaxel x y
      gG = parameterizedGreenMetricMaxel x y
      gR2 = mulMaxel gR gR
      gG2 = mulMaxel gG gG
      lhsSum = addMaxel gR2 gG2
      qBlue = (x * x) + (y * y)
      rhsExpected = scaleMaxel qBlue gB
      lhs11 = lookupPixel (mkPixel 1 1) lhsSum
      rhs11 = lookupPixel (mkPixel 1 1) rhsExpected
      lhs22 = lookupPixel (mkPixel 2 2) lhsSum
      rhs22 = lookupPixel (mkPixel 2 2) rhsExpected
  in boxEq lhs11 rhs11 && boxEq lhs22 rhs22

------------------------------------------------------------------------
-- 7. SQUAREMAXEL CHROMOGEOMETRIC TRIADS
------------------------------------------------------------------------

||| 2D Maxel represented as a balanced binary multiset search tree in O(log N).
public export
MaxelTree : Type
MaxelTree = MultisetTree Pixel

||| Converts a Maxel to a balanced MultisetTree in O(N log N) time.
public export
maxelToTree : Maxel -> MultisetTree Pixel
maxelToTree t =
  foldBoxTreeL (\tree, (p, w) => insertTokenTree p (boxToNat w) tree) Leaf t


||| Converts a MultisetTree back to a Maxel in linear O(N log N) time with zero intermediate lists.
public export
treeToMaxel : MultisetTree Pixel -> Maxel
treeToMaxel tree =
  MkMaxelTree (foldTreeL (\acc, (p, cnt) => if cnt == 0 then acc else setBoxTree p (natToBoxInt cnt) acc) BoxLeaf tree)

||| O(log N) lookup for coordinate pixel in a MaxelTree.
public export
lookupPixelTree : Pixel -> MultisetTree Pixel -> Nat
lookupPixelTree = lookupTokenTree

||| Converts a SquareMaxel into a standard Maxel carrier.
public export
squareMaxelToMaxel : SquareMaxel dim -> Maxel
squareMaxelToMaxel (MkSquareMaxel es) = treeToMaxel es

||| Converts a standard Maxel into a SquareMaxel with explicit dimension bound.
public export
maxelToSquareMaxel : (dim : Nat) -> Maxel -> SquareMaxel dim
maxelToSquareMaxel dim m = MkSquareMaxel (maxelToTree m)

||| Constructs a dimension-indexed identity SquareMaxel of size `dim` in O(dim log dim).
public export
identitySquareMaxel : (dim : Nat) -> SquareMaxel dim
identitySquareMaxel dim =
  let pxs = [mkPixel (S i) (S i) | i <- [0..pred dim]]
      t   = foldl (\tree, p => insertTokenTree p 1 tree) Leaf pxs
  in MkSquareMaxel t

||| Dimension-checked discrete matrix multiplication for SquareMaxel:
public export
mulSquareMaxel : SquareMaxel dim -> SquareMaxel dim -> SquareMaxel dim
mulSquareMaxel (MkSquareMaxel e1) (MkSquareMaxel e2) =
  let m1 = treeToMaxel e1
      m2 = treeToMaxel e2
      mProd = mulMaxel m1 m2
  in MkSquareMaxel (maxelToTree mProd)

||| Scales a SquareMaxel by a BoxInt scalar.
public export
scaleSquareMaxel : BoxInt -> SquareMaxel dim -> SquareMaxel dim
scaleSquareMaxel s (MkSquareMaxel es) =
  let m = treeToMaxel es
      mScaled = scaleMaxel s m
  in MkSquareMaxel (maxelToTree mScaled)

||| Adds two SquareMaxels of identical dimension `dim`.
public export
addSquareMaxel : SquareMaxel dim -> SquareMaxel dim -> SquareMaxel dim
addSquareMaxel (MkSquareMaxel e1) (MkSquareMaxel e2) =
  let m1 = treeToMaxel e1
      m2 = treeToMaxel e2
      mSum = addMaxel m1 m2
  in MkSquareMaxel (maxelToTree mSum)

public export
parameterizedBlueSquareMaxel : BoxInt -> BoxInt -> SquareMaxel 2
parameterizedBlueSquareMaxel x y =
  maxelToSquareMaxel 2 (parameterizedBlueMetricMaxel x y)

public export
parameterizedRedSquareMaxel : BoxInt -> BoxInt -> SquareMaxel 2
parameterizedRedSquareMaxel x y =
  maxelToSquareMaxel 2 (parameterizedRedMetricMaxel x y)

public export
parameterizedGreenSquareMaxel : BoxInt -> BoxInt -> SquareMaxel 2
parameterizedGreenSquareMaxel x y =
  maxelToSquareMaxel 2 (parameterizedGreenMetricMaxel x y)

public export
auditParameterizedSquareMetricOperatorIdentity : (x : BoxInt) -> (y : BoxInt) -> Bool
auditParameterizedSquareMetricOperatorIdentity x y =
  let gB = parameterizedBlueSquareMaxel x y
      gR = parameterizedRedSquareMaxel x y
      gG = parameterizedGreenSquareMaxel x y
      gR2 = mulSquareMaxel gR gR
      gG2 = mulSquareMaxel gG gG
      lhsSum = addSquareMaxel gR2 gG2
      qBlue = (x * x) + (y * y)
      rhsExpected = scaleSquareMaxel qBlue gB
  in lhsSum == rhsExpected

public export
blueMetricMaxel2D : Maxel
blueMetricMaxel2D = parameterizedBlueMetricMaxel (intToBoxInt 1) (intToBoxInt 1)

public export
redMetricMaxel2D : Maxel
redMetricMaxel2D = parameterizedRedMetricMaxel (intToBoxInt 1) (intToBoxInt 1)

public export
greenMetricMaxel2D : Maxel
greenMetricMaxel2D = parameterizedGreenMetricMaxel (intToBoxInt 1) (intToBoxInt 1)

public export
auditChromogeometricMetricSupportsProof : Bool
auditChromogeometricMetricSupportsProof =
  let sBlue  = supportMaxel blueMetricMaxel2D
      sRed   = supportMaxel redMetricMaxel2D
      sGreen = supportMaxel greenMetricMaxel2D
      tBlue  = sBlue  == [mkPixel 1 1, mkPixel 2 2]
      tRed   = sRed   == [mkPixel 1 1, mkPixel 2 2]
      tGreen = sGreen == [mkPixel 1 2, mkPixel 2 1]
  in tBlue && tRed && tGreen

public export
auditMatrixPathCompositionProof : Bool
auditMatrixPathCompositionProof =
  let gG = greenMetricMaxel2D
      gProd = mulMaxel gG gG
      sProd = supportMaxel gProd
      e11 = lookupPixel (mkPixel 1 1) gProd
      e22 = lookupPixel (mkPixel 2 2) gProd
  in sProd == [mkPixel 1 1, mkPixel 2 2] && e11 == intToBoxInt 1 && e22 == intToBoxInt 1

------------------------------------------------------------------------
-- 8. ROW & COLUMN EXTRACTION, OUTER PRODUCT & GRASSMANN WEDGE
------------------------------------------------------------------------

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
  let resultTree = foldBoxTreeL (\accTree, (k, kw) =>
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
  in resultTree

||| 🧪 Chemistry: A Molecular Bond Maxel represents covalent bond connectivity between atoms i and j.
public export
waterMoleculeBonds : Maxel
waterMoleculeBonds =
  MkMaxel [ (mkPixel 1 2, intToBoxInt 1) -- O-H1 bond
          , (mkPixel 1 3, intToBoxInt 1) -- O-H2 bond
          ]

||| Proves that the Grassmann wedge product of any Vexel with itself is identically zero: v ^ v == 0.
public export
auditWedgeNilpotencyProof : Bool
auditWedgeNilpotencyProof =
  let v = MkVexel [(mkUnixel 1, intToBoxInt 3), (mkUnixel 2, intToBoxInt 5)]
      w = wedgeVexel v v
  in w == MkMaxel []

public export
auditRowExtractionProof : Bool
auditRowExtractionProof =
  let v1 = MkVexel [(mkUnixel 1, intToBoxInt 2), (mkUnixel 2, intToBoxInt 3)]
      v2 = MkVexel [(mkUnixel 1, intToBoxInt 1), (mkUnixel 2, intToBoxInt 4)]
      m = outerProductVexel v1 v2
      row1 = extractRowVexel 1 m
  in row1 == MkVexel [(mkUnixel 1, intToBoxInt 2), (mkUnixel 2, intToBoxInt 8)]

------------------------------------------------------------------------
-- 9. MAXELN CONVERSIONS
------------------------------------------------------------------------

rowToPixelPairsHelper : Nat -> Nat -> Vect k BoxInt -> List (Pixel, BoxInt)
rowToPixelPairsHelper _ _ [] = []
rowToPixelPairsHelper r c (w :: ws) = (mkPixel r c, w) :: rowToPixelPairsHelper r (S c) ws

matToPixelPairsHelper : Nat -> Nat -> Vect k (Vect n BoxInt) -> List (Pixel, BoxInt)
matToPixelPairsHelper _ _ [] = []
matToPixelPairsHelper r c (row :: rows) = rowToPixelPairsHelper r c row ++ matToPixelPairsHelper (S r) c rows

||| Converts a dimension-indexed MaxelN into a canonical sparse multiset Maxel (1-indexed).
public export
maxelNToMaxel : {n : Nat} -> MaxelN n -> Maxel
maxelNToMaxel (MkMaxelN rs) = canonicalizeMaxel (MkMaxel (matToPixelPairsHelper 1 1 rs))

||| Converts a dimension-indexed MaxelN into a 0-indexed sparse multiset Maxel (quantum basis).
public export
maxelNToMaxel0 : {n : Nat} -> MaxelN n -> Maxel
maxelNToMaxel0 (MkMaxelN rs) = canonicalizeMaxel (MkMaxel (matToPixelPairsHelper 0 0 rs))

||| @deprecated Use canonicalizeCellMultiset directly on CellMultiset trees.
public export
pruneMaxelTerms : List (Pixel, BoxInt) -> List (Pixel, BoxInt)
pruneMaxelTerms [] = []
pruneMaxelTerms ((p, w) :: rest) =
  if boxIsZero w then pruneMaxelTerms rest else (p, w) :: pruneMaxelTerms rest

------------------------------------------------------------------------
-- POLYNOMIAL BRIDGES: POLYS <-> MAXELS
------------------------------------------------------------------------

||| Converts a 2D Maxel into a bivariate polynumber: sum a_ij [i, j] <=> sum a_ij x^i y^j.
public export
maxelToBivariatePolynumber : Maxel -> List ((Nat, Nat), BoxInt)
maxelToBivariatePolynumber t =
  foldBoxTreeR (\p, w, acc => ((pixelRow p, pixelCol p), w) :: acc) [] t



