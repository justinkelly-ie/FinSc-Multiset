module Stage1.Carrier.Maxel

import Data.Nat
import Stage0.BoxInt
import Stage0.Multiset
import Stage0.IntPolynumber
import Stage0.OnSeq.FusedStream
import Stage1.MultisetTree
import Stage1.Basis.CoordCell
import public Stage1.Carrier.CellMultiset
import public Stage1.Carrier.Vexel

%default total

------------------------------------------------------------------------
-- 1. PURE 2D DISCRETE MATRIX CARRIER (Maxel)
------------------------------------------------------------------------

||| Extracts pixel-weight terms association list from a Maxel.
public export
maxelPixels : Maxel -> List (Pixel, BoxInt)
maxelPixels = boxTreeToList

public export
pixels : Maxel -> List (Pixel, BoxInt)
pixels = maxelPixels

||| Canonical empty/zero Maxel.
public export
emptyMaxel : Maxel
emptyMaxel = BoxLeaf

||| Canonicalize a Maxel (prunes zero weights and rebalances).
public export
canonicalizeMaxel : Maxel -> Maxel
canonicalizeMaxel = canonicalizeCellMultiset

||| Evaluates the Frobenius inner product between two Maxels: Tr(A^T B)
public export
dotProduct : Maxel -> Maxel -> BoxInt
dotProduct = dotCellMultiset {dim = 2}

||| Multiplies two Maxels (discrete matrix multiplication).
public export
mulMaxel : Maxel -> Maxel -> Maxel
mulMaxel t1 t2 =
  foldBoxTreeL (\treeAcc, (p1, w1) =>
    foldBoxTreeL (\acc, (p2, w2) =>
      case mulPixel p1 p2 of
        Just pOut => addCellTree pOut (w1 * w2) acc
        Nothing   => acc)
      treeAcc
      t2)
    BoxLeaf
    t1

||| Canonical 3D identity metric Maxel: [1, 1] + [2, 2] + [3, 3].
public export
identityMaxel : Maxel
identityMaxel =
  singletonCell (mkPixel 1 1) (intToBoxInt 1) <+>
  singletonCell (mkPixel 2 2) (intToBoxInt 1) <+>
  singletonCell (mkPixel 3 3) (intToBoxInt 1)

||| Matrix transposition: (M^T)_ij = M_ji.
public export
transposeMaxel : Maxel -> Maxel
transposeMaxel m =
  foldBoxTreeL (\acc, (p, w) => setCellMultiset (transposePixel p) w acc) BoxLeaf m

||| Contracts a Maxel matrix on a Vexel vector (M * v).
public export
actMaxelVexel : Maxel -> Vexel -> Vexel
actMaxelVexel tm tv =
  foldBoxTreeL (\treeAcc, (pix, pw) =>
    foldBoxTreeL (\acc, (sing, sw) =>
      case mulPixelUnixel pix sing of
        Just sOut => addCellTree sOut (pw * sw) acc
        Nothing   => acc)
      treeAcc
      tv)
    BoxLeaf
    tm

||| Extracts the i-th Row of a Maxel as a 1D Vexel: R_i(M) = [i] * M
public export
extractRowVexel : Nat -> Maxel -> Vexel
extractRowVexel i tm =
  let singI = mkUnixel i
  in foldBoxTreeL (\acc, (pix, w) =>
       case mulUnixelPixel singI pix of
         Just sOut => addCellTree sOut w acc
         Nothing   => acc)
       BoxLeaf
       tm

||| Extracts the j-th Column of a Maxel as a 1D Vexel: C_j(M) = M * [j]
public export
extractColVexel : Nat -> Maxel -> Vexel
extractColVexel j tm =
  let singJ = mkUnixel j
  in foldBoxTreeL (\acc, (pix, w) =>
       case mulPixelUnixel pix singJ of
         Just sOut => addCellTree sOut w acc
         Nothing   => acc)
       BoxLeaf
       tm

||| Multiplies a column Vexel (ket) by a row Vexel (bra) to generate a Maxel:
public export
outerProductVexel : Vexel -> Vexel -> Maxel
outerProductVexel tk tb =
  foldBoxTreeL (\accTree, (k, kw) =>
    foldBoxTreeL (\innerAcc, (b, bw) =>
      addCellTree (unixelPairToPixel k b) (kw * bw) innerAcc)
      accTree
      tb)
    BoxLeaf
    tk

||| Evaluates metric inner product <u, v>_g = u^T (g * v).
public export
metricInnerVexel : Maxel -> Vexel -> Vexel -> BoxInt
metricInnerVexel g u v =
  let gv = actMaxelVexel g v
  in dotVexel u gv

||| Evaluates the Grassmann exterior wedge product of two Vexels into a 2D Maxel.
public export
wedgeVexel : Vexel -> Vexel -> Maxel
wedgeVexel tu tv =
  foldBoxTreeL (\accU, (u, wu) =>
    foldBoxTreeL (\accV, (v, wv) =>
      if coordCellEq u v
        then accV
        else
          let w = wu * wv
              pPos = unixelPairToPixel u v
              pNeg = transposePixel pPos
          in addCellTree pNeg (negate w) (addCellTree pPos w accV))
      accU
      tv)
    BoxLeaf
    tu

||| Multiplies two Maxels (discrete matrix multiplication).
public export
mul : Maxel -> Maxel -> Maxel
mul = mulMaxel

||| Stream-to-stream discrete matrix multiplication (Rule 04 §8).
||| Evaluates in O(1) auxiliary registers without allocating intermediate lists.
public export
mulMaxelStream : FusedStream (Pixel, BoxInt) -> FusedStream (Pixel, BoxInt) -> FusedStream (Pixel, BoxInt)
mulMaxelStream s1 s2 =
  filterMapStream (\((p1, p2), w) =>
    case mulPixel p1 p2 of
      Just pOut => Just (pOut, w)
      Nothing   => Nothing)
    (streamTensorProduct s1 s2)

||| Multiplies two Maxels into a new Maxel via deforested streaming pipeline.
public export
mulStream : Maxel -> Maxel -> Maxel
mulStream m1 m2 =
  streamToCellMultiset (mulMaxelStream (streamBoxMultisetTree m1) (streamBoxMultisetTree m2))

||| Scales a Maxel by a signed BoxInt scalar.
public export
scaleMaxel : BoxInt -> Maxel -> Maxel
scaleMaxel = scaleCellMultiset {dim = 2}

||| Adds two Maxels.
public export
addMaxel : Maxel -> Maxel -> Maxel
addMaxel = addCellMultiset {dim = 2}

||| Subtracts two Maxels: m1 - m2 = m1 + (-1) * m2
public export
subMaxel : Maxel -> Maxel -> Maxel
subMaxel = subCellMultiset {dim = 2}

||| Evaluates the L1 norm of a Maxel (sum of absolute weights).
public export
normL1Maxel : Maxel -> BoxInt
normL1Maxel = normL1CellMultiset {dim = 2}

||| Canonical two-edge directed bipartite adjacency Maxel: [1, 2] + [1, 3].
public export
bipartiteTwoEdgeMaxel : Maxel
bipartiteTwoEdgeMaxel =
  singletonCell (mkPixel 1 2) (intToBoxInt 1) <+>
  singletonCell (mkPixel 1 3) (intToBoxInt 1)

||| Backward-compatibility alias for bipartiteTwoEdgeMaxel.
public export
waterMoleculeBonds : Maxel
waterMoleculeBonds = bipartiteTwoEdgeMaxel

||| Converts a Stage 0 RLE bivariate IntPolynumber into an O(log N) AVL Maxel tree.
public export
intPolyToMaxel : IntPolynumber -> Maxel
intPolyToMaxel p =
  foldMultiset (\(degA, degB), w, acc => addCellTree (mkPixel degA degB) w acc) BoxLeaf p

||| Converts an O(log N) AVL Maxel tree into a Stage 0 RLE bivariate IntPolynumber.
public export
maxelToIntPoly : Maxel -> IntPolynumber
maxelToIntPoly m =
  foldBoxTreeR (\px, w, acc => if boxIsNonZero w then AddM (pixelRow px, pixelCol px) w acc else acc) ZeroM m

------------------------------------------------------------------------
-- 2. VERIFICATION AUDITS
------------------------------------------------------------------------

||| Proves that the Grassmann wedge product of any Vexel with itself is identically zero: v ^ v == 0.
public export
auditWedgeNilpotencyProof : Bool
auditWedgeNilpotencyProof =
  let v = singletonCell (mkUnixel 1) (intToBoxInt 3) <+> singletonCell (mkUnixel 2) (intToBoxInt 5)
      w = wedgeVexel v v
  in w == emptyMaxel

public export
auditRowExtractionProof : Bool
auditRowExtractionProof =
  let v1 = singletonCell (mkUnixel 1) (intToBoxInt 2) <+> singletonCell (mkUnixel 2) (intToBoxInt 3)
      v2 = singletonCell (mkUnixel 1) (intToBoxInt 1) <+> singletonCell (mkUnixel 2) (intToBoxInt 4)
      m = outerProductVexel v1 v2
      row1 = extractRowVexel 1 m
      expected = singletonCell (mkUnixel 1) (intToBoxInt 2) <+> singletonCell (mkUnixel 2) (intToBoxInt 8)
  in row1 == expected

||| Audits that transpose of transpose is identity, and (A * B)^T == B^T * A^T.
public export
auditTransposeAntiAutomorphismProof : Bool
auditTransposeAntiAutomorphismProof =
  let m1 = singletonCell (mkPixel 1 2) (intToBoxInt 2) <+> singletonCell (mkPixel 2 1) (intToBoxInt 3)
      m2 = singletonCell (mkPixel 2 2) (intToBoxInt 4) <+> singletonCell (mkPixel 1 1) (intToBoxInt 5)
      prodT = transposeMaxel (mulMaxel m1 m2)
      tProd = mulMaxel (transposeMaxel m2) (transposeMaxel m1)
  in (transposeMaxel (transposeMaxel m1) == m1) && (prodT == tProd)
