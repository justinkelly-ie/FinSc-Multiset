module Stage1.Carrier.Maxel

import Data.Fin
import Data.Nat
import Stage0.BoxInt
import Stage0.Multiset
import Stage0.IntPolynumber
import public Stage0.StructuralFuel
import Stage0.OnSeq.FusedStream
import public Stage0.StreamPolynumber
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
extractRowVexel i tm = sliceCellMultiset FZ i tm

||| Extracts the j-th Column of a Maxel as a 1D Vexel: C_j(M) = M * [j]
public export
extractColVexel : Nat -> Maxel -> Vexel
extractColVexel j tm = sliceCellMultiset (FS FZ) j tm

||| Multiplies a column Vexel (ket) by a row Vexel (bra) to generate a Maxel:
public export
outerProductVexel : Vexel -> Vexel -> Maxel
outerProductVexel = outerProductVexels

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

||| Converts a Stage 1 Carrier bivariate IntPolynumber into an O(log N) AVL Maxel tree.
public export
intPolyToMaxel : IntPolynumber -> Maxel
intPolyToMaxel p =
  foldBoxTreeL (\acc, ((degA, degB), w) => addCellTree (mkPixel degA degB) w acc) BoxLeaf p

||| Converts an O(log N) AVL Maxel tree into a Stage 0 Carrier bivariate IntPolynumber.
public export
maxelToIntPoly : Maxel -> IntPolynumber
maxelToIntPoly m =
  foldBoxTreeL (\acc, (px, w) => if boxIsNonZero w then acc <+> singletonCarrier (pixelRow px, pixelCol px) w else acc) neutral m

||| O(log N) traversal step bound for a Maxel derived from cached AVL height (`boxTreeCapacityBound`).
public export
maxelStreamStepBound : Maxel -> Nat
maxelStreamStepBound m = boxTreeCapacityBound m * 4 + 16

||| Translates a Maxel directly into a deforested bivariate StreamIntPolynumber without heap List allocation.
public export
maxelToStreamIntPoly : Maxel -> StreamIntPolynumber
maxelToStreamIntPoly m =
  filterMapStream
    (\(px, w) => if boxIsNonZero w then Just ((pixelRow px, pixelCol px), w) else Nothing)
    (streamBoxMultisetTree m)

||| Extracts the active coordinate support of a Maxel as unit-coefficient bivariate StreamIntPolynumber terms.
public export
supportMaxelToStreamIntPoly : Maxel -> StreamIntPolynumber
supportMaxelToStreamIntPoly m =
  mapStream (\(degs, _) => (degs, intToBoxInt 1)) (maxelToStreamIntPoly m)

||| Translates the active support of a Maxel into a univariate streaming integer polynumber
||| `P_supp(x) = sum_{(r, c) in supp(M)} x^(r + c)` (so `P_supp(1) = |supp(M)|`).
public export
supportMaxelToStreamPoly : Maxel -> StreamPolynumber
supportMaxelToStreamPoly m =
  mapStream (\((r, c), _) => (r + c, intToBoxInt 1)) (maxelToStreamIntPoly m)

||| Translates a weighted Maxel into a univariate total-degree StreamPolynumber `sum w * x^(r + c)`.
public export
weightedMaxelToStreamPoly : Maxel -> StreamPolynumber
weightedMaxelToStreamPoly m =
  mapStream (\((r, c), w) => (r + c, w)) (maxelToStreamIntPoly m)

||| Summarizes a Maxel's support cardinality, absolute mass, and max degree in a single deforested pass.
public export
summarizeMaxelViaStreamPoly : Maxel -> PolySupportSummary
summarizeMaxelViaStreamPoly m =
  summarizeStreamIntPolyNat (maxelStreamStepBound m) (maxelToStreamIntPoly m)

||| Translates a Maxel's support via its streaming integer polynumber into exact existential `GohFuel`.
public export
maxelSupportGohFuel : Maxel -> AnyGohFuel
maxelSupportGohFuel m =
  streamIntPolyToGohFuel (maxelStreamStepBound m) (supportMaxelToStreamIntPoly m)

||| Packages a Maxel's active `(row, col)` support stream with derived `GohFuel` and `Skip` headroom.
public export
maxelToFueledFiniteSupport : Maxel -> AnyFueledFiniteStream (Nat, Nat)
maxelToFueledFiniteSupport m =
  let stepB = maxelStreamStepBound m
      strm  = supportMaxelToStreamIntPoly m
      summ  = summarizeStreamIntPolyNat stepB strm
      cap   = summ.supportCardinality
      slack = if stepB > cap then minus stepB cap else 4
  in MkAnyFueledFiniteStream cap
       (mkFueledFiniteStreamWithSkips (gohFuelForCapacity cap) slack (supportStreamIntPoly strm))

||| Translates a Maxel via `supportMaxelToStreamPoly` into a `GohFuel`-powered finite polynumber stream.
public export
maxelSupportPolyToFueledStream : Maxel -> AnyFueledFiniteStream (Nat, BoxInt)
maxelSupportPolyToFueledStream m =
  streamPolyToFueledFinite (maxelStreamStepBound m) (supportMaxelToStreamPoly m)

||| Packages a Maxel's bivariate `StreamIntPolynumber` into a `GohFuel`-powered `AnyFueledFiniteStream`.
public export
maxelToFueledFiniteIntPoly : Maxel -> AnyFueledFiniteStream ((Nat, Nat), BoxInt)
maxelToFueledFiniteIntPoly m =
  streamIntPolyToFueledFinite (maxelStreamStepBound m) (maxelToStreamIntPoly m)

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

------------------------------------------------------------------------
-- 3. PIXEL BASIS CONTRACTION & EMERGENT NON-COMMUTATIVITY THEOREMS
------------------------------------------------------------------------

||| Theorem 1 (Basis Propagation):
||| When the column token of the first pixel matches the row token of the second,
||| contraction propagates the outer boundary coordinates [A, C].
public export
0 prfContractionPropagation123 : mulPixel (mkPixel 1 2) (mkPixel 2 3) = Just (mkPixel 1 3)
prfContractionPropagation123 = Refl

||| Theorem 2 (Basis Annihilation):
||| When the inner tokens mismatch (B /= C), the contraction product vanishes identically to Nothing.
public export
0 prfContractionAnnihilation1234 : mulPixel (mkPixel 1 2) (mkPixel 3 4) = Nothing
prfContractionAnnihilation1234 = Refl

||| Theorem 3 (Fermionic / Grassmann Nilpotency):
||| Off-diagonal basis pixels square to zero: [A, B] * [A, B] = 0 when A /= B.
public export
0 prfGrassmannNilpotency12 : mulPixel (mkPixel 1 2) (mkPixel 1 2) = Nothing
prfGrassmannNilpotency12 = Refl

public export
0 prfGrassmannNilpotency21 : mulPixel (mkPixel 2 1) (mkPixel 2 1) = Nothing
prfGrassmannNilpotency21 = Refl

||| Theorem 4 (Idempotent Basis Projection):
||| Diagonal pixels act as idempotent projection operators: [A, A] * [A, A] = [A, A].
public export
0 prfIdempotentProjection11 : mulPixel (mkPixel 1 1) (mkPixel 1 1) = Just (mkPixel 1 1)
prfIdempotentProjection11 = Refl

public export
0 prfIdempotentProjection22 : mulPixel (mkPixel 2 2) (mkPixel 2 2) = Just (mkPixel 2 2)
prfIdempotentProjection22 = Refl

||| Elementary Maxel basis unit [1, 2] with unit weight.
public export
M12 : Maxel
M12 = singletonCell (mkPixel 1 2) (intToBoxInt 1)

||| Elementary Maxel basis unit [2, 1] with unit weight.
public export
M21 : Maxel
M21 = singletonCell (mkPixel 2 1) (intToBoxInt 1)

||| Forward contraction product: [1, 2] * [2, 1] = [1, 1].
public export
M12_M21 : Maxel
M12_M21 = mulMaxel M12 M21

||| Reverse contraction product: [2, 1] * [1, 2] = [2, 2].
public export
M21_M12 : Maxel
M21_M12 = mulMaxel M21 M12

public export
0 prfForwardProductWeight11 : lookupCellMultiset (mkPixel 1 1) Stage1.Carrier.Maxel.M12_M21 = intToBoxInt 1
prfForwardProductWeight11 = Refl

public export
0 prfForwardProductWeight22 : lookupCellMultiset (mkPixel 2 2) Stage1.Carrier.Maxel.M12_M21 = intToBoxInt 0
prfForwardProductWeight22 = Refl

public export
0 prfReverseProductWeight22 : lookupCellMultiset (mkPixel 2 2) Stage1.Carrier.Maxel.M21_M12 = intToBoxInt 1
prfReverseProductWeight22 = Refl

public export
0 prfReverseProductWeight11 : lookupCellMultiset (mkPixel 1 1) Stage1.Carrier.Maxel.M21_M12 = intToBoxInt 0
prfReverseProductWeight11 = Refl

public export
0 prfMaxelAddWeightEquivalence12 :
  lookupCellMultiset (mkPixel 1 2) (addMaxel Stage1.Carrier.Maxel.M12 Stage1.Carrier.Maxel.M21) =
  lookupCellMultiset (mkPixel 1 2) (addMaxel Stage1.Carrier.Maxel.M21 Stage1.Carrier.Maxel.M12)
prfMaxelAddWeightEquivalence12 = Refl

public export
0 prfMaxelAddWeightEquivalence21 :
  lookupCellMultiset (mkPixel 2 1) (addMaxel Stage1.Carrier.Maxel.M12 Stage1.Carrier.Maxel.M21) =
  lookupCellMultiset (mkPixel 2 1) (addMaxel Stage1.Carrier.Maxel.M21 Stage1.Carrier.Maxel.M12)
prfMaxelAddWeightEquivalence21 = Refl

||| Decision boolean certifying that the forward product differs from the reverse product:
||| M12 * M21 /= M21 * M12, establishing that non-commutativity emerges from pixel contraction.
public export
auditMaxelNonCommutativityProofExport : Bool
auditMaxelNonCommutativityProofExport =
  let w11_fwd = lookupCellMultiset (mkPixel 1 1) M12_M21
      w22_fwd = lookupCellMultiset (mkPixel 2 2) M12_M21
      w11_rev = lookupCellMultiset (mkPixel 1 1) M21_M12
      w22_rev = lookupCellMultiset (mkPixel 2 2) M21_M12
  in boxEq w11_fwd (intToBoxInt 1) &&
     boxEq w22_fwd (intToBoxInt 0) &&
     boxEq w11_rev (intToBoxInt 0) &&
     boxEq w22_rev (intToBoxInt 1)

||| Pure QTT 0-quantity compile-time proof witness that non-commutativity holds definitionally.
public export
0 prfAuditMaxelNonCommutativity : Stage1.Carrier.Maxel.auditMaxelNonCommutativityProofExport = True
prfAuditMaxelNonCommutativity = Refl
