module Stage1.Carrier.Maxel

import Data.Nat
import Stage0.BoxInt
import Stage0.OnSeq.FusedStream
import Stage1.MultisetTree
import Stage1.Basis.CoordCell
import public Stage1.Carrier.CellMultiset
import public Stage1.Carrier.Vexel

%default total

------------------------------------------------------------------------
-- 1. PURE 2D DISCRETE MATRIX CARRIER (Maxel)
------------------------------------------------------------------------

||| Backward-compatibility constructor alias for tree-backed Maxels.
public export
MkMaxelTree : BoxMultisetTree Pixel -> Maxel
MkMaxelTree t = t

||| Backward-compatibility constructor alias for list of pixel-weight pairs.
public export
MkMaxel : List (Pixel, BoxInt) -> Maxel
MkMaxel = mkCellMultiset

public export
mkMaxel : List (Pixel, BoxInt) -> Maxel
mkMaxel = mkCellMultiset

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
normL1Maxel m =
  foldBoxTreeL (\acc, (_, w) => acc + absBox w) (intToBoxInt 0) (the (BoxMultisetTree (CoordCell 2)) m)

||| A Molecular Bond Maxel represents covalent bond connectivity between atoms i and j.
public export
waterMoleculeBonds : Maxel
waterMoleculeBonds =
  MkMaxel [ (mkPixel 1 2, intToBoxInt 1) -- O-H1 bond
          , (mkPixel 1 3, intToBoxInt 1) -- O-H2 bond
          ]
