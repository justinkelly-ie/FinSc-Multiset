module Stage1.Carrier.HyperBoxel

import Data.Nat
import Data.Fin
import Stage0.BoxInt
import Stage0.OnSeq.FusedStream
import Stage1.MultisetTree
import Stage1.Basis.CoordCell
import public Stage1.Carrier.CellMultiset
import public Stage1.Carrier.Vexel
import public Stage1.Carrier.Maxel
import public Stage1.Carrier.Boxel

%default total

------------------------------------------------------------------------
-- 1. PURE 4D SPATIOTEMPORAL TENSOR CARRIER (HyperBoxel)
------------------------------------------------------------------------

||| Backward-compatibility constructor alias for tree-backed HyperBoxels.
public export
MkHyperBoxelTree : BoxMultisetTree Tesseract -> HyperBoxel
MkHyperBoxelTree t = t



||| Canonical empty/zero HyperBoxel.
public export
emptyHyperBoxel : HyperBoxel
emptyHyperBoxel = BoxLeaf

||| Canonicalize a HyperBoxel (prunes zero weights and rebalances).
public export
canonicalizeHyperBoxel : HyperBoxel -> HyperBoxel
canonicalizeHyperBoxel = canonicalizeCellMultiset

||| Compresses a HyperBoxel by pruning zero weights and rebalancing.
public export
compressHyperBoxel : HyperBoxel -> HyperBoxel
compressHyperBoxel = canonicalizeCellMultiset

||| Extracts tesseract-weight terms association list from a 4D HyperBoxel.
public export
hyperBoxels : HyperBoxel -> List (Tesseract, BoxInt)
hyperBoxels = boxTreeToList

||| Lookups the signed BoxInt weight of a coordinate Tesseract in O(log N) time.
public export
lookupTesseract : Tesseract -> HyperBoxel -> BoxInt
lookupTesseract = lookupCellMultiset

||| Evaluates the standard Euclidean inner product between two HyperBoxels:
||| <h1, h2> = sum w1_i * w2_i
public export
dotProduct : HyperBoxel -> HyperBoxel -> BoxInt
dotProduct = dotCellMultiset {dim = 4}

||| Specialized alias for dotProduct on 4D HyperBoxels.
public export
dotHyperBoxel : HyperBoxel -> HyperBoxel -> BoxInt
dotHyperBoxel = dotCellMultiset {dim = 4}

||| Evaluates the inner product between two HyperBoxels via deforested stream (Rule 04 §8).
public export
dotProductStream : HyperBoxel -> HyperBoxel -> BoxInt
dotProductStream = dotCellMultisetStream {dim = 4}

||| Scales a HyperBoxel by a signed BoxInt scalar.
public export
scaleHyperBoxel : BoxInt -> HyperBoxel -> HyperBoxel
scaleHyperBoxel = scaleCellMultiset {dim = 4}

||| Adds two HyperBoxels.
public export
addHyperBoxel : HyperBoxel -> HyperBoxel -> HyperBoxel
addHyperBoxel = addCellMultiset {dim = 4}

||| Subtracts two HyperBoxels: h1 - h2 = h1 + (-1) * h2
public export
subHyperBoxel : HyperBoxel -> HyperBoxel -> HyperBoxel
subHyperBoxel = subCellMultiset {dim = 4}

||| Evaluates the L1 norm of a HyperBoxel (sum of absolute weights).
public export
normL1HyperBoxel : HyperBoxel -> BoxInt
normL1HyperBoxel h =
  foldBoxTreeL (\acc, (_, w) => acc + absBox w) (intToBoxInt 0) (the (BoxMultisetTree (CoordCell 4)) h)

||| Computes total weight across all tesseracts in a HyperBoxel.
public export
totalHyperBoxelWeight : HyperBoxel -> BoxInt
totalHyperBoxelWeight = totalCellMultisetWeight

||| Stream representation of the finite active support of a HyperBoxel in O(1) registers.
public export
supportHyperBoxelStream : HyperBoxel -> FusedStream Tesseract
supportHyperBoxelStream = supportCellStream

||| Converts a HyperBoxel to a deforested stream of (Tesseract, BoxInt) pairs in O(1) registers.
public export
streamHyperBoxel : HyperBoxel -> FusedStream (Tesseract, BoxInt)
streamHyperBoxel = streamCellMultiset

||| Collects a deforested stream of (Tesseract, BoxInt) pairs into a canonical HyperBoxel.
public export
streamToHyperBoxel : FusedStream (Tesseract, BoxInt) -> HyperBoxel
streamToHyperBoxel = streamToCellMultiset

------------------------------------------------------------------------
-- 2. SPATIOTEMPORAL TENSOR PRODUCTS & TEMPORAL SLICING
------------------------------------------------------------------------

||| Slices a 4D HyperBoxel at a fixed temporal coordinate t = targetT into a 3D spatial Boxel.
public export
sliceHyperBoxelT : Nat -> HyperBoxel -> Boxel
sliceHyperBoxelT targetT h = sliceCellMultiset (FS (FS (FS FZ))) targetT h

||| Proves that slicing a 4D HyperBoxel at time t=2 extracts the exact 3D spatial Boxel.
public export
auditHyperBoxelSliceProof : Bool
auditHyperBoxelSliceProof =
  let b = singletonCell (mkVoxel 1 2 3) (intToBoxInt 5) <+> singletonCell (mkVoxel 2 1 1) (intToBoxInt 7)
      v = singletonCell (mkUnixel 2) (intToBoxInt 1) <+> singletonCell (mkUnixel 4) (intToBoxInt 3)
      h = outerProductVexelBoxel v b
      bSliced2 = sliceHyperBoxelT 2 h
      bSliced4 = sliceHyperBoxelT 4 h
      bSliced1 = sliceHyperBoxelT 1 h
  in (bSliced2 == b) &&
     (bSliced4 == scaleBoxel (intToBoxInt 3) b) &&
     (bSliced1 == emptyBoxel)
