module Stage1.Carrier.CellMultiset

import Data.Fin
import Data.Nat
import Data.Vect
import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.StructuralFuel
import Language.Reflection
import Stage1.TypeTheory.Staging
import Stage0.Token
import Stage0.Singleton.Sing
import public Stage0.OnSeq.FusedStream
import public Stage1.MultisetTree
import public Stage1.Basis.CoordCell
import public Stage1.MultisetTensor

%default total

------------------------------------------------------------------------
-- 1. CANONICAL CARRIER MULTISET (CellMultiset) & SPATIAL TRANSLATION
------------------------------------------------------------------------

||| A CellMultiset is an AVL multiset of D-dimensional coordinate basis cells.
public export
CellMultiset : (dim : Nat) -> Type
CellMultiset dim = BoxMultisetTree (CoordCell dim)

||| Empty cell multiset.
public export
emptyCellMultiset : {dim : Nat} -> CellMultiset dim
emptyCellMultiset = BoxLeaf

||| Direct O(1) singleton construction of a CellMultiset without intermediate List allocation.
public export
singletonCell : {dim : Nat} -> CoordCell dim -> BoxInt -> CellMultiset dim
singletonCell c w =
  if boxIsZero w then BoxLeaf
  else BoxNode 1 BoxLeaf c w BoxLeaf

||| Direct O(1) construction of a CellMultiset from a basis token with unit weight 1.
public export
tokenToCellMultiset : {dim : Nat} -> Token (CoordCell dim) -> CellMultiset dim
tokenToCellMultiset (MkToken c) = singletonCell c (intToBoxInt 1)

||| Direct O(1) construction of a CellMultiset from a basis singleton with unit weight 1.
public export
singToCellMultiset : {dim : Nat} -> Sing (CoordCell dim) -> CellMultiset dim
singToCellMultiset (MkSing c) = singletonCell c (intToBoxInt 1)

||| Constructs a CellMultiset from a fixed-length Vect of coordinate-weight pairs
||| with compile-time known length k and structural fuel bounds.
public export
fromVectCells : {dim, k : Nat} -> Vect k (CoordCell dim, BoxInt) -> CellMultiset dim
fromVectCells xs =
  foldl (\t, (c, w) =>
          if boxIsZero w then t
          else let cur = lookupBoxTree c t
                   newW = cur + w
               in if boxIsZero newW
                    then setBoxTree c (intToBoxInt 0) t
                    else setBoxTree c newW t)
        BoxLeaf
        xs

||| Deforested zero-allocation stream extractor for the active support of a CellMultiset.
||| Emits strictly non-zero basis cells in O(1) auxiliary registers (Rule 04 §8).
public export
supportCellStream : {dim : Nat} -> CellMultiset dim -> FusedStream (CoordCell dim)
supportCellStream t =
  filterMapStream (\(c, w) => if boxIsNonZero w then Just c else Nothing) (streamBoxMultisetTree t)

||| Zero-allocation stream generator for all (coordinate, weight) entries in a CellMultiset.
public export
streamCellMultiset : {dim : Nat} -> CellMultiset dim -> FusedStream (CoordCell dim, BoxInt)
streamCellMultiset = streamBoxMultisetTree

||| Assembles a CellMultiset from a deforested FusedStream in O(N log N) time without intermediate List allocation.
public export
streamToCellMultiset : {dim : Nat} -> FusedStream (CoordCell dim, BoxInt) -> CellMultiset dim
streamToCellMultiset strm =
  foldStream (\t, (c, w) =>
    if boxIsZero w then t
    else let cur = lookupBoxTree c t
             newW = cur + w
         in if boxIsZero newW
              then setBoxTree c (intToBoxInt 0) t
              else setBoxTree c newW t)
    BoxLeaf
    strm



||| Lookups the weight of a coordinate cell in a CellMultiset in O(log N).
public export
lookupCellMultiset : {dim : Nat} -> CoordCell dim -> CellMultiset dim -> BoxInt
lookupCellMultiset = lookupBoxTree

||| Adds two cell multisets by merging coordinate weights.
public export
addCellMultiset : {dim : Nat} -> CellMultiset dim -> CellMultiset dim -> CellMultiset dim
addCellMultiset t1 t2 =
  foldBoxTreeL (\tree, (c, w) =>
    let cur = lookupBoxTree c tree
        newW = cur + w
    in if boxIsZero newW
         then setBoxTree c (intToBoxInt 0) tree
         else setBoxTree c newW tree)
    t1
    t2

||| Scales a cell multiset by a BoxInt scalar.
public export
scaleCellMultiset : {dim : Nat} -> BoxInt -> CellMultiset dim -> CellMultiset dim
scaleCellMultiset s t =
  if boxIsZero s then BoxLeaf
  else mapBoxTreeWeight (s *) t

||| Computes total weight across all cells in a CellMultiset.
public export
totalCellMultisetWeight : {dim : Nat} -> CellMultiset dim -> BoxInt
totalCellMultisetWeight t =
  foldBoxTreeL (\acc, (_, w) => acc + w) (intToBoxInt 0) t

||| Universal spatial translation of a cell multiset by a displacement coordinate cell.
public export
translateCell : CoordCell dim -> CellMultiset dim -> CellMultiset dim
translateCell delta mset =
  foldBoxTreeL (\acc, (c, w) => setBoxTree (addCoordCell c delta) w acc) BoxLeaf mset

||| Canonical zero-cost dimension synonyms:
public export Vexel       : Type; Vexel       = CellMultiset 1
public export Maxel       : Type; Maxel       = CellMultiset 2
public export Boxel       : Type; Boxel       = CellMultiset 3
public export HyperBoxel  : Type; HyperBoxel  = CellMultiset 4

||| Lookups the signed BoxInt weight of a coordinate Pixel in O(log N) time.
public export
lookupPixel : Pixel -> Maxel -> BoxInt
lookupPixel = lookupCellMultiset

||| Lookups the signed BoxInt weight of a coordinate Unixel in O(log N) time.
public export
lookupUnixel : Unixel -> Vexel -> BoxInt
lookupUnixel = lookupCellMultiset

public export totalVexelMass : Vexel -> BoxInt; totalVexelMass = totalCellMultisetWeight
public export totalVexelWeight : Vexel -> BoxInt; totalVexelWeight = totalCellMultisetWeight
public export totalMaxelWeight : Maxel -> BoxInt; totalMaxelWeight = totalCellMultisetWeight

||| Extracts coordinate cell terms association list from a CellMultiset.
public export
cellTerms : {dim : Nat} -> CellMultiset dim -> List (CoordCell dim, BoxInt)
cellTerms = boxTreeToList

||| Universal tree field identity projection for backwards compatibility with (.tree).
public export
tree : CellMultiset dim -> CellMultiset dim
tree t = t

public export
subCellMultiset : {dim : Nat} -> CellMultiset dim -> CellMultiset dim -> CellMultiset dim
subCellMultiset t1 t2 = addCellMultiset t1 (scaleCellMultiset (intToBoxInt (-1)) t2)

||| Rebuilds a canonical CellMultiset by filtering non-zero weights and rebalancing.
public export
canonicalizeCellMultiset : {dim : Nat} -> CellMultiset dim -> CellMultiset dim
canonicalizeCellMultiset t =
  foldBoxTreeL (\acc, (c, w) => if boxIsNonZero w then setBoxTree c w acc else acc) BoxLeaf t

public export
canonicalizeCell : {dim : Nat} -> CellMultiset dim -> CellMultiset dim
canonicalizeCell = canonicalizeCellMultiset

||| Canonicalize / compress a Maxel (prunes zero weights and rebalances).
public export
compressMaxel : Maxel -> Maxel
compressMaxel = canonicalizeCellMultiset

||| Extracts the finite active support of a CellMultiset as a list.
||| @deprecated Use supportCellStream (FusedStream). Materializing support as List is forbidden by Rule 04 §8.
public export
supportCellMultiset : {dim : Nat} -> CellMultiset dim -> List (CoordCell dim)
supportCellMultiset t =
  foldBoxTreeR (\c, w, acc => if boxIsNonZero w then c :: acc else acc) [] t

public export
supportMaxel : Maxel -> List Pixel
supportMaxel = supportCellMultiset

public export
supportVexel : Vexel -> List Unixel
supportVexel = supportCellMultiset

||| Deforested zero-allocation stream extractor for the active support of a Maxel (Rule 04 §8).
public export
supportMaxelStream : Maxel -> FusedStream Pixel
supportMaxelStream = supportCellStream

||| Deforested zero-allocation stream extractor for the active support of a Vexel (Rule 04 §8).
public export
supportVexelStream : Vexel -> FusedStream Unixel
supportVexelStream = supportCellStream

public export
{dim : Nat} -> Semigroup (CellMultiset dim) where
  (<+>) = addCellMultiset

public export
{dim : Nat} -> Monoid (CellMultiset dim) where
  neutral = BoxLeaf

------------------------------------------------------------------------
-- 2. DISCRETE MATRIX, VECTOR & EXTERIOR ALGEBRA OPERATORS
------------------------------------------------------------------------

||| Evaluates the canonical Frobenius / multiset inner product between two CellMultisets directly via BoxMultisetTree.
public export
dotCellMultiset : {dim : Nat} -> CellMultiset dim -> CellMultiset dim -> BoxInt
dotCellMultiset t1 t2 =
  foldBoxTreeL (\acc, (u, w1) =>
    let w2 = lookupCellMultiset u t2
    in acc + (w1 * w2))
    (intToBoxInt 0)
    t1

||| Evaluates the inner product between two CellMultisets directly via FusedStream (Rule 04 §8).
public export
dotCellMultisetStream : {dim : Nat} -> CellMultiset dim -> CellMultiset dim -> BoxInt
dotCellMultisetStream t1 t2 =
  foldStream (\acc, (u, w1) =>
    let w2 = lookupCellMultiset u t2
    in acc + (w1 * w2))
    (intToBoxInt 0)
    (streamCellMultiset t1)

||| Evaluates the standard Euclidean inner product between two Vexels directly via BoxMultisetTree.
public export
dotVexel : Vexel -> Vexel -> BoxInt
dotVexel = dotCellMultiset {dim = 1}

||| Evaluates the Frobenius inner product between two Maxels directly via BoxMultisetTree: Tr(A^T B).
public export
dotMaxel : Maxel -> Maxel -> BoxInt
dotMaxel = dotCellMultiset {dim = 2}


