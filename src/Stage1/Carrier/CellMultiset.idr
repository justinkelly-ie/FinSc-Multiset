module Stage1.Carrier.CellMultiset

import Data.Nat
import Data.Vect
import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.StructuralFuel
import public Stage0.OnSeq.FusedStream
import public Stage1.MultisetTree
import public Stage1.Basis.CoordCell

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

||| Constructs a CellMultiset from a list of coordinate-weight pairs in O(N log N).
||| @deprecated Use singletonCell + (<+>), streamToCellMultiset, or fromVectCells. Avoid heap List materialization.
public export
mkCellMultiset : {dim : Nat} -> List (CoordCell dim, BoxInt) -> CellMultiset dim
mkCellMultiset xs =
  foldl (\t, (c, w) =>
          if boxIsZero w then t
          else let cur = lookupBoxTree c t
                   newW = cur + w
               in if boxIsZero newW
                    then setBoxTree c (intToBoxInt 0) t
                    else setBoxTree c newW t)
        BoxLeaf
        xs

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

public export
{dim : Nat} -> Semigroup (CellMultiset dim) where
  (<+>) = addCellMultiset

public export
{dim : Nat} -> Monoid (CellMultiset dim) where
  neutral = BoxLeaf


