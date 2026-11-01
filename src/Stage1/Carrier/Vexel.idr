module Stage1.Carrier.Vexel

import Data.Nat
import Stage0.BoxInt
import Stage0.OnSeq.FusedStream
import Stage0.Token
import Stage0.Singleton.Sing
import Stage1.MultisetTree
import Stage1.Basis.CoordCell
import public Stage1.Carrier.CellMultiset

%default total

------------------------------------------------------------------------
-- 1. PURE 1D DISCRETE VECTOR CARRIER (Vexel)
------------------------------------------------------------------------

||| Backward-compatibility constructor alias for tree-backed Vexels.
public export
MkVexelTree : BoxMultisetTree Unixel -> Vexel
MkVexelTree t = t

||| Injects a 1D coordinate token into a Vexel with unit weight 1.
public export
tokenToVexel : Token (CoordCell 1) -> Vexel
tokenToVexel = tokenToCellMultiset

||| Injects a 1D coordinate singleton into a Vexel with unit weight 1.
public export
singToVexel : Sing (CoordCell 1) -> Vexel
singToVexel = singToCellMultiset



||| Extracts unixel-weight terms association list from a Vexel.
public export
vexelTerms : Vexel -> List (Unixel, BoxInt)
vexelTerms = boxTreeToList

public export
terms : Vexel -> List (Unixel, BoxInt)
terms = vexelTerms

||| Canonical empty/zero Vexel.
public export
emptyVexel : Vexel
emptyVexel = BoxLeaf

||| Canonicalize a Vexel (prunes zero weights and rebalances).
public export
canonicalizeVexel : Vexel -> Vexel
canonicalizeVexel = canonicalizeCellMultiset

||| Compresses a Vexel by pruning zero weights and rebalancing.
public export
compressVexel : Vexel -> Vexel
compressVexel = canonicalizeCellMultiset

||| Evaluates the standard Euclidean inner product between two Vexels:
||| <u, v> = sum u_i * v_i
public export
dotProduct : Vexel -> Vexel -> BoxInt
dotProduct = dotCellMultiset {dim = 1}

||| Evaluates the Euclidean inner product via deforested stream (Rule 04 §8).
public export
dotProductStream : Vexel -> Vexel -> BoxInt
dotProductStream = dotCellMultisetStream {dim = 1}

||| Scales a Vexel by a signed BoxInt scalar.
public export
scaleVexel : BoxInt -> Vexel -> Vexel
scaleVexel = scaleCellMultiset {dim = 1}

||| Adds two Vexels.
public export
addVexel : Vexel -> Vexel -> Vexel
addVexel = addCellMultiset {dim = 1}

||| Subtracts two Vexels: u - v = u + (-1) * v
public export
subVexel : Vexel -> Vexel -> Vexel
subVexel = subCellMultiset {dim = 1}

||| Evaluates the L1 norm of a Vexel (sum of absolute weights).
public export
normL1Vexel : Vexel -> BoxInt
normL1Vexel v =
  foldBoxTreeL (\acc, (_, w) => acc + absBox w) (intToBoxInt 0) (the (BoxMultisetTree (CoordCell 1)) v)

||| A Quark Vexel represents the 3 color charges (Red=[1], Green=[2], Blue=[3]) of a Baryon singlet.
public export
nucleonQuarkVexel : Vexel
nucleonQuarkVexel =
  singletonCell (mkCell1 1) (intToBoxInt 1) <+>
  singletonCell (mkCell1 2) (intToBoxInt 1) <+>
  singletonCell (mkCell1 3) (intToBoxInt 1)
