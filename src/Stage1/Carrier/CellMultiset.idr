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

||| Direct O(1) construction of a CellMultiset from a coordinate cell with unit weight 1.
public export
coordCellToCellMultiset : {dim : Nat} -> CoordCell dim -> CellMultiset dim
coordCellToCellMultiset c = singletonCell c (intToBoxInt 1)

||| Direct O(1) construction of a CellMultiset 1 from a 1D Unixel with unit weight 1.
public export
unixelToCellMultiset : Unixel -> CellMultiset 1
unixelToCellMultiset u = singletonCell u (intToBoxInt 1)

||| Direct O(1) construction of a CellMultiset 0 from a 0D Nullexel with unit weight 1.
public export
nullexelToCellMultiset : Nullexel -> CellMultiset 0
nullexelToCellMultiset n = singletonCell n (intToBoxInt 1)

||| Direct O(1) construction of a CellMultiset from a basis singleton with unit weight 1 (legacy alias).
public export
singToCellMultiset : {dim : Nat} -> Sing (CoordCell dim) -> CellMultiset dim
singToCellMultiset = tokenToCellMultiset

||| Lookups the weight of a coordinate cell in a CellMultiset in O(log N) via monomorphic CoordCell comparators.
public export
lookupCellMultiset : {dim : Nat} -> CoordCell dim -> CellMultiset dim -> BoxInt
lookupCellMultiset c t = lookupBoxTreeBy coordCellLT coordCellEq c t

||| Sets the exact weight of a coordinate cell in a CellMultiset in O(log N), removing zero-weight nodes.
public export
setCellMultiset : {dim : Nat} -> CoordCell dim -> BoxInt -> CellMultiset dim -> CellMultiset dim
setCellMultiset c w t = setBoxTreeBy coordCellLT coordCellEq c w t

||| Single-pass additive update of a coordinate cell weight in a CellMultiset in O(log N), removing zero-weight nodes.
public export
addCellTree : {dim : Nat} -> CoordCell dim -> BoxInt -> CellMultiset dim -> CellMultiset dim
addCellTree c delta t = addBoxTreeBy coordCellLT coordCellEq c delta t

||| Inserts a coordinate cell with Nat multiplicity into a MultisetTree (CoordCell dim) in O(log N) without Ord.
public export
insertCellTokenTree : {dim : Nat} -> CoordCell dim -> Nat -> MultisetTree (CoordCell dim) -> MultisetTree (CoordCell dim)
insertCellTokenTree c cnt t = insertTokenTreeBy coordCellLT coordCellEq c cnt t

||| Lookups the Nat multiplicity of a coordinate cell in a MultisetTree (CoordCell dim) in O(log N) without Ord.
public export
lookupCellTokenTree : {dim : Nat} -> CoordCell dim -> MultisetTree (CoordCell dim) -> Nat
lookupCellTokenTree c t = lookupTokenTreeBy coordCellLT coordCellEq c t

||| Merges two MultisetTree (CoordCell dim) trees without Ord.
public export
mergeCellTokenTrees : {dim : Nat} -> MultisetTree (CoordCell dim) -> MultisetTree (CoordCell dim) -> MultisetTree (CoordCell dim)
mergeCellTokenTrees target Leaf = target
mergeCellTokenTrees target (Node _ l x c r) =
  let t1 = insertCellTokenTree x c target
      t2 = mergeCellTokenTrees t1 l
  in mergeCellTokenTrees t2 r

||| Constructs a CellMultiset from a fixed-length Vect of coordinate-weight pairs
||| with compile-time known length k and structural fuel bounds.
public export
fromVectCells : {dim, k : Nat} -> Vect k (CoordCell dim, BoxInt) -> CellMultiset dim
fromVectCells xs =
  foldl (\t, (c, w) => addCellTree c w t) BoxLeaf xs

||| Constructs a CellMultiset from a List of coordinate-weight pairs.
public export
fromListCellMultiset : {dim : Nat} -> List (CoordCell dim, BoxInt) -> CellMultiset dim
fromListCellMultiset xs =
  foldl (\t, (c, w) => addCellTree c w t) BoxLeaf xs

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
  foldStream (\t, (c, w) => addCellTree c w t) BoxLeaf strm

||| Adds two cell multisets by merging coordinate weights in a single pass per node.
public export
addCellMultiset : {dim : Nat} -> CellMultiset dim -> CellMultiset dim -> CellMultiset dim
addCellMultiset t1 t2 =
  foldBoxTreeL (\tree, (c, w) => addCellTree c w tree) t1 t2

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

||| Evaluates the L1 norm of a CellMultiset (sum of absolute weights) across arbitrary dimension `dim`.
public export
normL1CellMultiset : {dim : Nat} -> CellMultiset dim -> BoxInt
normL1CellMultiset t =
  foldBoxTreeL (\acc, (_, w) => acc + absBox w) (intToBoxInt 0) t

||| Universal spatial translation of a cell multiset by a displacement coordinate cell.
public export
translateCell : {dim : Nat} -> CoordCell dim -> CellMultiset dim -> CellMultiset dim
translateCell delta mset =
  foldBoxTreeL (\acc, (c, w) => setCellMultiset (addCoordCell c delta) w acc) BoxLeaf mset

||| Universal Free Adjunction Spatial Pushforward (F ⊣ U):
||| Lifts a transformation on coordinate basis tokens to a unique homomorphism over entire CellMultisets.
public export
liftCoordCellToken : {dim, dim' : Nat} -> (Token (CoordCell dim) -> CellMultiset dim') -> CellMultiset dim -> CellMultiset dim'
liftCoordCellToken f BoxLeaf = BoxLeaf
liftCoordCellToken f (BoxNode _ l c w r) =
  let leftM = liftCoordCellToken f l
      rightM = liftCoordCellToken f r
      thisM = if boxIsZero w then BoxLeaf
              else scaleCellMultiset w (f (MkToken c))
  in addCellMultiset (addCellMultiset leftM thisM) rightM

||| Canonical category-theoretic free monoid adjunction homomorphism for CellMultisets.
public export
liftCellMultisetHom : {dim, dim' : Nat} -> (Token (CoordCell dim) -> CellMultiset dim') -> CellMultiset dim -> CellMultiset dim'
liftCellMultisetHom = liftCoordCellToken

||| Identity Proof: Lifting on empty CellMultiset definitionally preserves empty CellMultiset.
public export
0 prfLiftCoordCellZero : {dim, dim' : Nat} -> (f : Token (CoordCell dim) -> CellMultiset dim') -> liftCoordCellToken f (the (CellMultiset dim) BoxLeaf) = the (CellMultiset dim') BoxLeaf
prfLiftCoordCellZero _ = Refl

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
subCellMultiset t1 t2 =
  foldBoxTreeL (\tree, (c, w) => addCellTree c (negate w) tree) t1 t2

||| Rebuilds a canonical CellMultiset by filtering non-zero weights and rebalancing.
public export
canonicalizeCellMultiset : {dim : Nat} -> CellMultiset dim -> CellMultiset dim
canonicalizeCellMultiset t =
  foldBoxTreeL (\acc, (c, w) => if boxIsNonZero w then setCellMultiset c w acc else acc) BoxLeaf t

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

||| Evaluates the Hadamard (pointwise) product between two CellMultisets directly via BoxMultisetTree:
||| (A ⊙ B)(c) = A(c) * B(c) in O(N log N) AVL tree operations.
public export
hadamardCellMultiset : {dim : Nat} -> CellMultiset dim -> CellMultiset dim -> CellMultiset dim
hadamardCellMultiset t1 t2 =
  foldBoxTreeL (\acc, (c, w1) =>
    let w2 = lookupCellMultiset c t2
        prod = mulBox w1 w2
    in if boxIsZero prod then acc else setCellMultiset c prod acc)
    BoxLeaf
    t1

||| Evaluates the Tropical infimum / lattice intersection between two CellMultisets:
||| (A ⊓ B)(c) = min(A(c), B(c)) in O(N log N) AVL tree operations.
public export
minCellMultiset : {dim : Nat} -> CellMultiset dim -> CellMultiset dim -> CellMultiset dim
minCellMultiset t1 t2 =
  foldBoxTreeL (\acc, (c, w1) =>
    let w2 = lookupCellMultiset c t2
        minW = if w1 <= w2 then w1 else w2
    in if minW > intToBoxInt 0 then setCellMultiset c minW acc else acc)
    BoxLeaf
    t1

||| Evaluates the Tropical supremum / join between two CellMultisets:
||| (A ⊔ B)(c) = max(A(c), B(c)) in O((N + M) log(N + M)) AVL tree operations.
public export
maxCellMultiset : {dim : Nat} -> CellMultiset dim -> CellMultiset dim -> CellMultiset dim
maxCellMultiset t1 t2 =
  let step1 = foldBoxTreeL (\acc, (c, w1) =>
        let w2 = lookupCellMultiset c t2
            maxW = if w1 >= w2 then w1 else w2
        in if boxIsZero maxW then acc else setCellMultiset c maxW acc)
        BoxLeaf
        t1
      step2 = foldBoxTreeL (\acc, (c, w2) =>
        let w1 = lookupCellMultiset c t1
        in if boxIsNonZero w1 then acc
           else let maxW = if w2 >= intToBoxInt 0 then w2 else intToBoxInt 0
                in if boxIsZero maxW then acc else setCellMultiset c maxW acc)
        step1
        t2
  in step2

||| Evaluates multi-dimensional Cauchy convolution of two CellMultisets via vector coordinate addition:
||| (A * B)(c1 + c2) = A(c1) * B(c2).
public export
convCellMultiset : {dim : Nat} -> CellMultiset dim -> CellMultiset dim -> CellMultiset dim
convCellMultiset t1 t2 =
  foldBoxTreeL (\treeAcc, (c1, w1) =>
    foldBoxTreeL (\acc, (c2, w2) =>
      let cOut = addCoordCell c1 c2
          prod = mulBox w1 w2
      in if boxIsZero prod then acc else addCellTree cOut prod acc)
      treeAcc
      t2)
    BoxLeaf
    t1

public export
{dim : Nat} -> MultisetAlgebra (CellMultiset dim) where
  zeroM     = emptyCellMultiset
  addM      = addCellMultiset
  subM      = subCellMultiset
  scaleM    = scaleCellMultiset
  mulM      = convCellMultiset
  hadamardM = hadamardCellMultiset
  minM      = minCellMultiset
  maxM      = maxCellMultiset
  dotM      = dotCellMultiset

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

------------------------------------------------------------------------
-- 3. UNIVERSAL GRADED TENSOR PRODUCT & DEC FIBER SLICING
------------------------------------------------------------------------

||| Universal Graded Exterior Tensor Product of CellMultisets:
||| Evaluates (A ⊗ B)(c1 ++ c2) = A(c1) * B(c2) in O(N log(NM)) AVL tree operations
||| with zero intermediate List allocation.
public export
tensorCellMultiset : {n, m : Nat} -> CellMultiset n -> CellMultiset m -> CellMultiset (n + m)
tensorCellMultiset m1 m2 =
  foldBoxTreeL (\acc1, (c1, w1) =>
    foldBoxTreeL (\acc2, (c2, w2) =>
      addCellTree (appendCell c1 c2) (w1 * w2) acc2
    ) acc1 m2
  ) BoxLeaf m1

||| 2D Outer Product: Vexel (1D) ⊗ Vexel (1D) -> Maxel (2D).
public export
outerProductVexels : Vexel -> Vexel -> Maxel
outerProductVexels v1 v2 = tensorCellMultiset v1 v2

||| 3D Outer Product: Vexel (1D) ⊗ Maxel (2D) -> Boxel (3D).
public export
outerProductVexelMaxel : Vexel -> Maxel -> Boxel
outerProductVexelMaxel v m = tensorCellMultiset v m

||| 4D Outer Product: Vexel (1D) ⊗ Boxel (3D) -> HyperBoxel (4D).
public export
outerProductVexelBoxel : Vexel -> Boxel -> HyperBoxel
outerProductVexelBoxel v b = tensorCellMultiset b v

||| 4D Outer Product: Maxel (2D) ⊗ Maxel (2D) -> HyperBoxel (4D).
public export
outerProductMaxelMaxel : Maxel -> Maxel -> HyperBoxel
outerProductMaxelMaxel m1 m2 = tensorCellMultiset m1 m2

||| Universal DEC Fiber Slicing:
||| Extracts the (D-1)-dimensional slice at coordinate `val` along `axis`
||| using canonical faceCell token projections in O(N log N) tree operations.
public export
sliceCellMultiset : {dim : Nat} -> (axis : Fin (S dim)) -> (val : Nat) -> CellMultiset (S dim) -> CellMultiset dim
sliceCellMultiset axis val mset =
  foldBoxTreeL (\acc, (c, w) =>
    if coordCellCoord axis c == val
      then addCellTree (faceCell axis c) w acc
      else acc
  ) BoxLeaf mset

------------------------------------------------------------------------
-- 4. COMPILE-TIME INVARIANT AUDITS (%macro)
------------------------------------------------------------------------

||| Audit: Universal tensor product [1] ⊗ [2, 3] = [1, 2, 3] with exact weight 3 * 5 = 15.
public export
auditUniversalTensorProductProof : Bool
auditUniversalTensorProductProof =
  let v1 = singletonCell (mkUnixel 1) (intToBoxInt 3)
      v2 = singletonCell (mkCell2 2 3) (intToBoxInt 5)
      t = tensorCellMultiset v1 v2
      expected = lookupCellMultiset (mkVoxel 1 2 3) t
      totalW = totalCellMultisetWeight t
  in expected == intToBoxInt 15 && totalW == intToBoxInt 15

public export
%macro
auditUniversalTensorProduct : Elab (Stage1.Carrier.CellMultiset.auditUniversalTensorProductProof = True)
auditUniversalTensorProduct = pure Refl

||| Audit: Universal fiber slicing of 3D voxel [1, 2, 3] along axis 0 at val 1 yields 2D pixel [2, 3].
public export
auditUniversalFiberSlicingProof : Bool
auditUniversalFiberSlicingProof =
  let b = singletonCell (mkVoxel 1 2 3) (intToBoxInt 7)
      slice1 = sliceCellMultiset FZ 1 b
      w1 = lookupCellMultiset (mkCell2 2 3) slice1
      sliceEmpty = sliceCellMultiset FZ 99 b
      wEmpty = totalCellMultisetWeight sliceEmpty
  in w1 == intToBoxInt 7 && wEmpty == intToBoxInt 0

public export
%macro
auditUniversalFiberSlicing : Elab (Stage1.Carrier.CellMultiset.auditUniversalFiberSlicingProof = True)
auditUniversalFiberSlicing = pure Refl



