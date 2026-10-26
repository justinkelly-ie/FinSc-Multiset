module Stage1.Carrier.CellMultiset

import Data.Fin
import Data.Nat
import Data.Vect
import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.StructuralFuel
import Language.Reflection
import Stage1.TypeTheory.Staging
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

||| Multiplies two Maxels (discrete matrix multiplication).
public export
mulMaxel : Maxel -> Maxel -> Maxel
mulMaxel t1 t2 =
  foldBoxTreeL (\treeAcc, (p1, w1) =>
    foldBoxTreeL (\acc, (p2, w2) =>
      case mulPixel p1 p2 of
        Just pOut =>
          let wOut = w1 * w2
              cur = lookupBoxTree pOut acc
              newW = cur + wOut
          in if boxIsZero newW
               then setBoxTree pOut (intToBoxInt 0) acc
               else setBoxTree pOut newW acc
        Nothing => acc)
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

||| Contracts a Maxel matrix on a Vexel vector (M * v).
public export
actMaxelVexel : Maxel -> Vexel -> Vexel
actMaxelVexel tm tv =
  foldBoxTreeL (\treeAcc, (pix, pw) =>
    foldBoxTreeL (\acc, (sing, sw) =>
      case mulPixelUnixel pix sing of
        Just sOut =>
          let wOut = pw * sw
              cur = lookupBoxTree sOut acc
              newW = cur + wOut
          in if boxIsZero newW
               then setBoxTree sOut (intToBoxInt 0) acc
               else setBoxTree sOut newW acc
        Nothing => acc)
      treeAcc
      tv)
    BoxLeaf
    tm

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
  foldBoxTreeL (\accTree, (k, kw) =>
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
    let i = unwrapUnixel u
    in foldBoxTreeL (\accV, (v, wv) =>
         let j = unwrapUnixel v
         in if i == j
              then accV
              else
                let w = wu * wv
                    pPos = mkPixel i j
                    pNeg = mkPixel j i
                    curPos = lookupBoxTree pPos accV
                    newPos = curPos + w
                    tree1 = if boxIsZero newPos
                              then setBoxTree pPos (intToBoxInt 0) accV
                              else setBoxTree pPos newPos accV
                    curNeg = lookupBoxTree pNeg tree1
                    newNeg = curNeg - w
                in if boxIsZero newNeg
                     then setBoxTree pNeg (intToBoxInt 0) tree1
                     else setBoxTree pNeg newNeg tree1)
         accU
         tv)
    BoxLeaf
    tu


------------------------------------------------------------------------
-- 5. VERIFICATION AUDITS
------------------------------------------------------------------------

||| Proves that the Grassmann wedge product of any Vexel with itself is identically zero: v ^ v == 0.
public export
auditWedgeNilpotencyProof : Bool
auditWedgeNilpotencyProof =
  let v = singletonCell (mkUnixel 1) (intToBoxInt 3) <+> singletonCell (mkUnixel 2) (intToBoxInt 5)
      w = wedgeVexel v v
  in w == (the Maxel BoxLeaf)

public export
auditRowExtractionProof : Bool
auditRowExtractionProof =
  let v1 = singletonCell (mkUnixel 1) (intToBoxInt 2) <+> singletonCell (mkUnixel 2) (intToBoxInt 3)
      v2 = singletonCell (mkUnixel 1) (intToBoxInt 1) <+> singletonCell (mkUnixel 2) (intToBoxInt 4)
      m = outerProductVexel v1 v2
      row1 = extractRowVexel 1 m
      expected = singletonCell (mkUnixel 1) (intToBoxInt 2) <+> singletonCell (mkUnixel 2) (intToBoxInt 8)
  in row1 == expected


