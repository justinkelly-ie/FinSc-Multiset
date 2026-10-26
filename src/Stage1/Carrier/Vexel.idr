module Stage1.Carrier.Vexel

import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.StructuralFuel
import Stage0.Multiset
import Stage1.Order.Preorder
import Stage1.MultisetTree
import Stage1.Polynumber
import Data.List
import Data.Vect
import Language.Reflection
import Stage1.TypeTheory.Staging
import public Stage1.Basis.Coordinate

%default total



------------------------------------------------------------------------
-- 2. VEXEL (1D WILDBERGER VECTOR MULTISET)
------------------------------------------------------------------------

||| @deprecated Use CellMultiset 1 directly. Transparent constructor bridge for Vexel.
public export
MkVexelTree : BoxMultisetTree Unixel -> Vexel
MkVexelTree t = t

||| Canonical unambiguous alias for discrete monomorphic 1D Wildberger vectors.
public export
DiscreteVexel : Type
DiscreteVexel = Vexel

||| Direct conversion of a list of Unixel-BoxInt pairs to a signed AVL BoxMultisetTree in O(N log N).
||| Prunes zero weights and collapses duplicate Unixels.
||| @deprecated Use singletonCell + (<+>), streamToCellMultiset, or fromVectCells. Avoid heap List materialization.
public export
vexelListToBoxTree : List (Unixel, BoxInt) -> BoxMultisetTree Unixel
vexelListToBoxTree = mkCellMultiset

||| Constructs a canonical Vexel from a list of Unixel-BoxInt pairs in O(N log N).
||| @deprecated Use singletonCell + (<+>), streamToCellMultiset, or fromVectCells. Avoid heap List materialization.
public export
mkVexel : List (Unixel, BoxInt) -> Vexel
mkVexel = mkCellMultiset

||| Canonical constructor alias for Vexel from coordinate pairs.
||| @deprecated Use singletonCell + (<+>), streamToCellMultiset, or fromVectCells. Avoid heap List materialization.
public export
MkVexel : List (Unixel, BoxInt) -> Vexel
MkVexel = mkCellMultiset

||| Flattens a Vexel to an association list in O(N) time.
||| @deprecated Use streamCellMultiset or foldBoxTreeL directly. Avoid materializing entire multiset as List.
public export
vexelTerms : Vexel -> List (Unixel, BoxInt)
vexelTerms = boxTreeToList

||| Projection view of Vexel terms.
||| @deprecated Use streamCellMultiset or foldBoxTreeL directly. Avoid materializing entire multiset as List.
public export
terms : Vexel -> List (Unixel, BoxInt)
terms = vexelTerms

||| Direct conversion of a Vexel to a signed AVL BoxMultisetTree in O(1).
public export
vexelToBoxTree : Vexel -> BoxMultisetTree Unixel
vexelToBoxTree t = t

||| Reconstructs a Vexel from a signed AVL BoxMultisetTree in O(1).
public export
boxTreeToVexel : BoxMultisetTree Unixel -> Vexel
boxTreeToVexel t = t

||| Canonicalize a Vexel via legacy Multiset linked list.
public export
canonicalizeVexelMultiset : Vexel -> Vexel
canonicalizeVexelMultiset = canonicalizeCellMultiset

||| Canonicalizes a Vexel by pruning zero weights and rebalancing.
public export
canonicalizeVexel : Vexel -> Vexel
canonicalizeVexel = canonicalizeCellMultiset

||| @deprecated Legacy bridge converting Vexel to heap-allocated linked list Multiset.
||| Use CellMultiset operations or boxTreeToList directly.
public export
vexelToMultiset : Vexel -> Multiset BoxInt Unixel
vexelToMultiset t = fromListBox (boxTreeToList t)

||| @deprecated Legacy bridge converting linked list Multiset to Vexel.
||| Use mkCellMultiset directly.
public export
multisetToVexel : Multiset BoxInt Unixel -> Vexel
multisetToVexel m = mkCellMultiset (multisetToList m)


------------------------------------------------------------------------
-- 3. DIMENSION-INDEXED TYPED VEXEL (VexelN - Provided by CellMultiset)
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 4. POINT LOOKUP, TOTAL MASS & ALGEBRAIC OPERATIONS
------------------------------------------------------------------------


||| Lookups the signed BoxInt weight of a basis Unixel in O(log N) time.
public export
lookupUnixel : Unixel -> Vexel -> BoxInt
lookupUnixel u t = lookupBoxTree u t

||| Computes the total integer mass of a Vexel vector via in-order tree fold in O(N).
public export
totalVexelMass : Vexel -> BoxInt
totalVexelMass = totalCellMultisetWeight

||| Alias for total mass of a Vexel vector.
public export
totalVexelWeight : Vexel -> BoxInt
totalVexelWeight = totalCellMultisetWeight

||| Adds two Vexels and consolidates duplicate coordinates directly via BoxMultisetTree in O(N log N).
public export
addVexel : Vexel -> Vexel -> Vexel
addVexel = addCellMultiset

public export
Num (CellMultiset 1) where
  (+) = addCellMultiset
  (*) _ _ = BoxLeaf
  fromInteger n = mkCellMultiset [(mkUnixel 0, intToBoxInt n)]

||| Subtracts two Vexels and consolidates duplicate coordinates directly via BoxMultisetTree in O(N log N).
public export
subVexel : Vexel -> Vexel -> Vexel
subVexel v1 v2 = addCellMultiset v1 (scaleCellMultiset (intToBoxInt (-1)) v2)

public export
Neg (CellMultiset 1) where
  negate = scaleCellMultiset (intToBoxInt (-1))
  (-) = subVexel


||| Scales a Vexel by a BoxInt scalar, pruning zero weights.
public export
scaleVexel : BoxInt -> Vexel -> Vexel
scaleVexel = scaleCellMultiset

||| The canonical zero/empty Vexel.
public export
emptyVexel : Vexel
emptyVexel = BoxLeaf

||| Compresses a Vexel by pruning zero weights.
public export
compressVexel : Vexel -> Vexel
compressVexel v = v


------------------------------------------------------------------------
-- 5. LOGARITHMIC AVL MULTISETTREE CARRIERS (SparseVexel)
------------------------------------------------------------------------

||| 1D Vexel represented as a balanced binary multiset search tree in O(log N).
public export
VexelTree : Type
VexelTree = MultisetTree Unixel

||| Converts a Vexel to a balanced MultisetTree in O(N log N) time.
public export
vexelToTree : Vexel -> MultisetTree Unixel
vexelToTree t =
  foldBoxTreeL (\tree, (u, w) => insertTokenTree u (boxToNat w) tree) Leaf t


||| Converts a MultisetTree back to a Vexel in linear O(N log N) time with zero intermediate lists.
public export
treeToVexel : MultisetTree Unixel -> Vexel
treeToVexel tree =
  MkVexelTree (foldTreeL (\acc, (u, cnt) => if cnt == 0 then acc else setBoxTree u (natToBoxInt cnt) acc) BoxLeaf tree)

||| O(log N) lookup for coordinate unixel in a VexelTree.
public export
lookupUnixelTree : Unixel -> MultisetTree Unixel -> Nat
lookupUnixelTree = lookupTokenTree

||| A SparseVexel is a discrete vector backed by a balanced AVL MultisetTree of Unixels in O(log N).
public export
record SparseVexel where
  constructor MkSparseVexel
  tree : MultisetTree Unixel

public export
Eq SparseVexel where
  (MkSparseVexel t1) == (MkSparseVexel t2) = t1 == t2

public export
Show SparseVexel where
  show (MkSparseVexel t) = "SparseVexel(" ++ show (treeToList t) ++ ")"

||| Adds two SparseVexels using direct multiset tree union.
public export
addSparseVexel : SparseVexel -> SparseVexel -> SparseVexel
addSparseVexel (MkSparseVexel t1) (MkSparseVexel t2) =
  let tMerged = foldTreeL (\acc, (u, cnt) => insertTokenTree u cnt acc) t1 t2
  in MkSparseVexel tMerged

public export
Semigroup SparseVexel where
  (<+>) = addSparseVexel

public export
Monoid SparseVexel where
  neutral = MkSparseVexel Leaf

public export
sparseVexelToVexel : SparseVexel -> Vexel
sparseVexelToVexel (MkSparseVexel t) = treeToVexel t

public export
vexelToSparseVexel : Vexel -> SparseVexel
vexelToSparseVexel v = MkSparseVexel (vexelToTree v)

------------------------------------------------------------------------
-- 6. VEXELN CONVERSION BRIDGES (Provided by CellMultiset)
------------------------------------------------------------------------


public export
vexelNToSparseVexel : {n : Nat} -> VexelN n -> SparseVexel
vexelNToSparseVexel vn = vexelToSparseVexel (vexelNToVexel0 vn)

public export
sparseVexelToVexelN : (n : Nat) -> SparseVexel -> VexelN n
sparseVexelToVexelN n sv = vexelToVexelN n (sparseVexelToVexel sv)

public export
lookupSparseVexel : Unixel -> SparseVexel -> BoxInt
lookupSparseVexel u (MkSparseVexel t) = natToBoxInt (lookupTokenTree u t)


------------------------------------------------------------------------
-- DIMENSION-MULTIPLYING KRONECKER TENSOR OPERATORS (RULE 03 & 2LTT)
------------------------------------------------------------------------

||| Multiplies two Vect BoxInt vectors via Kronecker tensor product: Vect (n * m) BoxInt.
public export
kroneckerVect : {n, m : Nat} -> Vect n BoxInt -> Vect m BoxInt -> Vect (n * m) BoxInt
kroneckerVect u v = concat (map (\x => map (mulBox x) v) u)

||| Kronecker tensor product of two dimension-indexed VexelN vectors: VexelN (n * m).
public export
kroneckerVexelN : {n, m : Nat} -> VexelN n -> VexelN m -> VexelN (n * m)
kroneckerVexelN (MkVexelN u) (MkVexelN v) = MkVexelN (kroneckerVect u v)

||| @deprecated Use canonicalizeCellMultiset directly on CellMultiset trees.
public export
pruneVexelTerms : List (Unixel, BoxInt) -> List (Unixel, BoxInt)
pruneVexelTerms [] = []
pruneVexelTerms ((s, w) :: rest) =
  if boxIsZero w then pruneVexelTerms rest else (s, w) :: pruneVexelTerms rest

||| 🌌 Physics: A Quark Vexel represents the 3 color charges (Red=[1], Green=[2], Blue=[3]) of a Baryon singlet.
public export
nucleonQuarkVexel : Vexel
nucleonQuarkVexel =
  singletonCell (mkCell1 1) (intToBoxInt 1) <+>
  singletonCell (mkCell1 2) (intToBoxInt 1) <+>
  singletonCell (mkCell1 3) (intToBoxInt 1)

------------------------------------------------------------------------
-- POLYNOMIAL BRIDGES: POLYS <-> VEXELS
------------------------------------------------------------------------

||| Converts a univariate Polynumber into a 1D Vexel: sum c_k x^k <=> sum c_k [k].
public export
polynumberToVexel : Polynumber -> Vexel
polynumberToVexel (MkPolynumber cs) =
  let pairs = zipWith (\idx, c => (mkUnixel idx, c)) [0..(length cs)] cs
  in canonicalizeVexel (MkVexel pairs)

||| Converts a 1D Vexel into a univariate Polynumber: sum c_k [k] <=> sum c_k x^k.
public export
vexelToPolynumber : Vexel -> Polynumber
vexelToPolynumber t =
  foldBoxTreeL (\acc, (sing, w) => addPolynumber acc (monomialPolynumber w (unwrapUnixel sing)))
        zeroPolynumber
        t



