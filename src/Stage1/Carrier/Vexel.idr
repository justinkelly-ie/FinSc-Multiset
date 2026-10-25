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
-- 1. AVL MULTISET TREE UTILITIES FOR CARRIERS
------------------------------------------------------------------------

||| Maps a function over all non-zero weights in a BoxMultisetTree, preserving AVL balance and key order.
public export
mapBoxTreeWeight : (BoxInt -> BoxInt) -> BoxMultisetTree a -> BoxMultisetTree a
mapBoxTreeWeight _ BoxLeaf = BoxLeaf
mapBoxTreeWeight f (BoxNode h l x c r) = BoxNode h (mapBoxTreeWeight f l) x (f c) (mapBoxTreeWeight f r)

||| Evaluates the total number of coordinate nodes in a BoxMultisetTree.
public export
boxTreeSize : BoxMultisetTree a -> Nat
boxTreeSize BoxLeaf = 0
boxTreeSize (BoxNode _ l _ _ r) = S (boxTreeSize l + boxTreeSize r)

------------------------------------------------------------------------
-- 2. VEXEL (1D WILDBERGER VECTOR MULTISET)
------------------------------------------------------------------------

||| A Vexel is a multiset of Singletons (Wildberger Vector).
||| Stored as an AVL BoxMultisetTree of weighted basis Singletons in O(log N).
public export
record Vexel where
  constructor MkVexelTree
  tree : BoxMultisetTree Unixel

||| Canonical unambiguous alias for discrete monomorphic 1D Wildberger vectors.
public export
DiscreteVexel : Type
DiscreteVexel = Vexel

||| Direct conversion of a list of Unixel-BoxInt pairs to a signed AVL BoxMultisetTree in O(N log N).
||| Prunes zero weights and collapses duplicate Unixels.
public export
vexelListToBoxTree : List (Unixel, BoxInt) -> BoxMultisetTree Unixel
vexelListToBoxTree terms =
  foldl (\t, (u, w) =>
          if boxIsZero w then t
          else let cur = lookupBoxTree u t
                   newW = cur + w
               in if boxIsZero newW
                    then setBoxTree u (intToBoxInt 0) t
                    else setBoxTree u newW t)
        BoxLeaf
        terms

||| Constructs a canonical Vexel from a list of Unixel-BoxInt pairs in O(N log N).
public export
mkVexel : List (Unixel, BoxInt) -> Vexel
mkVexel terms = MkVexelTree (vexelListToBoxTree terms)

||| Canonical constructor alias for Vexel from coordinate pairs.
public export
MkVexel : List (Unixel, BoxInt) -> Vexel
MkVexel = mkVexel

||| Flattens a Vexel to an association list in O(N) time.
public export
vexelTerms : Vexel -> List (Unixel, BoxInt)
vexelTerms (MkVexelTree t) = boxTreeToList t

||| Projection view of Vexel terms.
public export
terms : Vexel -> List (Unixel, BoxInt)
terms = vexelTerms

||| Direct conversion of a Vexel to a signed AVL BoxMultisetTree in O(1).
public export
vexelToBoxTree : Vexel -> BoxMultisetTree Unixel
vexelToBoxTree (MkVexelTree t) = t

||| Reconstructs a Vexel from a signed AVL BoxMultisetTree in O(1).
public export
boxTreeToVexel : BoxMultisetTree Unixel -> Vexel
boxTreeToVexel = MkVexelTree

||| Canonicalize a Vexel via legacy Multiset linked list.
public export
canonicalizeVexelMultiset : Vexel -> Vexel
canonicalizeVexelMultiset (MkVexelTree t) =
  MkVexelTree (vexelListToBoxTree (multisetToList (fromListBox (boxTreeToList t))))

||| Identity for tree-backed Vexels: AVL tree guarantees canonical representation by construction.
public export
canonicalizeVexel : Vexel -> Vexel
canonicalizeVexel v = v

public export
vexelToMultiset : Vexel -> Multiset BoxInt Unixel
vexelToMultiset (MkVexelTree t) = fromListBox (boxTreeToList t)

public export
multisetToVexel : Multiset BoxInt Unixel -> Vexel
multisetToVexel m = MkVexel (multisetToList m)

public export
Eq Vexel where
  (MkVexelTree t1) == (MkVexelTree t2) = boxTreeToList t1 == boxTreeToList t2

public export
Show Vexel where
  show (MkVexelTree t) = "Vexel(" ++ show (boxTreeToList t) ++ ")"

------------------------------------------------------------------------
-- 3. DIMENSION-INDEXED TYPED VEXEL (VexelN)
------------------------------------------------------------------------

||| A VexelN is a dimension-indexed discrete vector of dimension `n`,
||| holding `n` BoxInt scalar weights for unrolled 2LTT staging.
public export
record VexelN (n : Nat) where
  constructor MkVexelN
  components : Vect n BoxInt

public export
Eq (VexelN n) where
  (MkVexelN v1) == (MkVexelN v2) = v1 == v2

public export
{n : Nat} -> Show (VexelN n) where
  show (MkVexelN v) = "Vexel" ++ show n ++ "(" ++ show v ++ ")"

||| Constructor for 2-dimensional VexelN (single qubit state vector).
public export
mkVexel2 : BoxInt -> BoxInt -> VexelN 2
mkVexel2 v0 v1 = MkVexelN [v0, v1]

||| Constructor for 4-dimensional VexelN (two-qubit state vector).
public export
mkVexel4 : BoxInt -> BoxInt -> BoxInt -> BoxInt -> VexelN 4
mkVexel4 v0 v1 v2 v3 = MkVexelN [v0, v1, v2, v3]

------------------------------------------------------------------------
-- 4. POINT LOOKUP, TOTAL MASS & ALGEBRAIC OPERATIONS
------------------------------------------------------------------------

||| Lookups the signed BoxInt weight of a basis Unixel in O(log N) time.
public export
lookupUnixel : Unixel -> Vexel -> BoxInt
lookupUnixel u (MkVexelTree t) = lookupBoxTree u t

||| Computes the total integer mass of a Vexel vector via in-order tree fold in O(N).
public export
totalVexelMass : Vexel -> BoxInt
totalVexelMass (MkVexelTree t) =
  foldBoxTreeL (\acc, (_, w) => acc + w) (intToBoxInt 0) t

||| Alias for total mass of a Vexel vector.
public export
totalVexelWeight : Vexel -> BoxInt
totalVexelWeight = totalVexelMass

||| Adds two Vexels and consolidates duplicate coordinates directly via BoxMultisetTree in O(N log N).
public export
addVexel : Vexel -> Vexel -> Vexel
addVexel (MkVexelTree t1) (MkVexelTree t2) =
  let tMerged = foldBoxTreeL (\tree, (u, w) =>
                  let cur = lookupBoxTree u tree
                      newW = cur + w
                  in if boxIsZero newW
                       then setBoxTree u (intToBoxInt 0) tree
                       else setBoxTree u newW tree)
                  t1
                  t2
  in MkVexelTree tMerged

public export
Semigroup Vexel where
  (<+>) = addVexel

public export
Monoid Vexel where
  neutral = MkVexelTree BoxLeaf

public export
Num Vexel where
  (+) = addVexel
  (*) v1 v2 = MkVexelTree BoxLeaf
  fromInteger n = mkVexel [(MkUnixel 0, intToBoxInt n)]

||| Subtracts two Vexels and consolidates duplicate coordinates directly via BoxMultisetTree in O(N log N).
public export
subVexel : Vexel -> Vexel -> Vexel
subVexel (MkVexelTree t1) (MkVexelTree t2) =
  let tMerged = foldBoxTreeL (\tree, (u, w) =>
                  let cur = lookupBoxTree u tree
                      newW = cur - w
                  in if boxIsZero newW
                       then setBoxTree u (intToBoxInt 0) tree
                       else setBoxTree u newW tree)
                  t1
                  t2
  in MkVexelTree tMerged

public export
Neg Vexel where
  negate (MkVexelTree t) = MkVexelTree (mapBoxTreeWeight negate t)
  (-) = subVexel

||| Scales a Vexel by a BoxInt scalar, pruning zero weights.
public export
scaleVexel : BoxInt -> Vexel -> Vexel
scaleVexel s (MkVexelTree t) =
  if boxIsZero s
    then MkVexelTree BoxLeaf
    else MkVexelTree (mapBoxTreeWeight (s *) t)

||| Evaluates the standard Euclidean inner product between two Vexels directly via BoxMultisetTree in O(N log N).
public export
dotVexel : Vexel -> Vexel -> BoxInt
dotVexel (MkVexelTree t1) v2 =
  foldBoxTreeL (\acc, (u, w1) =>
    let w2 = lookupUnixel u v2
    in acc + (w1 * w2))
    (intToBoxInt 0)
    t1

||| The canonical zero/empty Vexel.
public export
emptyVexel : Vexel
emptyVexel = MkVexelTree BoxLeaf

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
vexelToTree (MkVexelTree t) =
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
-- 6. VEXELN CONVERSION BRIDGES
------------------------------------------------------------------------

vectToUnixelPairsHelper : Nat -> Vect k BoxInt -> List (Unixel, BoxInt)
vectToUnixelPairsHelper _ [] = []
vectToUnixelPairsHelper idx (w :: ws) = (MkUnixel idx, w) :: vectToUnixelPairsHelper (S idx) ws

||| Converts a dimension-indexed VexelN into a canonical sparse multiset Vexel (1-indexed).
public export
vexelNToVexel : {n : Nat} -> VexelN n -> Vexel
vexelNToVexel (MkVexelN comps) = canonicalizeVexel (MkVexel (vectToUnixelPairsHelper 1 comps))

||| Converts a dimension-indexed VexelN into a 0-indexed sparse multiset Vexel (quantum basis).
public export
vexelNToVexel0 : {n : Nat} -> VexelN n -> Vexel
vexelNToVexel0 (MkVexelN comps) = canonicalizeVexel (MkVexel (vectToUnixelPairsHelper 0 comps))

||| Converts a sparse multiset Vexel into a dimension-indexed VexelN (0-indexed).
public export
vexelToVexelN : (n : Nat) -> Vexel -> VexelN n
vexelToVexelN n v =
  MkVexelN (generateComponents 0 n)
  where
    generateComponents : Nat -> (k : Nat) -> Vect k BoxInt
    generateComponents _ Z = []
    generateComponents idx (S rem) =
      let w = lookupUnixel (MkUnixel idx) v
      in w :: generateComponents (S idx) rem

||| Converts a sparse multiset Vexel into a dimension-indexed VexelN (1-indexed).
public export
vexelToVexelN1 : (n : Nat) -> Vexel -> VexelN n
vexelToVexelN1 n v =
  MkVexelN (generateComponents 1 n)
  where
    generateComponents : Nat -> (k : Nat) -> Vect k BoxInt
    generateComponents _ Z = []
    generateComponents idx (S rem) =
      let w = lookupUnixel (MkUnixel idx) v
      in w :: generateComponents (S idx) rem

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

public export
pruneVexelTerms : List (Unixel, BoxInt) -> List (Unixel, BoxInt)
pruneVexelTerms [] = []
pruneVexelTerms ((s, w) :: rest) =
  if boxIsZero w then pruneVexelTerms rest else (s, w) :: pruneVexelTerms rest

||| 🌌 Physics: A Quark Vexel represents the 3 color charges (Red=[1], Green=[2], Blue=[3]) of a Baryon singlet.
public export
nucleonQuarkVexel : Vexel
nucleonQuarkVexel =
  MkVexel [ (MkUnixel 1, intToBoxInt 1)
          , (MkUnixel 2, intToBoxInt 1)
          , (MkUnixel 3, intToBoxInt 1)
          ]

------------------------------------------------------------------------
-- POLYNOMIAL BRIDGES: POLYS <-> VEXELS
------------------------------------------------------------------------

||| Converts a univariate Polynumber into a 1D Vexel: sum c_k x^k <=> sum c_k [k].
public export
polynumberToVexel : Polynumber -> Vexel
polynumberToVexel (MkPolynumber cs) =
  let pairs = zipWith (\idx, c => (MkUnixel idx, c)) [0..(length cs)] cs
  in canonicalizeVexel (MkVexel pairs)

||| Converts a 1D Vexel into a univariate Polynumber: sum c_k [k] <=> sum c_k x^k.
public export
vexelToPolynumber : Vexel -> Polynumber
vexelToPolynumber (MkVexelTree t) =
  foldBoxTreeL (\acc, (sing, w) => addPolynumber acc (monomialPolynumber w (index sing)))
        zeroPolynumber
        t


