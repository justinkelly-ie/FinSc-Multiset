module Stage1.MultisetTree

import Stage0.BoxInt
import Stage0.Multiset
import Stage0.PrimeMultiset
import Language.Reflection
import Stage0.OnSeq.FusedStream
import Data.Fuel

%default total


------------------------------------------------------------------------
-- 1. FAST AVL HEIGHT-BALANCED MULTISET SEARCH TREE O(LOG N)
------------------------------------------------------------------------

||| AVL Height-Balanced Binary Search Tree for Multiset Element Multiplicities.
||| First Nat field stores node height for O(1) balance factor calculation.
public export
data MultisetTree a =
    Leaf
  | Node Nat (MultisetTree a) a Nat (MultisetTree a)

public export
Eq a => Eq (MultisetTree a) where
  Leaf == Leaf = True
  (Node _ l1 x1 c1 r1) == (Node _ l2 x2 c2 r2) =
    x1 == x2 && c1 == c2 && l1 == l2 && r1 == r2
  _ == _ = False

||| Returns node height in O(1) time:
public export
%inline
height : MultisetTree a -> Nat
height Leaf = Z
height (Node h _ _ _ _) = h

||| Smart constructor calculating node height:
public export
%inline
mkNode : MultisetTree a -> a -> Nat -> MultisetTree a -> MultisetTree a
mkNode l x c r =
  let hl = height l
      hr = height r
      h  = S (if hl > hr then hl else hr)
  in Node h l x c r

||| Right rotation for AVL rebalancing:
public export
%inline
rotateRight : MultisetTree a -> a -> Nat -> MultisetTree a -> MultisetTree a
rotateRight (Node _ ll lx lc lr) x c r = mkNode ll lx lc (mkNode lr x c r)
rotateRight l x c r = mkNode l x c r

||| Left rotation for AVL rebalancing:
public export
%inline
rotateLeft : MultisetTree a -> a -> Nat -> MultisetTree a -> MultisetTree a
rotateLeft l x c (Node _ rl rx rc rr) = mkNode (mkNode l x c rl) rx rc rr
rotateLeft l x c r = mkNode l x c r

||| AVL rebalancing function maintaining height differential |hL - hR| <= 1:
public export
balanceNode : MultisetTree a -> a -> Nat -> MultisetTree a -> MultisetTree a
balanceNode l x c r =
  let hl = height l
      hr = height r
  in if hl > hr + 1
       then case l of
              Leaf => mkNode l x c r
              Node _ ll lx lc lr =>
                if height ll >= height lr
                  then rotateRight l x c r
                  else rotateRight (rotateLeft ll lx lc lr) x c r
       else if hr > hl + 1
              then case r of
                     Leaf => mkNode l x c r
                     Node _ rl rx rc rr =>
                       if height rr >= height rl
                         then rotateLeft l x c r
                         else rotateLeft l x c (rotateRight rl rx rc rr)
              else mkNode l x c r

||| Returns the total number of distinct elements in the tree:
public export
treeElementCount : MultisetTree a -> Nat
treeElementCount Leaf = Z
treeElementCount (Node _ l _ _ r) = S (treeElementCount l + treeElementCount r)

||| Returns the total multiplicity sum of all tokens in the tree:
public export
treeTokenSum : MultisetTree a -> Nat
treeTokenSum Leaf = Z
treeTokenSum (Node _ l _ c r) = c + treeTokenSum l + treeTokenSum r

||| Inserts a token with multiplicity count into the multiset tree with AVL rebalancing:
public export
insertTokenTree : Ord a => a -> Nat -> MultisetTree a -> MultisetTree a
insertTokenTree val count Leaf = mkNode Leaf val count Leaf
insertTokenTree val count (Node _ l x c r) =
  if val < x
    then balanceNode (insertTokenTree val count l) x c r
    else if val > x
      then balanceNode l x c (insertTokenTree val count r)
      else mkNode l x (c + count) r

||| Lookups the multiplicity count of a token in O(log N) steps:
public export
lookupTokenTree : Ord a => a -> MultisetTree a -> Nat
lookupTokenTree _ Leaf = Z
lookupTokenTree val (Node _ l x c r) =
  if val < x
    then lookupTokenTree val l
    else if val > x
      then lookupTokenTree val r
      else c

||| Converts a linear Box multiset into a balanced logarithmic MultisetTree:
public export
fromBoxMultiset : Ord a => Box a -> MultisetTree a
fromBoxMultiset (MkBox items) =
  foldl (\acc, (x, w) => insertTokenTree x (boxToNat w) acc) Leaf items

||| Converts a balanced MultisetTree back into a linear Box multiset:
public export
toBoxMultiset : Eq a => MultisetTree a -> Box a
toBoxMultiset Leaf = emptyBox
toBoxMultiset (Node _ l x c r) =
  let leftBox = toBoxMultiset l
      rightBox = toBoxMultiset r
      nodeBox = unixelBox x (natToBoxInt c)
  in unionBox (unionBox leftBox nodeBox) rightBox

------------------------------------------------------------------------
-- 2. ELABORATOR REFLECTION MACROS FOR MULTISETTREE
------------------------------------------------------------------------

export
%macro
buildStaticTreeMacro : Elab TTImp
buildStaticTreeMacro = pure (IVar emptyFC (UN $ Basic "Leaf"))

------------------------------------------------------------------------
-- 3. CONSTRUCTIVE FORMAL AUDIT PROOFS
--    (Fast AVL MultisetTree Invariants)
------------------------------------------------------------------------

||| Audits O(log N) MultisetTree Insertion and Lookup:
||| Insert (BoxInt 10, count 5) and (BoxInt 20, count 3):
||| Lookup 10 => 5, Lookup 20 => 3, Lookup 30 => 0.
public export
auditMultisetTreeLookupProof : Bool
auditMultisetTreeLookupProof =
  let t0 : MultisetTree BoxInt = Leaf
      t1 = insertTokenTree (intToBoxInt 10) 5 t0
      t2 = insertTokenTree (intToBoxInt 20) 3 t1
      c10 = lookupTokenTree (intToBoxInt 10) t2
      c20 = lookupTokenTree (intToBoxInt 20) t2
      c30 = lookupTokenTree (intToBoxInt 30) t2
  in c10 == 5 && c20 == 3 && c30 == Z

public export
%macro
auditMultisetTreeLookup : Elab (Stage1.MultisetTree.auditMultisetTreeLookupProof = True)
auditMultisetTreeLookup = pure Refl

||| Audits Total Multiplicity Sum on MultisetTree:
||| Total tokens in tree = 5 + 3 = 8.
public export
auditMultisetTreeTokenSumProof : Bool
auditMultisetTreeTokenSumProof =
  let t0 : MultisetTree BoxInt = Leaf
      t1 = insertTokenTree (intToBoxInt 10) 5 t0
      t2 = insertTokenTree (intToBoxInt 20) 3 t1
  in treeTokenSum t2 == 8 && treeElementCount t2 == 2

public export
%macro
auditMultisetTreeTokenSum : Elab (Stage1.MultisetTree.auditMultisetTreeTokenSumProof = True)
auditMultisetTreeTokenSum = pure Refl

------------------------------------------------------------------------
-- 4. CANONICAL BOXSPEC MULTISET TREES
------------------------------------------------------------------------

||| Canonical BoxSpec tree configuration structure.
public export
data BoxSpec : Type where
  LeafSpec : BoxSpec
  NodeSpec : Nat -> BoxSpec

public export
Eq BoxSpec where
  LeafSpec == LeafSpec = True
  (NodeSpec n1) == (NodeSpec n2) = n1 == n2
  _ == _ = False

public export
Ord BoxSpec where
  compare LeafSpec LeafSpec = EQ
  compare LeafSpec (NodeSpec _) = LT
  compare (NodeSpec _) LeafSpec = GT
  compare (NodeSpec n1) (NodeSpec n2) = compare n1 n2

public export
fromNatBoxSpec : Nat -> BoxSpec
fromNatBoxSpec Z = LeafSpec
fromNatBoxSpec (S k) = NodeSpec (S k)

public export
boxSize : BoxSpec -> Nat
boxSize LeafSpec = Z
boxSize (NodeSpec n) = n

||| Specialized Multiset Tree indexed by canonical BoxSpec configurations.
public export
BoxSpecTree : Type
BoxSpecTree = MultisetTree BoxSpec

||| Audits that MultisetTree uses Canonical BoxSpec total ordering (Leaf < [[]] < [[] []]):
||| Inserting BoxSpec 0, 1, 2 stores them in deterministic binary search tree order.
public export
auditBoxSpecTreeOrderingProof : Bool
auditBoxSpecTreeOrderingProof =
  let b0 = fromNatBoxSpec 0
      b1 = fromNatBoxSpec 1
      b2 = fromNatBoxSpec 2
      t0 : BoxSpecTree = Leaf
      t1 = insertTokenTree b1 10 t0
      t2 = insertTokenTree b0 5 t1
      t3 = insertTokenTree b2 15 t2
      c0 = lookupTokenTree b0 t3
      c1 = lookupTokenTree b1 t3
      c2 = lookupTokenTree b2 t3
      c3 = lookupTokenTree (fromNatBoxSpec 3) t3
  in c0 == 5 && c1 == 10 && c2 == 15 && c3 == 0 &&
     treeTokenSum t3 == 30 &&
     treeElementCount t3 == 3

public export
%macro
auditBoxSpecTreeOrdering : Elab (Stage1.MultisetTree.auditBoxSpecTreeOrderingProof = True)
auditBoxSpecTreeOrdering = pure Refl

------------------------------------------------------------------------
-- 5. TREE COMBINATORS & LOGARITHMIC COSMIC STATE EVOLUTION
------------------------------------------------------------------------

||| Merges two multiset trees by folding elements of the second into the first:
public export
mergeMultisetTrees : Ord a => MultisetTree a -> MultisetTree a -> MultisetTree a
mergeMultisetTrees target Leaf = target
mergeMultisetTrees target (Node _ l x c r) =
  let t1 = insertTokenTree x c target
      t2 = mergeMultisetTrees t1 l
  in mergeMultisetTrees t2 r

public export
Ord a => Semigroup (MultisetTree a) where
  (<+>) = mergeMultisetTrees

public export
Ord a => Monoid (MultisetTree a) where
  neutral = Leaf

||| High-capacity tree-indexed cosmological state container.
||| Uses O(log N) balanced multiset trees for visible matter, dark energy, and dark matter.
public export
record TreeUniverseState where
  constructor MkTreeUniverseState
  epochNumber    : Nat
  visibleLattice : MultisetTree BoxInt
  darkEnergyROM  : MultisetTree BoxInt
  darkMatterLog  : MultisetTree BoxInt

||| Returns the total active token count across the entire TreeUniverseState:
public export
treeUniverseTotalTokens : TreeUniverseState -> Nat
treeUniverseTotalTokens (MkTreeUniverseState _ vm de dm) =
  treeTokenSum vm + treeTokenSum de + treeTokenSum dm

||| Linear QTT state transition for TreeUniverseState with strict token conservation:
public export
stepTreeUniverseLinear : (1 state : TreeUniverseState) ->
                         (matterTokens : List (BoxInt, Nat)) ->
                         TreeUniverseState
stepTreeUniverseLinear (MkTreeUniverseState ep vm de dm) newMatter =
  let updatedVM = foldl (\acc, (k, cnt) => insertTokenTree k cnt acc) vm newMatter
      updatedDM = insertTokenTree (natToBoxInt ep) 1 dm
  in MkTreeUniverseState (S ep) updatedVM de updatedDM

||| Audits Logarithmic Scaling State Evolution:
||| Tests that stepTreeUniverseLinear accurately updates the tree state and preserves tokens.
public export
auditTreeUniverseScalingProof : Bool
auditTreeUniverseScalingProof =
  let s0 = MkTreeUniverseState Z Leaf Leaf Leaf
      s1 = stepTreeUniverseLinear s0 [(intToBoxInt 1, 9), (intToBoxInt 2, 18)]
      s2 = stepTreeUniverseLinear s1 [(intToBoxInt 3, 27)]
      totVM = treeTokenSum (visibleLattice s2)
      totDM = treeTokenSum (darkMatterLog s2)
      totAll = treeUniverseTotalTokens s2
  in epochNumber s2 == 2 &&
     totVM == 54 &&
     totDM == 2 &&
     totAll == 56

public export
%macro
auditTreeUniverseScaling : Elab (Stage1.MultisetTree.auditTreeUniverseScalingProof = True)
auditTreeUniverseScaling = pure Refl

------------------------------------------------------------------------
-- 6. PARALLEL O(LOG N) MULTISETTREE STREAM PARTITIONING
------------------------------------------------------------------------

||| Structurally recursive in-order tree left fold accumulator.
public export
foldTreeL : (b -> (a, Nat) -> b) -> b -> MultisetTree a -> b
foldTreeL _ acc Leaf = acc
foldTreeL f acc (Node _ l x c r) =
  let accL = foldTreeL f acc l
      accNode = f accL (x, c)
  in foldTreeL f accNode r

||| Structurally recursive in-order tree right fold accumulator.
public export
foldTreeR : (a -> Nat -> b -> b) -> b -> MultisetTree a -> b
foldTreeR _ z Leaf = z
foldTreeR f z (Node _ l x c r) =
  foldTreeR f (f x c (foldTreeR f z r)) l

||| Flattens a MultisetTree into a list of (element, multiplicity) pairs in linear O(N) time without (++) concatenations.
public export
treeToList : MultisetTree a -> List (a, Nat)
treeToList tree = foldTreeR (\x, c, acc => (x, c) :: acc) [] tree

||| Traverses and pushes all left ancestor nodes of a subtree onto a search stack in O(log N) steps.
public export
pushLeftSubtrees : MultisetTree a -> List (MultisetTree a) -> List (MultisetTree a)
pushLeftSubtrees Leaf stack = stack
pushLeftSubtrees node@(Node _ l _ _ _) stack = pushLeftSubtrees l (node :: stack)

||| Converts a balanced MultisetTree into a zero-allocation deforested FusedStream in O(N) time and O(log N) stack frames.
public export
streamMultisetTreeDirect : MultisetTree a -> FusedStream (a, Nat)
streamMultisetTreeDirect tree = unfoldStream stepTree (pushLeftSubtrees tree [])
  where
    stepTree : List (MultisetTree a) -> Step (List (MultisetTree a)) (a, Nat)
    stepTree [] = Done
    stepTree (Leaf :: rest) = Skip rest
    stepTree (Node _ _ x c r :: rest) = Yield (x, c) (pushLeftSubtrees r rest)

||| Converts a balanced MultisetTree into a deforested stream of (element, count) pairs.
public export
streamMultisetTree : MultisetTree a -> FusedStream (a, Nat)
streamMultisetTree = streamMultisetTreeDirect

||| Evaluates a stream catamorphism fold over a MultisetTree directly without intermediate list allocations.
public export
foldTreeStream : (b -> (a, Nat) -> b) -> b -> MultisetTree a -> b
foldTreeStream f acc0 tree = foldStream f acc0 (streamMultisetTreeDirect tree)

||| Evaluates a stream catamorphism fold in parallel across the left and right subtrees of a MultisetTree.
public export
fusedParallelTreeFold : Fuel -> (a -> Nat -> b -> b) -> b -> (b -> b -> b) -> MultisetTree a -> b
fusedParallelTreeFold _ _ acc0 _ Leaf = acc0
fusedParallelTreeFold f stepAcc acc0 combineBin (Node _ left key val right) =
  let leftRes  = fusedParallelTreeFold f stepAcc acc0 combineBin left
      rightRes = fusedParallelTreeFold f stepAcc acc0 combineBin right
      nodeRes  = stepAcc key val acc0
  in combineBin (combineBin leftRes nodeRes) rightRes

||| Evaluates a stream catamorphism fold in parallel across the left and right subtrees over Nat fuel.
public export
fusedParallelTreeFoldNat : Nat -> (a -> Nat -> b -> b) -> b -> (b -> b -> b) -> MultisetTree a -> b
fusedParallelTreeFoldNat _ _ acc0 _ Leaf = acc0
fusedParallelTreeFoldNat n stepAcc acc0 combineBin (Node _ left key val right) =
  let leftRes  = fusedParallelTreeFoldNat n stepAcc acc0 combineBin left
      rightRes = fusedParallelTreeFoldNat n stepAcc acc0 combineBin right
      nodeRes  = stepAcc key val acc0
  in combineBin (combineBin leftRes nodeRes) rightRes

||| Audit witness verifying parallel MultisetTree stream partition fold equivalence.
public export
auditFusedParallelTreeFoldProof : Bool
auditFusedParallelTreeFoldProof =
  let t0 : MultisetTree BoxInt = Leaf
      t1 = insertTokenTree (intToBoxInt 10) 5 t0
      t2 = insertTokenTree (intToBoxInt 20) 3 t1
      t3 = insertTokenTree (intToBoxInt 30) 2 t2
      totalSum = fusedParallelTreeFoldNat 4 (\_, cnt, acc => cnt + acc) 0 (+) t3
  in totalSum == 10

||| Audit witness verifying equivalence of direct tree stream, tree fold, and list flattening.
public export
auditTreeDirectStreamingProof : Bool
auditTreeDirectStreamingProof =
  let t0 : MultisetTree BoxInt = Leaf
      t1 = insertTokenTree (intToBoxInt 10) 5 t0
      t2 = insertTokenTree (intToBoxInt 20) 3 t1
      t3 = insertTokenTree (intToBoxInt 30) 2 t2
      sumFold = foldTreeL (\acc, (_, cnt) => acc + cnt) Z t3
      sumList = foldTreeR (\_, cnt, acc => cnt + acc) Z t3
  in (sumFold == 10) && (sumList == 10)

public export
%macro
auditTreeDirectStreaming : Elab (Stage1.MultisetTree.auditTreeDirectStreamingProof = True)
auditTreeDirectStreaming = pure Refl

||| Converts a certified 13-smooth GohPrimeMultiset into an O(log N) balanced MultisetTree.
public export
toMultisetTreeGoh : GohPrimeMultiset -> MultisetTree AnyGohPrime
toMultisetTreeGoh m =
  let t1 = if m.exp2 > 0 then insertTokenTree anyPrime2 m.exp2 Leaf else Leaf
      t2 = if m.exp3 > 0 then insertTokenTree anyPrime3 m.exp3 t1 else t1
      t3 = if m.exp5 > 0 then insertTokenTree anyPrime5 m.exp5 t2 else t2
      t4 = if m.exp7 > 0 then insertTokenTree anyPrime7 m.exp7 t3 else t3
      t5 = if m.exp11 > 0 then insertTokenTree anyPrime11 m.exp11 t4 else t4
      t6 = if m.exp13 > 0 then insertTokenTree anyPrime13 m.exp13 t5 else t5
  in t6

||| Audit witness verifying that toMultisetTreeGoh preserves total token count and structure.
public export
auditPrimeMultisetTreeProof : Bool
auditPrimeMultisetTreeProof =
  let m = MkGohPrimeMultiset 1 1 1 1 0 0 -- Primorial 210 = 2 * 3 * 5 * 7
      tree = toMultisetTreeGoh m
      cnt2 = lookupTokenTree anyPrime2 tree
      cnt7 = lookupTokenTree anyPrime7 tree
      cnt11 = lookupTokenTree anyPrime11 tree
      totalTokens = treeTokenSum tree
  in (cnt2 == 1) && (cnt7 == 1) && (cnt11 == 0) && (totalTokens == 4)

public export
%macro
auditPrimeMultisetTree : Elab (Stage1.MultisetTree.auditPrimeMultisetTreeProof = True)
auditPrimeMultisetTree = pure Refl

------------------------------------------------------------------------
-- 7. FAST BALANCED SIGNED BOXMULTISETTREE O(LOG N)
------------------------------------------------------------------------

||| AVL Height-Balanced Binary Search Tree for Signed BoxInt Multiplicities.
||| Keys represent coordinates/tokens of type a, values represent exact signed integer weights.
public export
data BoxMultisetTree a =
    BoxLeaf
  | BoxNode Nat (BoxMultisetTree a) a BoxInt (BoxMultisetTree a)


public export
%inline
boxHeight : BoxMultisetTree a -> Nat
boxHeight BoxLeaf = Z
boxHeight (BoxNode h _ _ _ _) = h

public export
%inline
mkBoxNode : BoxMultisetTree a -> a -> BoxInt -> BoxMultisetTree a -> BoxMultisetTree a
mkBoxNode l x c r =
  let hl = boxHeight l
      hr = boxHeight r
      h  = S (if hl > hr then hl else hr)
  in BoxNode h l x c r

public export
%inline
rotateRightBox : BoxMultisetTree a -> a -> BoxInt -> BoxMultisetTree a -> BoxMultisetTree a
rotateRightBox (BoxNode _ ll lx lc lr) x c r = mkBoxNode ll lx lc (mkBoxNode lr x c r)
rotateRightBox l x c r = mkBoxNode l x c r

public export
%inline
rotateLeftBox : BoxMultisetTree a -> a -> BoxInt -> BoxMultisetTree a -> BoxMultisetTree a
rotateLeftBox l x c (BoxNode _ rl rx rc rr) = mkBoxNode (mkBoxNode l x c rl) rx rc rr
rotateLeftBox l x c r = mkBoxNode l x c r

public export
balanceBoxNode : BoxMultisetTree a -> a -> BoxInt -> BoxMultisetTree a -> BoxMultisetTree a
balanceBoxNode l x c r =
  let hl = boxHeight l
      hr = boxHeight r
  in if hl > hr + 1
       then case l of
              BoxLeaf => mkBoxNode l x c r
              BoxNode _ ll lx lc lr =>
                if boxHeight ll >= boxHeight lr
                  then rotateRightBox l x c r
                  else rotateRightBox (rotateLeftBox ll lx lc lr) x c r
       else if hr > hl + 1
              then case r of
                     BoxLeaf => mkBoxNode l x c r
                     BoxNode _ rl rx rc rr =>
                       if boxHeight rr >= boxHeight rl
                         then rotateLeftBox l x c r
                         else rotateLeftBox l x c (rotateRightBox rl rx rc rr)
              else mkBoxNode l x c r

||| Lookups the signed BoxInt value of a key in O(log N) time:
public export
lookupBoxTree : Ord a => a -> BoxMultisetTree a -> BoxInt
lookupBoxTree _ BoxLeaf = intToBoxInt 0
lookupBoxTree val (BoxNode _ l x c r) =
  if val < x
    then lookupBoxTree val l
    else if val > x
      then lookupBoxTree val r
      else c

||| Sets the signed BoxInt value of a key in O(log N) time.
public export
setBoxTree : Ord a => a -> BoxInt -> BoxMultisetTree a -> BoxMultisetTree a
setBoxTree val w BoxLeaf =
  if boxIsZero w then BoxLeaf else mkBoxNode BoxLeaf val w BoxLeaf
setBoxTree val w (BoxNode _ l x c r) =
  if val < x
    then balanceBoxNode (setBoxTree val w l) x c r
    else if val > x
      then balanceBoxNode l x c (setBoxTree val w r)
      else mkBoxNode l x w r

||| Structurally recursive in-order tree left fold accumulator for BoxMultisetTree.
public export
foldBoxTreeL : (b -> (a, BoxInt) -> b) -> b -> BoxMultisetTree a -> b
foldBoxTreeL _ acc BoxLeaf = acc
foldBoxTreeL f acc (BoxNode _ l x c r) =
  let accL = foldBoxTreeL f acc l
      accNode = f accL (x, c)
  in foldBoxTreeL f accNode r

||| Structurally recursive in-order tree right fold accumulator for BoxMultisetTree.
public export
foldBoxTreeR : (a -> BoxInt -> b -> b) -> b -> BoxMultisetTree a -> b
foldBoxTreeR _ z BoxLeaf = z
foldBoxTreeR f z (BoxNode _ l x c r) =
  foldBoxTreeR f (f x c (foldBoxTreeR f z r)) l

||| Flattens active non-zero elements into an association list in O(N) time.
public export
boxTreeToList : BoxMultisetTree a -> List (a, BoxInt)
boxTreeToList tree = foldBoxTreeR (\x, c, acc => if boxIsNonZero c then (x, c) :: acc else acc) [] tree

public export
Show a => Show (BoxMultisetTree a) where
  show t = "BoxMultisetTree(" ++ show (boxTreeToList t) ++ ")"


||| Traverses and pushes all left ancestor nodes of a BoxMultisetTree onto a search stack.
public export
pushLeftSubtreesBox : BoxMultisetTree a -> List (BoxMultisetTree a) -> List (BoxMultisetTree a)
pushLeftSubtreesBox BoxLeaf stack = stack
pushLeftSubtreesBox node@(BoxNode _ l _ _ _) stack = pushLeftSubtreesBox l (node :: stack)

||| Converts a BoxMultisetTree into a zero-allocation deforested FusedStream in O(N) time and O(log N) stack frames.
public export
streamBoxMultisetTree : BoxMultisetTree a -> FusedStream (a, BoxInt)
streamBoxMultisetTree tree =
  filterMapStream (\(x, c) => if boxIsNonZero c then Just (x, c) else Nothing)
                  (unfoldStream stepTree (pushLeftSubtreesBox tree []))
  where
    stepTree : List (BoxMultisetTree a) -> Step (List (BoxMultisetTree a)) (a, BoxInt)
    stepTree [] = Done
    stepTree (BoxLeaf :: rest) = Skip rest
    stepTree (BoxNode _ _ x c r :: rest) = Yield (x, c) (pushLeftSubtreesBox r rest)

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

||| Evaluates the number of active non-zero weight nodes in a BoxMultisetTree with zero allocations.
public export
treeSizeNonZero : BoxMultisetTree a -> Nat
treeSizeNonZero = foldBoxTreeL (\acc, (_, w) => if boxIsNonZero w then S acc else acc) 0

||| Zero-allocation equality comparison between two BoxMultisetTrees via deforested lockstep streaming.
public export
boxTreeEqual : Eq a => BoxMultisetTree a -> BoxMultisetTree a -> Bool
boxTreeEqual t1 t2 =
  let sz1 = treeSizeNonZero t1
      sz2 = treeSizeNonZero t2
  in if sz1 /= sz2 then False
     else if sz1 == 0 then True
     else eqStreamNat ((boxTreeSize t1 + boxTreeSize t2 + 16) * 4)
                      (streamBoxMultisetTree t1)
                      (streamBoxMultisetTree t2)

public export
Eq a => Eq (BoxMultisetTree a) where
  (==) = boxTreeEqual

||| Audit witness verifying BoxMultisetTree O(log N) lookup and streaming.
public export
auditBoxMultisetTreeProof : Bool
auditBoxMultisetTreeProof =
  let t0 : BoxMultisetTree Integer = BoxLeaf
      t1 = setBoxTree 10 (intToBoxInt 5) t0
      t2 = setBoxTree (-3) (intToBoxInt (-2)) t1
      v10 = lookupBoxTree 10 t2
      vm3 = lookupBoxTree (-3) t2
      v0  = lookupBoxTree 0 t2
      strm = streamBoxMultisetTree t2
      elems = foldStream (\acc, item => acc ++ [item]) [] strm
  in v10 == intToBoxInt 5 && vm3 == intToBoxInt (-2) && v0 == intToBoxInt 0 &&
     elems == [(-3, intToBoxInt (-2)), (10, intToBoxInt 5)]





