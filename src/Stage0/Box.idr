module Stage0.Box

import Data.List
import public Stage0.BoxInt
import public Stage0.Interfaces

%default total

------------------------------------------------------------------------
-- 1. CANONICAL HEIGHT-CACHED AVL BOX CONTAINER (`Box c k`)
------------------------------------------------------------------------

||| Canonical coordinate-indexed multiset carrier (`Box c k`) backed by an
||| O(log N) height-cached AVL binary search tree mapping keys `k` to
||| multiplicity weights `c` (typically `BoxInt`, `SignedBit`, or `MultisetBit`).
public export
data Box : (c : Type) -> (k : Type) -> Type where
  BoxLeaf : Box c k
  BoxNode : (height : Nat) -> (left : Box c k) -> (key : k) -> (weight : c) -> (right : Box c k) -> Box c k

||| O(1) cached AVL height accessor.
public export
boxHeight : Box c k -> Nat
boxHeight BoxLeaf              = Z
boxHeight (BoxNode h _ _ _ _)  = h

||| Exact structural node count (non-zero entry bound) for `GohFuel` and zipper termination.
public export
boxNodeCount : Box c k -> Nat
boxNodeCount BoxLeaf             = Z
boxNodeCount (BoxNode _ l _ _ r) = S (boxNodeCount l + boxNodeCount r)

||| Alias for total node count in a `Box c k`.
public export
boxTreeSize : Box c k -> Nat
boxTreeSize = boxNodeCount

||| Exponential height upper bound `2^h` for AVL capacity fuel.
public export
pow2BoxBound : Nat -> Nat
pow2BoxBound Z     = 1
pow2BoxBound (S k) =
  let p = pow2BoxBound k
  in p + p

||| O(h) = O(log N) AVL node capacity upper bound derived from cached root height `h`: `2^h - 1`.
public export
boxTreeCapacityBound : Box c k -> Nat
boxTreeCapacityBound BoxLeaf             = Z
boxTreeCapacityBound (BoxNode h _ _ _ _) = minus (pow2BoxBound h) 1

||| Construct an AVL node recomputing cached height in O(1).
public export
mkBoxNode : Box c k -> k -> c -> Box c k -> Box c k
mkBoxNode l k w r =
  let hl = boxHeight l
      hr = boxHeight r
  in BoxNode (S (if hl >= hr then hl else hr)) l k w r

------------------------------------------------------------------------
-- 2. AVL ROTATIONS, BALANCING & DELETION
------------------------------------------------------------------------

||| Single right rotation preserving in-order key ordering.
public export
rotateRightBox : Box c k -> k -> c -> Box c k -> Box c k
rotateRightBox (BoxNode _ ll lx lc lr) x c r = mkBoxNode ll lx lc (mkBoxNode lr x c r)
rotateRightBox l                       x c r = mkBoxNode l x c r

||| Single left rotation preserving in-order key ordering.
public export
rotateLeftBox : Box c k -> k -> c -> Box c k -> Box c k
rotateLeftBox l x c (BoxNode _ rl rx rc rr) = mkBoxNode (mkBoxNode l x c rl) rx rc rr
rotateLeftBox l x c r                       = mkBoxNode l x c r

||| AVL height-rebalancing constructor (`balanceBoxNode` / `balanceBox`).
public export
balanceBoxNode : Box c k -> k -> c -> Box c k -> Box c k
balanceBoxNode l x c r =
  let hl = boxHeight l
      hr = boxHeight r
  in if hl > hr + 1 then
       case l of
         BoxLeaf => mkBoxNode l x c r
         BoxNode _ ll lx lc lr =>
           if boxHeight ll >= boxHeight lr
             then rotateRightBox l x c r
             else rotateRightBox (rotateLeftBox ll lx lc lr) x c r
     else if hr > hl + 1 then
       case r of
         BoxLeaf => mkBoxNode l x c r
         BoxNode _ rl rx rc rr =>
           if boxHeight rr >= boxHeight rl
             then rotateLeftBox l x c r
             else rotateLeftBox l x c (rotateRightBox rl rx rc rr)
     else
       mkBoxNode l x c r

||| Canonical AVL rebalance alias.
public export
balanceBox : Box c k -> k -> c -> Box c k -> Box c k
balanceBox = balanceBoxNode

||| Extracts and removes the minimum-key entry of a non-empty `Box c k`.
public export
deleteMinBoxNode : Box c k -> Maybe (k, c, Box c k)
deleteMinBoxNode BoxLeaf = Nothing
deleteMinBoxNode (BoxNode _ BoxLeaf x c r) = Just (x, c, r)
deleteMinBoxNode (BoxNode _ l x c r) =
  case deleteMinBoxNode l of
    Nothing => Just (x, c, r)
    Just (minK, minW, l') => Just (minK, minW, balanceBoxNode l' x c r)

||| Alias for `deleteMinBoxNode`.
public export
extractMinBox : Box c k -> Maybe (k, c, Box c k)
extractMinBox = deleteMinBoxNode

||| Deletes the root entry given left and right subtrees, rebalancing in O(log N).
public export
deleteRootBoxNode : Box c k -> k -> Box c k -> Box c k
deleteRootBoxNode BoxLeaf _ r = r
deleteRootBoxNode l       _ BoxLeaf = l
deleteRootBoxNode l       _ r =
  case deleteMinBoxNode r of
    Nothing => l
    Just (minK, minW, r') => balanceBoxNode l minK minW r'

||| Deletes a key from `Box c k` while preserving AVL balance.
public export
deleteBox : Ord k => k -> Box c k -> Box c k
deleteBox _ BoxLeaf = BoxLeaf
deleteBox target (BoxNode _ l k w r) =
  case compare target k of
    LT => balanceBoxNode (deleteBox target l) k w r
    GT => balanceBoxNode l k w (deleteBox target r)
    EQ => deleteRootBoxNode l k r

------------------------------------------------------------------------
-- 3. KEYED LOOKUPS, OVERWRITES & ACCUMULATING INSERTIONS
------------------------------------------------------------------------

||| Comparator-parameterised O(log N) lookup returning `zeroWeight` when absent.
public export
lookupBoxBy : MultisetWeight c => (lt : k -> k -> Bool) -> (eq : k -> k -> Bool) -> k -> Box c k -> c
lookupBoxBy _ _ _ BoxLeaf = zeroWeight
lookupBoxBy lt eq val (BoxNode _ l x w r) =
  if eq val x then w
  else if lt val x then lookupBoxBy lt eq val l
  else lookupBoxBy lt eq val r

||| Alias for `lookupBoxBy`.
public export
lookupBoxTreeBy : MultisetWeight c => (lt : k -> k -> Bool) -> (eq : k -> k -> Bool) -> k -> Box c k -> c
lookupBoxTreeBy = lookupBoxBy

||| Comparator-parameterised O(log N) canonical overwrite with zero-pruning.
public export
setBoxBy : MultisetWeight c => (lt : k -> k -> Bool) -> (eq : k -> k -> Bool) -> k -> c -> Box c k -> Box c k
setBoxBy _ _ val w BoxLeaf =
  if isZero w then BoxLeaf else BoxNode 1 BoxLeaf val w BoxLeaf
setBoxBy lt eq val w (BoxNode _ l x cur r) =
  if eq val x
    then if isZero w then deleteRootBoxNode l x r else mkBoxNode l x w r
    else if lt val x
      then balanceBoxNode (setBoxBy lt eq val w l) x cur r
      else balanceBoxNode l x cur (setBoxBy lt eq val w r)

||| Alias for `setBoxBy`.
public export
setBoxTreeBy : MultisetWeight c => (lt : k -> k -> Bool) -> (eq : k -> k -> Bool) -> k -> c -> Box c k -> Box c k
setBoxTreeBy = setBoxBy

||| Comparator-parameterised O(log N) accumulating addition with zero-pruning.
public export
addBoxBy : MultisetWeight c => (lt : k -> k -> Bool) -> (eq : k -> k -> Bool) -> k -> c -> Box c k -> Box c k
addBoxBy _ _ val dw BoxLeaf =
  if isZero dw then BoxLeaf else BoxNode 1 BoxLeaf val dw BoxLeaf
addBoxBy lt eq val dw node@(BoxNode _ l x cur r) =
  if isZero dw then node
  else if eq val x
    then let newW = addWeight cur dw
         in if isZero newW then deleteRootBoxNode l x r else mkBoxNode l x newW r
    else if lt val x
      then balanceBoxNode (addBoxBy lt eq val dw l) x cur r
      else balanceBoxNode l x cur (addBoxBy lt eq val dw r)

||| Alias for `addBoxBy`.
public export
addBoxTreeBy : MultisetWeight c => (lt : k -> k -> Bool) -> (eq : k -> k -> Bool) -> k -> c -> Box c k -> Box c k
addBoxTreeBy = addBoxBy

||| Looks up a key in `Box c k`, returning `zeroWeight` when absent.
public export
lookupBox : (Ord k, MultisetWeight c) => k -> Box c k -> c
lookupBox = lookupBoxBy (<) (==)

||| Alias for `lookupBox`.
public export
lookupBoxTree : (Ord k, MultisetWeight c) => k -> Box c k -> c
lookupBoxTree = lookupBox

||| Canonical zero-pruning overwrite: sets `target` to `val`, deleting the node
||| whenever `isZero val` holds so `BoxLeaf` remains the unique canonical zero.
public export
setBox : (Ord k, MultisetWeight c) => k -> c -> Box c k -> Box c k
setBox = setBoxBy (<) (==)

||| Alias for `setBox`.
public export
setBoxTree : (Ord k, MultisetWeight c) => k -> c -> Box c k -> Box c k
setBoxTree = setBox

||| Accumulates `delta` onto `target` (`cur + delta`), pruning on annihilation.
public export
addAtKeyBox : (Ord k, MultisetWeight c) => k -> c -> Box c k -> Box c k
addAtKeyBox = addBoxBy (<) (==)

||| Accumulating AVL insertion alias (`addBoxTree` / `insertBox` / `insertBoxFast`).
public export
addBoxTree : (Ord k, MultisetWeight c) => k -> c -> Box c k -> Box c k
addBoxTree = addAtKeyBox

||| Accumulating AVL insertion (backward-compatible with `Stage0.Multiset.insertBox`).
public export
insertBox : (Ord k, MultisetWeight c) => k -> c -> Box c k -> Box c k
insertBox = addAtKeyBox

||| Fast accumulating AVL insertion alias.
public export
insertBoxFast : (Ord k, MultisetWeight c) => k -> c -> Box c k -> Box c k
insertBoxFast = addAtKeyBox

------------------------------------------------------------------------
-- 4. CONSTRUCTORS & IN-ORDER FOLDING
------------------------------------------------------------------------

||| Constructs a zero-pruned singleton `Box c k`.
public export
singletonBox : MultisetWeight c => k -> c -> Box c k
singletonBox k w = if isZero w then BoxLeaf else BoxNode 1 BoxLeaf k w BoxLeaf

||| Constructs a balanced AVL `Box` from 1 key-weight pair in O(1) without `Ord`.
public export
mkSortedBox1 : MultisetWeight c => k -> c -> Box c k
mkSortedBox1 = singletonBox

||| Constructs a balanced AVL `Box` from 2 strictly ascending keys in O(1) without `Ord`.
public export
mkSortedBox2 : MultisetWeight c => k -> c -> k -> c -> Box c k
mkSortedBox2 k0 w0 k1 w1 =
  if isZero w0 then mkSortedBox1 k1 w1
  else if isZero w1 then BoxNode 1 BoxLeaf k0 w0 BoxLeaf
  else BoxNode 2 (BoxNode 1 BoxLeaf k0 w0 BoxLeaf) k1 w1 BoxLeaf

||| Constructs a balanced AVL `Box` from 3 strictly ascending keys in O(1) without `Ord`.
public export
mkSortedBox3 : MultisetWeight c => k -> c -> k -> c -> k -> c -> Box c k
mkSortedBox3 k0 w0 k1 w1 k2 w2 =
  if isZero w0 then mkSortedBox2 k1 w1 k2 w2
  else if isZero w1 then mkSortedBox2 k0 w0 k2 w2
  else if isZero w2 then BoxNode 2 (BoxNode 1 BoxLeaf k0 w0 BoxLeaf) k1 w1 BoxLeaf
  else BoxNode 2 (BoxNode 1 BoxLeaf k0 w0 BoxLeaf) k1 w1 (BoxNode 1 BoxLeaf k2 w2 BoxLeaf)

||| Constructs a balanced AVL `Box` from 4 strictly ascending keys in O(1) without `Ord`.
public export
mkSortedBox4 : MultisetWeight c => k -> c -> k -> c -> k -> c -> k -> c -> Box c k
mkSortedBox4 k0 w0 k1 w1 k2 w2 k3 w3 =
  if isZero w0 then mkSortedBox3 k1 w1 k2 w2 k3 w3
  else if isZero w1 then mkSortedBox3 k0 w0 k2 w2 k3 w3
  else if isZero w2 then mkSortedBox3 k0 w0 k1 w1 k3 w3
  else if isZero w3 then mkSortedBox3 k0 w0 k1 w1 k2 w2
  else BoxNode 3 (BoxNode 1 BoxLeaf k0 w0 BoxLeaf) k1 w1 (BoxNode 2 BoxLeaf k2 w2 (BoxNode 1 BoxLeaf k3 w3 BoxLeaf))

||| Constructs a balanced AVL `Box c k` from an association list of `(key, weight)` pairs,
||| consolidating duplicates and pruning zeros.
public export
MkBox : (Ord k, MultisetWeight c) => List (k, c) -> Box c k
MkBox [] = BoxLeaf
MkBox ((k, w) :: rest) = addAtKeyBox k w (MkBox rest)

||| In-order left fold `(k -> c -> acc -> acc)` over `Box c k`.
public export
foldBox : (k -> c -> acc -> acc) -> acc -> Box c k -> acc
foldBox _ acc BoxLeaf = acc
foldBox f acc (BoxNode _ l k w r) =
  let accL = foldBox f acc l
      accM = f k w accL
  in foldBox f accM r

||| In-order left fold taking `(b -> (k, c) -> b)`.
public export
foldBoxTreeL : (f : b -> (k, c) -> b) -> b -> Box c k -> b
foldBoxTreeL _ acc BoxLeaf = acc
foldBoxTreeL f acc (BoxNode _ l k w r) =
  let accL    = foldBoxTreeL f acc l
      accNode = f accL (k, w)
  in foldBoxTreeL f accNode r

||| Structurally recursive in-order right fold `(k -> c -> b -> b)` over `Box c k`.
public export
foldBoxTreeR : (f : k -> c -> b -> b) -> b -> Box c k -> b
foldBoxTreeR _ z BoxLeaf = z
foldBoxTreeR f z (BoxNode _ l k w r) =
  foldBoxTreeR f (f k w (foldBoxTreeR f z r)) l

||| O(N) difference-list right-to-left accumulator materializing sorted pairs.
public export
toAscListBoxAcc : Box c k -> List (k, c) -> List (k, c)
toAscListBoxAcc BoxLeaf acc = acc
toAscListBoxAcc (BoxNode _ l k w r) acc =
  toAscListBoxAcc l ((k, w) :: toAscListBoxAcc r acc)

||| Extracts ascending `(key, weight)` pairs from a `Box c k` in O(N).
public export
toAscListBox : Box c k -> List (k, c)
toAscListBox box = toAscListBoxAcc box []

||| Extracts active non-zero `(key, weight)` pairs sorted in ascending order.
public export
boxTreeToList : MultisetWeight c => Box c k -> List (k, c)
boxTreeToList tree =
  foldBoxTreeR (\x, c, acc => if isZero c then acc else (x, c) :: acc) [] tree

||| Extracts sorted active `(key, weight)` pairs from a `Box c k`.
public export
items : MultisetWeight c => Box c k -> List (k, c)
items = boxTreeToList

||| Maps a function over weights in `Box c k`, preserving AVL structure.
public export
mapBoxWeight : (c -> d) -> Box c k -> Box d k
mapBoxWeight _ BoxLeaf = BoxLeaf
mapBoxWeight f (BoxNode h l k w r) = BoxNode h (mapBoxWeight f l) k (f w) (mapBoxWeight f r)

||| Backward-compatible alias for `mapBoxWeight`.
public export
mapBoxTreeWeight : (c -> d) -> Box c k -> Box d k
mapBoxTreeWeight = mapBoxWeight

||| Evaluates the number of active non-zero weight nodes in a `Box c k` with zero heap allocation.
public export
treeSizeNonZero : MultisetWeight c => Box c k -> Nat
treeSizeNonZero = foldBox (\_, w, acc => if isZero w then acc else S acc) 0

------------------------------------------------------------------------
-- 5. BOUNDED LEFT-SPINE ZIPPER, EQUALITY & ORDERING (ZERO LIST ALLOCATION)
------------------------------------------------------------------------

||| Incremental AVL left-spine traversal zipper avoiding full-tree `List` allocation.
public export
BoxZipper : (c : Type) -> (k : Type) -> Type
BoxZipper c k = List (k, c, Box c k)

||| Pushes the left spine of a `Box c k` onto an existing zipper stack.
public export
pushLeftBox : Box c k -> BoxZipper c k -> BoxZipper c k
pushLeftBox BoxLeaf acc = acc
pushLeftBox (BoxNode _ l k w r) acc = pushLeftBox l ((k, w, r) :: acc)

||| Pops the next entry from a `BoxZipper c k` in O(log N) worst-case, O(1) amortized.
public export
stepBoxZipper : BoxZipper c k -> Maybe (k, c, BoxZipper c k)
stepBoxZipper [] = Nothing
stepBoxZipper ((k, w, r) :: rest) = Just (k, w, pushLeftBox r rest)

||| Pops the next active non-zero entry from a `BoxZipper c k`, bounded by remaining node count.
public export
popNextNonZeroZipper : MultisetWeight c => Nat -> BoxZipper c k -> Maybe (k, c, BoxZipper c k)
popNextNonZeroZipper Z _ = Nothing
popNextNonZeroZipper (S fuel) stk =
  case stk of
    [] => Nothing
    ((k, w, r) :: rest) =>
      let nextStk = pushLeftBox r rest
      in if isZero w then popNextNonZeroZipper fuel nextStk else Just (k, w, nextStk)

||| Counts active non-zero entries directly over `Box c k` without `List` allocation.
public export
countNonZeroBox : MultisetWeight c => Box c k -> Nat
countNonZeroBox BoxLeaf             = Z
countNonZeroBox (BoxNode _ l _ w r) =
  countNonZeroBox l + (if isZero w then 0 else 1) + countNonZeroBox r

||| Pushes the right spine of a `Box c k` onto a descending zipper stack (largest key on top).
public export
pushRightBox : Box c k -> BoxZipper c k -> BoxZipper c k
pushRightBox BoxLeaf acc = acc
pushRightBox (BoxNode _ l k w r) acc = pushRightBox r ((k, w, l) :: acc)

||| Pops the next entry from a descending `BoxZipper c k` in O(log N) worst-case, O(1) amortized.
public export
stepRevBoxZipper : BoxZipper c k -> Maybe (k, c, BoxZipper c k)
stepRevBoxZipper [] = Nothing
stepRevBoxZipper ((k, w, l) :: rest) = Just (k, w, pushRightBox l rest)

||| Pops the next active non-zero entry from a descending `BoxZipper c k`.
public export
popNextNonZeroRevZipper : MultisetWeight c => Nat -> BoxZipper c k -> Maybe (k, c, BoxZipper c k)
popNextNonZeroRevZipper Z _ = Nothing
popNextNonZeroRevZipper (S fuel) stk =
  case stk of
    [] => Nothing
    ((k, w, l) :: rest) =>
      let nextStk = pushRightBox l rest
      in if isZero w then popNextNonZeroRevZipper fuel nextStk else Just (k, w, nextStk)

||| Bidirectional McBride one-hole zipper centered around a pivot key, streaming
||| descending (`< pivot`) and ascending (`> pivot`) entries outward in radial shells.
public export
record RadialBoxZipper (c : Type) (k : Type) where
  constructor MkRadialZipper
  originEntry : Maybe (k, c)
  negDesc     : BoxZipper c k
  posAsc      : BoxZipper c k

||| Single O(log N) root-to-pivot descent splitting a `Box c k` into opposing outward spines.
public export
initRadialZipper : Ord k => k -> Box c k -> RadialBoxZipper c k
initRadialZipper pivot root = descend root [] []
  where
    descend : Box c k -> BoxZipper c k -> BoxZipper c k -> RadialBoxZipper c k
    descend BoxLeaf negStk posStk = MkRadialZipper Nothing negStk posStk
    descend (BoxNode _ l k w r) negStk posStk =
      case compare k pivot of
        LT => descend r ((k, w, l) :: negStk) posStk
        GT => descend l negStk ((k, w, r) :: posStk)
        EQ => MkRadialZipper (Just (k, w)) (pushRightBox l negStk) (pushLeftBox r posStk)

||| Single outward radial shell yielded by `stepRadialZipper`.
public export
data RadialShellStep : (c : Type) -> (k : Type) -> Type where
  RadialDone   : RadialShellStep c k
  RadialOrigin : (k, c) -> RadialBoxZipper c k -> RadialShellStep c k
  RadialSingle : (k, c) -> RadialBoxZipper c k -> RadialShellStep c k
  RadialPair   : (k, c) -> (k, c) -> RadialBoxZipper c k -> RadialShellStep c k

private
stepRadialOuter : MultisetWeight c =>
                  Nat ->
                  BoxZipper c k ->
                  BoxZipper c k ->
                  RadialShellStep c k
stepRadialOuter fuel neg pos =
  case (popNextNonZeroRevZipper fuel neg, popNextNonZeroZipper fuel pos) of
    (Nothing, Nothing) => RadialDone
    (Just (kn, wn, neg'), Nothing) =>
      RadialSingle (kn, wn) (MkRadialZipper Nothing neg' [])
    (Nothing, Just (kp, wp, pos')) =>
      RadialSingle (kp, wp) (MkRadialZipper Nothing [] pos')
    (Just (kn, wn, neg'), Just (kp, wp, pos')) =>
      RadialPair (kn, wn) (kp, wp) (MkRadialZipper Nothing neg' pos')

||| Steps outward by one symmetric shell from a `RadialBoxZipper c k` without list allocation.
public export
stepRadialZipper : MultisetWeight c => Nat -> RadialBoxZipper c k -> RadialShellStep c k
stepRadialZipper fuel (MkRadialZipper (Just (k0, w0)) neg pos) =
  if not (isZero w0)
    then RadialOrigin (k0, w0) (MkRadialZipper Nothing neg pos)
    else stepRadialOuter fuel neg pos
stepRadialZipper fuel (MkRadialZipper Nothing neg pos) =
  stepRadialOuter fuel neg pos

||| Fueled left-spine comparison on non-zero entries of two `Box c k` trees.
public export
compareBoxZipperFuel : (Ord k, MultisetWeight c) =>
                       Nat -> BoxZipper c k -> BoxZipper c k -> Ordering
compareBoxZipperFuel Z _ _ = EQ
compareBoxZipperFuel (S fuel) z1 z2 =
  case (popNextNonZeroZipper (S fuel) z1, popNextNonZeroZipper (S fuel) z2) of
    (Nothing, Nothing) => EQ
    (Nothing, Just _)  => LT
    (Just _,  Nothing) => GT
    (Just (k1, w1, r1), Just (k2, w2, r2)) =>
      case compare k1 k2 of
        EQ => case compare w1 w2 of
                EQ  => compareBoxZipperFuel fuel r1 r2
                ord => ord
        ord => ord

||| Structural equality test via incremental non-zero zipper without full list allocation.
public export
structuralBoxTreeEqual : (Eq k, MultisetWeight c) => Box c k -> Box c k -> Bool
structuralBoxTreeEqual t1 t2 =
  go (S (boxNodeCount t1 + boxNodeCount t2)) (pushLeftBox t1 []) (pushLeftBox t2 [])
  where
    go : Nat -> BoxZipper c k -> BoxZipper c k -> Bool
    go Z _ _ = True
    go (S fuel) z1 z2 =
      case (popNextNonZeroZipper (S fuel) z1, popNextNonZeroZipper (S fuel) z2) of
        (Nothing, Nothing) => True
        (Just (k1, w1, r1), Just (k2, w2, r2)) =>
          (k1 == k2) && (w1 == w2) && go fuel r1 r2
        _ => False

||| Equality alias for `structuralBoxTreeEqual`.
public export
boxTreeEqual : (Eq k, MultisetWeight c) => Box c k -> Box c k -> Bool
boxTreeEqual = structuralBoxTreeEqual

public export
(Eq k, MultisetWeight c) => Eq (Box c k) where
  (==) = structuralBoxTreeEqual

public export
(Ord k, MultisetWeight c) => Ord (Box c k) where
  compare t1 t2 =
    compareBoxZipperFuel (S (boxNodeCount t1 + boxNodeCount t2)) (pushLeftBox t1 []) (pushLeftBox t2 [])

public export
(Show k, Show c) => Show (Box c k) where
  show t = "Box(" ++ show (toAscListBox t) ++ ")"

public export
Foldable (Box c) where
  foldr f z t = foldBoxTreeR (\x, _, acc => f x acc) z t

------------------------------------------------------------------------
-- 6. POINTWISE ALGEBRAIC, RELATIONAL & PAIRWISE PRODUCT OPERATORS
------------------------------------------------------------------------

||| Re-consolidates a `Box c k` by pruning any zero weights and balancing.
public export
consolidateBox : (Ord k, MultisetWeight c) => Box c k -> Box c k
consolidateBox t = foldBox (\k, w, acc => if isZero w then acc else setBox k w acc) BoxLeaf t

||| Pointwise negation of all weights in a `Box c k`.
public export
negateBox : MultisetWeight c => Box c k -> Box c k
negateBox = mapBoxWeight negWeight

||| Exact pointwise superposition/sum of two `Box c k` structures (`A + B`), pruning zeros.
public export
unionBox : (Ord k, MultisetWeight c) => Box c k -> Box c k -> Box c k
unionBox BoxLeaf t2 = t2
unionBox t1 BoxLeaf = t1
unionBox t1 t2 = foldBox (\k, w, acc => addAtKeyBox k w acc) t1 t2

||| Pointwise difference of two `Box c k` structures (`A - B`), pruning zeros.
public export
subBox : (Ord k, MultisetWeight c) => Box c k -> Box c k -> Box c k
subBox t1 BoxLeaf = t1
subBox t1 t2 = foldBox (\k, w, acc => addAtKeyBox k (negWeight w) acc) t1 t2

||| Pointwise scalar multiplication by `s : c`, annihilating immediately when `isZero s` (no `Ord k` needed).
public export
scaleBox : MultisetWeight c => c -> Box c k -> Box c k
scaleBox s t =
  if isZero s then BoxLeaf else mapBoxWeight (mulWeight s) t

||| Total signed mass (`sum_k w_k`) across all active coordinates.
public export
totalMassBox : MultisetWeight c => Box c k -> c
totalMassBox = foldBox (\_, w, acc => addWeight acc w) zeroWeight

||| Filters entries of `Box c k` by a key predicate.
public export
filterBox : (Ord k, MultisetWeight c) => (k -> Bool) -> Box c k -> Box c k
filterBox p t =
  foldBox (\k, w, acc => if p k then setBox k w acc else acc) BoxLeaf t

||| Pointwise Hadamard product (`A .*. B`) on `Box c k`.
public export
hadamardBox : (Ord k, MultisetWeight c) => Box c k -> Box c k -> Box c k
hadamardBox BoxLeaf _ = BoxLeaf
hadamardBox _ BoxLeaf = BoxLeaf
hadamardBox t1 t2 =
  foldBox (\k, w1, acc =>
             let w2   = lookupBox k t2
                 prod = mulWeight w1 w2
             in if isZero prod then acc else setBox k prod acc)
          BoxLeaf
          t1

||| Symmetric pointwise tropical minimum envelope (`A /\ B`) satisfying `(A /\ B) + (A \/ B) = A + B`.
public export
minBox : (Ord k, MultisetWeight c) => Box c k -> Box c k -> Box c k
minBox BoxLeaf BoxLeaf = BoxLeaf
minBox t1 t2 =
  let step1 = foldBox (\k, w1, acc =>
                         let w2   = lookupBox k t2
                             minW = minWeight w1 w2
                         in if isZero minW then acc else setBox k minW acc)
                      BoxLeaf
                      t1
  in foldBox (\k, w2, acc =>
                let w1 = lookupBox k t1
                in if not (isZero w1)
                     then acc
                     else let minW = minWeight zeroWeight w2
                          in if isZero minW then acc else setBox k minW acc)
             step1
             t2

||| Alias for pointwise infimum intersection.
public export
intersectBox : (Ord k, MultisetWeight c) => Box c k -> Box c k -> Box c k
intersectBox = minBox

||| Symmetric pointwise tropical maximum envelope (`A \/ B`).
public export
maxBox : (Ord k, MultisetWeight c) => Box c k -> Box c k -> Box c k
maxBox BoxLeaf BoxLeaf = BoxLeaf
maxBox t1 t2 =
  let step1 = foldBox (\k, w1, acc =>
                         let w2   = lookupBox k t2
                             maxW = maxWeight w1 w2
                         in if isZero maxW then acc else setBox k maxW acc)
                      BoxLeaf
                      t1
  in foldBox (\k, w2, acc =>
                let w1 = lookupBox k t1
                in if not (isZero w1)
                     then acc
                     else let maxW = maxWeight zeroWeight w2
                          in if isZero maxW then acc else setBox k maxW acc)
             step1
             t2

||| Canonical inner product (`A <.> B`) returning scalar multiplicity weight `c`.
public export
dotBox : (Ord k, MultisetWeight c) => Box c k -> Box c k -> c
dotBox BoxLeaf _ = zeroWeight
dotBox _ BoxLeaf = zeroWeight
dotBox t1 t2 =
  foldBox (\k, w1, acc =>
             let w2 = lookupBox k t2
             in addWeight acc (mulWeight w1 w2))
          zeroWeight
          t1

||| Generalized all-pairs box multiplication (`pairBoxWith`):
||| Pairs every active `(k1, w1)` in `t1` with every active `(k2, w2)` in `t2`,
||| combines coordinates via `f k1 k2`, multiplies weights via `mulWeight w1 w2`,
||| and consolidates colliding output keys with automatic zero-pruning.
public export
pairBoxWith : (Ord k3, MultisetWeight c) =>
              (f : k1 -> k2 -> k3) ->
              Box c k1 ->
              Box c k2 ->
              Box c k3
pairBoxWith _ BoxLeaf _ = BoxLeaf
pairBoxWith _ _ BoxLeaf = BoxLeaf
pairBoxWith f t1 t2 =
  foldBox (\k1, w1, treeAcc =>
             foldBox (\k2, w2, acc =>
                        let prod = mulWeight w1 w2
                        in if isZero prod then acc else addAtKeyBox (f k1 k2) prod acc)
                     treeAcc
                     t2)
          BoxLeaf
          t1

||| Cartesian outer product (`tensorBox`): `Box c k1 -> Box c k2 -> Box c (k1, k2)`.
public export
tensorBox : (Ord k1, Ord k2, MultisetWeight c) => Box c k1 -> Box c k2 -> Box c (k1, k2)
tensorBox = pairBoxWith (,)

||| Right index contraction / marginalization summing out `k2`.
public export
contractRBox : (Ord k1, MultisetWeight c) => Box c (k1, k2) -> Box c k1
contractRBox BoxLeaf = BoxLeaf
contractRBox m = foldBox (\(c1, _), w, acc => addAtKeyBox c1 w acc) BoxLeaf m

||| Left index contraction / marginalization summing out `k1`.
public export
contractLBox : (Ord k2, MultisetWeight c) => Box c (k1, k2) -> Box c k2
contractLBox BoxLeaf = BoxLeaf
contractLBox m = foldBox (\(_, c2), w, acc => addAtKeyBox c2 w acc) BoxLeaf m

||| Coordinate pushforward re-indexing `k1 -> k2` and summing colliding multiplicities.
public export
mapBox : (Ord k2, MultisetWeight c) => (k1 -> k2) -> Box c k1 -> Box c k2
mapBox _ BoxLeaf = BoxLeaf
mapBox f m = foldBox (\c1, w, acc => addAtKeyBox (f c1) w acc) BoxLeaf m

||| Monoidal convolution (`mulBoxWith`) over any `MonoidCoord k` and `MultisetWeight c`.
public export
mulBoxWith : (MonoidCoord k, MultisetWeight c) => Box c k -> Box c k -> Box c k
mulBoxWith = pairBoxWith combine

||| Pair coordinate transposition: swaps (a, b) -> (b, a).
public export
transposeBox : (Ord a, Ord b, MultisetWeight c) => Box c (a, b) -> Box c (b, a)
transposeBox BoxLeaf = BoxLeaf
transposeBox m =
  foldBox (\(x, y), w, acc =>
            if isZero w then acc else addAtKeyBox (y, x) w acc)
          BoxLeaf m

||| Pixel-fusion multiset contraction: [a, b1] * [b2, c] -> [a, c] where b1 == b2.
public export
composeBox : (Ord a, Ord b, Ord c, MultisetWeight w) =>
             Box w (a, b) -> Box w (b, c) -> Box w (a, c)
composeBox BoxLeaf _ = BoxLeaf
composeBox _ BoxLeaf = BoxLeaf
composeBox m1 m2 =
  foldBox (\(a, b1), w1, acc1 =>
            if isZero w1 then acc1
            else foldBox (\(b2, c), w2, acc2 =>
                           if isZero w2 || b1 /= b2 then acc2
                           else addAtKeyBox (a, c) (mulWeight w1 w2) acc2)
                         acc1 m2)
          BoxLeaf m1

||| Trace of a square 2D multiset: sums multiplicities on the diagonal a1 == a2.
public export
traceBox : (Ord a, MultisetWeight c) => Box c (a, a) -> c
traceBox BoxLeaf = zeroWeight
traceBox m =
  foldBox (\(x, y), w, acc =>
            if x == y then addWeight acc w else acc)
          zeroWeight m

||| Diagonal projection mask: retains only entries on the coincidence diagonal a1 == a2.
public export
diagMaskBox : (Ord a, MultisetWeight c) => Box c (a, a) -> Box c (a, a)
diagMaskBox BoxLeaf = BoxLeaf
diagMaskBox m =
  foldBox (\(x, y), w, acc =>
            if x == y then addAtKeyBox (x, y) w acc else acc)
          BoxLeaf m

------------------------------------------------------------------------
-- 7. STANDARD ALGEBRAIC INSTANCES ON `Box c k`
------------------------------------------------------------------------

public export
(Ord k, MultisetWeight c) => Semigroup (Box c k) where
  (<+>) = unionBox

public export
(Ord k, MultisetWeight c) => Monoid (Box c k) where
  neutral = BoxLeaf

public export
(Ord k, MultisetWeight c) => WeightedMultisetAlgebra c (Box c k) where
  zeroWM     = BoxLeaf
  addWM      = unionBox
  subWM      = subBox
  scaleWM    = scaleBox
  mulWM      = hadamardBox
  hadamardWM = hadamardBox
  minWM      = minBox
  maxWM      = maxBox
  dotWM      = dotBox

public export
Ord k => MultisetAlgebra (Box BoxInt k) where
  zeroM     = BoxLeaf
  addM      = unionBox
  subM      = subBox
  scaleM    = scaleBox
  mulM      = hadamardBox
  hadamardM = hadamardBox
  minM      = minBox
  maxM      = maxBox
  dotM      = dotBox

public export
MonoidCoord k => Num (Box BoxInt k) where
  (+) = unionBox
  (*) = mulBoxWith
  fromInteger n = singletonBox origin (intToBoxInt n)

public export
MonoidCoord k => Neg (Box BoxInt k) where
  negate = scaleBox (intToBoxInt (-1))
  (-) = subBox

public export
(Ord k1, Ord k2, MultisetWeight c) => MultisetOuter (Box c k1) (Box c k2) (Box c (k1, k2)) where
  (><) = tensorBox


------------------------------------------------------------------------
-- CONSTRUCTIVIST CANONICAL AVL/ZERO-PRUNING RECOGNIZER (`recognition-rule.md`)
------------------------------------------------------------------------

||| Single-pass canonical invariant checker over `Box c k`:
||| Validates:
||| 1. No zero weights (`not (isZero w)`).
||| 2. Exact cached AVL height (`h == S (max (boxHeight l) (boxHeight r))`).
||| 3. AVL balance factor (`|hL - hR| <= 1`).
||| 4. Strict BST key ordering (`maxKey(l) < k < minKey(r)`).
||| 5. Key predicate `keyOk k` holds on every active node.
||| Returns `Nothing` if invalid, `Just Nothing` for `BoxLeaf`, or
||| `Just (Just (minKey, maxKey))` for non-empty valid subtrees.
public export
checkBoxBoundsBy : MultisetWeight c => Ord k => (k -> Bool) -> Box c k -> Maybe (Maybe (k, k))
checkBoxBoundsBy _ BoxLeaf = Just Nothing
checkBoxBoundsBy keyOk (BoxNode h l k w r) =
  if isZero w || not (keyOk k) then Nothing
  else
    let hl = boxHeight l
        hr = boxHeight r
        expectedH = S (if hl >= hr then hl else hr)
    in if h /= expectedH || hl > hr + 1 || hr > hl + 1 then Nothing
       else case (checkBoxBoundsBy keyOk l, checkBoxBoundsBy keyOk r) of
              (Just optL, Just optR) =>
                let leftOk  = case optL of Nothing => True; Just (_, lMax) => lMax < k
                    rightOk = case optR of Nothing => True; Just (rMin, _) => k < rMin
                in if leftOk && rightOk
                     then Just (Just (maybe k fst optL, maybe k snd optR))
                     else Nothing
              _ => Nothing

||| Boolean canonical predicate checking BST ordering, AVL balance, height cache,
||| and zero-weight absence on a `Box c k`.
public export
isCanonicalBox : MultisetWeight c => Ord k => Box c k -> Bool
isCanonicalBox b =
  case checkBoxBoundsBy (const True) b of
    Nothing => False
    Just _  => True

||| Proof predicate that a `Box c k` satisfies all canonical AVL and zero-pruning invariants.
public export
IsCanonicalBox : MultisetWeight c => Ord k => Box c k -> Type
IsCanonicalBox b = (isCanonicalBox b = True)

||| Total boolean-to-`Dec` witness lift with zero runtime overhead.
public export
decideBoolTrue : (cond : Bool) -> Dec (cond = True)
decideBoolTrue True  = Yes Refl
decideBoolTrue False = No (\case Refl impossible)

||| Total, terminating constructive `Dec` recognizer validating external or dynamic
||| `Box c k` carriers before entry into `MultisetExpr` / `StepKernel`.
public export
recognizeCanonicalBox : MultisetWeight c => Ord k => (b : Box c k) -> Dec (IsCanonicalBox b)
recognizeCanonicalBox b = decideBoolTrue (isCanonicalBox b)

||| Erased-proof `Subset` bundling a `Box c k` with its canonical invariant witness.
public export
CanonicalBox : (c : Type) -> (k : Type) -> (MultisetWeight c, Ord k) => Type
CanonicalBox c k = Subset (Box c k) IsCanonicalBox

||| Smart constructor packing a verified `Box c k` into `CanonicalBox c k`.
public export
toCanonicalBox : (MultisetWeight c, Ord k) => (b : Box c k) -> Maybe (CanonicalBox c k)
toCanonicalBox b =
  case recognizeCanonicalBox b of
    Yes prf => Just (Element b prf)
    No _    => Nothing
