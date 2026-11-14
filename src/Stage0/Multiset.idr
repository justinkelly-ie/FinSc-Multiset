module Stage0.Multiset

import Data.List
import Data.Linear
import public Stage0.Interfaces
import public Stage0.BoxInt

%default total

------------------------------------------------------------------------
-- 1. MULTISET DATA CONSTRUCTORS
------------------------------------------------------------------------

||| A Run-Length Encoded (RLE) Multiset optimized for high-generation Box Arithmetic.
public export
data Multiset : (c : Type) -> (a : Type) -> Type where
  ZeroM : Multiset c a
  AddM : a -> c -> Multiset c a -> Multiset c a

||| Strictly positive, non-empty Multiset (guarantees at least one element)
public export
data Multiset1 : (c : Type) -> (a : Type) -> Type where
  BaseM : a -> c -> Multiset1 c a
  AddM1 : a -> c -> Multiset1 c a -> Multiset1 c a

public export
insertItem : {auto eq : Eq a} -> {auto num : Num c} -> {auto eqC : Eq c} -> a -> c -> Multiset c a -> Multiset c a
insertItem k v ZeroM = if v == 0 then ZeroM else AddM k v ZeroM
insertItem k v (AddM k' v' rest) =
  if k == k' then
    let newV = v + v'
    in if newV == 0 then rest else AddM k newV rest
  else AddM k' v' (insertItem k v rest)

public export
insertItemBox : {auto eq : Eq a} -> a -> BoxInt -> Multiset BoxInt a -> Multiset BoxInt a
insertItemBox k (MkBoxInt v) ZeroM =
  case v of
    0 => ZeroM
    _ => AddM k (MkBoxInt v) ZeroM
insertItemBox k (MkBoxInt v) (AddM k' (MkBoxInt v') rest) =
  if k == k' then
    let newV = v + v'
    in case newV of
         0 => rest
         _ => AddM k (MkBoxInt newV) rest
  else AddM k' (MkBoxInt v') (insertItemBox k (MkBoxInt v) rest)

public export
addMultiset : Multiset c a -> Multiset c a -> Multiset c a
addMultiset ZeroM ys = ys
addMultiset (AddM x c xs) ys = AddM x c (addMultiset xs ys)

public export total
multisetToUrList : (1 _ : Multiset c a) -> Ur (List (a, c))
multisetToUrList ZeroM = MkUr []
multisetToUrList (AddM k v rest) =
  let MkUr listRest = multisetToUrList rest
  in MkUr ((k, v) :: listRest)

public export total
prependListToMultiset : List (a, c) -> (1 ys : Multiset c a) -> Multiset c a
prependListToMultiset [] ys = ys
prependListToMultiset ((k, v) :: xs) ZeroM = AddM k v (prependListToMultiset xs ZeroM)
prependListToMultiset ((k, v) :: xs) (AddM y c ys) = AddM k v (AddM y c (prependListToMultiset xs ys))

public export
laddMultiset : (1 xs : Multiset c a) -> (1 ys : Multiset c a) -> Multiset c a
laddMultiset xs ys =
  let MkUr listX = multisetToUrList xs
  in prependListToMultiset listX ys

public export
mapMultiset : (f : a -> b) -> Multiset c a -> Multiset c b
mapMultiset _ ZeroM = ZeroM
mapMultiset f (AddM x c xs) = AddM (f x) c (mapMultiset f xs)

public export
Functor (Multiset c) where
  map = mapMultiset

public export
Bifunctor Multiset where
  bimap f g ZeroM = ZeroM
  bimap f g (AddM x c xs) = AddM (g x) (f c) (bimap f g xs)

public export
Foldable (Multiset c) where
  foldr f z ZeroM = z
  foldr f z (AddM x _ xs) = f x (foldr f z xs)

  foldMap f ZeroM = neutral
  foldMap f (AddM x _ xs) = f x <+> foldMap f xs

||| Folds a function over all (item, weight) elements of a Multiset in single pass without list materialization.
public export
foldMultiset : (f : a -> c -> acc -> acc) -> acc -> Multiset c a -> acc
foldMultiset _ z ZeroM = z
foldMultiset f z (AddM x c xs) = f x c (foldMultiset f z xs)

public export
Traversable (Multiset c) where
  traverse f ZeroM = pure ZeroM
  traverse f (AddM x c xs) = [| AddM (f x) (pure c) (traverse f xs) |]

public export
Semigroup (Multiset c a) where
  (<+>) = addMultiset

public export
Monoid (Multiset c a) where
  neutral = ZeroM

public export
scaleMultiset : (Num c, Eq c) => c -> Multiset c a -> Multiset c a
scaleMultiset scalar xs = if scalar == 0 then ZeroM else go xs
  where
    go : Multiset c a -> Multiset c a
    go ZeroM = ZeroM
    go (AddM k v rest) = AddM k (v * scalar) (go rest)

public export
(Num c, Eq c) => Applicative (Multiset c) where
  pure x = AddM x 1 ZeroM

  ZeroM <*> _ = ZeroM
  (AddM f vf fs) <*> xs =
    addMultiset (mapMultiset f (scaleMultiset vf xs)) (fs <*> xs)

public export
(Num c, Eq c) => Monad (Multiset c) where
  ZeroM >>= _ = ZeroM
  (AddM x v xs) >>= f =
    addMultiset (scaleMultiset v (f x)) (xs >>= f)

public export
convolveMultiset : (Semigroup a, Num c, Eq c) => Multiset c a -> Multiset c a -> Multiset c a
convolveMultiset xs ys = [| (<+>) xs ys |]

public export
fiberPushforward : (a -> b) -> Multiset c a -> Multiset c b
fiberPushforward = mapMultiset

||| Intuitive zoomOutMultiset operator: coarse-grains fine micro-multiset tokens to coarse macro-multiset tokens (Technical: fiberPushforward / f_push / f_*).
public export
zoomOutMultiset : (a -> b) -> Multiset c a -> Multiset c b
zoomOutMultiset = fiberPushforward

public export
fiberPullback : (Num c, Eq c) => (b -> List a) -> Multiset c b -> Multiset c a
fiberPullback fiberMap ZeroM = ZeroM
fiberPullback fiberMap (AddM y v ys) =
  let fiberItems = foldr (\x, acc => AddM x v acc) ZeroM (fiberMap y)
  in addMultiset fiberItems (fiberPullback fiberMap ys)

||| Categorical monadic bind (Kleisli extension) directly on Multiset,
||| eliminating intermediate List allocations during categorical fiber pullbacks.
public export
bindMultiset : (Num c, Eq c) => (b -> Multiset c a) -> Multiset c b -> Multiset c a
bindMultiset f xs = xs >>= f

||| Pure Multiset fiber pullback operator directly between Multiset fibers without intermediate List allocations.
public export
fiberPullbackMultiset : (Num c, Eq c) => (b -> Multiset c a) -> Multiset c b -> Multiset c a
fiberPullbackMultiset = bindMultiset

||| Intuitive zoomInMultiset operator: expands coarse macro-multiset tokens to micro-multiset token fibers (Technical: fiberPullback / f_pull / f^*).
public export
zoomInMultiset : (Num c, Eq c) => (b -> List a) -> Multiset c b -> Multiset c a
zoomInMultiset = fiberPullback

public export
annihilateMultiset : (Eq a, Num c, Eq c) => Multiset c a -> Multiset c a
annihilateMultiset xs = go ZeroM xs
  where
    go : Multiset c a -> Multiset c a -> Multiset c a
    go acc ZeroM = acc
    go acc (AddM k v rest) = go (insertItem k v acc) rest

public export
multiplicityAll : (Num c, Abs c) => Multiset c a -> c
multiplicityAll ZeroM = 0
multiplicityAll (AddM x c xs) = abs c + multiplicityAll xs

||| Computes the total sum of BoxInt weights in a Multiset BoxInt a.
public export
multisetSum : Multiset BoxInt a -> BoxInt
multisetSum ZeroM = intToBoxInt 0
multisetSum (AddM _ w rest) = addBox w (multisetSum rest)

||| Data-structure entry point: looks up total element count in a `Multiset c a`.
||| 2LTT Staging Operation: Splicing (~t) - Queries object element token count from a concrete multiset vector.
public export
lookupCount : {auto eq : Eq a} -> {auto num : Num c} -> a -> Multiset c a -> c
lookupCount target ZeroM = 0
lookupCount target (AddM k v rest) =
  if target == k then v + lookupCount target rest else lookupCount target rest

||| Monomorphic BoxInt lookup in a Multiset BoxInt a, avoiding typeclass dictionary stalls.
public export
lookupCountBox : {auto eq : Eq a} -> a -> Multiset BoxInt a -> BoxInt
lookupCountBox target ZeroM = intToBoxInt 0
lookupCountBox target (AddM k v rest) =
  if target == k then addBox v (lookupCountBox target rest) else lookupCountBox target rest

||| Canonical mathematical observable: evaluates token multiplicity m_M(x) in a multiset M.
||| 2LTT Staging Operation: Splicing (~t) - Monomorphic extraction alias querying token multiplicity.
public export
multiplicity : (Eq a, Num c) => a -> Multiset c a -> c
multiplicity = lookupCount

public export
negateMultiset : Neg c => Multiset c a -> Multiset c a
negateMultiset ZeroM = ZeroM
negateMultiset (AddM x c xs) = AddM x (-c) (negateMultiset xs)

public export total
lnegateMultiset : Neg c => (1 _ : Multiset c a) -> Multiset c a
lnegateMultiset ZeroM = ZeroM
lnegateMultiset (AddM x c xs) = AddM x (-c) (lnegateMultiset xs)

public export
subMultiset : Neg c => Multiset c a -> Multiset c a -> Multiset c a
subMultiset a b = addMultiset a (negateMultiset b)

public export
lsubMultiset : Neg c => (1 xs : Multiset c a) -> (1 ys : Multiset c a) -> Multiset c a
lsubMultiset xs ys = laddMultiset xs (lnegateMultiset ys)

public export
(Eq a, Neg c, Num c, Eq c) => Eq (Multiset c a) where
  a == b = 
    let res = annihilateMultiset (addMultiset a (negateMultiset b))
    in isEmpty res
    where
      isEmpty : {0 b : Type} -> Multiset c b -> Bool
      isEmpty ZeroM = True
      isEmpty _ = False

export
(Show a, Show c) => Show (Multiset c a) where
  show ZeroM = "[]"
  show xs = "[" ++ showItems xs ++ "]"
    where
      showItems : Multiset c a -> String
      showItems ZeroM = ""
      showItems (AddM k v ZeroM) = "(" ++ show k ++ ", " ++ show v ++ ")"
      showItems (AddM k v rest) = "(" ++ show k ++ ", " ++ show v ++ "), " ++ showItems rest

public export
multisetToList : Multiset c a -> List (a, c)
multisetToList ZeroM = []
multisetToList (AddM k v rest) = (k, v) :: multisetToList rest

public export
fromList : (Eq a, Num c, Eq c) => List (a, c) -> Multiset c a
fromList [] = ZeroM
fromList ((k, v) :: rest) = insertItem k v (fromList rest)

public export
fromListBox : Eq a => List (a, BoxInt) -> Multiset BoxInt a
fromListBox [] = ZeroM
fromListBox ((k, v) :: rest) = insertItemBox k v (fromListBox rest)

public export total
dupMultiset : (1 _ : Multiset c a) -> (Multiset c a, Multiset c a)
dupMultiset ZeroM = (ZeroM, ZeroM)
dupMultiset (AddM x c xs) =
  let (xs1, xs2) = dupMultiset xs
  in (AddM x c xs1, AddM x c xs2)

public export total
consumeMultiset : (1 _ : Multiset c a) -> ()
consumeMultiset ZeroM = ()
consumeMultiset (AddM x c xs) = consumeMultiset xs

public export total
multisetToListL : (1 _ : Multiset c a) -> LPair (List (a, c)) (Multiset c a)
multisetToListL ZeroM = Builtin.(#) [] ZeroM
multisetToListL (AddM k v rest) =
  let (listRest # restM) = multisetToListL rest
  in Builtin.(#) ((k, v) :: listRest) (AddM k v restM)

------------------------------------------------------------------------
-- FIRST-CLASS AVL MULTISET CARRIERS (Box k = Carrier k = BoxMultisetTree k)
------------------------------------------------------------------------

||| Canonical coordinate-indexed multiset carrier (`Box k` / `Carrier k` / `BoxMultisetTree k`)
||| backed by an O(log N) AVL height-balanced binary search tree with signed BoxInt multiplicities.
public export
data Box a =
    BoxLeaf
  | BoxNode Nat (Box a) a BoxInt (Box a)

||| Canonical alias connecting `BoxMultisetTree` to `Box`.
public export
BoxMultisetTree : Type -> Type
BoxMultisetTree = Box

||| Canonical coordinate-indexed multiset carrier (`Gemini.md` & `ARCHITECTURE.md`).
public export
Carrier : Type -> Type
Carrier = Box

public export
%inline
boxHeight : Box a -> Nat
boxHeight BoxLeaf = Z
boxHeight (BoxNode h _ _ _ _) = h

public export
%inline
mkBoxNode : Box a -> a -> BoxInt -> Box a -> Box a
mkBoxNode l x c r =
  let hl = boxHeight l
      hr = boxHeight r
      h  = S (if hl > hr then hl else hr)
  in BoxNode h l x c r

public export
%inline
rotateRightBox : Box a -> a -> BoxInt -> Box a -> Box a
rotateRightBox (BoxNode _ ll lx lc lr) x c r = mkBoxNode ll lx lc (mkBoxNode lr x c r)
rotateRightBox l x c r = mkBoxNode l x c r

public export
%inline
rotateLeftBox : Box a -> a -> BoxInt -> Box a -> Box a
rotateLeftBox l x c (BoxNode _ rl rx rc rr) = mkBoxNode (mkBoxNode l x c rl) rx rc rr
rotateLeftBox l x c r = mkBoxNode l x c r

public export
balanceBoxNode : Box a -> a -> BoxInt -> Box a -> Box a
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

||| Extracts the minimum (leftmost) key-weight pair and returns the rebalanced remaining subtree.
public export
deleteMinBoxNode : Box a -> Maybe (a, BoxInt, Box a)
deleteMinBoxNode BoxLeaf = Nothing
deleteMinBoxNode (BoxNode _ BoxLeaf x c r) = Just (x, c, r)
deleteMinBoxNode (BoxNode _ l x c r) =
  case deleteMinBoxNode l of
    Nothing => Just (x, c, r)
    Just (minK, minW, l') => Just (minK, minW, balanceBoxNode l' x c r)

||| Removes the root of a BoxNode and rebalances its left and right subtrees.
public export
deleteRootBoxNode : Box a -> a -> Box a -> Box a
deleteRootBoxNode BoxLeaf _ r = r
deleteRootBoxNode l _ BoxLeaf = l
deleteRootBoxNode l _ r =
  case deleteMinBoxNode r of
    Nothing => l
    Just (minK, minW, r') => balanceBoxNode l minK minW r'

||| Monomorphic comparator-driven lookup in O(log N) time without Ord dictionary dispatch.
public export
lookupBoxTreeBy : (lt : a -> a -> Bool) -> (eq : a -> a -> Bool) -> a -> Box a -> BoxInt
lookupBoxTreeBy _ _ _ BoxLeaf = intToBoxInt 0
lookupBoxTreeBy lt eq val (BoxNode _ l x c r) =
  if eq val x then c
  else if lt val x then lookupBoxTreeBy lt eq val l
  else lookupBoxTreeBy lt eq val r

||| Monomorphic comparator-driven set in O(log N) time, pruning zero-weight nodes on cancellation.
public export
setBoxTreeBy : (lt : a -> a -> Bool) -> (eq : a -> a -> Bool) -> a -> BoxInt -> Box a -> Box a
setBoxTreeBy _ _ val w BoxLeaf =
  if boxIsZero w then BoxLeaf else mkBoxNode BoxLeaf val w BoxLeaf
setBoxTreeBy lt eq val w (BoxNode _ l x c r) =
  if eq val x
    then if boxIsZero w then deleteRootBoxNode l x r else mkBoxNode l x w r
    else if lt val x
      then balanceBoxNode (setBoxTreeBy lt eq val w l) x c r
      else balanceBoxNode l x c (setBoxTreeBy lt eq val w r)

||| Monomorphic comparator-driven additive update in a single O(log N) pass, pruning zero-weight nodes.
public export
addBoxTreeBy : (lt : a -> a -> Bool) -> (eq : a -> a -> Bool) -> a -> BoxInt -> Box a -> Box a
addBoxTreeBy _ _ val dw BoxLeaf =
  if boxIsZero dw then BoxLeaf else mkBoxNode BoxLeaf val dw BoxLeaf
addBoxTreeBy lt eq val dw node@(BoxNode _ l x c r) =
  if boxIsZero dw then node
  else if eq val x
    then let newW = addBox c dw
         in if boxIsZero newW then deleteRootBoxNode l x r else mkBoxNode l x newW r
    else if lt val x
      then balanceBoxNode (addBoxTreeBy lt eq val dw l) x c r
      else balanceBoxNode l x c (addBoxTreeBy lt eq val dw r)

||| Lookups the signed BoxInt value of a key in O(log N) time.
public export
lookupBoxTree : Ord a => a -> Box a -> BoxInt
lookupBoxTree = lookupBoxTreeBy (<) (==)

||| Sets the signed BoxInt value of a key in O(log N) time, removing the node when weight is zero.
public export
setBoxTree : Ord a => a -> BoxInt -> Box a -> Box a
setBoxTree = setBoxTreeBy (<) (==)

||| Adds a signed BoxInt delta to a key's weight in a single O(log N) pass, pruning zero-weight nodes.
public export
addBoxTree : Ord a => a -> BoxInt -> Box a -> Box a
addBoxTree = addBoxTreeBy (<) (==)

||| Structurally recursive in-order tree left fold accumulator for Box.
public export
foldBoxTreeL : (f : b -> (a, BoxInt) -> b) -> b -> Box a -> b
foldBoxTreeL _ acc BoxLeaf = acc
foldBoxTreeL f acc (BoxNode _ l x c r) =
  let accL = foldBoxTreeL f acc l
      accNode = f accL (x, c)
  in foldBoxTreeL f accNode r

||| Structurally recursive in-order tree right fold accumulator for Box.
public export
foldBoxTreeR : (f : a -> BoxInt -> b -> b) -> b -> Box a -> b
foldBoxTreeR _ z BoxLeaf = z
foldBoxTreeR f z (BoxNode _ l x c r) =
  foldBoxTreeR f (f x c (foldBoxTreeR f z r)) l

||| Flattens active non-zero elements into a sorted association list in O(N) time.
public export
boxTreeToList : Box a -> List (a, BoxInt)
boxTreeToList tree = foldBoxTreeR (\x, c, acc => if boxIsNonZero c then (x, c) :: acc else acc) [] tree

||| Extracts sorted (key, weight) pairs from a Box.
public export
items : Box a -> List (a, BoxInt)
items = boxTreeToList

||| Maps a function over all non-zero weights in a Box, preserving AVL balance and key order.
public export
mapBoxTreeWeight : (BoxInt -> BoxInt) -> Box a -> Box a
mapBoxTreeWeight _ BoxLeaf = BoxLeaf
mapBoxTreeWeight f (BoxNode h l x c r) = BoxNode h (mapBoxTreeWeight f l) x (f c) (mapBoxTreeWeight f r)

||| Evaluates the total number of coordinate nodes in a Box.
public export
boxTreeSize : Box a -> Nat
boxTreeSize BoxLeaf = 0
boxTreeSize (BoxNode _ l _ _ r) = S (boxTreeSize l + boxTreeSize r)

||| Evaluates the number of active non-zero weight nodes in a Box with zero allocations.
public export
treeSizeNonZero : Box a -> Nat
treeSizeNonZero = foldBoxTreeL (\acc, (_, w) => if boxIsNonZero w then S acc else acc) 0

||| Definitional structural equality comparison between two Boxes via in-order list projection.
public export
structuralBoxTreeEqual : Eq a => Box a -> Box a -> Bool
structuralBoxTreeEqual t1 t2 =
  boxTreeToList t1 == boxTreeToList t2

public export
boxTreeEqual : Eq a => Box a -> Box a -> Bool
boxTreeEqual = structuralBoxTreeEqual

public export
Eq a => Eq (Box a) where
  (==) = structuralBoxTreeEqual

public export
Ord a => Ord (Box a) where
  compare t1 t2 = compare (boxTreeToList t1) (boxTreeToList t2)

public export
Show a => Show (Box a) where
  show t = "Box(" ++ show (boxTreeToList t) ++ ")"

||| Empty carrier over coordinate domain `k`.
public export
emptyCarrier : Carrier k
emptyCarrier = BoxLeaf

||| Canonical empty multiset.
public export
emptyBox : Box a
emptyBox = BoxLeaf

||| Direct O(1) singleton construction of a Carrier k without intermediate List allocation.
public export
singletonCarrier : k -> BoxInt -> Carrier k
singletonCarrier c w =
  if boxIsZero w then BoxLeaf
  else BoxNode 1 BoxLeaf c w BoxLeaf

||| Creates a singleton multiset in O(1) without Ord constraint.
public export
unixelBox : a -> BoxInt -> Box a
unixelBox = singletonCarrier

||| Constructs a balanced AVL Box from an association list of (key, weight) pairs.
public export
MkBox : Ord a => List (a, BoxInt) -> Box a
MkBox [] = BoxLeaf
MkBox ((k, w) :: rest) = addBoxTree k w (MkBox rest)

||| Lookups the signed BoxInt multiplicity at coordinate `c` in O(log N) time.
public export
lookupCarrier : Ord k => k -> Carrier k -> BoxInt
lookupCarrier = lookupBoxTree

public export
lookupBox : Ord a => a -> Box a -> BoxInt
lookupBox = lookupBoxTree

||| Inserts or updates the multiplicity of an element in a single O(log N) AVL pass.
public export
insertBox : Ord a => a -> BoxInt -> Box a -> Box a
insertBox = addBoxTree

public export
insertBoxFast : Ord a => a -> BoxInt -> Box a -> Box a
insertBoxFast = addBoxTree

||| Converts a Multiset BoxInt a into a balanced AVL Box a.
public export
multisetToBox : Ord a => Multiset BoxInt a -> Box a
multisetToBox ZeroM = BoxLeaf
multisetToBox (AddM x w rest) = addBoxTree x w (multisetToBox rest)

||| Converts a Box a into a Multiset BoxInt a.
public export
boxToMultiset : Box a -> Multiset BoxInt a
boxToMultiset t = foldBoxTreeR (\x, w, acc => if boxIsZero w then acc else AddM x w acc) ZeroM t

||| Rebuilds a canonical Box by filtering non-zero weights and rebalancing.
public export
consolidateBox : Ord a => Box a -> Box a
consolidateBox t =
  foldBoxTreeL (\acc, (c, w) => if boxIsNonZero w then setBoxTree c w acc else acc) BoxLeaf t

||| Negates all weights in a Box a multiset.
public export
negateBox : Box a -> Box a
negateBox = mapBoxTreeWeight negBox

||| Pointwise multiset addition (AddM) over Carrier k in O(N log N) time.
public export
addCarrier : Ord k => Carrier k -> Carrier k -> Carrier k
addCarrier BoxLeaf t2 = t2
addCarrier t1 BoxLeaf = t1
addCarrier t1 t2 =
  foldBoxTreeL (\tree, (c, w) => addBoxTree c w tree) t1 t2

public export
unionBox : Ord a => Box a -> Box a -> Box a
unionBox = addCarrier

||| Pointwise multiset subtraction (SubM) over Carrier k in O(N log N) time.
public export
subCarrier : Ord k => Carrier k -> Carrier k -> Carrier k
subCarrier t1 BoxLeaf = t1
subCarrier t1 t2 =
  foldBoxTreeL (\tree, (c, w) => addBoxTree c (negate w) tree) t1 t2

public export
subBox : Ord a => Box a -> Box a -> Box a
subBox = subCarrier

||| Scalar multiplication of a Carrier k by a BoxInt factor.
public export
scaleCarrier : BoxInt -> Carrier k -> Carrier k
scaleCarrier s t =
  if boxIsZero s then BoxLeaf
  else mapBoxTreeWeight (s *) t

public export
scaleBox : BoxInt -> Box a -> Box a
scaleBox = scaleCarrier

||| Computes total multiset mass: sum of all item multiplicities in O(N) without list allocation.
public export
totalMassBox : Box a -> BoxInt
totalMassBox = foldBoxTreeL (\acc, (_, w) => acc + w) (intToBoxInt 0)

||| Filters a Box multiset by a coordinate predicate.
public export
filterBox : Ord a => (a -> Bool) -> Box a -> Box a
filterBox p t =
  foldBoxTreeL (\acc, (x, w) => if p x then setBoxTree x w acc else acc) BoxLeaf t

||| Pointwise Hadamard product (HadamardM) over Carrier k in O(N log N) time.
public export
hadamardCarrier : Ord k => Carrier k -> Carrier k -> Carrier k
hadamardCarrier t1 t2 =
  foldBoxTreeL (\acc, (c, w1) =>
    let w2 = lookupBoxTree c t2
        prod = mulBox w1 w2
    in if boxIsZero prod then acc else setBoxTree c prod acc)
    BoxLeaf
    t1

public export
hadamardBox : Ord a => Box a -> Box a -> Box a
hadamardBox = hadamardCarrier

||| Pointwise lattice infimum (MinM) over Carrier k in O(N log N) time.
public export
minCarrier : Ord k => Carrier k -> Carrier k -> Carrier k
minCarrier t1 t2 =
  foldBoxTreeL (\acc, (c, w1) =>
    let w2 = lookupBoxTree c t2
        minW = if w1 <= w2 then w1 else w2
    in if minW > intToBoxInt 0 then setBoxTree c minW acc else acc)
    BoxLeaf
    t1

public export
minBox : Ord a => Box a -> Box a -> Box a
minBox = minCarrier

public export
intersectBox : Ord a => Box a -> Box a -> Box a
intersectBox = minCarrier

||| Pointwise lattice supremum (MaxM) over Carrier k in O((N + M) log(N + M)) time.
public export
maxCarrier : Ord k => Carrier k -> Carrier k -> Carrier k
maxCarrier t1 t2 =
  let step1 = foldBoxTreeL (\acc, (c, w1) =>
        let w2 = lookupBoxTree c t2
            maxW = if w1 >= w2 then w1 else w2
        in if boxIsZero maxW then acc else setBoxTree c maxW acc)
        BoxLeaf
        t1
  in foldBoxTreeL (\acc, (c, w2) =>
       let w1 = lookupBoxTree c t1
       in if boxIsNonZero w1 then acc
          else let maxW = if w2 >= intToBoxInt 0 then w2 else intToBoxInt 0
               in if boxIsZero maxW then acc else setBoxTree c maxW acc)
       step1
       t2

public export
maxBox : Ord a => Box a -> Box a -> Box a
maxBox = maxCarrier

||| Computes total mass of common shared tokens between two multisets |A ∩ B|.
public export
boxIntersectionMass : Ord a => Box a -> Box a -> Nat
boxIntersectionMass a b = boxToNat (totalMassBox (minCarrier a b))

||| Computes total union mass |A ∪ B| = sum max(w_A, w_B).
public export
boxUnionMass : Ord a => Box a -> Box a -> Nat
boxUnionMass a b = boxToNat (totalMassBox (maxCarrier a b))

||| Multiset Symmetric Difference Information Distance.
public export
boxSymmetricDifference : Ord a => Box a -> Box a -> Nat
boxSymmetricDifference a b =
  let diff = subCarrier a b
  in foldBoxTreeL (\acc, (_, w) => acc + boxToNat (absBox w)) 0 diff

||| Canonical inner product (DotStatic) between two Carrier k multisets in O(N log N) time.
public export
dotCarrier : Ord k => Carrier k -> Carrier k -> BoxInt
dotCarrier t1 t2 =
  foldBoxTreeL (\acc, (c, w1) =>
    let w2 = lookupBoxTree c t2
    in acc + (w1 * w2))
    (intToBoxInt 0)
    t1

public export
dotBox : Ord a => Box a -> Box a -> BoxInt
dotBox = dotCarrier

||| Cartesian outer product (OuterM): Carrier k1 -> Carrier k2 -> Carrier (k1, k2).
public export
outerCarrier : (Ord k1, Ord k2) => Carrier k1 -> Carrier k2 -> Carrier (k1, k2)
outerCarrier m1 m2 =
  foldBoxTreeL (\acc1, (c1, w1) =>
    foldBoxTreeL (\acc2, (c2, w2) =>
      addBoxTree (c1, c2) (w1 * w2) acc2)
      acc1
      m2)
    BoxLeaf
    m1

public export
tensorBox : (Ord a, Ord b) => Box a -> Box b -> Box (a, b)
tensorBox = outerCarrier

public export
(><) : (Ord k1, Ord k2) => Box k1 -> Box k2 -> Box (k1, k2)
(><) = outerCarrier

||| Right index contraction / marginalization (ContractR):
||| Sums out k2 to project Carrier (k1, k2) -> Carrier k1 (relational GROUP BY k1).
public export
contractR : Ord k1 => Carrier (k1, k2) -> Carrier k1
contractR m =
  foldBoxTreeL (\acc, ((c1, _), w) => addBoxTree c1 w acc) BoxLeaf m

||| Left index contraction / marginalization (ContractL):
||| Sums out k1 to project Carrier (k1, k2) -> Carrier k2 (relational GROUP BY k2).
public export
contractL : Ord k2 => Carrier (k1, k2) -> Carrier k2
contractL m =
  foldBoxTreeL (\acc, ((_, c2), w) => addBoxTree c2 w acc) BoxLeaf m

||| Coordinate pushforward (f_* / aggregate): re-indexes a Carrier k1 along f : k1 -> k2,
||| summing multiplicities of colliding coordinates in k2.
public export
pushforwardCarrier : Ord k2 => (k1 -> k2) -> Carrier k1 -> Carrier k2
pushforwardCarrier f m =
  foldBoxTreeL (\acc, (c1, w) => addBoxTree (f c1) w acc) BoxLeaf m

public export
mapBox : Ord b => (a -> b) -> Box a -> Box b
mapBox = pushforwardCarrier

||| Cauchy convolution (MulStatic) on Carrier k over any MonoidCoord k.
public export
mulCarrier : MonoidCoord k => Carrier k -> Carrier k -> Carrier k
mulCarrier t1 t2 =
  foldBoxTreeL (\treeAcc, (c1, w1) =>
    foldBoxTreeL (\acc, (c2, w2) =>
      let cOut = combine c1 c2
          prod = mulBox w1 w2
      in if boxIsZero prod then acc else addBoxTree cOut prod acc)
      treeAcc
      t2)
    BoxLeaf
    t1

public export
convCarrier : MonoidCoord k => Carrier k -> Carrier k -> Carrier k
convCarrier = mulCarrier

public export
Foldable Box where
  foldr f z t = foldBoxTreeR (\x, _, acc => f x acc) z t

public export
Ord a => Semigroup (Box a) where
  (<+>) = addCarrier

public export
Ord a => Monoid (Box a) where
  neutral = BoxLeaf

public export
Ord a => MultisetAlgebra (Box a) where
  zeroM     = BoxLeaf
  addM      = addCarrier
  subM      = subCarrier
  scaleM    = scaleCarrier
  mulM      = hadamardCarrier
  hadamardM = hadamardCarrier
  minM      = minCarrier
  maxM      = maxCarrier
  dotM      = dotCarrier

public export
MonoidCoord k => Num (Box k) where
  (+) = addCarrier
  (*) = mulCarrier
  fromInteger n = singletonCarrier origin (intToBoxInt n)

public export
MonoidCoord k => Neg (Box k) where
  negate = scaleCarrier (intToBoxInt (-1))
  (-) = subCarrier

------------------------------------------------------------------------
-- 3. UNIFIED MULTISET COMBINATION, LATTICE & REACTION ALGEBRA
------------------------------------------------------------------------

||| Consolidating Multiset Union on Multiset BoxInt a: sums duplicate keys and prunes zeros.
public export
unionMultisetBox : Eq a => Multiset BoxInt a -> Multiset BoxInt a -> Multiset BoxInt a
unionMultisetBox ZeroM ys = annihilateMultiset ys
unionMultisetBox (AddM k v rest) ys = insertItemBox k v (unionMultisetBox rest ys)

||| Monomorphic BoxInt scaling on Multiset BoxInt a, pruning zero weights.
public export
scaleMultisetBox : BoxInt -> Multiset BoxInt a -> Multiset BoxInt a
scaleMultisetBox _ ZeroM = ZeroM
scaleMultisetBox s (AddM k v rest) =
  if boxIsZero s then ZeroM
  else let sv = mulBox s v
       in if boxIsZero sv then scaleMultisetBox s rest
          else AddM k sv (scaleMultisetBox s rest)

||| Inner product of two Multiset BoxInt a carriers: <M1, M2> = sum_x M1(x) * M2(x).
public export
dotMultisetBox : Eq a => Multiset BoxInt a -> Multiset BoxInt a -> BoxInt
dotMultisetBox m1 m2 =
  let c1 = annihilateMultiset m1
  in foldMultiset (\k, w1, acc => addBox acc (mulBox w1 (lookupCountBox k m2))) (intToBoxInt 0) c1

||| Hadamard (pointwise) product of two Multiset BoxInt a carriers: (M1 ⊙ M2)(x) = M1(x) * M2(x).
public export
hadamardMultisetBox : Eq a => Multiset BoxInt a -> Multiset BoxInt a -> Multiset BoxInt a
hadamardMultisetBox m1 m2 =
  let c1 = annihilateMultiset m1
  in foldMultiset (\k, w1, acc =>
       let w2 = lookupCountBox k m2
           prod = mulBox w1 w2
       in if boxIsZero prod then acc else insertItemBox k prod acc) ZeroM c1

||| Subtraction of two Multiset BoxInt a carriers: M1 - M2 = M1 + (-1)*M2.
public export
subMultisetBox : Eq a => Multiset BoxInt a -> Multiset BoxInt a -> Multiset BoxInt a
subMultisetBox m1 m2 = unionMultisetBox m1 (scaleMultisetBox (intToBoxInt (-1)) m2)

||| Tensor (Cartesian) product of two Multiset BoxInt carriers: (M1 ⊗ M2)(x, y) = M1(x) * M2(y).
public export
tensorMultisetBox : Multiset BoxInt a -> Multiset BoxInt b -> Multiset BoxInt (a, b)
tensorMultisetBox ZeroM _ = ZeroM
tensorMultisetBox (AddM x wx xs) ys =
  let row = foldMultiset (\y, wy, acc =>
              let prod = mulBox wx wy
              in if boxIsZero prod then acc else AddM (x, y) prod acc) ZeroM ys
  in addMultiset row (tensorMultisetBox xs ys)

||| Filters a Multiset c a by a predicate on its elements.
public export
filterMultiset : (p : a -> Bool) -> Multiset c a -> Multiset c a
filterMultiset _ ZeroM = ZeroM
filterMultiset p (AddM k v rest) =
  if p k then AddM k v (filterMultiset p rest) else filterMultiset p rest

||| Multiset Lattice Intersection (Infimum): (M1 ∩ M2)(x) = min(M1(x), M2(x)) for positive weights.
public export
intersectMultisetBox : Eq a => Multiset BoxInt a -> Multiset BoxInt a -> Multiset BoxInt a
intersectMultisetBox m1 m2 =
  let c1 = annihilateMultiset m1
  in foldMultiset (\k, w1, acc =>
       let w2 = lookupCountBox k m2
           minW = if w1 <= w2 then w1 else w2
       in if minW > intToBoxInt 0 then insertItemBox k minW acc else acc) ZeroM c1

||| Tropical infimum alias on Multiset BoxInt a: minM M1 M2 = M1 ⊓ M2.
public export
minMultisetBox : Eq a => Multiset BoxInt a -> Multiset BoxInt a -> Multiset BoxInt a
minMultisetBox = intersectMultisetBox

||| Multiset Lattice Join (Supremum Union): (M1 ∨ M2)(x) = max(M1(x), M2(x)) for positive weights.
public export
supremumUnionMultisetBox : Eq a => Multiset BoxInt a -> Multiset BoxInt a -> Multiset BoxInt a
supremumUnionMultisetBox m1 m2 =
  let allKeys = nub (map fst (multisetToList m1) ++ map fst (multisetToList m2))
  in foldr (\k, acc =>
       let w1 = lookupCountBox k m1
           w2 = lookupCountBox k m2
           maxW = if w1 >= w2 then w1 else w2
       in if maxW > intToBoxInt 0 then insertItemBox k maxW acc else acc) ZeroM allKeys

||| Tropical supremum alias on Multiset BoxInt a: maxM M1 M2 = M1 ⊔ M2.
public export
maxMultisetBox : Eq a => Multiset BoxInt a -> Multiset BoxInt a -> Multiset BoxInt a
maxMultisetBox = supremumUnionMultisetBox

public export
Eq a => MultisetAlgebra (Multiset BoxInt a) where
  zeroM     = ZeroM
  addM      = unionMultisetBox
  subM      = subMultisetBox
  scaleM    = scaleMultisetBox
  mulM      = hadamardMultisetBox
  hadamardM = hadamardMultisetBox
  minM      = minMultisetBox
  maxM      = maxMultisetBox
  dotM      = dotMultisetBox

||| Bounded Multiset Difference (Monus): (M1 \ M2)(x) = max(0, M1(x) - M2(x)).
public export
boundedDiffMultisetBox : Eq a => Multiset BoxInt a -> Multiset BoxInt a -> Multiset BoxInt a
boundedDiffMultisetBox m1 m2 =
  let c1 = annihilateMultiset m1
  in foldMultiset (\k, w1, acc =>
       let w2 = lookupCountBox k m2
           remW = Stage0.BoxInt.subBox w1 w2
       in if remW > intToBoxInt 0 then insertItemBox k remW acc else acc) ZeroM c1

||| Multiset Symmetric Difference: (M1 Δ M2)(x) = |M1(x) - M2(x)|.
public export
symmetricDiffMultisetBox : Eq a => Multiset BoxInt a -> Multiset BoxInt a -> Multiset BoxInt a
symmetricDiffMultisetBox m1 m2 =
  let allKeys = nub (map fst (multisetToList m1) ++ map fst (multisetToList m2))
  in foldr (\k, acc =>
       let w1 = lookupCountBox k m1
           w2 = lookupCountBox k m2
           diff = absBox (Stage0.BoxInt.subBox w1 w2)
       in if boxIsNonZero diff then insertItemBox k diff acc else acc) ZeroM allKeys

||| Computes the stoichiometric reaction quotient: maximum number of times `reactants`
||| is contained in `state` (min_{x in Supp(R)} floor(state(x) / R(x))).
public export
reactionQuotientBox : Eq a => (reactants : Multiset BoxInt a) -> Multiset BoxInt a -> BoxInt
reactionQuotientBox reactants state =
  let cReact = annihilateMultiset reactants
  in case cReact of
       ZeroM => intToBoxInt 0
       AddM k0 w0 rest =>
         let q0 = if w0 <= intToBoxInt 0 then intToBoxInt 0
                  else divBox (lookupCountBox k0 state) w0
             initQ = if q0 < intToBoxInt 0 then intToBoxInt 0 else q0
         in foldMultiset (\k, w, acc =>
              if w <= intToBoxInt 0 then acc
              else let q = divBox (lookupCountBox k state) w
                       qClamped = if q < intToBoxInt 0 then intToBoxInt 0 else q
                   in if qClamped < acc then qClamped else acc) initQ rest

||| Executes up to `maxReactions` stoichiometric reactions (reactants -> products) on `state`
||| using pure multiset combination operations: state' = (state \ (k * reactants)) + (k * products).
||| Returns (updatedState, actualReactionsExecuted).
public export
reactMultisetBox :
  Eq a =>
  (maxReactions : BoxInt) ->
  (reactants : Multiset BoxInt a) ->
  (products : Multiset BoxInt a) ->
  Multiset BoxInt a ->
  (Multiset BoxInt a, BoxInt)
reactMultisetBox maxReactions reactants products state =
  let avail = reactionQuotientBox reactants state
      k = if maxReactions < avail then maxReactions else avail
  in if k <= intToBoxInt 0
       then (state, intToBoxInt 0)
       else let consumed = scaleMultisetBox k reactants
                produced = scaleMultisetBox k products
                remState = boundedDiffMultisetBox state consumed
                nextState = unionMultisetBox remState produced
            in (nextState, k)

||| Cross-tier stoichiometric transmutation (reactants in M_A -> products in M_B):
||| Consumes `k * reactants` from `sourceState` and adds `k * products` to `targetState`.
||| Returns (nextSourceState, nextTargetState, actualReactionsExecuted).
public export
transmuteMultisetBox :
  (Eq a, Eq b) =>
  (maxReactions : BoxInt) ->
  (reactants : Multiset BoxInt a) ->
  (products : Multiset BoxInt b) ->
  Multiset BoxInt a ->
  Multiset BoxInt b ->
  (Multiset BoxInt a, Multiset BoxInt b, BoxInt)
transmuteMultisetBox maxReactions reactants products sourceState targetState =
  let avail = reactionQuotientBox reactants sourceState
      k = if maxReactions < avail then maxReactions else avail
  in if k <= intToBoxInt 0
       then (sourceState, targetState, intToBoxInt 0)
       else let consumed = scaleMultisetBox k reactants
                produced = scaleMultisetBox k products
                nextSource = boundedDiffMultisetBox sourceState consumed
                nextTarget = unionMultisetBox targetState produced
            in (nextSource, nextTarget, k)
