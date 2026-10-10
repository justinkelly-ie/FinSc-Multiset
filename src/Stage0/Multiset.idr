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

%inline public export
insertItem : (Eq a, Num c, Eq c) => a -> c -> Multiset c a -> Multiset c a
insertItem k v ZeroM = if v == 0 then ZeroM else AddM k v ZeroM
insertItem k v (AddM k' v' rest) =
  if k == k' then
    let newV = v + v'
    in if newV == 0 then rest else AddM k newV rest
  else AddM k' v' (insertItem k v rest)

%inline public export
insertItemBox : Eq a => a -> BoxInt -> Multiset BoxInt a -> Multiset BoxInt a
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
mapMultiset : (a -> b) -> Multiset c a -> Multiset c b
mapMultiset f ZeroM = ZeroM
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
lookupCount : (Eq a, Num c) => a -> Multiset c a -> c
lookupCount target ZeroM = 0
lookupCount target (AddM k v rest) =
  if target == k then v + lookupCount target rest else lookupCount target rest

||| Monomorphic BoxInt lookup in a Multiset BoxInt a, avoiding typeclass dictionary stalls.
public export
lookupCountBox : Eq a => a -> Multiset BoxInt a -> BoxInt
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
-- FIRST-CLASS MULTISET CONTAINERS (BOX)
------------------------------------------------------------------------

||| A discrete Multiset (bag) of elements with integer multiplicities.
public export
record Box a where
  constructor MkBox
  items : List (a, BoxInt)

public export
Eq a => Eq (Box a) where
  (MkBox xs) == (MkBox ys) = xs == ys

public export
Show a => Show (Box a) where
  show (MkBox xs) = "Box(" ++ show xs ++ ")"

||| Canonical empty multiset.
public export
emptyBox : Box a
emptyBox = MkBox []

||| Creates a singleton multiset.
public export
unixelBox : a -> BoxInt -> Box a
unixelBox x w = MkBox [(x, w)]

||| Fast O(1) multiset element insertion (prepending raw pair without eager consolidation).
%inline public export
insertBoxFast : a -> BoxInt -> Box a -> Box a
insertBoxFast x w (MkBox xs) =
  if unwrapBox w == 0 then MkBox xs else MkBox ((x, w) :: xs)

||| Converts a Multiset BoxInt a into a Box a.
public export
multisetToBox : Multiset BoxInt a -> Box a
multisetToBox ZeroM = emptyBox
multisetToBox (AddM x w rest) = insertBoxFast x w (multisetToBox rest)

||| Converts a Box a into a Multiset BoxInt a.
public export
boxToMultiset : Eq a => Box a -> Multiset BoxInt a
boxToMultiset (MkBox items) = fromListBox items

||| Lookups the multiplicity of an element in a multiset.
%inline
public export
lookupBox : Eq a => a -> Box a -> BoxInt
lookupBox _ (MkBox []) = intToBoxInt 0
lookupBox target (MkBox ((x, w) :: xs)) =
  if x == target then w else lookupBox target (MkBox xs)

||| Consolidates multiset entries by summing duplicate keys and removing zero multiplicities.
public export
consolidateBox : Eq a => Box a -> Box a
consolidateBox (MkBox items) = MkBox (go items [])
  where
    go : List (a, BoxInt) -> List (a, BoxInt) -> List (a, BoxInt)
    go [] acc = acc
    go ((x, w) :: rest) acc =
      case lookupBox x (MkBox acc) of
        (MkBoxInt 0) => if unwrapBox w == 0 then go rest acc else go rest ((x, w) :: acc)
        currentW =>
          let newW = currentW + w
              filteredAcc = filter (\(k, _) => k /= x) acc
          in if unwrapBox newW == 0
               then go rest filteredAcc
               else go rest ((x, newW) :: filteredAcc)

||| Inserts or updates the multiplicity of an element.
%inline
public export
insertBox : Eq a => a -> BoxInt -> Box a -> Box a
insertBox x w (MkBox xs) =
  let current = lookupBox x (MkBox xs)
      newWeight = current + w
      filtered = filter (\(k, _) => k /= x) xs
  in if unwrapBox newWeight == 0
       then MkBox filtered
       else MkBox ((x, newWeight) :: filtered)

||| Multiset Union (pouring containers together): adds multiplicities.
%inline
public export
unionBox : Eq a => Box a -> Box a -> Box a
unionBox (MkBox []) ys = ys
unionBox (MkBox ((x, w) :: xs)) ys =
  insertBox x w (unionBox (MkBox xs) ys)

public export
Eq a => Semigroup (Box a) where
  (<+>) = unionBox

public export
Eq a => Monoid (Box a) where
  neutral = emptyBox

||| Multiset Difference: subtracts multiplicities (bounded below by 0).
%inline
public export
subBox : Eq a => Box a -> Box a -> Box a
subBox (MkBox []) _ = MkBox []
subBox (MkBox ((k, w) :: xs)) ys =
  let subW = lookupBox k ys
      remW = w - subW
      (MkBox rest) = subBox (MkBox xs) ys
  in if unwrapBox remW > 0 then MkBox ((k, remW) :: rest) else MkBox rest

||| Computes total multiset mass: sum of all item multiplicities.
public export
totalMassBox : Box a -> BoxInt
totalMassBox (MkBox []) = intToBoxInt 0
totalMassBox (MkBox ((_, w) :: xs)) = w + totalMassBox (MkBox xs)

||| Filters a multiset by a predicate.
public export
filterBox : (a -> Bool) -> Box a -> Box a
filterBox p (MkBox xs) =
  MkBox (filter (\(x, _) => p x) xs)

||| Multiset Intersection: Computes the common shared tokens min(w_A, w_B).
public export
intersectBox : Eq a => Box a -> Box a -> Box a
intersectBox (MkBox xs) (MkBox ys) =
  let commonKeys = filter (\k => lookupBox k (MkBox ys) /= intToBoxInt 0) (nub (map fst xs))
      itemsList = map (\k =>
        let w1 = lookupBox k (MkBox xs)
            w2 = lookupBox k (MkBox ys)
            minW = if w1 <= w2 then w1 else w2
        in (k, minW)) commonKeys
  in MkBox (filter (\(_, w) => unwrapBox w > 0) itemsList)

||| Computes total mass of common shared tokens between two multisets |A ∩ B|.
public export
boxIntersectionMass : Eq a => Box a -> Box a -> Nat
boxIntersectionMass a b =
  let inter = intersectBox a b
      mass = unwrapBox (totalMassBox inter)
  in if mass <= 0 then 0 else integerToNat mass

||| Computes total union mass |A ∪ B| = sum max(w_A, w_B).
public export
boxUnionMass : Eq a => Box a -> Box a -> Nat
boxUnionMass (MkBox xs) (MkBox ys) =
  let allKeys = nub (map fst xs ++ map fst ys)
      maxWeights = map (\k =>
        let w1 = lookupBox k (MkBox xs)
            w2 = lookupBox k (MkBox ys)
            maxW = if w1 >= w2 then w1 else w2
            mw = unwrapBox maxW
        in if mw <= 0 then 0 else integerToNat mw) allKeys
  in sum maxWeights

||| Multiset Symmetric Difference Information Distance.
public export
boxSymmetricDifference : Eq a => Box a -> Box a -> Nat
boxSymmetricDifference (MkBox xs) (MkBox ys) =
  let allKeys = nub (map fst xs ++ map fst ys)
      diffs = map (\k =>
        let w1 = lookupBox k (MkBox xs)
            w2 = lookupBox k (MkBox ys)
            d = unwrapBox (if w1 >= w2 then w1 - w2 else w2 - w1)
        in integerToNat (if d >= 0 then d else -d)) allKeys
  in sum diffs
