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
-- FIRST-CLASS MULTISET CONTAINERS (BOX)
------------------------------------------------------------------------

||| A discrete Multiset (bag) of elements with integer multiplicities.
public export
record Box a where
  constructor MkBox
  items : List (a, BoxInt)

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
  if boxIsZero w then MkBox xs else MkBox ((x, w) :: xs)

||| Converts a Multiset BoxInt a into a Box a.
public export
multisetToBox : Multiset BoxInt a -> Box a
multisetToBox ZeroM = emptyBox
multisetToBox (AddM x w rest) = insertBoxFast x w (multisetToBox rest)

||| Converts a Box a into a Multiset BoxInt a.
public export
boxToMultiset : Eq a => Box a -> Multiset BoxInt a
boxToMultiset (MkBox items) = fromListBox items

||| Lookups the total multiplicity of an element in a Box multiset (summing any unconsolidated duplicate keys).
public export
lookupBox : Eq a => a -> Box a -> BoxInt
lookupBox _ (MkBox []) = intToBoxInt 0
lookupBox target (MkBox ((x, w) :: xs)) =
  if x == target then addBox w (lookupBox target (MkBox xs)) else lookupBox target (MkBox xs)

||| Inserts or updates the multiplicity of an element in a single structural pass without filter reallocations.
public export
insertBox : Eq a => a -> BoxInt -> Box a -> Box a
insertBox target w (MkBox xs) =
  if boxIsZero w then MkBox xs else MkBox (go target w xs)
  where
    go : a -> BoxInt -> List (a, BoxInt) -> List (a, BoxInt)
    go k dw [] = [(k, dw)]
    go k dw ((k', w') :: rest) =
      if k == k'
        then let newW = addBox w' dw
             in if boxIsZero newW then rest else (k, newW) :: rest
        else (k', w') :: go k dw rest

||| Consolidates multiset entries by summing duplicate keys and removing zero multiplicities via structural recursion.
public export
consolidateBox : Eq a => Box a -> Box a
consolidateBox (MkBox []) = emptyBox
consolidateBox (MkBox ((x, w) :: xs)) = insertBox x w (consolidateBox (MkBox xs))

||| Negates all weights in a Box a multiset.
public export
negateBox : Box a -> Box a
negateBox (MkBox []) = emptyBox
negateBox (MkBox ((x, w) :: xs)) =
  let MkBox rest = negateBox (MkBox xs)
  in MkBox ((x, negBox w) :: rest)

||| Multiset Union (pouring containers together): adds multiplicities.
public export
unionBox : Eq a => Box a -> Box a -> Box a
unionBox (MkBox []) ys = ys
unionBox (MkBox ((x, w) :: xs)) ys =
  insertBox x w (unionBox (MkBox xs) ys)

||| Extensional Multiset Equality on Box a: invariant under permutation and zero-weight cancellation.
public export
Eq a => Eq (Box a) where
  x == y =
    let MkBox diff = consolidateBox (unionBox x (negateBox y))
    in isNil diff
    where
      isNil : {0 b : Type} -> List (b, BoxInt) -> Bool
      isNil [] = True
      isNil _  = False

public export
Eq a => Semigroup (Box a) where
  (<+>) = unionBox

public export
Eq a => Monoid (Box a) where
  neutral = emptyBox

||| Multiset Difference: subtracts multiplicities (bounded below by 0).
public export
subBox : Eq a => Box a -> Box a -> Box a
subBox (MkBox []) _ = MkBox []
subBox (MkBox ((k, w) :: xs)) ys =
  let subW = lookupBox k ys
      remW = w - subW
      (MkBox rest) = subBox (MkBox xs) ys
  in if remW > intToBoxInt 0 then MkBox ((k, remW) :: rest) else MkBox rest

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
  in MkBox (filter (\(_, w) => w > intToBoxInt 0) itemsList)

||| Computes total mass of common shared tokens between two multisets |A ∩ B|.
public export
boxIntersectionMass : Eq a => Box a -> Box a -> Nat
boxIntersectionMass a b =
  let inter = intersectBox a b
  in boxToNat (totalMassBox inter)

||| Computes total union mass |A ∪ B| = sum max(w_A, w_B).
public export
boxUnionMass : Eq a => Box a -> Box a -> Nat
boxUnionMass (MkBox xs) (MkBox ys) =
  let allKeys = nub (map fst xs ++ map fst ys)
      maxWeights = map (\k =>
        let w1 = lookupBox k (MkBox xs)
            w2 = lookupBox k (MkBox ys)
            maxW = if w1 >= w2 then w1 else w2
        in boxToNat maxW) allKeys
  in sum maxWeights

||| Multiset Symmetric Difference Information Distance.
public export
boxSymmetricDifference : Eq a => Box a -> Box a -> Nat
boxSymmetricDifference (MkBox xs) (MkBox ys) =
  let allKeys = nub (map fst xs ++ map fst ys)
      diffs = map (\k =>
        let w1 = lookupBox k (MkBox xs)
            w2 = lookupBox k (MkBox ys)
            diff = if w1 >= w2 then w1 - w2 else w2 - w1
        in boxToNat diff) allKeys
  in sum diffs

||| Scales a Box a multiset by a BoxInt scalar, pruning zero weights.
public export
scaleBox : BoxInt -> Box a -> Box a
scaleBox s (MkBox xs) =
  if boxIsZero s then emptyBox
  else MkBox (mapMaybe (\(x, w) =>
         let sw = mulBox s w
         in if boxIsZero sw then Nothing else Just (x, sw)) xs)

||| Inner product of two Box a multisets: sum_x w_A(x) * w_B(x).
public export
dotBox : Eq a => Box a -> Box a -> BoxInt
dotBox a b =
  let MkBox xs = consolidateBox a
  in foldl (\acc, (k, w1) => addBox acc (mulBox w1 (lookupBox k b))) (intToBoxInt 0) xs

||| Tensor (Cartesian) product of two Box multisets: (A ⊗ B)(x, y) = A(x) * B(y).
public export
tensorBox : Box a -> Box b -> Box (a, b)
tensorBox (MkBox xs) (MkBox ys) =
  MkBox (concatMap (\(x, wx) =>
          mapMaybe (\(y, wy) =>
            let prod = mulBox wx wy
            in if boxIsZero prod then Nothing else Just ((x, y), prod)) ys) xs)

||| Functorial map over Box a elements (pushforward without eager consolidation).
public export
mapBox : (a -> b) -> Box a -> Box b
mapBox f (MkBox xs) = MkBox (map (\(x, w) => (f x, w)) xs)

public export
Functor Box where
  map = mapBox

public export
Foldable Box where
  foldr f z (MkBox xs) = foldr (\(x, _), acc => f x acc) z xs

public export
Eq a => MultisetAlgebra (Box a) where
  zeroM  = emptyBox
  addM   = unionBox
  scaleM = scaleBox
  dotM   = dotBox

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

public export
Eq a => MultisetAlgebra (Multiset BoxInt a) where
  zeroM  = ZeroM
  addM   = unionMultisetBox
  scaleM = scaleMultisetBox
  dotM   = dotMultisetBox

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
