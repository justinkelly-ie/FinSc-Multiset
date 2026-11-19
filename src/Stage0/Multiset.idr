module Stage0.Multiset

import Data.Fin
import Data.Nat
import Data.List
import Data.Linear
import public Stage0.Interfaces
import public Stage0.BoxInt
import public Stage0.Box

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

||| Direct fiber pullback extension (`>>=`) on Multiset,
||| eliminating intermediate List allocations during fiber pullbacks.
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
-- FIRST-CLASS AVL MULTISET CARRIERS (`Carrier k = Box BoxInt k`)
------------------------------------------------------------------------

||| Canonical coordinate-indexed multiset carrier (`Carrier k = Box BoxInt k` /
||| `BoxMultisetTree k`) backed by `Stage0.Box` signed `BoxInt` multiplicities.
public export
Carrier : Type -> Type
Carrier k = Box BoxInt k

||| Backward-compatible alias for `Carrier k = Box BoxInt k`.
public export
BoxMultisetTree : Type -> Type
BoxMultisetTree = Carrier

||| Empty carrier over coordinate domain `k`.
public export
emptyCarrier : Carrier k
emptyCarrier = BoxLeaf

||| Canonical empty `Carrier a` (`Box BoxInt a`), preserving the `{a}` implicit name.
public export
emptyBox : {0 a : Type} -> Carrier a
emptyBox = BoxLeaf

||| Direct O(1) singleton construction of a Carrier k without intermediate List allocation.
public export
singletonCarrier : k -> BoxInt -> Carrier k
singletonCarrier = singletonBox

||| Creates a singleton multiset in O(1) without Ord constraint.
public export
unixelBox : a -> BoxInt -> Carrier a
unixelBox = singletonCarrier

||| Lookups the signed BoxInt multiplicity at coordinate `c` in O(log N) time.
public export
lookupCarrier : DiscreteCoord k => k -> Carrier k -> BoxInt
lookupCarrier = lookupBox

||| Pointwise multiset addition (AddM) over Carrier k in O(N log N) time.
public export
addCarrier : DiscreteCoord k => Carrier k -> Carrier k -> Carrier k
addCarrier = unionBox

||| Pointwise multiset subtraction (SubM) over Carrier k in O(N log N) time.
public export
subCarrier : DiscreteCoord k => Carrier k -> Carrier k -> Carrier k
subCarrier = subBox

||| Scalar multiplication of a Carrier k by a BoxInt factor.
public export
scaleCarrier : BoxInt -> Carrier k -> Carrier k
scaleCarrier = scaleBox

||| Pointwise Hadamard product (HadamardM) over Carrier k in O(N log N) time.
public export
hadamardCarrier : DiscreteCoord k => Carrier k -> Carrier k -> Carrier k
hadamardCarrier = hadamardBox

||| Pointwise lattice infimum (MinM) over Carrier k in O(N log N) time.
public export
minCarrier : DiscreteCoord k => Carrier k -> Carrier k -> Carrier k
minCarrier = minBox

||| Pointwise lattice supremum (MaxM) over Carrier k in O((N + M) log(N + M)) time.
public export
maxCarrier : DiscreteCoord k => Carrier k -> Carrier k -> Carrier k
maxCarrier = maxBox

||| Computes total mass of common shared tokens between two multisets |A ∩ B|.
public export
boxIntersectionMass : Ord a => Carrier a -> Carrier a -> Nat
boxIntersectionMass a b = boxToNat (totalMassBox (minBox a b))

||| Computes total union mass |A ∪ B| = sum max(w_A, w_B).
public export
boxUnionMass : Ord a => Carrier a -> Carrier a -> Nat
boxUnionMass a b = boxToNat (totalMassBox (maxBox a b))

||| Multiset Symmetric Difference Information Distance.
public export
boxSymmetricDifference : Ord a => Carrier a -> Carrier a -> Nat
boxSymmetricDifference a b =
  let diff = subBox a b
  in foldBoxTreeL (\acc, (_, w) => acc + boxToNat (absBox w)) 0 diff

||| Canonical inner product (DotStatic) between two Carrier k multisets in O(N log N) time.
public export
dotCarrier : DiscreteCoord k => Carrier k -> Carrier k -> BoxInt
dotCarrier = dotBox

||| Cartesian outer product (OuterM): Carrier k1 -> Carrier k2 -> Carrier (k1, k2).
public export
outerCarrier : (DiscreteCoord k1, DiscreteCoord k2) => Carrier k1 -> Carrier k2 -> Carrier (k1, k2)
outerCarrier = tensorBox

||| Right index contraction / marginalization (ContractR):
||| Sums out k2 to project Carrier (k1, k2) -> Carrier k1 (relational GROUP BY k1).
public export
contractR : PairCoord k1 k2 => Carrier (k1, k2) -> Carrier k1
contractR = contractRBox

||| Left index contraction / marginalization (ContractL):
||| Sums out k1 to project Carrier (k1, k2) -> Carrier k2 (relational GROUP BY k2).
public export
contractL : PairCoord k1 k2 => Carrier (k1, k2) -> Carrier k2
contractL = contractLBox

||| Coordinate pushforward (f_* / aggregate): re-indexes a Carrier k1 along f : k1 -> k2,
||| summing multiplicities of colliding coordinates in k2.
public export
pushforwardCarrier : DiscreteCoord k2 => (k1 -> k2) -> Carrier k1 -> Carrier k2
pushforwardCarrier = mapBox

public export
buildOneCarrier : {0 k : Type} -> FiniteCoord k
               => (rem : Nat) -> (acc : Carrier k) -> Carrier k
buildOneCarrier Z     acc = acc
buildOneCarrier (S r) acc = case isLT r (cardinality {k}) of
  Yes lt => buildOneCarrier r (setBoxTree (fromIndex (natToFinLT r @{lt})) (intToBoxInt 1) acc)
  No _   => acc

||| Universal identity mask (OneM) assigning weight 1 to every coordinate in `FiniteCoord k`.
public export
oneCarrier : {0 k : Type} -> FiniteCoord k => Carrier k
oneCarrier = buildOneCarrier (cardinality {k}) BoxLeaf

||| Cauchy convolution (MulStatic) on Carrier k over any MonoidCoord k.
public export
mulCarrier : MonoidCoord k => Carrier k -> Carrier k -> Carrier k
mulCarrier = mulBoxWith

public export
convCarrier : MonoidCoord k => Carrier k -> Carrier k -> Carrier k
convCarrier = mulCarrier

||| Filters a Multiset c a by a predicate on its elements.
public export
filterMultiset : (p : a -> Bool) -> Multiset c a -> Multiset c a
filterMultiset _ ZeroM = ZeroM
filterMultiset p (AddM k v rest) =
  if p k then AddM k v (filterMultiset p rest) else filterMultiset p rest

------------------------------------------------------------------------
-- CANONICAL CARRIER STOICHIOMETRIC REACTIONS & DIFFERENCES
------------------------------------------------------------------------

||| Bounded Carrier Difference (Monus): (M1 \ M2)(x) = max(0, M1(x) - M2(x)).
public export
boundedDiffCarrier : DiscreteCoord k => Carrier k -> Carrier k -> Carrier k
boundedDiffCarrier m1 m2 =
  foldBoxTreeL (\acc, (x, w1) =>
    let w2 = lookupCarrier x m2
        remW = Stage0.BoxInt.subBox w1 w2
    in if remW > intToBoxInt 0 then setBoxTree x remW acc else acc) BoxLeaf m1

||| Carrier Symmetric Difference: (M1 Δ M2)(x) = |M1(x) - M2(x)|.
public export
symmetricDiffCarrier : DiscreteCoord k => Carrier k -> Carrier k -> Carrier k
symmetricDiffCarrier m1 m2 =
  let diff1 = foldBoxTreeL (\acc, (x, w1) =>
                let w2 = lookupCarrier x m2
                    d = absBox (Stage0.BoxInt.subBox w1 w2)
                in if boxIsNonZero d then setBoxTree x d acc else acc) BoxLeaf m1
  in foldBoxTreeL (\acc, (x, w2) =>
       if boxIsNonZero (lookupCarrier x m1)
         then acc
         else let d = absBox w2
              in if boxIsNonZero d then setBoxTree x d acc else acc) diff1 m2

||| Computes the stoichiometric reaction quotient on indexed Carriers:
||| maximum number of times `reactants` is contained in `state`.
public export
reactionQuotientCarrier : DiscreteCoord k => (reactants : Carrier k) -> Carrier k -> BoxInt
reactionQuotientCarrier BoxLeaf _ = intToBoxInt 0
reactionQuotientCarrier _ BoxLeaf = intToBoxInt 0
reactionQuotientCarrier reactants state =
  let res = foldBoxTreeL (\mMin, (x, w) =>
              if w <= intToBoxInt 0
                then mMin
                else let q = divBox (lookupCarrier x state) w
                         qClamped = if q < intToBoxInt 0 then intToBoxInt 0 else q
                     in case mMin of
                          Nothing => Just qClamped
                          Just cur => Just (if qClamped < cur then qClamped else cur))
              Nothing reactants
  in case res of
       Nothing => intToBoxInt 0
       Just q => q

||| Executes up to `maxReactions` stoichiometric reactions (`reactants -> products`)
||| on an indexed `Carrier k` state: `state' = (state \ (k * reactants)) <+> (k * products)`.
||| Returns `(updatedState, actualReactionsExecuted)`.
public export
reactCarrierBox :
  DiscreteCoord k =>
  (maxReactions : BoxInt) ->
  (reactants : Carrier k) ->
  (products : Carrier k) ->
  Carrier k ->
  (Carrier k, BoxInt)
reactCarrierBox maxReactions reactants products state =
  if maxReactions <= intToBoxInt 0
    then (state, intToBoxInt 0)
    else case state of
           BoxLeaf => (state, intToBoxInt 0)
           _ =>
             let avail = reactionQuotientCarrier reactants state
                 k = if maxReactions < avail then maxReactions else avail
             in if k <= intToBoxInt 0
                  then (state, intToBoxInt 0)
                  else let consumed = scaleCarrier k reactants
                           produced = scaleCarrier k products
                           remState = boundedDiffCarrier state consumed
                           nextState = addCarrier remState produced
                       in (nextState, k)

||| Cross-tier stoichiometric transmutation (`reactants` in `Carrier k1` -> `products` in `Carrier k2`):
||| Consumes `k * reactants` from `sourceState` and adds `k * products` to `targetState`.
||| Returns `(nextSourceState, nextTargetState, actualReactionsExecuted)`.
public export
transmuteCarrier :
  (DiscreteCoord k1, DiscreteCoord k2) =>
  (maxReactions : BoxInt) ->
  (reactants : Carrier k1) ->
  (products : Carrier k2) ->
  Carrier k1 ->
  Carrier k2 ->
  (Carrier k1, Carrier k2, BoxInt)
transmuteCarrier maxReactions reactants products sourceState targetState =
  if maxReactions <= intToBoxInt 0
    then (sourceState, targetState, intToBoxInt 0)
    else case sourceState of
           BoxLeaf => (sourceState, targetState, intToBoxInt 0)
           _ =>
             let avail = reactionQuotientCarrier reactants sourceState
                 k = if maxReactions < avail then maxReactions else avail
             in if k <= intToBoxInt 0
                  then (sourceState, targetState, intToBoxInt 0)
                  else let consumed = scaleCarrier k reactants
                           produced = scaleCarrier k products
                           nextSource = boundedDiffCarrier sourceState consumed
                           nextTarget = addCarrier targetState produced
                       in (nextSource, nextTarget, k)
