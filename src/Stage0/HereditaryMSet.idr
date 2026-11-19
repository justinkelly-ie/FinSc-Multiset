module Stage0.HereditaryMSet

import Data.List
import Data.Nat
import public Stage0.Box

%default total

------------------------------------------------------------------------
-- 1. RECURSIVE HEREDITARY MULTISET (`HereditaryMSet c` & `PureMultiset`)
------------------------------------------------------------------------

||| Unified recursive multiset container where every node is a height-cached AVL
||| `Box c (HereditaryMSet c)` of sub-multisets weighted by carrier `c`
||| (`BoxInt`, `SignedBit`, or `MultisetBit`), enforcing canonical zero-pruning (`[M, M^a] = []`).
public export
data HereditaryMSet : (c : Type) -> Type where
  MkHMSet : Box c (HereditaryMSet c) -> HereditaryMSet c

||| Canonical default alias backed by exact signed `BoxInt` multiplicities.
public export
PureMultiset : Type
PureMultiset = HereditaryMSet BoxInt

public export
emptyHMSet : HereditaryMSet c
emptyHMSet = MkHMSet BoxLeaf

public export
emptyPureMSet : PureMultiset
emptyPureMSet = emptyHMSet

||| Canonical signed scalar Laurent key `alpha^k` inside `PureMultiset`:
||| - `0` -> `emptyHMSet` (`[]`)
||| - `k` -> `{ [] -> k }` (`MkHMSet (setBox emptyHMSet (intToBoxInt k) BoxLeaf)`)
public export
scalarKeyHMSet : Integer -> PureMultiset
scalarKeyHMSet k =
  if k == 0
    then emptyHMSet
    else MkHMSet (singletonBox emptyHMSet (intToBoxInt k))

------------------------------------------------------------------------
-- 2. TOTAL STRUCTURAL EQUALITY, BOUNDED-ZIPPER ORDERING & SHOW
------------------------------------------------------------------------

-- Structural nesting-depth counter providing an exact upper bound for `Ord` and `Show` totality.
mutual
  public export
  hmDepth : HereditaryMSet c -> Nat
  hmDepth (MkHMSet b) = S (boxNestedDepth b)

  public export
  boxNestedDepth : Box c (HereditaryMSet c) -> Nat
  boxNestedDepth BoxLeaf             = 0
  boxNestedDepth (BoxNode _ l k _ r) =
    max (max (boxNestedDepth l) (boxNestedDepth r)) (hmDepth k)

-- Incremental left-spine comparison avoiding per-comparison `List` flattening.
-- Uses lexicographic function order defaulting missing keys to `zeroWeight`,
-- ensuring signed total order across Laurent keys (`... < -2 < -1 < 0 < +1 < +2 < ...`).
mutual
  public export
  compareHMSetFuel : MultisetWeight c => Nat -> HereditaryMSet c -> HereditaryMSet c -> Ordering
  compareHMSetFuel depthFuel (MkHMSet b1) (MkHMSet b2) =
    compareZipperHM depthFuel (S (boxNodeCount b1 + boxNodeCount b2)) (pushLeftBox b1 []) (pushLeftBox b2 [])

  public export
  compareZipperHM : MultisetWeight c =>
                    Nat ->
                    Nat ->
                    BoxZipper c (HereditaryMSet c) ->
                    BoxZipper c (HereditaryMSet c) ->
                    Ordering
  compareZipperHM _ _ [] []             = EQ
  compareZipperHM _ Z _ _               = EQ
  compareZipperHM depthFuel (S stepRem) [] ((_, w2, r2) :: ys) =
    case compare zeroWeight w2 of
      EQ  => compareZipperHM depthFuel stepRem [] (pushLeftBox r2 ys)
      ord => ord
  compareZipperHM depthFuel (S stepRem) ((_, w1, r1) :: xs) [] =
    case compare w1 zeroWeight of
      EQ  => compareZipperHM depthFuel stepRem (pushLeftBox r1 xs) []
      ord => ord
  compareZipperHM Z (S stepRem) ((_, w1, r1) :: xs) ((_, w2, r2) :: ys) =
    case compare w1 w2 of
      EQ  => compareZipperHM Z stepRem (pushLeftBox r1 xs) (pushLeftBox r2 ys)
      ord => ord
  compareZipperHM (S rem) (S stepRem) ((k1, w1, r1) :: xs) ((k2, w2, r2) :: ys) =
    case compareHMSetFuel rem k1 k2 of
      LT => case compare w1 zeroWeight of
              EQ  => compareZipperHM (S rem) stepRem (pushLeftBox r1 xs) ((k2, w2, r2) :: ys)
              ord => ord
      GT => case compare zeroWeight w2 of
              EQ  => compareZipperHM (S rem) stepRem ((k1, w1, r1) :: xs) (pushLeftBox r2 ys)
              ord => ord
      EQ => case compare w1 w2 of
              EQ  => compareZipperHM (S rem) stepRem (pushLeftBox r1 xs) (pushLeftBox r2 ys)
              ord => ord

public export
compareHMSet : MultisetWeight c => HereditaryMSet c -> HereditaryMSet c -> Ordering
compareHMSet m1 m2 = compareHMSetFuel (min (hmDepth m1) (hmDepth m2)) m1 m2

public export
MultisetWeight c => Eq (HereditaryMSet c) where
  a == b = compareHMSet a b == EQ

public export
MultisetWeight c => Ord (HereditaryMSet c) where
  compare = compareHMSet

mutual
  public export
  showHMSetFuel : Show c => Nat -> HereditaryMSet c -> String
  showHMSetFuel _ (MkHMSet BoxLeaf) = "[]"
  showHMSetFuel Z _                 = "[...]"
  showHMSetFuel (S rem) (MkHMSet b) =
    "{" ++ go (toAscListBox b) ++ "}"
    where
      go : List (HereditaryMSet c, c) -> String
      go []             = ""
      go [(k, w)]       = showHMSetFuel rem k ++ ":" ++ show w
      go ((k, w) :: xs) = showHMSetFuel rem k ++ ":" ++ show w ++ ", " ++ go xs

public export
Show c => Show (HereditaryMSet c) where
  show m = showHMSetFuel (hmDepth m) m

------------------------------------------------------------------------
-- 3. CORE CALCULUS OPERATORS ON `HereditaryMSet c`
------------------------------------------------------------------------

||| Superposition (`+` / `<+>`): merges two `HereditaryMSet c` structures with automatic annihilation.
public export
addHMSet : MultisetWeight c => HereditaryMSet c -> HereditaryMSet c -> HereditaryMSet c
addHMSet (MkHMSet b1) (MkHMSet b2) = MkHMSet (unionBox b1 b2)

||| Reflection / Anti-Multiset (`-x`): negates every top-level weight quantum (`M^a`).
public export
negHMSet : MultisetWeight c => HereditaryMSet c -> HereditaryMSet c
negHMSet (MkHMSet b) = MkHMSet (negateBox b)

||| Difference / Interference (`subM` / `-`): `a + (-b)` with exact zero pruning.
public export
subHMSet : MultisetWeight c => HereditaryMSet c -> HereditaryMSet c -> HereditaryMSet c
subHMSet (MkHMSet b1) (MkHMSet b2) = MkHMSet (subBox b1 b2)

||| Scalar scaling (`scaleWM` / `scaleM`): scales all top-level multiplicities by `s : c`.
public export
scaleHMSet : MultisetWeight c => c -> HereditaryMSet c -> HereditaryMSet c
scaleHMSet s (MkHMSet b) = MkHMSet (scaleBox s b)

||| Pointwise Hadamard Masking (`.*.`): intersects shared keys, multiplying their weights.
public export
hadamardHMSet : MultisetWeight c => HereditaryMSet c -> HereditaryMSet c -> HereditaryMSet c
hadamardHMSet (MkHMSet b1) (MkHMSet b2) = MkHMSet (hadamardBox b1 b2)

||| Inner Product / Mass Projection (`<.>`): sums `mulWeight w1 w2` over matching keys into `c`.
public export
dotHMSet : MultisetWeight c => HereditaryMSet c -> HereditaryMSet c -> c
dotHMSet (MkHMSet b1) (MkHMSet b2) = dotBox b1 b2

||| Tropical Minimum Envelope (`/\`): pointwise `minWeight` across the union of keys.
public export
minHMSet : MultisetWeight c => HereditaryMSet c -> HereditaryMSet c -> HereditaryMSet c
minHMSet (MkHMSet b1) (MkHMSet b2) = MkHMSet (minBox b1 b2)

||| Tropical Maximum Envelope (`\/`): pointwise `maxWeight` across the union of keys.
public export
maxHMSet : MultisetWeight c => HereditaryMSet c -> HereditaryMSet c -> HereditaryMSet c
maxHMSet (MkHMSet b1) (MkHMSet b2) = MkHMSet (maxBox b1 b2)

||| Total Mass / Volume (`sumHMSet`): sums all active weights in `c`.
public export
sumHMSet : MultisetWeight c => HereditaryMSet c -> c
sumHMSet (MkHMSet b) = totalMassBox b

||| Pairwise box convolution parameterized by an inner key-combining operation.
public export
convolveWith : MultisetWeight c =>
               (HereditaryMSet c -> HereditaryMSet c -> HereditaryMSet c) ->
               HereditaryMSet c ->
               HereditaryMSet c ->
               HereditaryMSet c
convolveWith innerOp (MkHMSet b1) (MkHMSet b2) =
  MkHMSet (pairBoxWith innerOp b1 b2)

||| Level-indexed hyper-operation tower (`0 = +`, `1 = *`, `2 = ^`, ...):
||| preserves vertical nesting depth while combining sub-multiset keys at `level`.
public export
hyperOp : MultisetWeight c =>
          (level : Nat) ->
          HereditaryMSet c ->
          HereditaryMSet c ->
          HereditaryMSet c
hyperOp Z         = addHMSet
hyperOp (S level) = convolveWith (hyperOp level)

||| Wildberger Structural Multiplication (`*`):
||| Bilinearly combines elements via Level-1 `hyperOp` (`addHMSet` on keys),
||| weighted by `mulWeight w1 w2`.
public export
mulHMSet : MultisetWeight c => HereditaryMSet c -> HereditaryMSet c -> HereditaryMSet c
mulHMSet = hyperOp 1

||| Kuratowski Cartesian Outer Product (`><`):
||| Forms pure multiset pairs `{{k1}, {k1, k2}} = [[k1], [k1, k2]]` internally,
||| weighted by `mulWeight w1 w2`.
public export
outerHMSet : MultisetWeight c => HereditaryMSet c -> HereditaryMSet c -> HereditaryMSet c
outerHMSet (MkHMSet b1) (MkHMSet b2) =
  let one : c
      one = oneWeight {c}
      pairKey : HereditaryMSet c -> HereditaryMSet c -> HereditaryMSet c
      pairKey a b =
        let sa  = MkHMSet (setBox a one BoxLeaf)
            sab = MkHMSet (setBox b one (setBox a one BoxLeaf))
        in MkHMSet (setBox sab one (setBox sa one BoxLeaf))
  in MkHMSet $ foldBox (\k1, w1, accOuter =>
                         foldBox (\k2, w2, accInner =>
                                   addAtKeyBox (pairKey k1 k2) (mulWeight w1 w2) accInner)
                                 accOuter
                                 b2)
                       BoxLeaf
                       b1

------------------------------------------------------------------------
-- 4. CANONICAL SYMBOLIC ALGEBRA INSTANCES ON `HereditaryMSet c`
------------------------------------------------------------------------

public export
MultisetWeight c => Semigroup (HereditaryMSet c) where
  (<+>) = addHMSet

public export
MultisetWeight c => Monoid (HereditaryMSet c) where
  neutral = emptyHMSet

public export
MultisetWeight c => WeightedMultisetAlgebra c (HereditaryMSet c) where
  zeroWM     = emptyHMSet
  addWM      = addHMSet
  subWM      = subHMSet
  scaleWM    = scaleHMSet
  mulWM      = hadamardHMSet
  hadamardWM = hadamardHMSet
  minWM      = minHMSet
  maxWM      = maxHMSet
  dotWM      = dotHMSet

public export
MultisetWeight c => MultisetOuter (HereditaryMSet c) (HereditaryMSet c) (HereditaryMSet c) where
  (><) = outerHMSet

public export
MultisetAlgebra PureMultiset where
  zeroM     = emptyPureMSet
  addM      = addHMSet
  subM      = subHMSet
  scaleM    = scaleHMSet
  mulM      = hadamardHMSet
  hadamardM = hadamardHMSet
  minM      = minHMSet
  maxM      = maxHMSet
  dotM      = dotHMSet

public export
Num PureMultiset where
  (+) = addHMSet
  (*) = mulHMSet
  fromInteger n =
    let w = intToBoxInt n
    in if boxIsZero w then emptyPureMSet else MkHMSet (setBox emptyPureMSet w BoxLeaf)

public export
Neg PureMultiset where
  negate = negHMSet
  (-) = subHMSet


------------------------------------------------------------------------
-- CONSTRUCTIVIST HEREDITARY MULTISET RECOGNIZER (`recognition-rule.md`)
------------------------------------------------------------------------

public export
checkHMSetFuel : MultisetWeight c => Nat -> HereditaryMSet c -> Bool
checkHMSetFuel Z     (MkHMSet BoxLeaf) = True
checkHMSetFuel Z     _                 = False
checkHMSetFuel (S rem) (MkHMSet b) =
  case checkBoxBoundsBy (checkHMSetFuel rem) b of
    Nothing => False
    Just _  => True

||| Checks recursively (bounded by cached `hmDepth`) that every AVL node at every
||| hereditary level satisfies strict BST ordering, exact `boxHeight` caches,
||| AVL balance `<= 1`, and zero-pruned weights (`[M, M^a] = []`).
public export
isCanonicalHMSet : MultisetWeight c => HereditaryMSet c -> Bool
isCanonicalHMSet m = checkHMSetFuel (hmDepth m) m

||| Proof predicate witnessing recursive canonical well-formedness of `HereditaryMSet c`.
public export
IsCanonicalHMSet : MultisetWeight c => HereditaryMSet c -> Type
IsCanonicalHMSet m = (isCanonicalHMSet m = True)

||| Total `Dec` recognizer verifying external or deserialized `HereditaryMSet c` candidates.
public export
recognizeCanonicalHMSet : MultisetWeight c => (m : HereditaryMSet c) -> Dec (IsCanonicalHMSet m)
recognizeCanonicalHMSet m = decideBoolTrue (isCanonicalHMSet m)

||| Erased-proof `Subset` alias storing a verified `HereditaryMSet c`.
public export
CanonicalHMSet : (c : Type) -> MultisetWeight c => Type
CanonicalHMSet c = Subset (HereditaryMSet c) IsCanonicalHMSet

||| Smart constructor packing a verified `HereditaryMSet c` into `CanonicalHMSet c`.
public export
toCanonicalHMSet : MultisetWeight c => (m : HereditaryMSet c) -> Maybe (CanonicalHMSet c)
toCanonicalHMSet m =
  case recognizeCanonicalHMSet m of
    Yes prf => Just (Element m prf)
    No _    => Nothing

------------------------------------------------------------------------
-- 6. INTRINSIC `GohFuel` DERIVATION & SELF-FUELING ON `HereditaryMSet c`
------------------------------------------------------------------------

||| Backward-or-stay half-step dipole (`alpha^(-1) + 1`) as a `PureMultiset`.
public export
halfStepBackward : HereditaryMSet BoxInt
halfStepBackward =
  MkHMSet $ setBox (scalarKeyHMSet (-1)) (intToBoxInt 1)
          ( setBox (scalarKeyHMSet 0)    (intToBoxInt 1) BoxLeaf )

||| Forward-or-stay half-step dipole (`alpha^(+1) + 1`) as a `PureMultiset`.
public export
halfStepForward : HereditaryMSet BoxInt
halfStepForward =
  MkHMSet $ setBox (scalarKeyHMSet 0) (intToBoxInt 1)
          ( setBox (scalarKeyHMSet 1) (intToBoxInt 1) BoxLeaf )

||| Full symmetric motion tick (`(alpha^(-1) + 1) * (alpha^(+1) + 1) = alpha^(-1) + 2*alpha^0 + alpha^(+1)`).
public export
symmetricMotionTick : HereditaryMSet BoxInt
symmetricMotionTick = mulHMSet halfStepBackward halfStepForward

||| Fundamental binary polarity count (`2`) extracted directly as pure Peano `Nat`
||| from the two opposing non-origin poles (`-1` and `+1`) of `symmetricMotionTick`
||| inside the multiset algebra—zero `integerToNat` / `assert_total`, pure `Refl` reduction.
public export
elementaryPolarityCount : Nat
elementaryPolarityCount =
  let (MkHMSet box) = symmetricMotionTick
  in boxNodeCount (deleteBox emptyHMSet box)

||| Compile-time audit verifying `elementaryPolarityCount` reduces definitionally to `2`.
public export
0 prfElementaryPolarityTwo : Stage0.HereditaryMSet.elementaryPolarityCount = 2
prfElementaryPolarityTwo = Refl

||| Two boundary endpoints (`low` entry `Skip` and `high` exit `Skip`)
||| required to bracket any finite causal interval `[low, high]`.
public export
boundaryBracketOverhead : Nat
boundaryBracketOverhead = elementaryPolarityCount

||| Spatial axis count (`3` dimensions: center + 2 opposing poles).
public export
spatialAxisCount : Nat
spatialAxisCount = S elementaryPolarityCount

||| Helper to calculate `2^n` for `Nat` buffer depth from `elementaryPolarityCount`.
public export
fastNatPower2 : Nat -> Nat
fastNatPower2 Z     = S Z
fastNatPower2 (S k) = elementaryPolarityCount * fastNatPower2 k

||| Division by `2` via structural recursion.
public export
half : Nat -> Nat
half Z         = Z
half (S Z)     = Z
half (S (S k)) = S (half k)

||| Monomorphic less-than-or-equal test on inductive Peano `Nat` for fuel budgets.
public export
fuelLTE : Nat -> Nat -> Bool
fuelLTE Z _         = True
fuelLTE (S _) Z     = False
fuelLTE (S k) (S j) = fuelLTE k j

||| Monomorphic maximum on inductive Peano `Nat` for fuel envelopes.
public export
fuelMax : Nat -> Nat -> Nat
fuelMax Z b         = b
fuelMax a Z         = a
fuelMax (S a) (S b) = S (fuelMax a b)

||| Canonical Goh factorisation formula computing exact fuel steps natively in `Nat`:
||| `Fuel(S k) = S k + floor(k/2) + boundaryBracketOverhead` (e.g. `Fuel(210) = 316`).
public export
gohFuelNat : Nat -> Nat
gohFuelNat Z     = S Z
gohFuelNat (S k) = S k + half k + boundaryBracketOverhead

||| First-class constructivist Goh Fuel indexed directly by model capacity.
public export
record GohFuel (capacity : Nat) where
  constructor MkGohFuel
  fuelSteps : Nat

public export
Eq (GohFuel cap) where
  (MkGohFuel s1) == (MkGohFuel s2) = s1 == s2

public export
Show (GohFuel cap) where
  show (MkGohFuel s) = "GohFuel(" ++ show s ++ " steps)"

||| Canonical smart constructor generating exact fuel from capacity.
public export
gohFuelForCapacity : (capacity : Nat) -> GohFuel capacity
gohFuelForCapacity cap = MkGohFuel (gohFuelNat cap)

||| Zero-cost projection to raw steps for loop pattern-matching (`Z` and `S f`).
public export
gohSteps : GohFuel cap -> Nat
gohSteps f = f.fuelSteps

||| Existential model-indexed `GohFuel` envelope for streams whose active capacity is
||| derived dynamically from a `HereditaryMSet c` support summary.
public export
data AnyGohFuel : Type where
  MkAnyGohFuel : (capacity : Nat) -> GohFuel capacity -> AnyGohFuel

public export
Eq AnyGohFuel where
  (MkAnyGohFuel c1 f1) == (MkAnyGohFuel c2 f2) = c1 == c2 && gohSteps f1 == gohSteps f2

public export
Show AnyGohFuel where
  show (MkAnyGohFuel cap gf) = "AnyGohFuel(cap=" ++ show cap ++ ", steps=" ++ show (gohSteps gf) ++ ")"

||| Constructs an existential `GohFuel` envelope from a derived natural capacity.
public export
anyGohFuel : (capacity : Nat) -> AnyGohFuel
anyGohFuel cap = MkAnyGohFuel cap (gohFuelForCapacity cap)

||| Extracts the raw step budget from an existential `GohFuel` envelope.
public export
anyGohSteps : AnyGohFuel -> Nat
anyGohSteps (MkAnyGohFuel _ gf) = gohSteps gf

||| Single-pass invariants extracted polymorphically from any `HereditaryMSet c`:
||| - `nnz`       : Support cardinality `chi_Supp(1)` (non-zero entries)
||| - `totalMass` : Absolute multiplicity magnitude sum via `weightMagnitude`
||| - `maxDeg`    : Maximum structural degree / nesting height encountered
public export
record SupportStats where
  constructor MkSupportStats
  nnz       : Nat
  totalMass : Nat
  maxDeg    : Nat

public export
emptySupportStats : SupportStats
emptySupportStats = MkSupportStats 0 0 0

||| Extracts the maximum nested `weightMagnitude` inside a hereditary box
||| bounded cleanly by remaining hereditary nesting depth `fuel`.
public export
maxWeightInBox : MultisetWeight c => Nat -> Box c (HereditaryMSet c) -> Nat
maxWeightInBox Z _ = 0
maxWeightInBox (S rem) box = goBox box
  where
    goBox : Box c (HereditaryMSet c) -> Nat
    goBox BoxLeaf = 0
    goBox (BoxNode _ l (MkHMSet sub) w r) =
      let here = fuelMax (weightMagnitude w) (maxWeightInBox rem sub)
      in fuelMax (goBox l) (fuelMax here (goBox r))

||| Polymorphic single-pass AVL fold updating `nnz`, `totalMass`, and `maxDeg` across
||| any `MultisetWeight c` carrier (`BoxInt`, `SignedBit`, or `MultisetBit`).
public export
collectSupportStats : MultisetWeight c => Box c (HereditaryMSet c) -> SupportStats
collectSupportStats BoxLeaf = emptySupportStats
collectSupportStats (BoxNode _ left (MkHMSet innerBox) w right) =
  let lStats     = collectSupportStats left
      rStats     = collectSupportStats right
      absW       = weightMagnitude w
      childDeg   = case innerBox of
                     BoxLeaf => 0
                     BoxNode _ BoxLeaf (MkHMSet BoxLeaf) expW BoxLeaf =>
                       weightMagnitude expW
                     _ => fuelMax (boxHeight innerBox) (maxWeightInBox (boxNestedDepth innerBox) innerBox)
      selfNnz    = if isZero w then 0 else 1
      mergedNnz  = lStats.nnz + selfNnz + rStats.nnz
      mergedMass = lStats.totalMass + absW + rStats.totalMass
      mergedMax  = fuelMax lStats.maxDeg (fuelMax childDeg rStats.maxDeg)
  in MkSupportStats mergedNnz mergedMass mergedMax

||| Classifies binary multiset interactions for tight `multiStreamFuelOfHMSet` / `hyperOpFuelOfHMSet` sizing.
public export
data InteractionMode : Type where
  AdditiveMode      : InteractionMode
  IntersectionMode  : InteractionMode
  ConvolutionalMode : InteractionMode
  CaretationMode    : InteractionMode

public export
combineSupportStats : InteractionMode -> SupportStats -> SupportStats -> SupportStats
combineSupportStats AdditiveMode a b =
  MkSupportStats (a.nnz + b.nnz) (a.totalMass + b.totalMass) (fuelMax a.maxDeg b.maxDeg)
combineSupportStats IntersectionMode a b =
  MkSupportStats (min a.nnz b.nnz) (min a.totalMass b.totalMass) (min a.maxDeg b.maxDeg)
combineSupportStats ConvolutionalMode a b =
  MkSupportStats (a.nnz * b.nnz) (a.totalMass * b.totalMass) (a.maxDeg + b.maxDeg)
combineSupportStats CaretationMode a b =
  MkSupportStats (a.nnz * b.nnz) (a.totalMass * b.totalMass) (a.maxDeg * b.maxDeg)

public export
mkBudgetFromStatsWith : (Nat -> Nat) -> (cap : Nat) -> (treeBound : Nat) -> SupportStats -> (GohFuel cap, Nat)
mkBudgetFromStatsWith fuelFn cap treeBound stats =
  let boundedCap = min cap (stats.nnz + S stats.maxDeg)
      ySteps     = fuelFn boundedCap
      yieldFuel  = MkGohFuel ySteps
      stepBudget = ySteps + treeBound + stats.nnz
  in (yieldFuel, stepBudget)

public export
mkBudgetFromStats : (cap : Nat) -> (treeBound : Nat) -> SupportStats -> (GohFuel cap, Nat)
mkBudgetFromStats = mkBudgetFromStatsWith gohFuelNat

||| Polymorphic single-pass `(yieldFuel, stepBudget)` sizer directly over `HereditaryMSet c`
||| (`BoxInt`, `SignedBit`, or `MultisetBit`), clamped to `cap`.
public export
fuelOfHMSet : MultisetWeight c => (cap : Nat) -> HereditaryMSet c -> (GohFuel cap, Nat)
fuelOfHMSet cap (MkHMSet rootBox) =
  mkBudgetFromStats cap (fastNatPower2 (boxHeight rootBox)) (collectSupportStats rootBox)

||| Parameterized uncapped intrinsic self-fuel extractor deriving `cap = nnz + S maxDeg`
||| directly from a `HereditaryMSet c` with a caller-supplied fuel scaling law.
public export
selfFuelOfHMSetWith : MultisetWeight c => (Nat -> Nat) -> HereditaryMSet c -> (AnyGohFuel, Nat)
selfFuelOfHMSetWith fuelFn (MkHMSet rootBox) =
  let treeBound  = fastNatPower2 (boxHeight rootBox)
      stats      = collectSupportStats rootBox
      cap        = stats.nnz + S stats.maxDeg
      ySteps     = fuelFn cap
      yieldFuel  = MkGohFuel ySteps
      stepBudget = ySteps + treeBound + stats.nnz
  in (MkAnyGohFuel cap yieldFuel, stepBudget)

||| Uncapped intrinsic self-fuel extractor deriving `cap = nnz + S maxDeg` directly
||| from a `HereditaryMSet c` without requiring an external capacity ceiling.
public export
selfFuelOfHMSet : MultisetWeight c => HereditaryMSet c -> (AnyGohFuel, Nat)
selfFuelOfHMSet = selfFuelOfHMSetWith gohFuelNat

||| Strictly O(1) height-only `GohFuel` upper bound derived from cached `boxTreeCapacityBound`
||| (`2^h - 1`) without traversing the AVL tree.
public export
quickFuelOfHMSet : (cap : Nat) -> HereditaryMSet c -> GohFuel cap
quickFuelOfHMSet cap (MkHMSet rootBox) =
  MkGohFuel (gohFuelNat (min cap (boxTreeCapacityBound rootBox)))

||| Binary multi-stream fuel combiner directly over `HereditaryMSet c`.
public export
multiStreamFuelOfHMSet : MultisetWeight c =>
                         (cap : Nat) ->
                         InteractionMode ->
                         HereditaryMSet c ->
                         HereditaryMSet c ->
                         (GohFuel cap, Nat)
multiStreamFuelOfHMSet cap mode (MkHMSet boxA) (MkHMSet boxB) =
  let treeBound = fastNatPower2 (boxHeight boxA) + fastNatPower2 (boxHeight boxB)
      combined  = combineSupportStats mode (collectSupportStats boxA) (collectSupportStats boxB)
  in mkBudgetFromStats cap treeBound combined

public export
pairHyperOpFuelHM : MultisetWeight c =>
                    InteractionMode ->
                    (extraBound : Nat) ->
                    (cap : Nat) ->
                    HereditaryMSet c ->
                    HereditaryMSet c ->
                    (GohFuel cap, Nat)
pairHyperOpFuelHM mode extraBound cap (MkHMSet boxA) (MkHMSet boxB) =
  let baseBound = fastNatPower2 (boxHeight boxA + boxHeight boxB)
      pairBound = if extraBound == 0 then baseBound else baseBound + extraBound
      combined  = combineSupportStats mode (collectSupportStats boxA) (collectSupportStats boxB)
  in mkBudgetFromStats cap pairBound combined

||| Polymorphic level-aware `hyperOp` fuel sizer directly over `HereditaryMSet c`:
||| - Level `0` (`+`): `AdditiveMode` with `2^hA + 2^hB` tree bound.
||| - Level `1` (`*`): `ConvolutionalMode` with exact pairwise bound `2^(hA + hB)`.
||| - Level `2+` (`^`, ...): `CaretationMode` (`maxDeg = dA * dB`) with `2^(hA + hB) + boundaryBracketOverhead`.
public export
hyperOpFuelOfHMSet : MultisetWeight c =>
                     (level : Nat) ->
                     (cap : Nat) ->
                     HereditaryMSet c ->
                     HereditaryMSet c ->
                     (GohFuel cap, Nat)
hyperOpFuelOfHMSet Z cap mA mB = multiStreamFuelOfHMSet cap AdditiveMode mA mB
hyperOpFuelOfHMSet (S Z) cap mA mB = pairHyperOpFuelHM ConvolutionalMode 0 cap mA mB
hyperOpFuelOfHMSet (S (S _)) cap mA mB = pairHyperOpFuelHM CaretationMode boundaryBracketOverhead cap mA mB
