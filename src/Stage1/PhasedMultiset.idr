module Stage1.PhasedMultiset

import public Stage0.BoxInt
import public Stage0.Box
import public Stage0.SignedBit
import public Stage0.HereditaryMSet
import public Stage0.StructuralFuel
import public Stage0.OnSeq.FusedStream
import public Stage1.ConvolutionAdmissibility
import public Stage1.Views

%default total

------------------------------------------------------------------------
-- 1. UNIFIED PHASE INDEX (`0`-QUANTITY COMPILE-TIME METADATA)
------------------------------------------------------------------------

public export
record AlgebraicPhase where
  constructor MkPhase
  hyperLevel : Nat
  regime     : LaurentRegime
  fuelCap    : Nat

||| Zero-overhead phased multiset wrapper:
||| Erases to `HereditaryMSet c` at runtime while enforcing `hyperLevel`,
||| `LaurentRegime`, and `GohFuel` invariants at compile time.
public export
record Multiset (0 phase : AlgebraicPhase) (c : Type) where
  constructor MkPhasedMSet
  rawHMSet : HereditaryMSet c

------------------------------------------------------------------------
-- 2. PHASE-AWARE ALGEBRAIC OPERATIONS (`+`, `*`, `^`, `<.>`)
------------------------------------------------------------------------

||| Level 0 Superposition (`+`): Valid across every `AlgebraicPhase`.
public export
addPhased : MultisetWeight c =>
            {0 phase : AlgebraicPhase} ->
            Stage1.PhasedMultiset.Multiset phase c ->
            Stage1.PhasedMultiset.Multiset phase c ->
            Stage1.PhasedMultiset.Multiset phase c
addPhased (MkPhasedMSet a) (MkPhasedMSet b) =
  MkPhasedMSet (addHMSet a b)

||| Exact signed subtraction (`-`): Zero-pruning cancellation across every `AlgebraicPhase`.
public export
subPhased : MultisetWeight c =>
            {0 phase : AlgebraicPhase} ->
            Stage1.PhasedMultiset.Multiset phase c ->
            Stage1.PhasedMultiset.Multiset phase c ->
            Stage1.PhasedMultiset.Multiset phase c
subPhased (MkPhasedMSet a) (MkPhasedMSet b) =
  MkPhasedMSet (subHMSet a b)

||| Scalar carrier weighting across every `AlgebraicPhase`.
public export
scalePhased : MultisetWeight c =>
              {0 phase : AlgebraicPhase} ->
              c ->
              Stage1.PhasedMultiset.Multiset phase c ->
              Stage1.PhasedMultiset.Multiset phase c
scalePhased s (MkPhasedMSet a) =
  MkPhasedMSet (scaleHMSet s a)

||| Pointwise Hadamard mask/interaction (`.*.`) within a shared `AlgebraicPhase`.
public export
hadamardPhased : MultisetWeight c =>
                 {0 phase : AlgebraicPhase} ->
                 Stage1.PhasedMultiset.Multiset phase c ->
                 Stage1.PhasedMultiset.Multiset phase c ->
                 Stage1.PhasedMultiset.Multiset phase c
hadamardPhased (MkPhasedMSet a) (MkPhasedMSet b) =
  MkPhasedMSet (hadamardHMSet a b)

||| Pointwise Hadamard horizon slicing (`.*.`) intersecting an arbitrary `rA` carrier
||| with a certified bounded mask `rMask`, tightening the result into `(rMask, min c1 cM)`.
public export
hadamardSlicePhased : MultisetWeight c =>
                      {0 lvl : Nat} -> {0 rA, rMask : LaurentRegime} -> {0 c1, cM : Nat} ->
                      {auto 0 ok : BoundedRegime rMask} ->
                      Multiset (MkPhase lvl rA c1) c ->
                      Multiset (MkPhase lvl rMask cM) c ->
                      Multiset (MkPhase lvl rMask (min c1 cM)) c
hadamardSlicePhased (MkPhasedMSet a) (MkPhasedMSet m) =
  MkPhasedMSet (hadamardHMSet a m)

||| Unitary contact reflection `psi - 2 * (psi .*. mask)` inverting Black/Red polarity
||| on the support selected by an indicator `{0, 1}` mask multiset.
public export
contactReflectPhased : {0 phase : AlgebraicPhase} ->
                       Multiset phase BoxInt ->
                       Multiset phase BoxInt ->
                       Multiset phase BoxInt
contactReflectPhased psi mask =
  subPhased psi (scalePhased (intToBoxInt 2) (hadamardPhased psi mask))

||| Level 1 Cauchy Convolution (`*`): Guarded by `CanConvolve` on `regime`
||| and combines fuel capacities additively (`c1 + c2`).
public export
mulPhased : MultisetWeight c =>
            {0 lvl : Nat} -> {0 rA, rB, rOut : LaurentRegime} -> {0 c1, c2 : Nat} ->
            {auto 0 ok : admissibleConvolution rA rB = Just rOut} ->
            Multiset (MkPhase lvl rA c1) c ->
            Multiset (MkPhase lvl rB c2) c ->
            Multiset (MkPhase lvl rOut (c1 + c2)) c
mulPhased (MkPhasedMSet a) (MkPhasedMSet b) =
  MkPhasedMSet (mulHMSet a b)

||| Level 2 Dirichlet Caretation (`^`): Requires `hyperLevel = S (S lvl)` (`>= 2`)
||| and `caretRegime rA rB = Just rOut`, guaranteeing sound degree bounds at compile time.
public export
caretPhased : MultisetWeight c =>
              {0 lvl : Nat} -> {0 rA, rB, rOut : LaurentRegime} -> {0 c1, c2 : Nat} ->
              {auto 0 ok : caretRegime rA rB = Just rOut} ->
              Multiset (MkPhase (S (S lvl)) rA c1) c ->
              Multiset (MkPhase (S (S lvl)) rB c2) c ->
              Multiset (MkPhase (S (S lvl)) rOut (c1 * c2)) c
caretPhased (MkPhasedMSet a) (MkPhasedMSet b) =
  MkPhasedMSet (hyperOp 2 a b)

||| Bounded Inner Product / Trace (`<.>`): Statically restricted to compact
||| `StaticHorizon` or `BoundedHorizon` regimes (disallowed on `OpenFuture`).
public export
dotStaticPhased : MultisetWeight c =>
                  {0 lvl : Nat} -> {0 low, high : Integer} -> {0 cap : Nat} ->
                  Multiset (MkPhase lvl (StaticHorizon low high) cap) c ->
                  Multiset (MkPhase lvl (StaticHorizon low high) cap) c ->
                  c
dotStaticPhased (MkPhasedMSet a) (MkPhasedMSet b) =
  dotHMSet a b

------------------------------------------------------------------------
-- 3. TYPED PHASE PROMOTION & FREEZE-OUT TRANSITIONS
------------------------------------------------------------------------

||| Partitions a `PureMultiset` into strictly positive scalar degrees (`e >= 1`, `Poly*`)
||| and the complementary non-positive/nested residue (`e <= 0`), conserving total mass.
public export
partitionPolyStarPure : PureMultiset -> (PureMultiset, PureMultiset)
partitionPolyStarPure (MkHMSet box) =
  let (posBox, resBox) =
        foldBox (\key, w, (posAcc, resAcc) =>
                   case classifyLaurentKey unwrapBox key of
                     ExponentKey e =>
                       if e >= 1
                         then (addAtKeyBox key w posAcc, resAcc)
                         else (posAcc, addAtKeyBox key w resAcc)
                     NestedTermKey _ =>
                       (posAcc, addAtKeyBox key w resAcc))
                (BoxLeaf, BoxLeaf)
                box
  in (MkHMSet posBox, MkHMSet resBox)

||| Promotes a Level-1 `PureMultiset` Laurent multiset into a Level-2 `Poly*` multiset
||| (`minAllowedDegree = 1`), tightening `reg` via `polyStarRegime reg` and returning
||| both the zero-free `Poly*` core (`e >= 1`) and the non-positive residue (`e <= 0`).
public export
partitionPolyStarPhased : {0 reg : LaurentRegime} -> {0 cap : Nat} ->
                          Stage1.PhasedMultiset.Multiset (MkPhase 1 reg cap) BoxInt ->
                          (Stage1.PhasedMultiset.Multiset (MkPhase 2 (polyStarRegime reg) cap) BoxInt, PureMultiset)
partitionPolyStarPhased (MkPhasedMSet m) =
  let (posM, resM) = partitionPolyStarPure m
  in (MkPhasedMSet posM, resM)

||| Promotes a Level-1 `PureMultiset` Laurent multiset into a Level-2 `Poly*`
||| (`NatStar`, strictly `e >= 1`) multiset, tightening `reg` via `polyStarRegime reg`.
public export
promoteToPolyStar : {0 reg : LaurentRegime} -> {0 cap : Nat} ->
                    Stage1.PhasedMultiset.Multiset (MkPhase 1 reg cap) BoxInt ->
                    Stage1.PhasedMultiset.Multiset (MkPhase 2 (polyStarRegime reg) cap) BoxInt
promoteToPolyStar m = fst (partitionPolyStarPhased m)

||| Extracts self-carrying `GohFuel` directly from `phase.fuelCap` without
||| requiring the caller to pass `cap` manually.
public export
phasedFuelOf : {0 lvl : Nat} -> {0 reg : LaurentRegime} -> {cap : Nat} ->
               Multiset (MkPhase lvl reg cap) BoxInt ->
               (GohFuel cap, Nat)
phasedFuelOf (MkPhasedMSet m) = fuelOfM cap m

||| Minimum permitted scalar Laurent exponent at a given `AlgebraicPhase`:
||| - Level `0` (`+`) & Level `1` (`*`): `0` (all integer keys allowed; negative degrees valid).
||| - Level `2` (`^`, `Poly*`): `1` (excludes `0` pole).
||| - Level `3+`: `natToInteger (minus hyperLevel 1)` (excludes absorbing fixed points).
public export
minAllowedDegree : AlgebraicPhase -> Integer
minAllowedDegree ph =
  case ph.hyperLevel of
    Z     => 0
    S Z   => 0
    S lvl => natToInteger lvl

||| Bounded inner product (`<.>`) statically guarded by `BoundedRegime reg`
||| (`StaticHorizon`, `BoundedHorizon`, `RetroBoundedHorizon`, `WindowedHorizon`).
public export
dotBoundedPhased : MultisetWeight c =>
                   {0 lvl : Nat} -> {0 reg : LaurentRegime} -> {0 cap : Nat} ->
                   {auto 0 ok : BoundedRegime reg} ->
                   Multiset (MkPhase lvl reg cap) c ->
                   Multiset (MkPhase lvl reg cap) c ->
                   c
dotBoundedPhased (MkPhasedMSet a) (MkPhasedMSet b) = dotHMSet a b

||| Bounded total mass (`sumHMSet`) statically guarded by `BoundedRegime reg`.
public export
sumBoundedPhased : MultisetWeight c =>
                   {0 lvl : Nat} -> {0 reg : LaurentRegime} -> {0 cap : Nat} ->
                   {auto 0 ok : BoundedRegime reg} ->
                   Multiset (MkPhase lvl reg cap) c ->
                   c
sumBoundedPhased (MkPhasedMSet a) = sumHMSet a

||| Constructive `Dec` recognizer validating canonical AVL structure on a phased multiset.
public export
recognizeCanonicalPhased : MultisetWeight c =>
                           {0 phase : AlgebraicPhase} ->
                           (m : Stage1.PhasedMultiset.Multiset phase c) ->
                           Dec (IsCanonicalHMSet m.rawHMSet)
recognizeCanonicalPhased (MkPhasedMSet m) = recognizeCanonicalHMSet m

------------------------------------------------------------------------
-- 5. LAURENT REGIMES AS MULTISETS (CARRIER PROGRESSION)
------------------------------------------------------------------------

||| Carrier progression for Laurent Horizon indicators:
||| - `MultisetBit`: Unsigned support topology ({0, 1})
||| - `SignedBit`  : Balanced ternary polarity / causal direction ({-1, 0, +1})
||| - `BoxInt`     : Weighted multiplicity / channel capacity (ℤ)

||| Generates the unsigned support multiset (`Carrier MultisetBit Integer`) for a regime
||| truncated to the observation interval `[low, high]`.
public export
regimeSupportBit : LaurentRegime -> Integer -> Integer -> Box MultisetBit Integer
regimeSupportBit reg low high =
  foldl (\acc, k =>
           if inRegime reg k
             then addAtKeyBox k OneBit acc
             else acc)
        BoxLeaf
        [low .. high]
  where
    inRegime : LaurentRegime -> Integer -> Bool
    inRegime (StaticHorizon l h)       k = (k >= l) && (k <= h)
    inRegime (BoundedHorizon cap)      k = (k >= 0) && (k <= natToInteger cap)
    inRegime (RetroBoundedHorizon cap) k = (k >= - (natToInteger cap)) && (k <= 0)
    inRegime (WindowedHorizon win)     k =
      let half = (natToInteger win) `div` 2
      in (k >= -half) && (k <= half)
    inRegime OpenFuture                k = k >= 0
    inRegime BilateralOpen             _ = True

||| Generates the directional / chiral multiset (`Carrier SignedBit Integer`) for a regime:
||| - `PosBit` (+1) on forward causal / matter rays (`BoundedHorizon`, `OpenFuture`)
||| - `NegBit` (-1) on backward UV / antimatter rays (`RetroBoundedHorizon`)
||| - `ZeroBit` (0) outside the horizon
public export
regimeSignedBit : LaurentRegime -> Integer -> Integer -> Box SignedBit Integer
regimeSignedBit reg low high =
  foldl (\acc, k =>
           case signedWeight reg k of
             ZeroBit => acc
             bit     => addAtKeyBox k bit acc)
        BoxLeaf
        [low .. high]
  where
    signedWeight : LaurentRegime -> Integer -> SignedBit
    signedWeight (StaticHorizon l h)       k = if (k >= l) && (k <= h) then PosBit else ZeroBit
    signedWeight (BoundedHorizon cap)      k = if (k >= 0) && (k <= natToInteger cap) then PosBit else ZeroBit
    signedWeight (RetroBoundedHorizon cap) k = if (k >= - (natToInteger cap)) && (k <= 0) then NegBit else ZeroBit
    signedWeight (WindowedHorizon win)     k =
      let half = (natToInteger win) `div` 2
      in if (k >= -half) && (k <= half) then PosBit else ZeroBit
    signedWeight OpenFuture                k = if k >= 0 then PosBit else ZeroBit
    signedWeight BilateralOpen             k = if k >= 0 then PosBit else NegBit

||| Generates the weighted indicator multiset (`Carrier BoxInt Integer`) of a regime
||| with uniform weight 1 on its support.
public export
regimeBoxInt : LaurentRegime -> Integer -> Integer -> Box BoxInt Integer
regimeBoxInt reg low high =
  foldl (\acc, k =>
           if inRegime reg k
             then addAtKeyBox k (intToBoxInt 1) acc
             else acc)
        BoxLeaf
        [low .. high]
  where
    inRegime : LaurentRegime -> Integer -> Bool
    inRegime (StaticHorizon l h)       k = (k >= l) && (k <= h)
    inRegime (BoundedHorizon cap)      k = (k >= 0) && (k <= natToInteger cap)
    inRegime (RetroBoundedHorizon cap) k = (k >= - (natToInteger cap)) && (k <= 0)
    inRegime (WindowedHorizon win)     k =
      let half = (natToInteger win) `div` 2
      in (k >= -half) && (k <= half)
    inRegime OpenFuture                k = k >= 0
    inRegime BilateralOpen             _ = True

||| Slices a localized WindowedHorizon win shell from an Integer-indexed Box multiset
||| centered around `center`.
public export
sliceWindowInt : MultisetWeight c => (win : Nat) -> (center : Integer) -> Box c Integer -> Box c Integer
sliceWindowInt win center box =
  let half = (natToInteger win) `div` 2
      low  = center - half
      high = center + half
      mask : Box c Integer
      mask = foldl (\acc, k => addAtKeyBox k (the c oneWeight) acc) BoxLeaf [low .. high]
  in hadamardBox box mask
