module Stage0.SignedBit

import public Stage0.BoxInt
import public Stage0.HereditaryMSet

%default total

------------------------------------------------------------------------
-- 1. UNSIGNED SUPPORT BIT (`EmptyBit = []`, `OneBit = [[]]`)
------------------------------------------------------------------------

||| Unsigned support bit representing occupancy (`EmptyBit = []`, `OneBit = [[]]`)
||| and modulo-2 fermionic parity (`Z_2`).
public export
data MultisetBit : Type where
  EmptyBit : MultisetBit
  OneBit   : MultisetBit

public export
Eq MultisetBit where
  EmptyBit == EmptyBit = True
  OneBit   == OneBit   = True
  _        == _        = False

public export
Ord MultisetBit where
  compare EmptyBit EmptyBit = EQ
  compare EmptyBit OneBit   = LT
  compare OneBit   EmptyBit = GT
  compare OneBit   OneBit   = EQ

public export
Show MultisetBit where
  show EmptyBit = "0"
  show OneBit   = "1"

||| Modulo-2 (`Z_2`) weight instance for `HereditaryMSet MultisetBit`
public export
MultisetWeight MultisetBit where
  zeroWeight        = EmptyBit
  oneWeight         = OneBit
  isZero EmptyBit   = True
  isZero OneBit     = False
  addWeight EmptyBit y        = y
  addWeight x        EmptyBit = x
  addWeight OneBit   OneBit   = EmptyBit -- Pauli exclusion / Z_2 cancellation
  negWeight x                 = x        -- Self-inverse in Z_2
  mulWeight OneBit   OneBit   = OneBit
  mulWeight _        _        = EmptyBit
  minWeight OneBit   OneBit   = OneBit
  minWeight _        _        = EmptyBit
  maxWeight EmptyBit y        = y
  maxWeight x        EmptyBit = x
  maxWeight OneBit   OneBit   = OneBit

public export
QuantumCarrier MultisetBit where
  peelQuantum EmptyBit = Nothing
  peelQuantum OneBit   = Just (Left EmptyBit)

------------------------------------------------------------------------
-- 2. SIGNED BIT / POLARITY CARRIER (`[]`, `[[]]`, `[-[]]`)
------------------------------------------------------------------------

||| Balanced ternary polarity carrier capturing Wildberger's vacuum split
||| `[] = [+1, -1]` and mutual annihilation (`PosBit + NegBit = ZeroBit`):
||| - `ZeroBit` : Empty vacuum `[]` (`0`)
||| - `PosBit`  : Positive Black quantum `[[]]` (`+1`)
||| - `NegBit`  : Negative Red quantum `[-[]]` (`-1`)
public export
data SignedBit : Type where
  ZeroBit : SignedBit
  PosBit  : SignedBit
  NegBit  : SignedBit

public export
Eq SignedBit where
  ZeroBit == ZeroBit = True
  PosBit  == PosBit  = True
  NegBit  == NegBit  = True
  _       == _       = False

public export
Ord SignedBit where
  compare NegBit  NegBit  = EQ
  compare NegBit  _       = LT
  compare ZeroBit NegBit  = GT
  compare ZeroBit ZeroBit = EQ
  compare ZeroBit PosBit  = LT
  compare PosBit  PosBit  = EQ
  compare PosBit  _       = GT

public export
Show SignedBit where
  show ZeroBit = "0"
  show PosBit  = "+1"
  show NegBit  = "-1"

------------------------------------------------------------------------
-- 3. POLARITY ALGEBRA OPERATIONS
------------------------------------------------------------------------

||| Flips Black (`+1`) <-> Red (`-1`), leaving vacuum `0` invariant.
public export
negateSignedBit : SignedBit -> SignedBit
negateSignedBit ZeroBit = ZeroBit
negateSignedBit PosBit  = NegBit
negateSignedBit NegBit  = PosBit

||| Saturated addition with exact matter-antimatter annihilation:
||| - `PosBit + NegBit = ZeroBit`
||| - `PosBit + PosBit = PosBit` (Fermionic saturation)
||| - `NegBit + NegBit = NegBit`
public export
addSignedBit : SignedBit -> SignedBit -> SignedBit
addSignedBit ZeroBit y       = y
addSignedBit x       ZeroBit = x
addSignedBit PosBit  NegBit  = ZeroBit
addSignedBit NegBit  PosBit  = ZeroBit
addSignedBit PosBit  PosBit  = PosBit
addSignedBit NegBit  NegBit  = NegBit

||| Signed multiplication over `{-1, 0, +1}` (`NegBit * NegBit = PosBit`).
public export
mulSignedBit : SignedBit -> SignedBit -> SignedBit
mulSignedBit ZeroBit _       = ZeroBit
mulSignedBit _       ZeroBit = ZeroBit
mulSignedBit PosBit  y       = y
mulSignedBit NegBit  PosBit  = NegBit
mulSignedBit NegBit  NegBit  = PosBit

||| Lattice meet (`min`) under `NegBit < ZeroBit < PosBit`.
public export
minSignedBit : SignedBit -> SignedBit -> SignedBit
minSignedBit a b = if a <= b then a else b

||| Lattice join (`max`) under `NegBit < ZeroBit < PosBit`.
public export
maxSignedBit : SignedBit -> SignedBit -> SignedBit
maxSignedBit a b = if a >= b then a else b

------------------------------------------------------------------------
-- 4. `MultisetWeight` & `QuantumCarrier` INSTANCES FOR `SignedBit`
------------------------------------------------------------------------

||| Enables all 7 core calculus operators (`+`, `-`, `*`, `.*.`, `<.>`, `/\`, `\/`)
||| directly on `HereditaryMSet SignedBit` and `Box SignedBit k`.
public export
MultisetWeight SignedBit where
  zeroWeight  = ZeroBit
  oneWeight   = PosBit
  isZero ZeroBit = True
  isZero _       = False
  addWeight   = addSignedBit
  negWeight   = negateSignedBit
  mulWeight   = mulSignedBit
  minWeight   = minSignedBit
  maxWeight   = maxSignedBit

||| Enables `viewAsAntiBox` to peel `PopBlackBox` for `PosBit` and `PopRedBox` for `NegBit`.
public export
QuantumCarrier SignedBit where
  peelQuantum ZeroBit = Nothing
  peelQuantum PosBit  = Just (Left ZeroBit)
  peelQuantum NegBit  = Just (Right ZeroBit)

------------------------------------------------------------------------
-- 5. CARRIER PROJECTION CHAIN (`BoxInt` -> `SignedBit` -> `MultisetBit`)
------------------------------------------------------------------------

||| Clamps an arbitrary `BoxInt` multiplicity into `SignedBit` (`signum` projection).
public export
boxIntToSignedBit : BoxInt -> SignedBit
boxIntToSignedBit (MkBoxInt w) =
  if w > 0 then PosBit
  else if w < 0 then NegBit
  else ZeroBit

||| Projects `SignedBit` onto its unsigned support `MultisetBit` (`PosBit | NegBit -> OneBit`).
public export
toMultisetBit : SignedBit -> MultisetBit
toMultisetBit ZeroBit = EmptyBit
toMultisetBit PosBit  = OneBit
toMultisetBit NegBit  = OneBit

||| Lifts `SignedBit` back into `BoxInt` (`-1`, `0`, or `+1`).
public export
signedBitToBoxInt : SignedBit -> BoxInt
signedBitToBoxInt ZeroBit = intToBoxInt 0
signedBitToBoxInt PosBit  = intToBoxInt 1
signedBitToBoxInt NegBit  = intToBoxInt (-1)

||| Converts `SignedBit` to a raw `Integer` (`-1`, `0`, `1`) for `viewAsLaurent`.
public export
signedBitToInteger : SignedBit -> Integer
signedBitToInteger ZeroBit = 0
signedBitToInteger PosBit  = 1
signedBitToInteger NegBit  = (-1)


------------------------------------------------------------------------
-- PHASE CARRIER PROJECTIONS (`BoxInt -> SignedBit -> MultisetBit`)
------------------------------------------------------------------------

private
toSupportMSetLoop : Nat -> HereditaryMSet BoxInt -> HereditaryMSet MultisetBit
toSupportMSetLoop Z _ = emptyHMSet
toSupportMSetLoop (S rem) (MkHMSet box) =
  MkHMSet $
    foldBox (\key, weight, acc =>
              if isZero weight
                then acc
                else setBox (toSupportMSetLoop rem key) OneBit acc)
            BoxLeaf
            box

||| Geometric support extraction (`HereditaryMSet BoxInt -> HereditaryMSet MultisetBit`),
||| collapsing all non-zero multiplicities to `OneBit` (`[[]]`) using idempotent
||| union (`setBox`) so distinct inner sub-multisets cannot parity-cancel.
||| Feeds `Stage0.StructuralFuel.fuelFromSupport`.
public export
toSupportMSet : HereditaryMSet BoxInt -> HereditaryMSet MultisetBit
toSupportMSet m = toSupportMSetLoop (hmDepth m) m

private
freezeToSignedPhaseLoop : Nat -> HereditaryMSet BoxInt -> HereditaryMSet SignedBit
freezeToSignedPhaseLoop Z _ = emptyHMSet
freezeToSignedPhaseLoop (S rem) (MkHMSet box) =
  MkHMSet $
    foldBox (\key, weight, acc =>
              let signedW = boxIntToSignedBit weight
              in if isZero signedW
                   then acc
                   else addAtKeyBox (freezeToSignedPhaseLoop rem key) signedW acc)
            BoxLeaf
            box

||| Thermal freeze-out phase transition (`BoxInt -> SignedBit`), saturating charges
||| into discrete `+1` (`PosBit`) / `-1` (`NegBit`) dipoles while annihilating
||| colliding opposite polarities (`PosBit + NegBit = ZeroBit`).
public export
freezeToSignedPhase : HereditaryMSet BoxInt -> HereditaryMSet SignedBit
freezeToSignedPhase m = freezeToSignedPhaseLoop (hmDepth m) m

private
coolToParityPhaseLoop : Nat -> HereditaryMSet SignedBit -> HereditaryMSet MultisetBit
coolToParityPhaseLoop Z _ = emptyHMSet
coolToParityPhaseLoop (S rem) (MkHMSet box) =
  MkHMSet $
    foldBox (\key, weight, acc =>
              let parityW = toMultisetBit weight
              in if isZero parityW
                   then acc
                   else addAtKeyBox (coolToParityPhaseLoop rem key) parityW acc)
            BoxLeaf
            box

||| Fermionic / Pauli cooling transition (`SignedBit -> MultisetBit`), projecting
||| polarized spin quanta into modulo-2 parity (`OneBit + OneBit = EmptyBit`).
public export
coolToParityPhase : HereditaryMSet SignedBit -> HereditaryMSet MultisetBit
coolToParityPhase m = coolToParityPhaseLoop (hmDepth m) m

||| Composed Boson -> Spin -> Fermion cooling transition (`BoxInt -> MultisetBit`).
public export
coolMSetToParityPhase : HereditaryMSet BoxInt -> HereditaryMSet MultisetBit
coolMSetToParityPhase = coolToParityPhase . freezeToSignedPhase
