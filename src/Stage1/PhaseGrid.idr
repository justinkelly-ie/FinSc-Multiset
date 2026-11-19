module Stage1.PhaseGrid

import Data.Vect
import public Stage0.BoxInt
import public Stage0.HereditaryMSet
import public Stage0.SignedBit
import public Stage0.StructuralFuel
import public Stage0.LinearBuffer
import public Stage0.OnSeq.FusedStream
import public Stage1.ConvolutionAdmissibility
import public Stage1.Views
import public Stage1.Lenses
import public Stage1.Bridge.LaurentAntiMSetBridge

%default total

------------------------------------------------------------------------
-- 1. THE 2D PHASE GRID: `LaurentRegime x Carrier c` (`CosmicState`)
------------------------------------------------------------------------

||| Unified 2D Phase-Grid carrier indexed jointly by support horizon (`LaurentRegime`)
||| and multiplicity carrier (`c : Type` with `MultisetWeight c`, e.g. `BoxInt`, `SignedBit`,
||| or `MultisetBit`). See `.agents/rules/09-multiplicity-carriers-and-phase-grid.md`.
public export
data CosmicState : (0 reg : LaurentRegime) -> (c : Type) -> Type where
  ||| Frozen relic crystal or closed valence/register lattice over `[low, high]`.
  StaticCrystal   : {0 low, high : Integer}
                 -> (field : HereditaryMSet c)
                 -> CosmicState (StaticHorizon low high) c
  ||| Forward causal cosmic epoch `[0, cap]` governed by decoupled `(yieldFuel, stepBudget)`.
  BoundedEpoch    : {cap : Nat}
                 -> (field : HereditaryMSet c)
                 -> (yieldFuel : GohFuel cap)
                 -> (stepBudget : Nat)
                 -> CosmicState (BoundedHorizon cap) c
  ||| Retrograde UV inspection `[-cap, 0]` probing microscopic scale fibers.
  RetroUVProbe    : {cap : Nat}
                 -> (field : HereditaryMSet c)
                 -> (yieldFuel : GohFuel cap)
                 -> (stepBudget : Nat)
                 -> CosmicState (RetroBoundedHorizon cap) c
  ||| Sliding Hubble causal patch `[t - win, t]` storing the last `win` field slices.
  HubblePatch     : {win : Nat}
                 -> (history : Vect win (HereditaryMSet c))
                 -> CosmicState (WindowedHorizon win) c
  ||| Open-ended expanding ray starting at Tick `epochTick`.
  ExpandingRay    : (epochTick : Nat)
                 -> (field : HereditaryMSet c)
                 -> CosmicState OpenFuture c
  ||| Two-sided steady-state configuration centered around Laurent degree `centerExp`.
  SteadyBilateral : (centerExp : Integer)
                 -> (field : HereditaryMSet c)
                 -> CosmicState BilateralOpen c

------------------------------------------------------------------------
-- 2. PHASE-GRID EXTRACTION & CONSTRUCTIVE CONSTRUCTORS
------------------------------------------------------------------------

||| Extracts the active instantaneous `HereditaryMSet c` snapshot from any `CosmicState`.
||| For `HubblePatch`, returns the head (most recent slice) or empty vacuum when `win = 0`.
public export
cosmicField : MultisetWeight c => CosmicState reg c -> HereditaryMSet c
cosmicField (StaticCrystal f)     = f
cosmicField (BoundedEpoch f _ _)  = f
cosmicField (RetroUVProbe f _ _)  = f
cosmicField (HubblePatch [])      = emptyHMSet
cosmicField (HubblePatch (x :: _)) = x
cosmicField (ExpandingRay _ f)    = f
cosmicField (SteadyBilateral _ f) = f

||| Seeds a forward bosonic `BoundedHorizon cap` epoch with single-pass support fuel (`fuelOfM`).
public export
mkBoundedEpoch : (cap : Nat) -> PureMultiset -> CosmicState (BoundedHorizon cap) BoxInt
mkBoundedEpoch cap field =
  let (yf, sb) = fuelOfM cap field
  in BoundedEpoch field yf sb

||| Seeds a forward fermionic/support `BoundedHorizon cap` epoch sized directly by `fuelFromSupport`.
public export
mkSupportEpoch : (cap : Nat) -> PureMultiset -> CosmicState (BoundedHorizon cap) MultisetBit
mkSupportEpoch cap field =
  let supp     = toSupportMSet field
      (yf, sb) = fuelFromSupport cap supp
  in BoundedEpoch supp yf sb

||| Freezes a completed `SolidifiedCarrier` cosmic epoch into a `StaticCrystal` (`BlueEuclidean`).
public export
solidifyEpochToCrystal : {cap : Nat} -> SolidifiedCarrier cap PureMultiset -> CosmicState (StaticHorizon 0 (natToInteger cap)) BoxInt
solidifyEpochToCrystal res = StaticCrystal res.carrier

------------------------------------------------------------------------
-- 3. PHYSICAL PHASE TRANSITIONS (`BoxInt -> SignedBit -> MultisetBit`)
------------------------------------------------------------------------

||| Maps the carrier projection across any horizon regime without altering its causal bounds.
public export
mapCosmicHMSet : {0 reg : LaurentRegime} -> (HereditaryMSet a -> HereditaryMSet b) -> CosmicState reg a -> CosmicState reg b
mapCosmicHMSet fn (StaticCrystal f)     = StaticCrystal (fn f)
mapCosmicHMSet fn (BoundedEpoch f y s)  = BoundedEpoch (fn f) y s
mapCosmicHMSet fn (RetroUVProbe f y s)  = RetroUVProbe (fn f) y s
mapCosmicHMSet fn (HubblePatch hist)    = HubblePatch (map fn hist)
mapCosmicHMSet fn (ExpandingRay t f)    = ExpandingRay t (fn f)
mapCosmicHMSet fn (SteadyBilateral e f) = SteadyBilateral e (fn f)

||| Thermal Plasma -> Saturated Spin Glass / Ising Dipoles (`BoxInt -> SignedBit`).
public export
freezeCosmicToSigned : {0 reg : LaurentRegime} -> CosmicState reg BoxInt -> CosmicState reg SignedBit
freezeCosmicToSigned = mapCosmicHMSet freezeToSignedPhase

||| Polarized Spin -> Z_2 Fermionic / Pauli Parity (`SignedBit -> MultisetBit`).
public export
coolCosmicToParity : {0 reg : LaurentRegime} -> CosmicState reg SignedBit -> CosmicState reg MultisetBit
coolCosmicToParity = mapCosmicHMSet coolToParityPhase

||| End-to-end Boson -> Spin -> Fermion cooling across any Laurent horizon (`BoxInt -> MultisetBit`).
public export
coolCosmicBoxToParity : {0 reg : LaurentRegime} -> CosmicState reg BoxInt -> CosmicState reg MultisetBit
coolCosmicBoxToParity = mapCosmicHMSet coolMSetToParityPhase

||| Superfluid / BEC -> Mott Insulator geometric support projection (`BoxInt -> MultisetBit`).
public export
mottSupportCosmic : {0 reg : LaurentRegime} -> CosmicState reg BoxInt -> CosmicState reg MultisetBit
mottSupportCosmic = mapCosmicHMSet toSupportMSet

||| Applies Wildberger's vacuum split kernel (`[] -> +alpha^(+1) - alpha^(-1)`) on `OpenFuture`.
public export
stepExpandingVacuum : CosmicState OpenFuture BoxInt -> CosmicState OpenFuture BoxInt
stepExpandingVacuum (ExpandingRay tick f) = ExpandingRay (S tick) (vacuumSplitKernel f)

------------------------------------------------------------------------
-- 4. EXTERNAL PHYSICAL LENS ATTACHMENT (`ScaleLens` & `ThermodynamicLens`)
------------------------------------------------------------------------

||| Applies a coarse-graining IR scale shift (`* alpha^(+k)`) via `ScaleLens`.
public export
zoomOutCosmic : {0 reg : LaurentRegime} -> ScaleLens -> Nat -> CosmicState reg BoxInt -> CosmicState reg BoxInt
zoomOutCosmic sLens k = mapCosmicHMSet (sLens.zoomOut k)

||| Applies a fine-graining UV scale shift (`* alpha^(-k)`) via `ScaleLens`.
public export
zoomInCosmic : {0 reg : LaurentRegime} -> ScaleLens -> Nat -> CosmicState reg BoxInt -> CosmicState reg BoxInt
zoomInCosmic sLens k = mapCosmicHMSet (sLens.zoomIn k)

||| Evaluates discrete structural free energy over the active cosmic snapshot via `ThermodynamicLens`.
public export
evaluateCosmicEnergy : {0 reg : LaurentRegime} -> ThermodynamicLens -> CosmicState reg BoxInt -> BoxInt
evaluateCosmicEnergy tLens st = tLens.freeEnergyOf (cosmicField st)

------------------------------------------------------------------------
-- 5. RULE 08 REGIME BRIDGES: `WindowedRingBuf`, `RetroBounded`, `BilateralOpen`
------------------------------------------------------------------------

public export
dropLastVect : {m : Nat} -> Vect (S m) a -> Vect m a
dropLastVect {m = Z}     (_ :: []) = []
dropLastVect {m = S _}   (x :: xs) = x :: dropLastVect xs

||| Allocates an empty circular ring buffer (`O(win)`) for sliding `HubblePatch` histories.
public export
emptyHubbleRing : {win : Nat} -> MultisetWeight c => WindowedRingBuf (S win) (HereditaryMSet c)
emptyHubbleRing = emptyRingBuf emptyHMSet

||| Pushes an instantaneous `HereditaryMSet c` snapshot into `WindowedRingBuf (S win)` in O(1).
public export
ringPushHubble : {win : Nat} -> HereditaryMSet c -> WindowedRingBuf (S win) (HereditaryMSet c) -> WindowedRingBuf (S win) (HereditaryMSet c)
ringPushHubble = pushRingBuf

||| Materializes a `WindowedRingBuf (S win)` snapshot into `CosmicState (WindowedHorizon (S win)) c`
||| with index `0` (`head`) holding the most recent tick.
public export
ringToHubblePatch : {win : Nat} -> WindowedRingBuf (S win) (HereditaryMSet c) -> CosmicState (WindowedHorizon (S win)) c
ringToHubblePatch rb =
  HubblePatch (goTab (S win) 0)
  where
    goTab : (rem : Nat) -> Nat -> Vect rem (HereditaryMSet c)
    goTab Z     _   = []
    goTab (S r) off = readRingOffset off rb :: goTab r (S off)

||| Shifts a new slice into a `HubblePatch` (`Vect (S win)`), evicting modes older than `win`.
public export
pushHubblePatch : {win : Nat} -> HereditaryMSet c -> CosmicState (WindowedHorizon (S win)) c -> CosmicState (WindowedHorizon (S win)) c
pushHubblePatch snap (HubblePatch hist) = HubblePatch (snap :: dropLastVect hist)

||| Seeds a retrograde UV inspection probe (`RetroBoundedHorizon cap`) via `uvIrDual` (`alpha^e <-> alpha^(-e)`).
public export
mkRetroUVProbe : (cap : Nat) -> PureMultiset -> CosmicState (RetroBoundedHorizon cap) BoxInt
mkRetroUVProbe cap field =
  let uvField  = uvIrDual field
      (yf, sb) = fuelOfM cap uvField
  in RetroUVProbe uvField yf sb

||| Freezes a completed retrograde UV probe back into a static `BlueEuclidean` relic crystal.
public export
solidifyRetroProbe : {cap : Nat} -> SolidifiedCarrier cap PureMultiset -> CosmicState (StaticHorizon 0 (natToInteger cap)) BoxInt
solidifyRetroProbe res = StaticCrystal (uvIrDual res.carrier)

||| Filters a `PureMultiset` down to `[center - win, center + win]` along the Laurent exponent axis
||| directly via `foldBox` (`Rule 08` §1 `WindowedHorizon` causal patch).
public export
sliceHubbleLaurentPatch : (center : Integer) -> (win : Nat) -> PureMultiset -> PureMultiset
sliceHubbleLaurentPatch center win (MkHMSet box) =
  let lo = center - cast win
      hi = center + cast win
  in MkHMSet $ foldBox (\key, w, acc =>
                         case classifyLaurentKey unwrapBox key of
                           ExponentKey expK =>
                             if expK >= lo && expK <= hi
                               then addAtKeyBox key w acc
                               else acc
                           NestedTermKey sub =>
                             let e = readCoordSlot 0 sub
                             in if e >= lo && e <= hi
                                  then addAtKeyBox key w acc
                                  else acc)
                       BoxLeaf
                       box

||| Admissible `BilateralOpen * WindowedHorizon` convolution (`Rule 08` §3):
||| slices the bilateral state to `[center - win, center + win]` and convolves with a compact FIR filter.
public export
convolveBilateralWithFilter : (center : Integer)
                           -> (win : Nat)
                           -> CosmicState BilateralOpen BoxInt
                           -> PureMultiset
                           -> CosmicState (WindowedHorizon 1) BoxInt
convolveBilateralWithFilter center win (SteadyBilateral _ field) compactFilter =
  let patch  = sliceHubbleLaurentPatch center win field
      conv   = mulHMSet patch compactFilter
      outWin = sliceHubbleLaurentPatch center win conv
  in HubblePatch [outWin]

||| Regime-guarded net charge sum (`sumHMSet`) statically requiring a `BoundedRegime` proof (`Rule 08` §1 & §5).
public export
totalMassCosmic : {reg : LaurentRegime} -> {auto 0 ok : BoundedRegime reg}
               -> CosmicState reg BoxInt -> BoxInt
totalMassCosmic st = sumHMSet (cosmicField st)

||| Regime-guarded discrete free-energy evaluation statically excluding `OpenFuture` and `BilateralOpen` (`Rule 08` §1 & §5).
public export
evaluateBoundedCosmicEnergy : {reg : LaurentRegime} -> {auto 0 ok : BoundedRegime reg}
                           -> ThermodynamicLens -> CosmicState reg BoxInt -> BoxInt
evaluateBoundedCosmicEnergy tLens st = tLens.freeEnergyOf (cosmicField st)

||| Slices an `ExpandingRay` (`OpenFuture`) around `center` (`[center - win, center + win]`) into a
||| `HubblePatch (WindowedHorizon 1)` before global reduction (`Rule 08` §1 & §5).
public export
sliceExpandingRayToHubble : (center : Integer) -> (win : Nat)
                         -> CosmicState OpenFuture BoxInt
                         -> CosmicState (WindowedHorizon 1) BoxInt
sliceExpandingRayToHubble center win (ExpandingRay _ f) =
  HubblePatch [sliceHubbleLaurentPatch center win f]

||| Slices a `SteadyBilateral` (`BilateralOpen`) around its `centerExp` into a local
||| `HubblePatch (WindowedHorizon 1)` causal horizon (`Rule 08` §1 & §5).
public export
sliceBilateralToHubble : (win : Nat)
                      -> CosmicState BilateralOpen BoxInt
                      -> CosmicState (WindowedHorizon 1) BoxInt
sliceBilateralToHubble win (SteadyBilateral cExp f) =
  HubblePatch [sliceHubbleLaurentPatch cExp win f]

