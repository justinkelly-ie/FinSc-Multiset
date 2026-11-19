module Stage1.UniverseTicks

import public Stage0.HereditaryMSet
import public Stage1.Fuse
import public Stage1.PhasedMultiset
import public Stage1.PhaseGrid

%default total

--------------------------------------------------------------------------------
-- 1. Key Lookup & Affine Nucleation Helpers
--------------------------------------------------------------------------------

||| Lookup the signed `BoxInt` multiplicity at key `key : PureMultiset`
||| inside a `PureMultiset` (`HereditaryMSet BoxInt`), returning zero if absent.
public export
lookupPureKey : PureMultiset -> PureMultiset -> BoxInt
lookupPureKey key (MkHMSet box) = lookupBox key box

||| One affine nucleation step: polarizes the empty vacuum into the signed
||| dipole `halfStepForward - halfStepBackward`, and multiplies populated
||| states by `symmetricMotionTick` (`(\alpha^{+1/2} + \alpha^{-1/2})^2`).
public export
affineNucleationStep : PureMultiset -> PureMultiset
affineNucleationStep (MkHMSet BoxLeaf) = halfStepForward - halfStepBackward
affineNucleationStep st = hyperOp 1 st symmetricMotionTick

--------------------------------------------------------------------------------
-- 2. Tick 0 -> Tick 1: Vacuum & Polarized Dipole
--------------------------------------------------------------------------------

||| Tick 0: Unpolarized empty vacuum `[]`.
public export
tick0Vacuum : PureMultiset
tick0Vacuum = emptyPureMSet

||| Tick 1: Polarized vacuum dipole `\alpha^{+1} - \alpha^{-1}` (`altBinomial 1`).
public export
tick1PolarizedDipole : PureMultiset
tick1PolarizedDipole = affineNucleationStep tick0Vacuum

--------------------------------------------------------------------------------
-- 3. Tick 2: Squared Dipole & Spin Shell
--------------------------------------------------------------------------------

||| Tick 2 (dipole channel): `(\alpha^{+1} - \alpha^{-1})^2 = \alpha^{+2} - 2 + \alpha^{-2}`.
public export
tick2SquaredDipole : PureMultiset
tick2SquaredDipole = hyperOp 1 tick1PolarizedDipole tick1PolarizedDipole

||| Tick 2 (central spin shell): `C_1 * C_1 = C_2 + C_0`.
public export
tick2SpinShellSquare : PureMultiset
tick2SpinShellSquare = hyperOp 1 (centralPoly 1) (centralPoly 1)

--------------------------------------------------------------------------------
-- 4. Tick 3: Poly* Seed, Non-Positive Residue & Caret Condensation
--------------------------------------------------------------------------------

||| Positive `Poly*` sector partitioned out of `tick1PolarizedDipole + tick2SquaredDipole`.
public export
tick3PolyStarSeed : PureMultiset
tick3PolyStarSeed = fst (partitionPolyStarPure (tick1PolarizedDipole + tick2SquaredDipole))

||| Complementary non-positive (`<= 0`) Laurent residue from `tick1PolarizedDipole + tick2SquaredDipole`.
public export
tick3NonPosResidue : PureMultiset
tick3NonPosResidue = snd (partitionPolyStarPure (tick1PolarizedDipole + tick2SquaredDipole))

||| Tick 3 condensation: fueled Level-2 caretation `tick3PolyStarSeed ^ tick3PolyStarSeed`.
public export
tick3PolyStarCondensation : PureMultiset
tick3PolyStarCondensation = hyperOp 2 tick3PolyStarSeed tick3PolyStarSeed

--------------------------------------------------------------------------------
-- 5. Tick 4: Dual-Channel Fueled Freeze-Out into Static BlueEuclidean Crystal
--------------------------------------------------------------------------------

||| Unfold step condensing negative/non-positive channel modes inward (`\alpha^{-1}`)
||| bounded by structural tree depth.
public export
negCondenseStep : (PureMultiset, Nat) -> Step (PureMultiset, Nat) PureMultiset
negCondenseStep (_, Z) = Done
negCondenseStep (cur, S rem) =
  let c = laurentZoomIn 1 cur
  in Yield c (c, rem)

||| Unfold step expanding the positive channel outward (`\alpha^{+1}`) while disjoint
||| from the condensed negative background (`Skip` on collision).
public export
posExpandOverBgStep : PureMultiset -> PureMultiset -> Step PureMultiset PureMultiset
posExpandOverBgStep bg cur =
  let c = laurentZoomOut 1 cur
  in if (c .*. bg) == emptyPureMSet then Yield c c else Skip c

||| Outcome record for Tick 4 decoupled dual-channel freeze-out.
public export
record Tick4FreezeOutcome (cap : Nat) where
  constructor MkTick4FreezeOutcome
  posOutcome   : SolidifiedCarrier cap PureMultiset
  negOutcome   : SolidifiedCarrier cap PureMultiset
  recombined   : PureMultiset
  relicCrystal : CosmicState (StaticHorizon 0 (natToInteger cap)) BoxInt
  irEnergy     : BoxInt
  freeEnergy   : BoxInt

||| Run asymmetric dual-channel `GohFuel` evolution over `PureMultiset`, recombine
||| channels, solidify `posOutcome` into a static crystal, and measure IR/free energy.
public export
evolveTick4FreezeOut : (cap : Nat) -> PureMultiset -> Tick4FreezeOutcome cap
evolveTick4FreezeOut cap m =
  let ch = splitChannels m
      (posFuel, posSteps) = fuelOfHMSet cap ch.posChannel
      (negFuel, negSteps) = fuelOfHMSet cap ch.negChannel
      negDepth = case ch.negChannel of MkHMSet negBox => S (boxHeight negBox)
      keepLatest = \nextSt, _ => nextSt
      negRes = runDecoupledStream negFuel negSteps negCondenseStep keepLatest ch.negChannel (ch.negChannel, negDepth)
      posRes = runDecoupledStream posFuel posSteps (posExpandOverBgStep negRes.carrier) keepLatest ch.posChannel ch.posChannel
      recomb = interactChannels (MkDualChannels posRes.carrier negRes.carrier)
      crys = solidifyEpochToCrystal posRes
      irE = expandAndMeasureLaurent laurentScaleLens blueEuclideanLens 1 recomb
      fe = freeEnergyProxy recomb
  in MkTick4FreezeOutcome posRes negRes recomb crys irE fe

||| Canonical Tick 4 frozen relic at Primorial `210` budget.
public export
tick4FrozenRelic : Tick4FreezeOutcome 210
tick4FrozenRelic = evolveTick4FreezeOut 210 (tick3PolyStarCondensation + tick3NonPosResidue)

--------------------------------------------------------------------------------
-- 6. Tick 5: Thermodynamic Condensation & SignedBit / MultisetBit Cooling
--------------------------------------------------------------------------------

||| Outcome record for Tick 5 cooling projection (`BoxInt -> SignedBit -> MultisetBit`).
public export
record Tick5CooledRelic where
  constructor MkTick5CooledRelic
  condensedMSet : PureMultiset
  releasedHeat  : BoxInt
  signedPhase   : HereditaryMSet SignedBit
  parityPhase   : HereditaryMSet MultisetBit

||| Condense a `PureMultiset` via `defaultThermoLens.condenseStep`, emitting heat
||| and projecting down to balanced ternary `SignedBit` and unsigned `MultisetBit`.
public export
evolveTick5PhaseCool : PureMultiset -> Tick5CooledRelic
evolveTick5PhaseCool m =
  let (cond, heat) = defaultThermoLens.condenseStep m
      signedP = freezeToSignedPhase cond
      parityP = coolToParityPhase signedP
  in MkTick5CooledRelic cond heat signedP parityP

||| Canonical Tick 5 cooled matter projected from Tick 4's recombined relic.
public export
tick5CooledMatter : Tick5CooledRelic
tick5CooledMatter = evolveTick5PhaseCool tick4FrozenRelic.recombined

--------------------------------------------------------------------------------
-- 7. Pure QTT 0 Refl Audits across Ticks 1 -> 3
--------------------------------------------------------------------------------

||| Audit 1: Tick 1 dipole matches Stage 1 `altBinomial 1`.
public export
0 prfTick1MatchesA1 :
  (Stage1.UniverseTicks.tick1PolarizedDipole == Stage1.Fuse.altBinomial 1) = True
prfTick1MatchesA1 = Refl

||| Audit 2: UV-IR duality maps `\alpha^{+1} - \alpha^{-1}` to its exact additive inverse.
public export
0 prfTick1UvIrAntisymmetric :
  (Stage1.Bridge.LaurentAntiMSetBridge.uvIrDual Stage1.UniverseTicks.tick1PolarizedDipole
    == Stage0.HereditaryMSet.negHMSet Stage1.UniverseTicks.tick1PolarizedDipole) = True
prfTick1UvIrAntisymmetric = Refl

||| Audit 3: Tick 2 squared dipole has origin quadrance multiplicity `-2`.
public export
0 prfTick2OriginQuadrance :
  Stage1.UniverseTicks.lookupPureKey Stage0.HereditaryMSet.emptyHMSet Stage1.UniverseTicks.tick2SquaredDipole = MkBoxInt (-2)
prfTick2OriginQuadrance = Refl

||| Audit 4: Clebsch-Gordan identity `C_1 * C_1 = C_2 + C_0`.
public export
0 prfTick2SpinClebschGordan :
  (Stage1.UniverseTicks.tick2SpinShellSquare ==
     Stage0.HereditaryMSet.addHMSet (Stage1.Fuse.centralPoly 2) (Stage1.Fuse.centralPoly 0)) = True
prfTick2SpinClebschGordan = Refl

||| Audit 5: Tick 2 Laurent exponents emerge in canonical ascending order `[-2, 0, 2]`.
public export
0 prfTick2LaurentOrderAscending :
  Stage1.Views.toLaurentTerms Stage0.BoxInt.unwrapBox Stage1.UniverseTicks.tick2SquaredDipole =
    [(-2, MkBoxInt 1), (0, MkBoxInt (-2)), (2, MkBoxInt 1)]
prfTick2LaurentOrderAscending = Refl

||| Audit 6: Poly* partitioning conserves total multiset charge (`sum seed + sum nonPos = 0`).
public export
0 prfTick3ChargePartitionConserved :
  Stage0.BoxInt.addBox
    (Stage0.HereditaryMSet.sumHMSet Stage1.UniverseTicks.tick3PolyStarSeed)
    (Stage0.HereditaryMSet.sumHMSet Stage1.UniverseTicks.tick3NonPosResidue) = MkBoxInt 0
prfTick3ChargePartitionConserved = Refl

||| Audit 7: Tick 3 caretation populates 2nd and 4th harmonic modes with multiplicities `(2, 1)`.
public export
0 prfTick3HarmonicModes :
  ( Stage1.UniverseTicks.lookupPureKey (Stage0.HereditaryMSet.scalarKeyHMSet 2) Stage1.UniverseTicks.tick3PolyStarCondensation
  , Stage1.UniverseTicks.lookupPureKey (Stage0.HereditaryMSet.scalarKeyHMSet 4) Stage1.UniverseTicks.tick3PolyStarCondensation
  ) = (MkBoxInt 2, MkBoxInt 1)
prfTick3HarmonicModes = Refl
