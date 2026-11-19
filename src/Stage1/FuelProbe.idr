module Stage1.FuelProbe

import Data.Vect
import public Stage0.SignedFraction
import public Stage0.OnSeq.OnHereditaryMSet
import public Stage1.Lenses
import public Stage1.PhaseGrid
import public Stage1.Views
import public Stage1.Bridge.LaurentAntiMSetBridge
import public Stage1.WeylBasis

%default total

--------------------------------------------------------------------------------
-- 1. EXACT RATIONAL HELPERS & MULTIPLICITY OBSERVABLES (`MSetFraction`)
--------------------------------------------------------------------------------

||| Strict less-than on `MSetFraction` via cross-multiplication (`den : PosNat > 0`).
public export
msfLT : MSetFraction -> MSetFraction -> Bool
msfLT (MkMSF a b) (MkMSF c d) =
  (unwrapBox a * natToInteger d) < (unwrapBox c * natToInteger b)

||| Strict greater-than on `MSetFraction` via cross-multiplication.
public export
msfGT : MSetFraction -> MSetFraction -> Bool
msfGT a b = msfLT b a

||| Less-than-or-equal on `MSetFraction` via cross-multiplication.
public export
msfLE : MSetFraction -> MSetFraction -> Bool
msfLE (MkMSF a b) (MkMSF c d) =
  (unwrapBox a * natToInteger d) <= (unwrapBox c * natToInteger b)

||| Exact integer power of an `MSetFraction` (`r^n`).
public export
powMSF : Nat -> MSetFraction -> MSetFraction
powMSF Z     _ = oneMSF
powMSF (S k) r = mulMSF r (powMSF k r)

||| Exact Nat division by 4 via structural pattern matching.
public export
div4Nat : Nat -> Nat
div4Nat (S (S (S (S k)))) = S (div4Nat k)
div4Nat _                 = Z

||| Blue Euclidean quadrance of a `PureMultiset` coefficient vector: `sum_k w_k^2`.
public export
coeffEuclideanQuadrance : PureMultiset -> BoxInt
coeffEuclideanQuadrance (MkHMSet box) =
  foldBox (\_, (MkBoxInt w), acc => addBox acc (intToBoxInt (w * w)))
          (intToBoxInt 0)
          box

||| Normalized two-point correlation amplitude `Q_Blue(m) / (totalMass(m))^2`.
public export
normalizedQuadranceRatio : PureMultiset -> MSetFraction
normalizedQuadranceRatio m@(MkHMSet box) =
  let q     = coeffEuclideanQuadrance m
      stats = collectSupportStats box
  in mkMSF q (stats.totalMass * stats.totalMass)

||| Origin return probability weight `w(0) / totalMass(m)` as an exact `MSetFraction`.
public export
originReturnRatio : PureMultiset -> MSetFraction
originReturnRatio (MkHMSet box) =
  let w0    = lookupBox emptyPureMSet box
      stats = collectSupportStats box
  in mkMSF w0 stats.totalMass

--------------------------------------------------------------------------------
-- 2. `OnSeq` OBSERVABLE PROJECTIONS
--------------------------------------------------------------------------------

||| Maps each step snapshot along an `OnSeq` trajectory to its allocation bloat `allocatedSteps / max(1, usedSteps)`.
public export
budgetBloatOnSeq : OnSeq (FuelStepSnapshot cap c) -> OnSeq MSetFraction
budgetBloatOnSeq = Stage0.OnSeq.OnMSet.map (\s =>
  mkMSF (intToBoxInt (natToInteger s.allocatedSteps)) (max 1 s.usedSteps))

||| Maps each `OnSeq` snapshot to its origin return fraction `P(0, t)`.
public export
originReturnOnSeq : OnSeq (FuelStepSnapshot cap BoxInt) -> OnSeq MSetFraction
originReturnOnSeq = Stage0.OnSeq.OnMSet.map (\s => originReturnRatio s.state)

||| Maps each unbounded `InfFuelSnapshot` to its origin return fraction `P(0, t)`.
public export
infOriginReturnOnSeq : OnSeq (InfFuelSnapshot BoxInt) -> OnSeq MSetFraction
infOriginReturnOnSeq = Stage0.OnSeq.OnMSet.map (\s => originReturnRatio s.state)

||| Maps a return-ratio `OnSeq` `t -> P(0, t)` to its doubling decay ratio `P(0, 2t) / P(0, t)`.
public export
spectralDecayOnSeq : OnSeq MSetFraction -> OnSeq MSetFraction
spectralDecayOnSeq (MkOnSeq start atFn) =
  MkOnSeq start (\t => divMSF (atFn (t + t)) (atFn t))

||| Maps each `OnSeq` snapshot to `True` iff its carrier is invariant under `uvIrDual`.
public export
symmetryOnSeq : OnSeq (FuelStepSnapshot cap BoxInt) -> OnSeq Bool
symmetryOnSeq = Stage0.OnSeq.OnMSet.map (\s => uvIrDual s.state == s.state)

||| Maps each `OnSeq` snapshot to its normalized quadrance correlation `Q_Blue(m) / M^2`.
public export
quadranceRatioOnSeq : OnSeq (FuelStepSnapshot cap BoxInt) -> OnSeq MSetFraction
quadranceRatioOnSeq = Stage0.OnSeq.OnMSet.map (\s => normalizedQuadranceRatio s.state)

--------------------------------------------------------------------------------
-- 3. PROBE A: STEP-BUDGET TIGHTNESS & ANTI-MASS-BLOWUP
--------------------------------------------------------------------------------

public export
record BudgetBloatReport where
  constructor MkBudgetBloatReport
  policyName        : String
  maxAllocatedSteps : Nat
  maxUsedSteps      : Nat
  worstBloat        : MSetFraction
  passesLinearBound : Bool

||| Probe A: Runs `symmetricMotionTick^t` (`t = 1..maxTick`) under `policy` and `cap`,
||| detecting quadratic-free linear allocation vs. exponential `totalMass` blowup.
public export
probeBudgetBloat : FuelPolicy -> (cap : Nat) -> (maxTick : Nat) -> BudgetBloatReport
probeBudgetBloat pol cap maxTick =
  let traj      = evolveOnHMSet pol 1 cap (mkLaurentPure [(0, 1)]) symmetricMotionTick
      snaps     = (getClip traj 1 maxTick).elements
      bloatSeq  = budgetBloatOnSeq traj
      bloats    = (getClip bloatSeq 1 maxTick).elements
      maxAlloc  = foldl (\acc, s => max acc s.allocatedSteps) 0 snaps
      maxUsed   = foldl (\acc, s => max acc s.usedSteps) 0 snaps
      worstB    = foldl (\acc, r => if msfGT r acc then r else acc) zeroMSF bloats
      boundOk   = maxAlloc <= 16 * max 1 maxUsed
  in MkBudgetBloatReport pol.policyName maxAlloc maxUsed worstB boundOk

--------------------------------------------------------------------------------
-- 4. PROBE B: FREEZE-OUT UV-IR SYMMETRY & ORIGIN SURVIVAL
--------------------------------------------------------------------------------

public export
record FreezeSymmetryReport where
  constructor MkFreezeSymmetryReport
  policyName        : String
  firstFreezeTick   : Maybe Nat
  allSymmetric      : Bool
  originSurvives    : Bool
  finalOriginReturn : MSetFraction

||| Probe B: Tracks `uvIrDual` symmetry and origin weight `P(0, t)` past `YieldExhausted`.
public export
probeFreezeSymmetry : FuelPolicy -> (cap : Nat) -> (maxTick : Nat) -> FreezeSymmetryReport
probeFreezeSymmetry pol cap maxTick =
  let traj    = evolveOnHMSet pol 1 cap (mkLaurentPure [(0, 1)]) symmetricMotionTick
      snaps   = (getClip traj 1 maxTick).elements
      syms    = (getClip (symmetryOnSeq traj) 1 maxTick).elements
      rets    = (getClip (originReturnOnSeq traj) 1 maxTick).elements
      firstFr = findFirstFreeze snaps
      symOk   = all id syms
      lastRet = foldl (\_, r => r) zeroMSF rets
      origOk  = msfGT lastRet zeroMSF
  in MkFreezeSymmetryReport pol.policyName firstFr symOk origOk lastRet
  where
    findFirstFreeze : List (FuelStepSnapshot c ty) -> Maybe Nat
    findFirstFreeze [] = Nothing
    findFirstFreeze (s :: rest) =
      if s.freezeReason /= NaturalCompletion
        then Just s.tickIdx
        else findFirstFreeze rest

--------------------------------------------------------------------------------
-- 4B. ORACLE COMPARISON: BOUNDED `GohFuel` VS. UNBOUNDED `InfFuel` (`Data.Fuel`)
--------------------------------------------------------------------------------

public export
record InfOracleReport where
  constructor MkInfOracleReport
  policyName          : String
  infAllNatural       : Bool
  infAllSymmetric     : Bool
  preFreezeExactMatch : Bool
  firstDivergenceTick : Maybe Nat

private
findFirstDivergence : List (InfFuelSnapshot BoxInt) -> List (FuelStepSnapshot c BoxInt) -> Maybe Nat
findFirstDivergence [] _ = Nothing
findFirstDivergence _ [] = Nothing
findFirstDivergence (si :: ri) (sg :: rg) =
  if si.state /= sg.state
    then Just sg.tickIdx
    else findFirstDivergence ri rg

private
checkPreFreezeMatch : List (InfFuelSnapshot BoxInt) -> List (FuelStepSnapshot c BoxInt) -> Bool
checkPreFreezeMatch [] _ = True
checkPreFreezeMatch _ [] = True
checkPreFreezeMatch (si :: ri) (sg :: rg) =
  if sg.freezeReason == NaturalCompletion
    then (sg.state == si.state) && checkPreFreezeMatch ri rg
    else True

||| Compares a bounded `FuelPolicy` trajectory against the streaming `InfFuel` -> `Data.Fuel`
||| oracle (`openInfFuel`) across ticks `1..maxTick`, certifying exact pre-freeze equivalence
||| and pinpointing the exact freeze divergence tick.
public export
probeInfOracleComparison : FuelPolicy -> (cap : Nat) -> (maxTick : Nat) -> InfOracleReport
probeInfOracleComparison pol cap maxTick =
  let infSeq   = evolveOnHMSetInfFuel openInfFuel 1 (mkLaurentPure [(0, 1)]) symmetricMotionTick
      gohSeq   = evolveOnHMSet pol 1 cap (mkLaurentPure [(0, 1)]) symmetricMotionTick
      infSnaps = (getClip infSeq 1 maxTick).elements
      gohSnaps = (getClip gohSeq 1 maxTick).elements
      natOk    = all (\s => s.freezeReason == NaturalCompletion) infSnaps
      symOk    = all (\s => uvIrDual s.state == s.state) infSnaps
      preOk    = checkPreFreezeMatch infSnaps gohSnaps
      divTick  = findFirstDivergence infSnaps gohSnaps
  in MkInfOracleReport pol.policyName natOk symOk preOk divTick

--------------------------------------------------------------------------------
-- 5. PROBE C: COMOVING SCALE INVARIANCE (`n_s = 1`) VS. COOLING RED TILT
--------------------------------------------------------------------------------

public export
record ScaleTiltReport where
  constructor MkScaleTiltReport
  win                   : Nat
  steps                 : Nat
  nonVacuous            : Bool
  controlScaleInvariant : Bool
  q0                    : MSetFraction
  q1                    : MSetFraction
  fe0                   : BoxInt
  fe1                   : BoxInt
  releasedHeat1         : BoxInt
  coolingBreaksFlatness : Bool

private
iterateCondense : Nat -> PureMultiset -> PureMultiset
iterateCondense Z     m = m
iterateCondense (S k) m = iterateCondense k (fst (defaultThermoLens.condenseStep m))

||| Probe C: Verifies exact `n_s = 1` normalized-quadrance scale invariance on comoving
||| `laurentZoomOut` patches, then tests that `defaultThermoLens.condenseStep` induces
||| heat release and breaks scale flatness (`q0 /= q1`).
public export
probeScaleInvarianceAndTilt : (win : Nat) -> (steps : Nat) -> ScaleTiltReport
probeScaleInvarianceAndTilt win steps =
  let seed       = mkLaurentPure [(-2, 1), (-1, 2), (0, 3), (1, 2), (2, 1)]
      zoomSeq    = MkOnSeq 0 (\k => sliceHubbleLaurentPatch (natToInteger k) win (laurentZoomOut k seed))
      ctrlClip   = (getClip (Stage0.OnSeq.OnMSet.map normalizedQuadranceRatio zoomSeq) 0 (S steps)).elements
      qBase      = normalizedQuadranceRatio seed
      nonVac     = all (\r => msfGT r zeroMSF) ctrlClip
      ctrlInv    = all (\r => r == qBase) ctrlClip
      coolSeq    = MkOnSeq 0 (\k => iterateCondense k seed)
      cool1      = fromMaybe seed (getTerm coolSeq 1)
      heat1      = snd (defaultThermoLens.condenseStep seed)
      qCool0     = normalizedQuadranceRatio seed
      qCool1     = normalizedQuadranceRatio cool1
      feBase     = freeEnergyProxy seed
      feNext     = freeEnergyProxy cool1
      breaksFlat = (qCool0 /= qCool1)
                && (unwrapBox heat1 > 0)
                && (unwrapBox feNext < unwrapBox feBase)
  in MkScaleTiltReport win steps nonVac ctrlInv qCool0 qCool1 feBase feNext heat1 breaksFlat

--------------------------------------------------------------------------------
-- 6. PROBE D: RECURSIVE `childDeg` CALIBRATION & 1D -> 2D -> 4D SPECTRAL FLOW
--------------------------------------------------------------------------------

||| Exact 2D outer-product box helper on `(Integer, Integer)` exponent pairs.
public export
outerBox2D : PureMultiset -> PureMultiset -> Box BoxInt (Integer, Integer)
outerBox2D m1 m2 =
  let t1 = toLaurentTerms unwrapBox m1
      t2 = toLaurentTerms unwrapBox m2
  in foldl (\acc, (e1, w1) =>
             foldl (\accIn, (e2, w2) =>
                     addAtKeyBox (e1, e2) (mulBox w1 w2) accIn)
                   acc
                   t2)
           BoxLeaf
           t1

public export
returnRatioBox2D : Box BoxInt (Integer, Integer) -> MSetFraction
returnRatioBox2D b =
  let w0   = lookupBox (0, 0) b
      totM = foldBox (\_, (MkBoxInt w), acc => acc + integerToNat (abs w)) (the Nat 0) b
  in mkMSF w0 totM

public export
record SpectralDimReport where
  constructor MkSpectralDimReport
  legacy3DDeg      : Nat
  recursive3DDeg   : Nat
  decay1D          : MSetFraction
  decay2DObs       : MSetFraction
  decay4D          : MSetFraction
  monoAxes4        : Nat
  primeAxes4       : Nat
  monoAxes10       : Nat
  decayMono4       : MSetFraction
  decayPrime4      : MSetFraction
  decayMacro10     : MSetFraction
  dimFlowMonotonic : Bool

||| Probe D: Compares `legacyHeightOnlyStats` (`2`) vs. upgraded `Stage0.HereditaryMSet.collectSupportStats`
||| (`100`) on `encodeVec3MSet [100, 50, 25]`, drives the 1D baseline from `InfFuel` (`Data.Fuel`),
||| cross-checks concrete 2D `convBox2D`, and demonstrates monotonic dimensional opening under `primeSplitFuelNat`.
public export
probeSpectralDimAndChildDeg : SpectralDimReport
probeSpectralDimAndChildDeg =
  let vec3Wrapped = MkHMSet (setBox (encodeVec3MSet [100, 50, 25]) (intToBoxInt 1) BoxLeaf)
      legDeg      = case vec3Wrapped of MkHMSet b => (legacyHeightOnlyStats b).maxDeg
      recDeg      = case vec3Wrapped of MkHMSet b => (collectSupportStats b).maxDeg

      p1Seq       = infOriginReturnOnSeq
                      (evolveOnHMSetInfFuel openInfFuel 1 (mkLaurentPure [(0, 1)]) symmetricMotionTick)
      decSeq      = spectralDecayOnSeq p1Seq
      d1_4to8     = fromMaybe zeroMSF (getTerm decSeq 4)
      d1_1to2     = fromMaybe zeroMSF (getTerm decSeq 1)
      d4          = powMSF 4 d1_4to8

      k2D         = outerBox2D symmetricMotionTick symmetricMotionTick
      k2D_2       = convBox2D k2D k2D
      d2Obs       = divMSF (returnRatioBox2D k2D_2) (returnRatioBox2D k2D)

      activeAxes : Nat -> Nat
      activeAxes stps = min 4 (max 1 (div4Nat stps))

      mAxes4   = activeAxes (gohFuelNat 4)
      pAxes4   = activeAxes (primeSplitFuelNat 4)
      mAxes10  = activeAxes (gohFuelNat 10)
      dMono4   = powMSF mAxes4 d1_4to8
      dPrime4  = powMSF pAxes4 d1_4to8
      dMacro10 = powMSF mAxes10 d1_4to8

      okFlow = msfGT d1_4to8 (mkMSF 68 100)
            && msfLT d1_4to8 (mkMSF 76 100)
            && (d2Obs == powMSF 2 d1_1to2)
            && msfGT d4 (mkMSF 24 100)
            && msfLT d4 (mkMSF 29 100)
            && msfGT dMono4 dPrime4
            && msfGT dPrime4 dMacro10
  in MkSpectralDimReport legDeg recDeg d1_4to8 d2Obs d4 mAxes4 pAxes4 mAxes10 dMono4 dPrime4 dMacro10 okFlow

--------------------------------------------------------------------------------
-- 7. PROBE E: MF 236 BABY WEYL COMPRESSION & `A_2` OCTET MULTISET CHECK
--------------------------------------------------------------------------------

public export
record WeylCompressionReport where
  constructor MkWeylCompressionReport
  directYields    : Nat
  weylYields      : Nat
  weylQuotientOk  : Bool
  decYesOk        : Bool
  decNoOk         : Bool
  a2OctetMass     : BoxInt
  a2OctetOrigin   : BoxInt
  a2OctetNodes    : Nat
  passesWeylProbe : Bool

||| Probe E: Benchmarks direct `C_3 * C_4` (`20` yields) against Baby Weyl
||| `A_4 * C_4` (`10` yields) + `weylDivideByA1`, verifies constructive `Dec`
||| recognition (`recognizeWeylDivisibleByA1`), and audits `a2BaryonOctet` (`mass=8`, `origin=2`, `nodes=7`).
public export
probeWeylCompression : WeylCompressionReport
probeWeylCompression =
  let c3          = centralPoly 3
      c4          = centralPoly 4
      a4          = altBinomial 4
      expectedCG  = clebschGordanSum 3 4
      (yfDir, _)  = hyperOpFuelOfHMSet 1 210 c3 c4
      solDir      = runFueledHyperOp 1 210 c3 c4
      usedDir     = minus (gohSteps yfDir) (gohSteps solDir.remainingYield)

      (yfWeyl, _) = hyperOpFuelOfHMSet 1 210 a4 c4
      wPair       = weylCompressMul 210 3 4
      solWeyl     = fst wPair
      qOpt        = snd wPair
      usedWeyl    = minus (gohSteps yfWeyl) (gohSteps solWeyl.remainingYield)

      qOk         = (qOpt == Just expectedCG) && (solDir.carrier == expectedCG)
      decY        = case recognizeWeylDivisibleByA1 (altBinomial 5) of
                      Yes _ => True
                      No  _ => False
      decN        = case recognizeWeylDivisibleByA1 (symPairPoly 1) of
                      Yes _ => False
                      No  _ => True

      octMass     = foldBox (\_, w, acc => addBox acc w) (intToBoxInt 0) a2BaryonOctet
      octOrigin   = lookupBox (0, 0) a2BaryonOctet
      octNodes    = boxNodeCount a2BaryonOctet

      passOk      = (usedDir == 20)
                 && (usedWeyl == 10)
                 && (usedWeyl < usedDir)
                 && qOk
                 && decY
                 && decN
                 && (octMass == intToBoxInt 8)
                 && (octOrigin == intToBoxInt 2)
                 && (octNodes == 7)
  in MkWeylCompressionReport usedDir usedWeyl qOk decY decN octMass octOrigin octNodes passOk

--------------------------------------------------------------------------------
-- 8. COMPILE-TIME QTT 0 `Refl` RE-AUDITS
--------------------------------------------------------------------------------

public export
0 prfFuelProbePrimeSplit4 :
  Stage0.OnSeq.OnHereditaryMSet.primeSplitFuelNat 4 = 8
prfFuelProbePrimeSplit4 = Refl

public export
0 prfFuelProbePrimeSplit8 :
  Stage0.OnSeq.OnHereditaryMSet.primeSplitFuelNat 8 = 15
prfFuelProbePrimeSplit8 = Refl
