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
-- 5B. CHROMOGEOMETRIC 3D SPACETIME METRIC OBSERVABLE (RED MINKOWSKI VS BLUE)
--------------------------------------------------------------------------------

public export
record SpacetimeMetricReport where
  constructor MkSpacetimeMetricReport
  redTimelike            : BoxInt
  blueTimelike           : BoxInt
  redDilated             : BoxInt
  blueDilated            : BoxInt
  redNull                : BoxInt
  blueNull               : BoxInt
  redSpacelike           : BoxInt
  blueSpacelike          : BoxInt
  dilationRatioInvariant : Bool
  nullConeExactZero      : Bool
  spacelikeSignFlip      : Bool
  causalPrecedenceSplit  : Bool
  passesSpacetimeProbe   : Bool

||| Evaluates `traceWith redMinkowskiLens` vs. `traceWith blueEuclideanLens` on
||| genuine 3D `encodeVec3MSet [t, r, s]` carriers across timelike, dilated,
||| null light-cone, and spacelike configurations.
public export
probeChromaticSpacetimeMetric : SpacetimeMetricReport
probeChromaticSpacetimeMetric =
  let timelike3D =
        addHMSet
          (MkHMSet (setBox (encodeVec3MSet [3, 1, 0]) (intToBoxInt 2) BoxLeaf))
          (MkHMSet (setBox (encodeVec3MSet [4, 0, 1]) (intToBoxInt 1) BoxLeaf))
      dilated3D =
        addHMSet
          (MkHMSet (setBox (encodeVec3MSet [6, 2, 0]) (intToBoxInt 2) BoxLeaf))
          (MkHMSet (setBox (encodeVec3MSet [8, 0, 2]) (intToBoxInt 1) BoxLeaf))
      null3D =
        MkHMSet (setBox (encodeVec3MSet [5, 3, 4]) (intToBoxInt 1) BoxLeaf)
      spacelike3D =
        addHMSet
          (MkHMSet (setBox (encodeVec3MSet [3, 3, 2]) (intToBoxInt 2) BoxLeaf))
          (MkHMSet (setBox (encodeVec3MSet [4, 3, 2]) (intToBoxInt 1) BoxLeaf))

      rTime = traceWith redMinkowskiLens  timelike3D  timelike3D
      bTime = traceWith blueEuclideanLens timelike3D  timelike3D
      rDil  = traceWith redMinkowskiLens  dilated3D   dilated3D
      bDil  = traceWith blueEuclideanLens dilated3D   dilated3D
      rNull = traceWith redMinkowskiLens  null3D      null3D
      bNull = traceWith blueEuclideanLens null3D      null3D
      rSpc  = traceWith redMinkowskiLens  spacelike3D spacelike3D
      bSpc  = traceWith blueEuclideanLens spacelike3D spacelike3D

      ratBase = mkMSF rTime (integerToNat (abs (unwrapBox bTime)))
      ratDil  = mkMSF rDil  (integerToNat (abs (unwrapBox bDil)))
      dilOk   = (unwrapBox rTime > 0) && (unwrapBox bTime > 0) && (ratBase == ratDil)
      nullOk  = (rNull == intToBoxInt 0) && (unwrapBox bNull > 0)
      spcOk   = (unwrapBox rSpc < 0) && (unwrapBox bSpc > 0)
      evA     = encodeVec3MSet [1, 0, 0]
      evB     = encodeVec3MSet [3, 1, 0]
      precOk  = redMinkowskiLens.causallyPrecedes evA evB
             && not (blueEuclideanLens.causallyPrecedes evA evB)
      passOk  = dilOk && nullOk && spcOk && precOk
  in MkSpacetimeMetricReport rTime bTime rDil bDil rNull bNull rSpc bSpc dilOk nullOk spcOk precOk passOk

--------------------------------------------------------------------------------
-- 6. PROBE D: RECURSIVE `childDeg`, DIRECT 1D/2D/4D WALKS, 1D->2D CROSSOVER & A_2 HEX
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

||| Single-axis 1D convolution shift along one of the 4 axes of `Box BoxInt (Integer, Integer, Integer, Integer)`.
public export
shiftAxis4D : Nat -> Box BoxInt (Integer, Integer, Integer, Integer) -> Box BoxInt (Integer, Integer, Integer, Integer)
shiftAxis4D axis box =
  foldBox (\(t, x, y, z), w, acc =>
            if isZero w
              then acc
              else
                let w2 = addBox w w
                    addShift : Integer -> BoxInt -> Box BoxInt (Integer, Integer, Integer, Integer) -> Box BoxInt (Integer, Integer, Integer, Integer)
                    addShift d coeff bAcc =
                      let key = case axis of
                                  0 => (t + d, x, y, z)
                                  1 => (t, x + d, y, z)
                                  2 => (t, x, y + d, z)
                                  _ => (t, x, y, z + d)
                      in addAtKeyBox key coeff bAcc
                in addShift (-1) w (addShift 0 w2 (addShift 1 w acc)))
          BoxLeaf
          box

||| Exact 4-axis isotropic Laplacian step on a 4D integer grid (`mass * 256` per step).
public export
stepWalk4D : Box BoxInt (Integer, Integer, Integer, Integer) -> Box BoxInt (Integer, Integer, Integer, Integer)
stepWalk4D = shiftAxis4D 3 . shiftAxis4D 2 . shiftAxis4D 1 . shiftAxis4D 0

public export
returnRatioBox4D : Box BoxInt (Integer, Integer, Integer, Integer) -> MSetFraction
returnRatioBox4D b =
  let w0   = lookupBox (0, 0, 0, 0) b
      totM = foldBox (\_, (MkBoxInt w), acc => acc + integerToNat (abs w)) (the Nat 0) b
  in mkMSF w0 totM

private
countTransverseNodes2D : Box BoxInt (Integer, Integer) -> Nat
countTransverseNodes2D =
  foldBox (\(_, y), (MkBoxInt w), acc =>
            if y /= 0 && w /= 0 then S acc else acc)
          0

||| Constant-mass (`16` per site) threshold-coupled walk on Wildberger's 2D `(alpha, beta)` grid:
||| - `|w| < threshold` : 1D vertical `alpha`-diffusion `(-1, 0):4, (0, 0):8, (1, 0):4`
||| - `|w| >= threshold`: full 2D `(alpha, beta)`-diffusion `(-1:1, 0:2, 1:1) x (-1:1, 0:2, 1:1)`
public export
stepAniso2D : Integer -> Box BoxInt (Integer, Integer) -> Box BoxInt (Integer, Integer)
stepAniso2D threshold =
  foldBox (\(x, y), (MkBoxInt w), acc =>
            if w == 0
              then acc
              else if abs w < threshold
                     then addAtKeyBox (x + 1, y) (intToBoxInt (w * 4))
                            (addAtKeyBox (x, y) (intToBoxInt (w * 8))
                              (addAtKeyBox (x - 1, y) (intToBoxInt (w * 4)) acc))
                     else
                       let w2 = w * 2
                           w4 = w * 4
                       in addAtKeyBox (x + 1, y + 1) (intToBoxInt w)
                            (addAtKeyBox (x, y + 1) (intToBoxInt w2)
                              (addAtKeyBox (x - 1, y + 1) (intToBoxInt w)
                                (addAtKeyBox (x + 1, y) (intToBoxInt w2)
                                  (addAtKeyBox (x, y) (intToBoxInt w4)
                                    (addAtKeyBox (x - 1, y) (intToBoxInt w2)
                                      (addAtKeyBox (x + 1, y - 1) (intToBoxInt w)
                                        (addAtKeyBox (x, y - 1) (intToBoxInt w2)
                                          (addAtKeyBox (x - 1, y - 1) (intToBoxInt w) acc)))))))))
          BoxLeaf

public export
record SpectralDimReport where
  constructor MkSpectralDimReport
  legacy3DDeg        : Nat
  recursive3DDeg     : Nat
  decay1D            : MSetFraction
  decay2DObs         : MSetFraction
  decay2DDirect      : MSetFraction
  decay4DDirect      : MSetFraction
  crossoverUvDecay   : MSetFraction
  crossoverIrDecay   : MSetFraction
  uvTransverseNodes  : Nat
  irTransverseNodes  : Nat
  a2HexDecay         : MSetFraction
  a2HexWeylInvariant : Bool
  dimFlowMonotonic   : Bool

||| Probe D: Compares `legacyHeightOnlyStats` (`2`) vs. upgraded `Stage0.HereditaryMSet.collectSupportStats`
||| (`100`) on `encodeVec3MSet [100, 50, 25]`, then directly evolves:
||| - 1D `InfFuel` walk (`d1(P8/P4)`),
||| - 2D `convBox2D` walk (`P_2D(0,4)/P_2D(0,2)`),
||| - 4D `stepWalk4D` walk (`P_4D(0,2)/P_4D(0,1)`),
||| - threshold-coupled 1D -> 2D dynamical crossover on the `(alpha, beta)` grid (`stepAniso2D 32`),
||| - 2D `A_2` hexagonal walk (`a2HexTick`) with `W(A_2)` reflection invariance.
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
      p1_2to4     = fromMaybe zeroMSF (getTerm decSeq 2)

      k2D         = outerBox2D symmetricMotionTick symmetricMotionTick
      k2D_2       = convBox2D k2D k2D
      k2D_4       = convBox2D k2D_2 k2D_2
      d2Obs       = divMSF (returnRatioBox2D k2D_2) (returnRatioBox2D k2D)
      d2Dir       = divMSF (returnRatioBox2D k2D_4) (returnRatioBox2D k2D_2)

      seed4D      = setBox (the (Integer, Integer, Integer, Integer) (0, 0, 0, 0)) (intToBoxInt 1) BoxLeaf
      w4_1        = stepWalk4D seed4D
      w4_2        = stepWalk4D w4_1
      d4Dir       = divMSF (returnRatioBox4D w4_2) (returnRatioBox4D w4_1)

      seed2D      = setBox (the (Integer, Integer) (0, 0)) (intToBoxInt 1) BoxLeaf
      a1          = stepAniso2D 32 seed2D
      a2          = stepAniso2D 32 a1
      a3          = stepAniso2D 32 a2
      a4          = stepAniso2D 32 a3
      uvDec       = divMSF (returnRatioBox2D a2) (returnRatioBox2D a1)
      irDec       = divMSF (returnRatioBox2D a4) (returnRatioBox2D a2)
      uvTrans     = countTransverseNodes2D a2
      irTrans     = countTransverseNodes2D a4

      h1          = a2HexTick
      h2          = convBox2D h1 h1
      h4          = convBox2D h2 h2
      hDec        = divMSF (returnRatioBox2D h4) (returnRatioBox2D h2)
      hInv        = isA2WeylInvariant h4

      okFlow = msfGT d1_4to8 (mkMSF 68 100)
            && msfLT d1_4to8 (mkMSF 76 100)
            && (d2Obs == powMSF 2 d1_1to2)
            && msfGT d1_4to8 d2Dir
            && msfGT d2Dir d4Dir
            && (uvTrans == 0)
            && (irTrans > 0)
            && msfGT uvDec irDec
            && msfGT p1_2to4 irDec
            && hInv
            && msfGT hDec (mkMSF 45 100)
            && msfLT hDec (mkMSF 60 100)
  in MkSpectralDimReport legDeg recDeg d1_4to8 d2Obs d2Dir d4Dir uvDec irDec uvTrans irTrans hDec hInv okFlow

--------------------------------------------------------------------------------
-- 7. PROBE E: MF 236 BABY WEYL COMPRESSION, `S_n` ORBIT FAST-PATH & `210` SPLIT
--------------------------------------------------------------------------------

public export
record WeylCompressionReport where
  constructor MkWeylCompressionReport
  directYields        : Nat
  weylYields          : Nat
  weylQuotientOk      : Bool
  decYesOk            : Bool
  decNoOk             : Bool
  a2OctetMass         : BoxInt
  a2OctetOrigin       : BoxInt
  a2OctetNodes        : Nat
  orbitDirectYields6  : Nat
  orbitFastYields6    : Nat
  orbitMatchesInf6    : Bool
  cachedParityOk      : Bool
  decomposedFuel210   : Nat
  monolithicFuel210   : Nat
  passesWeylProbe     : Bool

||| Probe E: Benchmarks direct `C_3 * C_4` (`20` yields) against Baby Weyl (`10` yields),
||| verifies `recognizeWeylDivisibleByA1` and `recognizeSymmetricLaurent`, benchmarks
||| `evolveSymmetricOrbitFastPath` over 6 ticks (`108 -> 42` yields, exact `InfOracle` match),
||| verifies `CachedHMSet` O(1) fuel parity, `decomposedPrimeFuelNat 210 == 340`, and `a2BaryonOctet`.
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

      symY        = case recognizeSymmetricLaurent symmetricMotionTick of
                      Yes _ => True
                      No  _ => False
      symN        = case recognizeSymmetricLaurent (mkLaurentPure [(1, 1)]) of
                      Yes _ => False
                      No  _ => True

      seed1       = mkLaurentPure [(0, 1)]
      infSeq6     = evolveOnHMSetInfFuel openInfFuel 1 seed1 symmetricMotionTick
      infSnaps6   = (getClip infSeq6 1 6).elements
      dirY6       = foldl (\acc, s => acc + s.usedYield) (the Nat 0) infSnaps6
      infState6   = foldl (\_, s => s.state) emptyPureMSet infSnaps6
      (orbY6, orbMatch) =
        case evolveSymmetricOrbitFastPath 6 seed1 symmetricMotionTick of
          Nothing        => (the Nat 0, False)
          Just (st6, y6) => (y6, st6 == infState6)

      cachedTick  = cacheHMSet symmetricMotionTick
      cacheDecOk  = case recognizeCachedHMSet cachedTick of
                      Yes _ => True
                      No  _ => False
      cacheOk     = cacheDecOk
                 && (hyperOpFuelOfCachedHMSet 1 210 cachedTick cachedTick
                       == hyperOpFuelOfHMSet 1 210 symmetricMotionTick symmetricMotionTick)

      dec210      = decomposedPrimeFuelNat 210
      mono210     = gohFuelNat 210

      octMass     = foldBox (\_, w, acc => addBox acc w) (intToBoxInt 0) a2BaryonOctet
      octOrigin   = lookupBox (0, 0) a2BaryonOctet
      octNodes    = boxNodeCount a2BaryonOctet

      passOk      = (usedDir == 20)
                 && (usedWeyl == 10)
                 && (usedWeyl < usedDir)
                 && qOk
                 && decY
                 && decN
                 && symY
                 && symN
                 && orbMatch
                 && (orbY6 > 0)
                 && (orbY6 < dirY6)
                 && cacheOk
                 && (dec210 == 340)
                 && (dec210 > mono210)
                 && (octMass == intToBoxInt 8)
                 && (octOrigin == intToBoxInt 2)
                 && (octNodes == 7)
  in MkWeylCompressionReport
       usedDir usedWeyl qOk decY decN
       octMass octOrigin octNodes
       dirY6 orbY6 orbMatch cacheOk dec210 mono210 passOk

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

public export
0 prfFuelProbeDecomposed210 :
  Stage0.OnSeq.OnHereditaryMSet.decomposedPrimeFuelNat 210 = 340
prfFuelProbeDecomposed210 = Refl
