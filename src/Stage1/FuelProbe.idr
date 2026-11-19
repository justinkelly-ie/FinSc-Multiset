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

||| Strict boolean conjunction over a list, avoiding nested `Lazy`/`Delay` closure lifting
||| in large `let` blocks during Idris 2 elaboration.
public export
andAll : List Bool -> Bool
andAll []            = True
andAll (False :: _)  = False
andAll (True  :: xs) = andAll xs

||| Fuel-bounded Euclidean GCD over `Integer` (256 steps covers inputs beyond 10^50).
public export
gcdIntFuel : Nat -> Integer -> Integer -> Integer
gcdIntFuel Z     a _ = if a == 0 then 1 else abs a
gcdIntFuel (S k) a b =
  if b == 0 then (if a == 0 then 1 else abs a)
  else gcdIntFuel k b (a `mod` b)

||| Reduces an `MSetFraction` to lowest coprime terms using `gcdIntFuel 256`.
public export
reduceMSF : MSetFraction -> MSetFraction
reduceMSF (MkMSF a d) =
  let n = unwrapBox a
      m = natToInteger d
      g = gcdIntFuel 256 (abs n) (abs m)
  in if g <= 1
       then MkMSF a d
       else mkMSF (intToBoxInt (n `div` g)) (integerToNat (m `div` g))

||| Exact absolute difference `|a - b|` of two `MSetFraction` values, reduced via GCD.
public export
msfAbsDiff : MSetFraction -> MSetFraction -> MSetFraction
msfAbsDiff a b =
  let d = subMSF a b
  in reduceMSF (mkMSF (intToBoxInt (abs (unwrapBox d.num))) d.den)

||| Formats an exact `MSetFraction` as a 4-decimal fixed-point string using
||| pure exact integer arithmetic (`(abs num * 10000) `div` den`, zero floats).
public export
showMSFFixed4 : MSetFraction -> String
showMSFFixed4 (MkMSF a d) =
  let n      = unwrapBox a
      m      = max 1 (natToInteger d)
      signS  = if n < 0 then "-" else ""
      scaled = (abs n * 10000) `div` m
      whole  = scaled `div` 10000
      frac   = scaled `mod` 10000
      pad4 : Integer -> String
      pad4 f =
        if f < 10 then "000" ++ show f
        else if f < 100 then "00" ++ show f
        else if f < 1000 then "0" ++ show f
        else show f
  in signS ++ show whole ++ "." ++ pad4 frac

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
export
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
export
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
export
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
-- 4C. LIGHT-CONE TRUNCATION AUDIT (EXACT CORE RADIUS VS. CAUSAL PREDICTION)
--------------------------------------------------------------------------------

||| Exact central binomial multiplicity `C(2t, t)` via the incremental
||| multiplicative recurrence `acc * (t + i) / i` (exact at every step).
public export
centralBinomial : Nat -> Integer
centralBinomial t = go 1 1 t
  where
    go : Integer -> Integer -> Nat -> Integer
    go acc _ Z     = acc
    go acc i (S k) = go ((acc * (natToInteger t + i)) `div` i) (i + 1) k

||| Signed multiplicity at Laurent exponent `x` (`0` when absent).
public export
coeffAtExp : Integer -> PureMultiset -> Integer
coeffAtExp x (MkHMSet b) = unwrapBox (lookupBox (signedKeyM x) b)

||| Largest `|x|` carrying a non-zero scalar Laurent multiplicity (`Nothing` on the vacuum).
public export
supportRadius : PureMultiset -> Maybe Integer
supportRadius (MkHMSet b) =
  foldBox (\k, w, acc =>
            if isZero w then acc
            else case classifyLaurentKey unwrapBox k of
                   ExponentKey e =>
                     let a = abs e
                     in Just (maybe a (max a) acc)
                   NestedTermKey _ => acc)
          Nothing
          b

||| Observed exact core radius at tick `t`: the largest `rho` such that the bounded
||| carrier agrees with the exact `InfFuel` oracle on every exponent `|x| <= rho`
||| (`Nothing` = the whole causal cone `|x| <= t + 1` is exact; `Just (-1)` = origin corrupted).
private
observedCore : Nat -> PureMultiset -> PureMultiset -> Maybe Integer
observedCore t approx exact = go 0 (S (S t))
  where
    agreeAt : Integer -> Bool
    agreeAt x = coeffAtExp x approx == coeffAtExp x exact
             && coeffAtExp (negate x) approx == coeffAtExp (negate x) exact
    go : Integer -> Nat -> Maybe Integer
    go _   Z     = Nothing
    go rho (S k) = if agreeAt rho then go (rho + 1) k else Just (rho - 1)

||| Causal prediction of the exact core radius under symmetric radial freeze with a
||| nearest-neighbour kernel (signal speed `1` cell / tick, strictly positive weights):
||| - a truncated tick retaining input shells `|x| <= Rin` yields core `Rin - 1`,
||| - an existing corruption front at `e` advances inward to `e - 1` every tick.
||| Input is `(truncated?, Rin)` per tick, with `Rin = supportRadius(out) - 1`.
private
predictCores : List (Bool, Integer) -> List (Maybe Integer)
predictCores = go Nothing
  where
    clampCore : Integer -> Integer
    clampCore e = if e < -1 then -1 else e
    go : Maybe Integer -> List (Bool, Integer) -> List (Maybe Integer)
    go _    []                    = []
    go prev ((trunc, rin) :: rest) =
      let next = case (prev, trunc) of
                   (Nothing, False) => Nothing
                   (Nothing, True)  => Just (clampCore (rin - 1))
                   (Just e,  False) => Just (clampCore (e - 1))
                   (Just e,  True)  => Just (clampCore (min e rin - 1))
      in next :: go next rest

public export
record LightConeReport where
  constructor MkLightConeReport
  policyName       : String
  observedCores    : List (Maybe Integer)
  predictedCores   : List (Maybe Integer)
  coneConsistent   : Bool
  originExactUntil : Nat
  originExactAtEnd : Bool
  oracleIsBinomial : Bool

private
coreKeepsOrigin : Maybe Integer -> Bool
coreKeepsOrigin Nothing  = True
coreKeepsOrigin (Just e) = e >= 0

private
countLeading : (a -> Bool) -> List a -> Nat
countLeading _ []        = 0
countLeading p (x :: xs) = if p x then S (countLeading p xs) else 0

private
zipLists : List a -> List b -> List (a, b)
zipLists (x :: xs) (y :: ys) = (x, y) :: zipLists xs ys
zipLists _         _         = []

||| Light-cone audit: compares the observed exact core radius of a symmetric-freeze
||| `FuelPolicy` trajectory against the causal prediction tick-by-tick, certifying that
||| truncation error propagates inward at exactly one cell per tick, and that the origin
||| is exact at `T` iff no dropped shell ever entered the origin's backward cone
||| `|x| <= T - s + 1`. Also certifies the oracle origin equals `C(2t, t)`.
export
probeLightConeTruncation : FuelPolicy -> (cap : Nat) -> (maxTick : Nat) -> LightConeReport
probeLightConeTruncation pol cap maxTick =
  let infSeq   = evolveOnHMSetInfFuel openInfFuel 1 (mkLaurentPure [(0, 1)]) symmetricMotionTick
      gohSeq   = evolveOnHMSet pol 1 cap (mkLaurentPure [(0, 1)]) symmetricMotionTick
      infSnaps = (getClip infSeq 1 maxTick).elements
      gohSnaps = (getClip gohSeq 1 maxTick).elements
      pairs    = zipLists gohSnaps infSnaps
      obs      = map (\(g, i) => observedCore g.tickIdx g.state i.state) pairs
      truncIn  = map (\g => ( g.freezeReason /= NaturalCompletion
                            , maybe (-1) (\r => r - 1) (supportRadius g.state))) gohSnaps
      pred     = predictCores truncIn
      binomOk  = all (\i => coeffAtExp 0 i.state == centralBinomial i.tickIdx) infSnaps
      untilT   = countLeading coreKeepsOrigin obs
      endOk    = case foldl (\_, c => Just c) Nothing obs of
                   Nothing => True
                   Just c  => coreKeepsOrigin c
  in MkLightConeReport pol.policyName obs pred (obs == pred) untilT endOk binomOk

--------------------------------------------------------------------------------
-- 4D. CAUSAL-DIAMOND HORIZON-AWARE FUEL SCHEDULE (ZERO ORIGIN LEAK)
--------------------------------------------------------------------------------

private
halfNatLocal : Nat -> Nat
halfNatLocal (S (S k)) = S (halfNatLocal k)
halfNatLocal _         = Z

public export
record CausalDiamondReport where
  constructor MkCausalDiamondReport
  horizonT          : Nat
  diamondTotalYield : Nat
  flatEqTotalYield  : Nat
  infTotalYield     : Nat
  originWeight      : Integer
  exactBinomial     : Integer
  originExact       : Bool
  allSymmetric      : Bool
  savesYields       : Bool

||| Generalized causal-diamond vs. flat-equator vs. uncapped `InfFuel` benchmark
||| parameterized by symmetric convolution `kernel` and expected exact origin multiplicity.
||| Delegates directly to `Stage0.OnSeq.OnHereditaryMSet.evolveCausalDiamond` and
||| `evolveFlatEquator`.
export
probeCausalDiamondKernel : (horizonT : Nat) ->
                           (kernel : PureMultiset) ->
                           (expectedOrigin : Integer) ->
                           CausalDiamondReport
probeCausalDiamondKernel horizonT kernel expectedOrigin =
  let seed     = mkLaurentPure [(0, 1)]
      dOut     = evolveCausalDiamond 1 horizonT seed kernel
      fOut     = evolveFlatEquator   1 horizonT seed kernel
      infSnaps = (getClip (evolveOnHMSetInfFuel openInfFuel 1 seed kernel) 1 horizonT).elements
      iY       = foldl (\acc, s => acc + s.usedYield) (the Nat 0) infSnaps
      dY       = dOut.totalUsedYield
      fY       = fOut.totalUsedYield
      w0       = coeffAtExp 0 dOut.finalState
      symOk    = uvIrDual dOut.finalState == dOut.finalState
  in MkCausalDiamondReport horizonT dY fY iY w0 expectedOrigin (w0 == expectedOrigin) symOk (andAll [dY < fY, fY < iY])

||| Radius-1 `[1, 2, 1]` causal-diamond benchmark preserving `C(2T, T)` at `(0, T)`.
export
probeCausalDiamond : (horizonT : Nat) -> CausalDiamondReport
probeCausalDiamond horizonT =
  probeCausalDiamondKernel horizonT symmetricMotionTick (centralBinomial horizonT)

||| Radius-2 five-point stencil `[1, 4, 6, 4, 1]` causal-diamond benchmark at `T=6`,
||| verifying exact `C(24, 12) = 2704156` via `(x^-1 + 2 + x)^12`
||| with generalized equator sizing (`210 < 270 < 330`).
export
probeCausalDiamondRad2 : CausalDiamondReport
probeCausalDiamondRad2 =
  let kernel2 = mulHMSet symmetricMotionTick symmetricMotionTick
  in probeCausalDiamondKernel 6 kernel2 (centralBinomial 12)

--------------------------------------------------------------------------------
-- 5. PROBE C: COMOVING SCALE INVARIANCE (`n_s = 1`) VS. COOLING RED TILT
--------------------------------------------------------------------------------

||| Exact two-point spatial autocorrelation multiset `C_m(Delta) = (m * uvIrDual m)_Delta`.
||| Under `laurentZoomOut k` (`* alpha^k`), `(alpha^k m) * (alpha^-k uvIrDual m) = m * uvIrDual m`,
||| cancelling scale shifts algebraically across all lags `Delta` via Cauchy convolution.
public export
autoCorrHMSet : PureMultiset -> PureMultiset
autoCorrHMSet m = mulHMSet m (uvIrDual m)

||| Normalized lag-1 / lag-0 two-point correlation ratio `C_m(1) / C_m(0)` measuring
||| spatial correlation length (decreases under UV clumping, increases under IR smoothing).
public export
autoCorrLag1Ratio : PureMultiset -> MSetFraction
autoCorrLag1Ratio m =
  let ac = autoCorrHMSet m
      c0 = coeffAtExp 0 ac
      c1 = coeffAtExp 1 ac
  in reduceMSF (mkMSF (intToBoxInt c1) (integerToNat (abs c0)))

||| Exact floor division by 2 over signed `Integer` (`-2 -> -1`, `-1 -> -1`, `0 -> 0`, `1 -> 0`, `2 -> 1`).
public export
divFloor2 : Integer -> Integer
divFloor2 x =
  if x >= 0
    then x `div` 2
    else negate ((negate x + 1) `div` 2)

||| 2-to-1 real-space block-spin decimation (`e -> floor(e / 2)`), summing adjacent bins.
public export
coarseGrain2 : PureMultiset -> PureMultiset
coarseGrain2 (MkHMSet box) =
  MkHMSet $ foldBox (\key, weight, acc =>
                      case classifyLaurentKey unwrapBox key of
                        ExponentKey e   => addAtKeyBox (signedKeyM (divFloor2 e)) weight acc
                        NestedTermKey m => addAtKeyBox m weight acc)
                    BoxLeaf
                    box

public export
record ScaleTiltReport where
  constructor MkScaleTiltReport
  win                    : Nat
  steps                  : Nat
  nonVacuous             : Bool
  controlScaleInvariant  : Bool
  q0                     : MSetFraction
  q1                     : MSetFraction
  fe0                    : BoxInt
  fe1                    : BoxInt
  releasedHeat1          : BoxInt
  autoCorrScaleInvariant : Bool
  lagRatioSeed           : MSetFraction
  lagRatioCondensed      : MSetFraction
  lagRatioDiffused       : MSetFraction
  tiltDirectionOrdered   : Bool
  rgDiffErr1             : MSetFraction
  rgDiffErr2             : MSetFraction
  rgCondShift            : MSetFraction
  rgFixedPointOk         : Bool
  coolingBreaksFlatness  : Bool

private
iterateCondense : Nat -> PureMultiset -> PureMultiset
iterateCondense Z     m = m
iterateCondense (S k) m = iterateCondense k (fst (defaultThermoLens.condenseStep m))

||| Probe C: Verifies exact `n_s = 1` normalized-quadrance and two-point autocorrelation
||| (`m * uvIrDual m`) scale invariance on comoving `laurentZoomOut` patches, tests the
||| dynamical z=2 block-spin RG fixed point (`coarseGrain2 (walk 4t) ~ walk t`), and verifies
||| that `defaultThermoLens.condenseStep` induces heat release, breaks scale flatness, and
||| shifts the lag-1 correlation ratio oppositely to IR diffusion.
export
probeScaleInvarianceAndTilt : (win : Nat) -> (steps : Nat) -> ScaleTiltReport
probeScaleInvarianceAndTilt win steps =
  let seed       = mkLaurentPure [(-2, 1), (-1, 2), (0, 3), (1, 2), (2, 1)]
      zoomSeq    = MkOnSeq 0 (\k => sliceHubbleLaurentPatch (natToInteger k) win (laurentZoomOut k seed))
      ctrlClip   = (getClip (Stage0.OnSeq.OnMSet.map normalizedQuadranceRatio zoomSeq) 0 (S steps)).elements
      qBase      = normalizedQuadranceRatio seed
      nonVac     = all (\r => msfGT r zeroMSF) ctrlClip
      ctrlInv    = all (\r => r == qBase) ctrlClip

      acBase      = autoCorrHMSet seed
      zoomAutoSeq = MkOnSeq 0 (\k => autoCorrHMSet (laurentZoomOut k seed))
      acClips     = (getClip zoomAutoSeq 0 (S steps)).elements
      acInv       = andAll [ coeffAtExp 0 acBase == unwrapBox (coeffEuclideanQuadrance seed)
                           , all (\ac => ac == acBase) acClips
                           ]

      coolSeq    = MkOnSeq 0 (\k => iterateCondense k seed)
      cool1      = fromMaybe seed (getTerm coolSeq 1)
      diff1      = mulHMSet seed symmetricMotionTick
      heat1      = snd (defaultThermoLens.condenseStep seed)
      qCool0     = normalizedQuadranceRatio seed
      qCool1     = normalizedQuadranceRatio cool1
      feBase     = freeEnergyProxy seed
      feNext     = freeEnergyProxy cool1

      lagSeed    = autoCorrLag1Ratio seed
      lagCond    = autoCorrLag1Ratio cool1
      lagDiff    = autoCorrLag1Ratio diff1
      tiltOrd    = andAll [msfLT lagCond lagSeed, msfGT lagDiff lagSeed]

      walkSeq    = evolveOnHMSetInfFuel openInfFuel 1 (mkLaurentPure [(0, 1)]) symmetricMotionTick
      w1         = maybe seed (.state) (getTerm walkSeq 1)
      w2         = maybe seed (.state) (getTerm walkSeq 2)
      w4         = maybe seed (.state) (getTerm walkSeq 4)
      w8         = maybe seed (.state) (getTerm walkSeq 8)
      rgErr1     = msfAbsDiff (autoCorrLag1Ratio (coarseGrain2 w4)) (autoCorrLag1Ratio w1)
      rgErr2     = msfAbsDiff (autoCorrLag1Ratio (coarseGrain2 w8)) (autoCorrLag1Ratio w2)
      rgCond     = msfAbsDiff (autoCorrLag1Ratio (coarseGrain2 cool1)) lagCond
      rgOk       = andAll [ msfLT rgErr2 rgErr1
                          , msfLT rgErr2 (mkMSF 1 100)
                          , msfLT rgErr1 rgCond
                          ]

      breaksFlat = andAll [ qCool0 /= qCool1
                          , unwrapBox heat1 > 0
                          , unwrapBox feNext < unwrapBox feBase
                          , acInv
                          , tiltOrd
                          , rgOk
                          ]
  in MkScaleTiltReport win steps nonVac ctrlInv qCool0 qCool1 feBase feNext heat1
       acInv lagSeed lagCond lagDiff tiltOrd rgErr1 rgErr2 rgCond rgOk breaksFlat

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
  boostedRedTimelike     : BoxInt
  boostedBlueTimelike    : BoxInt
  boostPreservesRed      : Bool
  boostMovesBlue         : Bool
  boostPreservesCausal   : Bool
  twoPhotonMass2         : BoxInt
  twoPhotonOk            : Bool
  passesSpacetimeProbe   : Bool

||| Integer Lorentz transformation in `O(2,1; Z)` (Barning-Hall matrix):
||| `[[3,2,2],[2,1,2],[2,2,1]]` preserves `t^2 - r^2 - s^2` exactly over `Integer`
||| (column quadrances `+1, -1, -1`, pairwise Red-orthogonal) and is orthochronous.
public export
hallBoostVec3 : Vect 3 Integer -> Vect 3 Integer
hallBoostVec3 [t, r, s] = [3*t + 2*r + 2*s, 2*t + r + 2*s, 2*t + 2*r + s]

||| Pushforward of a 3D spacetime multiset along `hallBoostVec3`, re-indexing every
||| `encodeVec3MSet` key and summing colliding multiplicities.
public export
boostHMSet3D : PureMultiset -> PureMultiset
boostHMSet3D (MkHMSet box) =
  MkHMSet (foldBox (\k, w, acc =>
                     addAtKeyBox (encodeVec3MSet (hallBoostVec3 (decodeVec3MSet k))) w acc)
                   BoxLeaf
                   box)

||| `True` iff the Red Minkowski quadrance of `m` is unchanged by `boostHMSet3D`.
public export
redFixedByBoost : PureMultiset -> Bool
redFixedByBoost m =
  let bm = boostHMSet3D m
  in traceWith redMinkowskiLens bm bm == traceWith redMinkowskiLens m m

private
mkVec3Node : Integer -> Integer -> Integer -> Integer -> PureMultiset
mkVec3Node t r s w =
  MkHMSet (setBox (encodeVec3MSet [t, r, s]) (intToBoxInt w) BoxLeaf)

private
timelikeSample3D : PureMultiset
timelikeSample3D = addHMSet (mkVec3Node 3 1 0 2) (mkVec3Node 4 0 1 1)

private
dilatedSample3D : PureMultiset
dilatedSample3D = addHMSet (mkVec3Node 6 2 0 2) (mkVec3Node 8 0 2 1)

private
nullSample3D : PureMultiset
nullSample3D = mkVec3Node 5 3 4 1

private
spacelikeSample3D : PureMultiset
spacelikeSample3D = addHMSet (mkVec3Node 3 3 2 2) (mkVec3Node 4 3 2 1)

private
evalBoostChecks : PureMultiset -> BoxInt -> (BoxInt, BoxInt, Bool, Bool, Bool)
evalBoostChecks base3D bBase =
  let bSet    = boostHMSet3D base3D
      rBT     = traceWith redMinkowskiLens  bSet bSet
      bBT     = traceWith blueEuclideanLens bSet bSet
      redOk   = andAll [ redFixedByBoost timelikeSample3D
                       , redFixedByBoost dilatedSample3D
                       , redFixedByBoost nullSample3D
                       , redFixedByBoost spacelikeSample3D
                       ]
      blueOk  = (bBT /= bBase)
      evA'    = encodeVec3MSet (hallBoostVec3 [1, 0, 0])
      evB'    = encodeVec3MSet (hallBoostVec3 [3, 1, 0])
      causalOk = redMinkowskiLens.causallyPrecedes evA' evB'
  in (rBT, bBT, redOk, blueOk, causalOk)

private
evalTwoPhotonCheck : (BoxInt, Bool)
evalTwoPhotonCheck =
  let photA   = mkVec3Node 5 3 4 1
      photB   = mkVec3Node 5 (-3) (-4) 1
      photons = addHMSet photA photB
      m2Pair  = traceWith redMinkowskiLens photons photons
      bPhot   = boostHMSet3D photons
      photOk  = andAll [ traceWith redMinkowskiLens photA photA == intToBoxInt 0
                       , traceWith redMinkowskiLens photB photB == intToBoxInt 0
                       , m2Pair == intToBoxInt 100
                       , traceWith redMinkowskiLens bPhot bPhot == intToBoxInt 100
                       ]
  in (m2Pair, photOk)

||| Evaluates `traceWith redMinkowskiLens` vs. `traceWith blueEuclideanLens` on
||| genuine 3D `encodeVec3MSet [t, r, s]` carriers across timelike, dilated,
||| null light-cone, and spacelike configurations.
export
probeChromaticSpacetimeMetric : SpacetimeMetricReport
probeChromaticSpacetimeMetric =
  let rTime = traceWith redMinkowskiLens  timelikeSample3D  timelikeSample3D
      bTime = traceWith blueEuclideanLens timelikeSample3D  timelikeSample3D
      rDil  = traceWith redMinkowskiLens  dilatedSample3D   dilatedSample3D
      bDil  = traceWith blueEuclideanLens dilatedSample3D   dilatedSample3D
      rNull = traceWith redMinkowskiLens  nullSample3D      nullSample3D
      bNull = traceWith blueEuclideanLens nullSample3D      nullSample3D
      rSpc  = traceWith redMinkowskiLens  spacelikeSample3D spacelikeSample3D
      bSpc  = traceWith blueEuclideanLens spacelikeSample3D spacelikeSample3D

      ratBase = mkMSF rTime (integerToNat (abs (unwrapBox bTime)))
      ratDil  = mkMSF rDil  (integerToNat (abs (unwrapBox bDil)))
      dilOk   = andAll [unwrapBox rTime > 0, unwrapBox bTime > 0, ratBase == ratDil]
      nullOk  = andAll [rNull == intToBoxInt 0, unwrapBox bNull > 0]
      spcOk   = andAll [unwrapBox rSpc < 0, unwrapBox bSpc > 0]
      precOk  = andAll [ redMinkowskiLens.causallyPrecedes (encodeVec3MSet [1, 0, 0]) (encodeVec3MSet [3, 1, 0])
                       , not (blueEuclideanLens.causallyPrecedes (encodeVec3MSet [1, 0, 0]) (encodeVec3MSet [3, 1, 0]))
                       ]

      (rBT, bBT, boostRedOk, boostBlueOk, boostCausalOk) = evalBoostChecks timelikeSample3D bTime
      (m2Pair, photOk) = evalTwoPhotonCheck

      passOk  = andAll [dilOk, nullOk, spcOk, precOk, boostRedOk, boostBlueOk, boostCausalOk, photOk]
  in MkSpacetimeMetricReport rTime bTime rDil bDil rNull bNull rSpc bSpc dilOk nullOk spcOk precOk
       rBT bBT boostRedOk boostBlueOk boostCausalOk m2Pair photOk passOk

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

||| Effective dimension power `2^{d_s} = (P(0, t) / P(0, 2t))^2 = 1 / decay^2` (reduced).
public export
effDimPower2 : MSetFraction -> MSetFraction
effDimPower2 dec = reduceMSF (divMSF oneMSF (mulMSF dec dec))

private
iterateBox : Nat -> (a -> a) -> a -> a
iterateBox Z     _ x = x
iterateBox (S k) f x = iterateBox k f (f x)

private
sortPairInt : Integer -> Integer -> (Integer, Integer)
sortPairInt a b = if a <= b then (a, b) else (b, a)

||| Canonical representative in the fundamental `W(B_4)` Weyl chamber
||| `0 <= a <= b <= c <= d` (sign flips + axis permutations, order `384`).
public export
canonB4 : (Integer, Integer, Integer, Integer) -> (Integer, Integer, Integer, Integer)
canonB4 (x0, x1, x2, x3) =
  let (a0, b0) = sortPairInt (abs x0) (abs x1)
      (c0, d0) = sortPairInt (abs x2) (abs x3)
      (a1, c1) = sortPairInt a0 c0
      (b1, d1) = sortPairInt b0 d0
      (b2, c2) = sortPairInt b1 c1
  in (a1, b2, c2, d1)

private
b4KernelShifts : List ((Integer, Integer, Integer, Integer), Integer)
b4KernelShifts =
  [ ((1, 0, 0, 0), 1), ((-1, 0, 0, 0), 1)
  , ((0, 1, 0, 0), 1), ((0, -1, 0, 0), 1)
  , ((0, 0, 1, 0), 1), ((0, 0, -1, 0), 1)
  , ((0, 0, 0, 1), 1), ((0, 0, 0, -1), 1)
  ]

private
stepB4With : (proj : (Integer, Integer, Integer, Integer) -> (Integer, Integer, Integer, Integer)) ->
             Box BoxInt (Integer, Integer, Integer, Integer) ->
             Box BoxInt (Integer, Integer, Integer, Integer)
stepB4With proj =
  foldBox (\(t, x, y, z), (MkBoxInt w), acc =>
            if w == 0
              then acc
              else foldl (\bAcc, ((dt, dx, dy, dz), kw) =>
                           addAtKeyBox (proj (t + dt, x + dx, y + dy, z + dz)) (intToBoxInt (w * kw)) bAcc)
                         acc
                         b4KernelShifts)
          BoxLeaf

||| `W(B_4)` Weyl-chamber orbit-mass pushforward for the pure 8-neighbor 4D Laplacian
||| (`stay = 0`, `mass * 8` per tick, `8` nodes at `t=4`, `32` at `t=8`, `200` at `t=16`).
public export
stepB4Chamber : Box BoxInt (Integer, Integer, Integer, Integer) -> Box BoxInt (Integer, Integer, Integer, Integer)
stepB4Chamber = stepB4With canonB4

||| Uncompressed pure 8-neighbor 4D Laplacian (cross-check baseline against `stepB4Chamber`).
public export
stepB4Full : Box BoxInt (Integer, Integer, Integer, Integer) -> Box BoxInt (Integer, Integer, Integer, Integer)
stepB4Full = stepB4With id

private
d4RootShifts : List (Integer, Integer, Integer, Integer)
d4RootShifts =
  [ ( 1,  1,  0,  0), ( 1, -1,  0,  0), (-1,  1,  0,  0), (-1, -1,  0,  0)
  , ( 1,  0,  1,  0), ( 1,  0, -1,  0), (-1,  0,  1,  0), (-1,  0, -1,  0)
  , ( 1,  0,  0,  1), ( 1,  0,  0, -1), (-1,  0,  0,  1), (-1,  0,  0, -1)
  , ( 0,  1,  1,  0), ( 0,  1, -1,  0), ( 0, -1,  1,  0), ( 0, -1, -1,  0)
  , ( 0,  1,  0,  1), ( 0,  1,  0, -1), ( 0, -1,  0,  1), ( 0, -1,  0, -1)
  , ( 0,  0,  1,  1), ( 0,  0,  1, -1), ( 0,  0, -1,  1), ( 0,  0, -1, -1)
  ]

||| Pure non-bipartite 4D `D_4` root-lattice Laplacian (`stay = 0`, `24` roots `(+-1, +-1, 0, 0)`,
||| `mass * 24` per tick) compressed onto the `W(B_4)` fundamental chamber (`144` nodes at `t=8`, `1311` at `t=16`).
public export
stepD4Chamber : Box BoxInt (Integer, Integer, Integer, Integer) -> Box BoxInt (Integer, Integer, Integer, Integer)
stepD4Chamber =
  foldBox (\(t, x, y, z), (MkBoxInt w), acc =>
            if w == 0
              then acc
              else foldl (\bAcc, (dt, dx, dy, dz) =>
                           addAtKeyBox (canonB4 (t + dt, x + dx, y + dy, z + dz)) (intToBoxInt w) bAcc)
                         acc
                         d4RootShifts)
          BoxLeaf

||| Total L1 mass `sum_{(x,y)} |w(x,y)|` of a 2D `(Integer, Integer)` box.
public export
totalMassBox2D : Box BoxInt (Integer, Integer) -> Integer
totalMassBox2D =
  foldBox (\_, (MkBoxInt w), acc => acc + abs w) 0

||| Non-separable 2D comb lattice step (constant site mass multiplier `8`):
||| - Backbone (`y == 0`): steps along backbone `(x +/- 1, 0):1` and teeth `(x, +/- 1):1`, plus `(x, 0):4`.
||| - Teeth (`y /= 0`): 1D vertical diffusion `(x, y +/- 1):2` and `(x, y):4` (zero horizontal hops).
||| Exhibits anomalous subdiffusion with asymptotic spectral dimension `d_s = 3/2` (`1 < d_s < 2`).
public export
stepComb2D : Box BoxInt (Integer, Integer) -> Box BoxInt (Integer, Integer)
stepComb2D =
  foldBox (\(x, y), (MkBoxInt w), acc =>
            if w == 0
              then acc
              else if y == 0
                     then addAtKeyBox (x, 0) (intToBoxInt (w * 4))
                            (addAtKeyBox (x + 1, 0) (intToBoxInt w)
                              (addAtKeyBox (x - 1, 0) (intToBoxInt w)
                                (addAtKeyBox (x, 1) (intToBoxInt w)
                                  (addAtKeyBox (x, -1) (intToBoxInt w) acc))))
                     else addAtKeyBox (x, y) (intToBoxInt (w * 4))
                            (addAtKeyBox (x, y + 1) (intToBoxInt (w * 2))
                              (addAtKeyBox (x, y - 1) (intToBoxInt (w * 2)) acc)))
          BoxLeaf

||| Constant-mass (`16` per site) normalized-density-coupled walk on Wildberger's 2D `(alpha, beta)` grid:
||| - High normalized density `|w| * invRhoCrit >= totalMass`: 1D UV `alpha`-confinement `(-1, 0):4, (0, 0):8, (1, 0):4`
||| - Low normalized density  `|w| * invRhoCrit <  totalMass`: 2D IR `(alpha, beta)`-deconfinement `(-1:1, 0:2, 1:1)^2`
public export
stepAniso2D : (invRhoCrit : Integer) -> Box BoxInt (Integer, Integer) -> Box BoxInt (Integer, Integer)
stepAniso2D invRhoCrit box =
  let totMass = max 1 (totalMassBox2D box)
  in foldBox (\(x, y), (MkBoxInt w), acc =>
               if w == 0
                 then acc
                 else if abs w * invRhoCrit >= totMass
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
             box

public export
record SpectralDimReport where
  constructor MkSpectralDimReport
  legacy3DDeg          : Nat
  recursive3DDeg       : Nat
  decay1D              : MSetFraction
  decay2DObs           : MSetFraction
  decay2DDirect        : MSetFraction
  decay4DDirect        : MSetFraction
  combDecay1to2        : MSetFraction
  combDecay2to4        : MSetFraction
  combDecay4to8        : MSetFraction
  b4ChamberDecay4to8   : MSetFraction
  b4ChamberDecay8to16  : MSetFraction
  d4ChamberDecay4to8   : MSetFraction
  d4ChamberDecay8to16  : MSetFraction
  b4ChamberNodes8      : Nat
  b4ChamberNodes16     : Nat
  d4ChamberNodes8      : Nat
  d4ChamberNodes16     : Nat
  b4ChamberExactAt2    : Bool
  crossoverUvDecay     : MSetFraction
  crossoverIrDecay     : MSetFraction
  uvTransverseNodes    : Nat
  irTransverseNodes    : Nat
  a2HexDecay           : MSetFraction
  a2HexWeylInvariant   : Bool
  equalTimeOrdered     : Bool
  equalTime4to8Ordered : Bool
  universality4DOk     : Bool
  effDim2Pow1D         : MSetFraction
  effDim2PowComb       : MSetFraction
  effDim2Pow2D         : MSetFraction
  effDim2PowA2         : MSetFraction
  effDim2Pow4D         : MSetFraction
  effDim2PowComb48     : MSetFraction
  effDim2Pow2D48       : MSetFraction
  effDim2PowA248       : MSetFraction
  effDim2PowB448       : MSetFraction
  effDim2PowD448       : MSetFraction
  effDim2PowB4816      : MSetFraction
  effDim2PowD4816      : MSetFraction
  dimFlowMonotonic     : Bool

private
eval1DWalkMetrics : (MSetFraction, MSetFraction, MSetFraction)
eval1DWalkMetrics =
  let p1Seq = infOriginReturnOnSeq
                (evolveOnHMSetInfFuel openInfFuel 1 (mkLaurentPure [(0, 1)]) symmetricMotionTick)
      decSeq  = spectralDecayOnSeq p1Seq
      d1_1to2 = reduceMSF (fromMaybe zeroMSF (getTerm decSeq 1))
      d1_2to4 = reduceMSF (fromMaybe zeroMSF (getTerm decSeq 2))
      d1_4to8 = reduceMSF (fromMaybe zeroMSF (getTerm decSeq 4))
  in (d1_1to2, d1_2to4, d1_4to8)

private
eval2DSquareWalkMetrics : (MSetFraction, MSetFraction, MSetFraction)
eval2DSquareWalkMetrics =
  let k2D     = outerBox2D symmetricMotionTick symmetricMotionTick
      k2D_2   = convBox2D k2D k2D
      k2D_4   = convBox2D k2D_2 k2D_2
      k2D_8   = convBox2D k2D_4 k2D_4
      d2Obs   = reduceMSF (divMSF (returnRatioBox2D k2D_2) (returnRatioBox2D k2D))
      d2Dir   = reduceMSF (divMSF (returnRatioBox2D k2D_4) (returnRatioBox2D k2D_2))
      d2_4to8 = reduceMSF (divMSF (returnRatioBox2D k2D_8) (returnRatioBox2D k2D_4))
  in (d2Obs, d2Dir, d2_4to8)

private
origin4D : (Integer, Integer, Integer, Integer)
origin4D = (0, 0, 0, 0)

private
record Walk4DMetrics where
  constructor MkWalk4DMetrics
  d4Direct   : MSetFraction
  b4_4to8    : MSetFraction
  b4_8to16   : MSetFraction
  d4_4to8    : MSetFraction
  d4_8to16   : MSetFraction
  b4Nodes8   : Nat
  b4Nodes16  : Nat
  d4Nodes8   : Nat
  d4Nodes16  : Nat
  b4Exact2   : Bool

private
evalB4Metrics : (MSetFraction, MSetFraction, Nat, Nat, Bool)
evalB4Metrics =
  let seed4D   = setBox origin4D (intToBoxInt 1) BoxLeaf
      b4Full2  = iterateBox 2 stepB4Full seed4D
      b4Ch2    = iterateBox 2 stepB4Chamber seed4D
      b4Ch4    = iterateBox 2 stepB4Chamber b4Ch2
      b4Ch8    = iterateBox 4 stepB4Chamber b4Ch4
      b4Ch16   = iterateBox 8 stepB4Chamber b4Ch8
      r48      = reduceMSF (divMSF (returnRatioBox4D b4Ch8)  (returnRatioBox4D b4Ch4))
      r816     = reduceMSF (divMSF (returnRatioBox4D b4Ch16) (returnRatioBox4D b4Ch8))
      wFull    = lookupBox origin4D b4Full2
      wCh      = lookupBox origin4D b4Ch2
      exact2   = andAll [ wFull == wCh
                        , wCh == intToBoxInt 8
                        , returnRatioBox4D b4Full2 == returnRatioBox4D b4Ch2
                        ]
  in (r48, r816, boxNodeCount b4Ch8, boxNodeCount b4Ch16, exact2)

private
evalD4Metrics : (MSetFraction, MSetFraction, Nat, Nat)
evalD4Metrics =
  let seed4D = setBox origin4D (intToBoxInt 1) BoxLeaf
      d4Ch4  = iterateBox 4 stepD4Chamber seed4D
      d4Ch8  = iterateBox 4 stepD4Chamber d4Ch4
      d4Ch16 = iterateBox 8 stepD4Chamber d4Ch8
      r48    = reduceMSF (divMSF (returnRatioBox4D d4Ch8)  (returnRatioBox4D d4Ch4))
      r816   = reduceMSF (divMSF (returnRatioBox4D d4Ch16) (returnRatioBox4D d4Ch8))
  in (r48, r816, boxNodeCount d4Ch8, boxNodeCount d4Ch16)

private
eval4DChamberMetrics : Walk4DMetrics
eval4DChamberMetrics =
  let seed4D = setBox origin4D (intToBoxInt 1) BoxLeaf
      w4_1   = stepWalk4D seed4D
      w4_2   = stepWalk4D w4_1
      d4Dir  = reduceMSF (divMSF (returnRatioBox4D w4_2) (returnRatioBox4D w4_1))
      (b48, b816, nb8, nb16, ex2) = evalB4Metrics
      (d48, d816, nd8, nd16)      = evalD4Metrics
  in MkWalk4DMetrics d4Dir b48 b816 d48 d816 nb8 nb16 nd8 nd16 ex2

private
evalCombWalkMetrics : (MSetFraction, MSetFraction, MSetFraction)
evalCombWalkMetrics =
  let seed2D      = setBox (the (Integer, Integer) (0, 0)) (intToBoxInt 1) BoxLeaf
      c1          = stepComb2D seed2D
      c2          = stepComb2D c1
      c4          = iterateBox 2 stepComb2D c2
      c8          = iterateBox 4 stepComb2D c4
      combDec1to2 = reduceMSF (divMSF (returnRatioBox2D c2) (returnRatioBox2D c1))
      combDec2to4 = reduceMSF (divMSF (returnRatioBox2D c4) (returnRatioBox2D c2))
      combDec4to8 = reduceMSF (divMSF (returnRatioBox2D c8) (returnRatioBox2D c4))
  in (combDec1to2, combDec2to4, combDec4to8)

private
evalCrossoverWalkMetrics : (MSetFraction, MSetFraction, Nat, Nat)
evalCrossoverWalkMetrics =
  let seed2D = setBox (the (Integer, Integer) (0, 0)) (intToBoxInt 1) BoxLeaf
      a1     = stepAniso2D 4 seed2D
      a2     = stepAniso2D 4 a1
      a3     = stepAniso2D 4 a2
      a4     = stepAniso2D 4 a3
      uvDec  = reduceMSF (divMSF (returnRatioBox2D a2) (returnRatioBox2D a1))
      irDec  = reduceMSF (divMSF (returnRatioBox2D a4) (returnRatioBox2D a2))
  in (uvDec, irDec, countTransverseNodes2D a2, countTransverseNodes2D a4)

private
evalA2HexMetrics : (MSetFraction, MSetFraction, Bool)
evalA2HexMetrics =
  let h1      = a2HexTick
      h2      = convBox2D h1 h1
      h4      = convBox2D h2 h2
      h8      = convBox2D h4 h4
      hDec    = reduceMSF (divMSF (returnRatioBox2D h4) (returnRatioBox2D h2))
      a2_4to8 = reduceMSF (divMSF (returnRatioBox2D h8) (returnRatioBox2D h4))
  in (hDec, a2_4to8, isA2WeylInvariant h4)

||| Probe D: Compares `legacyHeightOnlyStats` (`2`) vs. upgraded `Stage0.HereditaryMSet.collectSupportStats`
||| (`100`) on `encodeVec3MSet [100, 50, 25]`, then directly evolves:
||| - 1D `InfFuel` walk (`d1(P8/P4)`),
||| - non-separable 2D Comb lattice (`stepComb2D`, anomalous subdiffusion `d_s = 3/2`) through `t=8`,
||| - 2D `convBox2D` square walk through `t=8` (`k2D_8 = convBox2D k2D_4 k2D_4`),
||| - 2D `A_2` hexagonal walk (`a2HexTick`) through `t=8` (`h8 = convBox2D h4 h4`),
||| - zero-stay `W(B_4)` chamber-compressed 4D `B_4` (`32 -> 200` nodes) and non-separable `D_4` (`144 -> 1311` nodes) through `t=16`,
||| - normalized-density-coupled 1D -> 2D dynamical crossover on the `(alpha, beta)` grid (`stepAniso2D 4`).
export
probeSpectralDimAndChildDeg : SpectralDimReport
probeSpectralDimAndChildDeg =
  let vec3Wrapped = MkHMSet (setBox (encodeVec3MSet [100, 50, 25]) (intToBoxInt 1) BoxLeaf)
      legDeg      = case vec3Wrapped of MkHMSet b => (legacyHeightOnlyStats b).maxDeg
      recDeg      = case vec3Wrapped of MkHMSet b => (collectSupportStats b).maxDeg

      (d1_1to2, p1_2to4, d1_4to8)             = eval1DWalkMetrics
      (d2Obs, d2Dir, d2_4to8)                 = eval2DSquareWalkMetrics
      w4M                                     = eval4DChamberMetrics
      d4Dir                                   = w4M.d4Direct
      b4_4to8                                 = w4M.b4_4to8
      b4_8to16                                = w4M.b4_8to16
      d4_4to8                                 = w4M.d4_4to8
      d4_8to16                                = w4M.d4_8to16
      nB8                                     = w4M.b4Nodes8
      nB16                                    = w4M.b4Nodes16
      nD8                                     = w4M.d4Nodes8
      nD16                                    = w4M.d4Nodes16
      b4Exact2                                = w4M.b4Exact2
      (combDec1to2, combDec2to4, combDec4to8) = evalCombWalkMetrics
      (uvDec, irDec, uvTrans, irTrans)                                   = evalCrossoverWalkMetrics
      (hDec, a2_4to8, hInv)                                              = evalA2HexMetrics

      eqTimeOk    = andAll [ msfGT d1_1to2 combDec1to2
                           , msfGT combDec1to2 d2Obs
                           , msfGT d2Obs d4Dir
                           , msfGT p1_2to4 combDec2to4
                           , msfGT combDec2to4 d2Dir
                           ]

      e1D         = effDimPower2 d1_4to8
      eComb       = effDimPower2 combDec2to4
      e2D         = effDimPower2 d2Dir
      eA2         = effDimPower2 hDec
      e4D         = effDimPower2 d4Dir

      eComb48     = effDimPower2 combDec4to8
      e2D48       = effDimPower2 d2_4to8
      eA248       = effDimPower2 a2_4to8
      eB448       = effDimPower2 b4_4to8
      eD448       = effDimPower2 d4_4to8
      eB4816      = effDimPower2 b4_8to16
      eD4816      = effDimPower2 d4_8to16

      univ4DOk    = andAll [ msfLT eB448 eB4816
                           , msfLT eB4816 (mkMSF 16 1)
                           , msfLT eD448 eD4816
                           , msfLT eD4816 (mkMSF 16 1)
                           , msfGT eB4816 (mkMSF 14 1)
                           , msfGT eD4816 (mkMSF 14 1)
                           , msfLT (msfAbsDiff eB448 eD448) (mkMSF 1 2)
                           ]

      eqTime48Ok  = andAll [ msfGT d1_4to8 combDec4to8
                           , msfGT combDec4to8 d2_4to8
                           , msfGT d2_4to8 b4_4to8
                           , msfGT b4_4to8 d4_4to8
                           , msfLT e1D eComb48
                           , msfLT eComb48 e2D48
                           , msfLT e2D48 eB448
                           , msfLT e2D48 eD448
                           , msfGT eB448 (mkMSF 12 1)
                           , msfGT eD448 (mkMSF 12 1)
                           , univ4DOk
                           ]

      okFlow      = andAll [ msfGT d1_4to8 (mkMSF 68 100)
                           , msfLT d1_4to8 (mkMSF 76 100)
                           , d2Obs == powMSF 2 d1_1to2
                           , eqTimeOk
                           , b4Exact2
                           , eqTime48Ok
                           , msfGT d1_4to8 d2Dir
                           , msfGT d2Dir d4Dir
                           , uvTrans == 0
                           , irTrans > 0
                           , msfGT uvDec irDec
                           , msfGT p1_2to4 irDec
                           , msfGT irDec d4Dir
                           , msfLT e1D eComb
                           , msfLT eComb e2D
                           , msfLT e2D e4D
                           , hInv
                           , msfGT hDec (mkMSF 45 100)
                           , msfLT hDec (mkMSF 60 100)
                           ]
  in MkSpectralDimReport legDeg recDeg d1_4to8 d2Obs d2Dir d4Dir
       combDec1to2 combDec2to4 combDec4to8 b4_4to8 b4_8to16 d4_4to8 d4_8to16
       nB8 nB16 nD8 nD16 b4Exact2
       uvDec irDec uvTrans irTrans hDec hInv
       eqTimeOk eqTime48Ok univ4DOk e1D eComb e2D eA2 e4D
       eComb48 e2D48 eA248 eB448 eD448 eB4816 eD4816 okFlow

--------------------------------------------------------------------------------
-- 6B. INTERACTING & NON-GAUSSIAN 1D RG UNIVERSALITY CLASSES (KURTOSIS & z)
--------------------------------------------------------------------------------

||| Exact second-moment variance `<x^2>` of a 1D `Box BoxInt Integer` distribution.
public export
varianceBox1D : Box BoxInt Integer -> MSetFraction
varianceBox1D box =
  let (m0, m2) = foldBox (\x, (MkBoxInt w), (a0, a2) =>
                           let aw = abs w
                           in (a0 + aw, a2 + aw * x * x))
                         (the Integer 0, the Integer 0)
                         box
  in reduceMSF (mkMSF (intToBoxInt m2) (integerToNat (max 1 m0)))

||| Exact excess-free kurtosis `<x^4> / <x^2>^2 = (m4 * m0) / (m2 * m2)` (`3` = Gaussian).
public export
kurtosisBox1D : Box BoxInt Integer -> MSetFraction
kurtosisBox1D box =
  let (m0, (m2, m4)) =
        foldBox (\x, (MkBoxInt w), (a0, (a2, a4)) =>
                  let aw = abs w
                      x2 = x * x
                  in (a0 + aw, (a2 + aw * x2, a4 + aw * x2 * x2)))
                (the Integer 0, (the Integer 0, the Integer 0))
                box
  in reduceMSF (mkMSF (intToBoxInt (m4 * m0)) (integerToNat (max 1 (m2 * m2))))

||| Projects a 2D `Box BoxInt (Integer, Integer)` onto its horizontal `x`-marginal.
public export
xMarginal2D : Box BoxInt (Integer, Integer) -> Box BoxInt Integer
xMarginal2D =
  foldBox (\(x, _), w, acc => addAtKeyBox x w acc) BoxLeaf

||| Constant-mass (`x8`) 1D linear Gaussian step `[-1:2, 0:4, 1:2]`.
public export
stepGauss1DBox : Box BoxInt Integer -> Box BoxInt Integer
stepGauss1DBox =
  foldBox (\x, (MkBoxInt w), acc =>
            if w == 0
              then acc
              else addAtKeyBox (x - 1) (intToBoxInt (w * 2))
                     (addAtKeyBox x (intToBoxInt (w * 4))
                       (addAtKeyBox (x + 1) (intToBoxInt (w * 2)) acc)))
          BoxLeaf

||| Constant-mass (`x8`, linear `O(t)` bit growth) 1D nonlinear crowding step:
||| - High normalized density `|w| * 4 >= totalMass`: repulsive spreading `[-1:3, 0:2, 1:3]`
||| - Low normalized density  `|w| * 4 <  totalMass`: slow spreading `[-1:1, 0:6, 1:1]`
public export
stepNonlinearCrowding1D : Box BoxInt Integer -> Box BoxInt Integer
stepNonlinearCrowding1D box =
  let totMass = max (the Integer 1) (foldBox (\_, (MkBoxInt w), acc => acc + abs w) (the Integer 0) box)
  in foldBox (\x, (MkBoxInt w), acc =>
               if w == 0
                 then acc
                 else if abs w * 4 >= totMass
                        then addAtKeyBox (x - 1) (intToBoxInt (w * 3))
                               (addAtKeyBox x (intToBoxInt (w * 2))
                                 (addAtKeyBox (x + 1) (intToBoxInt (w * 3)) acc))
                        else addAtKeyBox (x - 1) (intToBoxInt w)
                               (addAtKeyBox x (intToBoxInt (w * 6))
                                 (addAtKeyBox (x + 1) (intToBoxInt w) acc)))
             BoxLeaf
             box

public export
record NonGaussianRGReport where
  constructor MkNonGaussianRGReport
  varRatioGauss      : MSetFraction
  varRatioComb       : MSetFraction
  varRatioNL1D       : MSetFraction
  kurtGauss16        : MSetFraction
  kurtComb16         : MSetFraction
  kurtNL1D16         : MSetFraction
  passesNonGaussianRG : Bool

||| Separates three universality classes by dynamical exponent ratio `V(16)/V(8) = 2^{2/z}`
||| and kurtosis `K(16) = <x^4>/<x^2>^2`:
||| - Free Gaussian: exact `V(16)/V(8) = 2/1` (`z = 2`), `K = 47/16 = 2.9375 -> 3`,
||| - 2D Comb `x`-marginal: subdiffusive `z > 2`, leptokurtic (`K > 4`),
||| - 1D Nonlinear Crowding: subdiffusive `z > 2`, platykurtic (`K < K_Gauss < 3`).
export
probeNonGaussianRG : NonGaussianRGReport
probeNonGaussianRG =
  let seed1D = setBox (the Integer 0) (intToBoxInt 1) BoxLeaf
      g8     = iterateBox 8 stepGauss1DBox seed1D
      g16    = iterateBox 8 stepGauss1DBox g8
      vG     = reduceMSF (divMSF (varianceBox1D g16) (varianceBox1D g8))
      kG     = kurtosisBox1D g16

      seed2D = setBox (the (Integer, Integer) (0, 0)) (intToBoxInt 1) BoxLeaf
      c8     = iterateBox 8 stepComb2D seed2D
      c16    = iterateBox 8 stepComb2D c8
      vC     = reduceMSF (divMSF (varianceBox1D (xMarginal2D c16)) (varianceBox1D (xMarginal2D c8)))
      kC     = kurtosisBox1D (xMarginal2D c16)

      nl8    = iterateBox 8 stepNonlinearCrowding1D seed1D
      nl16   = iterateBox 8 stepNonlinearCrowding1D nl8
      vNL    = reduceMSF (divMSF (varianceBox1D nl16) (varianceBox1D nl8))
      kNL    = kurtosisBox1D nl16

      passOk = andAll [ vG == mkMSF 2 1
                      , msfLT vC  (mkMSF 18 10)
                      , msfLT vNL (mkMSF 18 10)
                      , msfLT kNL kG
                      , msfLT kG  (mkMSF 3 1)
                      , msfGT kC  (mkMSF 4 1)
                      ]
  in MkNonGaussianRGReport vG vC vNL kG kC kNL passOk

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
export
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

      qOk         = andAll [qOpt == Just expectedCG, solDir.carrier == expectedCG]
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
      cacheOk     = andAll
                      [ cacheDecOk
                      , hyperOpFuelOfCachedHMSet 1 210 cachedTick cachedTick
                          == hyperOpFuelOfHMSet 1 210 symmetricMotionTick symmetricMotionTick
                      ]

      dec210      = decomposedPrimeFuelNat 210
      mono210     = gohFuelNat 210

      octMass     = foldBox (\_, w, acc => addBox acc w) (intToBoxInt 0) a2BaryonOctet
      octOrigin   = lookupBox (0, 0) a2BaryonOctet
      octNodes    = boxNodeCount a2BaryonOctet

      passOk      = andAll
                      [ usedDir == 20
                      , usedWeyl == 10
                      , usedWeyl < usedDir
                      , qOk
                      , decY
                      , decN
                      , symY
                      , symN
                      , orbMatch
                      , orbY6 > 0
                      , orbY6 < dirY6
                      , cacheOk
                      , dec210 == 340
                      , dec210 > mono210
                      , octMass == intToBoxInt 8
                      , octOrigin == intToBoxInt 2
                      , octNodes == 7
                      ]
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
prfFuelProbeDecomposed210 = Stage0.OnSeq.OnHereditaryMSet.prfDecomposedPrime210
