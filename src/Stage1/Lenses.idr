module Stage1.Lenses

import Data.Vect
import public Stage0.BoxInt
import public Stage0.HereditaryMSet
import public Stage0.StructuralFuel
import public Stage0.OnSeq.FusedStream
import public Stage1.Bridge.LaurentAntiMSetBridge

%default total

------------------------------------------------------------------------
-- 1. COORDINATE ENCODING & DECODING HELPERS FOR `PureMultiset` KEYS
------------------------------------------------------------------------

||| Canonical coordinate key encoder mapping index `idx` and signed value `val`
||| into a nested `PureMultiset` entry `{ idx -> val }`.
public export
coordSlotKey : Integer -> Integer -> PureMultiset
coordSlotKey idx val =
  MkHMSet $ setBox (signedKeyM idx) (intToBoxInt val) BoxLeaf

||| Encodes a 3D spacetime vector `[t, r, s]` into a canonical `PureMultiset` key.
public export
encodeVec3MSet : Vect 3 Integer -> PureMultiset
encodeVec3MSet [t, r, s] =
  let one = intToBoxInt 1
  in MkHMSet $ setBox (coordSlotKey 2 s) one
             ( setBox (coordSlotKey 1 r) one
             ( setBox (coordSlotKey 0 t) one BoxLeaf ))

||| Helper: Extracts the signed `Integer` value stored at coordinate tag `idx`
||| inside an encoded coordinate `PureMultiset` (returns `0` if absent).
public export
readCoordSlot : Integer -> PureMultiset -> Integer
readCoordSlot idx (MkHMSet box) =
  foldBox
    (\slotKey, _, acc =>
      case slotKey of
        MkHMSet inner =>
          let (MkBoxInt v) = lookupBox (signedKeyM idx) inner
          in if v /= 0 then v else acc)
    0
    box

||| Decodes a 3D spacetime vector `[t, r, s]` from an encoded coordinate `PureMultiset`.
public export
decodeVec3MSet : PureMultiset -> Vect 3 Integer
decodeVec3MSet m =
  [ readCoordSlot 0 m
  , readCoordSlot 1 m
  , readCoordSlot 2 m
  ]

------------------------------------------------------------------------
-- 2. METRIC LENS: CHROMATIC BILINEAR GEOMETRIES (`Red`, `Green`, `Blue`)
------------------------------------------------------------------------

||| Chromatic metric regime classification driven by `GohFuel` & velocity spread.
public export
data MetricColor : Type where
  RedMinkowski  : MetricColor
  GreenGalilean : MetricColor
  BlueEuclidean : MetricColor

public export
Eq MetricColor where
  RedMinkowski  == RedMinkowski  = True
  GreenGalilean == GreenGalilean = True
  BlueEuclidean == BlueEuclidean = True
  _             == _             = False

public export
Show MetricColor where
  show RedMinkowski  = "RedMinkowski"
  show GreenGalilean = "GreenGalilean"
  show BlueEuclidean = "BlueEuclidean"

||| External Geometric Lens over `PureMultiset` (`HereditaryMSet BoxInt`):
||| Attaches quadrance Q(v), bilinear inner product <u, v>, and causal precedence
||| without adding geometric fields to `Stage0.HereditaryMSet`.
public export
record MetricLens where
  constructor MkMetricLens
  metricColor      : MetricColor
  quadranceOf      : PureMultiset -> BoxInt
  bilinearDot      : PureMultiset -> PureMultiset -> BoxInt
  causallyPrecedes : PureMultiset -> PureMultiset -> Bool

||| 1. Red Minkowski Lens (`Signature (1, 2)`):
|||    Q_r(t, r, s) = t^2 - r^2 - s^2
|||    <u, v>_r     = t1*t2 - r1*r2 - s1*s2
|||    u \prec v   <=> (t2 > t1) && Q_r(v - u) > 0
public export
redMinkowskiLens : MetricLens
redMinkowskiLens =
  MkMetricLens
    { metricColor = RedMinkowski
    , quadranceOf = \u =>
        let [t, r, s] = decodeVec3MSet u
        in intToBoxInt (t*t - r*r - s*s)
    , bilinearDot = \u, v =>
        let [t1, r1, s1] = decodeVec3MSet u
            [t2, r2, s2] = decodeVec3MSet v
        in intToBoxInt (t1*t2 - r1*r2 - s1*s2)
    , causallyPrecedes = \u, v =>
        let [t1, r1, s1] = decodeVec3MSet u
            [t2, r2, s2] = decodeVec3MSet v
            dt = t2 - t1
            dr = r2 - r1
            ds = s2 - s1
        in (dt > 0) && ((dt*dt - dr*dr - ds*ds) > 0)
    }

||| 2. Green Galilean Lens (`Degenerate Contraction Limit`, c -> open):
|||    Q_g(t, r, s) = t^2  (invariant absolute time under unipotent shears)
|||    <u, v>_g     = t1*t2
|||    u \prec v   <=> t2 > t1  (absolute universal chronological order)
public export
greenGalileanLens : MetricLens
greenGalileanLens =
  MkMetricLens
    { metricColor = GreenGalilean
    , quadranceOf = \u =>
        let [t, _, _] = decodeVec3MSet u
        in intToBoxInt (t * t)
    , bilinearDot = \u, v =>
        let [t1, _, _] = decodeVec3MSet u
            [t2, _, _] = decodeVec3MSet v
        in intToBoxInt (t1 * t2)
    , causallyPrecedes = \u, v =>
        let [t1, _, _] = decodeVec3MSet u
            [t2, _, _] = decodeVec3MSet v
        in t2 > t1
    }

||| 3. Blue Euclidean Lens (`Frozen Spatial Relic`, dt = 0):
|||    Q_b(t, r, s) = r^2 + s^2  (positive-definite spatial quadrance)
|||    <u, v>_b     = r1*r2 + s1*s2
|||    u \prec v   <=> False      (static frozen crystal, no temporal progression)
public export
blueEuclideanLens : MetricLens
blueEuclideanLens =
  MkMetricLens
    { metricColor = BlueEuclidean
    , quadranceOf = \u =>
        let [_, r, s] = decodeVec3MSet u
        in intToBoxInt (r*r + s*s)
    , bilinearDot = \u, v =>
        let [_, r1, s1] = decodeVec3MSet u
            [_, r2, s2] = decodeVec3MSet v
        in intToBoxInt (r1*r2 + s1*s2)
    , causallyPrecedes = \_, _ => False
    }

||| Selects the active `MetricLens` directly from a `SolidifiedCarrier` freeze-out state:
||| - `YieldExhausted` / `StepHorizonReached` (frozen `Dry` relic) -> `blueEuclideanLens`
||| - Active `GohFuel` with slow drift (`stepCount >> yieldCount`) -> `greenGalileanLens`
||| - Active `GohFuel` with relativistic flux -> `redMinkowskiLens`
public export
selectMetricLensFromFuel : GohFuel cap -> (yieldCount : Nat) -> (stepCount : Nat) -> MetricLens
selectMetricLensFromFuel fuel yCount sCount =
  if gohSteps fuel == 0 then
    blueEuclideanLens
  else if sCount > (yCount * yCount + 1) then
    greenGalileanLens
  else
    redMinkowskiLens

public export
bilinearTraceBy : (PureMultiset -> PureMultiset -> BoxInt) -> PureMultiset -> PureMultiset -> BoxInt
bilinearTraceBy dotFn (MkHMSet boxA) (MkHMSet boxB) =
  foldBox
    (\u, (MkBoxInt wu), accOuter =>
      foldBox
        (\v, (MkBoxInt wv), accInner =>
          let (MkBoxInt dotUV) = dotFn u v
          in addBox accInner (intToBoxInt (wu * wv * dotUV)))
        accOuter
        boxB)
    (intToBoxInt 0)
    boxA

||| Evaluates the bilinear trace <M, N>_lens across two field distributions:
|||   traceWith lens M N = sum_{u in M, v in N} w_M(u) * w_N(v) * lens.bilinearDot u v
public export
traceWith : MetricLens -> PureMultiset -> PureMultiset -> BoxInt
traceWith lens = bilinearTraceBy lens.bilinearDot

||| Laurent-aware bilinear inner product between two sub-multiset keys:
||| - On scalar Laurent keys `(ExponentKey e1, ExponentKey e2)`: exact 1D scale product `e1 * e2`.
||| - On nested 3D spacetime vector keys: delegates to `lens.bilinearDot`.
public export
laurentBilinearDot : MetricLens -> PureMultiset -> PureMultiset -> BoxInt
laurentBilinearDot lens u v =
  case (classifyLaurentKey unwrapBox u, classifyLaurentKey unwrapBox v) of
    (ExponentKey e1, ExponentKey e2) => intToBoxInt (e1 * e2)
    _                                => lens.bilinearDot u v

||| Evaluates the Laurent-aware bilinear trace `<M, N>_lens` across 1D Laurent
||| or 3D spacetime distributions.
public export
traceLaurentWith : MetricLens -> PureMultiset -> PureMultiset -> BoxInt
traceLaurentWith lens = bilinearTraceBy (laurentBilinearDot lens)

------------------------------------------------------------------------
-- 3. SCALE LENS: LAURENT RENORMALIZATION & UV-IR DUALITY
------------------------------------------------------------------------

||| External Scale & Renormalization Lens over `PureMultiset`:
||| Packages coarse-graining (`zoomOut`), fine-graining (`zoomIn`), and UV-IR duality
||| (`alpha^n <-> alpha^-n`) without modifying `Stage0.HereditaryMSet`.
public export
record ScaleLens where
  constructor MkScaleLens
  zoomOut : (k : Nat) -> PureMultiset -> PureMultiset
  zoomIn  : (k : Nat) -> PureMultiset -> PureMultiset
  dualize : PureMultiset -> PureMultiset

||| Canonical Laurent Scale Lens backed by `LaurentAntiMSetBridge`.
public export
laurentScaleLens : ScaleLens
laurentScaleLens =
  MkScaleLens
    { zoomOut = laurentZoomOut
    , zoomIn  = laurentZoomIn
    , dualize = uvIrDual
    }

||| Evolves a `PureMultiset` outward by `steps` scale ticks using `ScaleLens`
||| and measures its resulting geometric action/norm under `MetricLens` (3D vector keys).
public export
expandAndMeasure : ScaleLens -> MetricLens -> (steps : Nat) -> PureMultiset -> BoxInt
expandAndMeasure sLens mLens steps state =
  let expanded = sLens.zoomOut steps state
  in traceWith mLens expanded expanded

||| Evolves a `PureMultiset` outward by `steps` scale ticks using `ScaleLens`
||| and measures its Laurent-aware action/norm under `MetricLens`.
public export
expandAndMeasureLaurent : ScaleLens -> MetricLens -> (steps : Nat) -> PureMultiset -> BoxInt
expandAndMeasureLaurent sLens mLens steps state =
  let expanded = sLens.zoomOut steps state
  in traceLaurentWith mLens expanded expanded

------------------------------------------------------------------------
-- 4. THERMODYNAMIC LENS: NESTING FREE ENERGY & CONDENSATION
------------------------------------------------------------------------

||| External Thermodynamic Lens evaluating structural binding energy and
||| radiative release over `PureMultiset` without polluting `Stage0`.
public export
record ThermodynamicLens where
  constructor MkThermoLens
  ||| Computes structural free energy proxy (totalMass + height + maxDeg)
  freeEnergyOf : PureMultiset -> BoxInt
  ||| Condenses a state by 1 scale unit toward degree 0 and returns `(condensed, releasedHeat)`
  condenseStep : PureMultiset -> (PureMultiset, BoxInt)

||| Structural free-energy proxy combining active mass, AVL height, and true Laurent degree.
public export
freeEnergyProxy : PureMultiset -> BoxInt
freeEnergyProxy (MkHMSet box) =
  let stats = collectSupportStats box
      h     = boxHeight box
  in intToBoxInt (natToInteger (stats.totalMass + h + stats.maxDeg))

||| Contracts every scalar Laurent exponent `e` by `1` step inward toward degree `0`
||| (`e > 0 => e - 1`, `e < 0 => e + 1`, `0 => 0`), preserving nested keys.
public export
condenseTowardOrigin : PureMultiset -> PureMultiset
condenseTowardOrigin (MkHMSet box) =
  MkHMSet $ foldBox (\key, weight, acc =>
                      case classifyLaurentKey unwrapBox key of
                        ExponentKey e =>
                          let e' = if e > 0 then e - 1 else if e < 0 then e + 1 else 0
                          in addAtKeyBox (signedKeyM e') weight acc
                        NestedTermKey m =>
                          addAtKeyBox m weight acc)
                    BoxLeaf
                    box

public export
defaultThermoLens : ThermodynamicLens
defaultThermoLens =
  MkThermoLens
    { freeEnergyOf = freeEnergyProxy
    , condenseStep = \m =>
        let condensed = condenseTowardOrigin m
            eBefore   = unwrapBox (freeEnergyProxy m)
            eAfter    = unwrapBox (freeEnergyProxy condensed)
        in (condensed, intToBoxInt (eBefore - eAfter))
    }


------------------------------------------------------------------------
-- 4. CONSTRUCTIVIST METRIC & STABILITY RECOGNIZERS (`recognition-rule.md`)
------------------------------------------------------------------------

||| Boolean check for forward-directed Red Minkowski timelike separation:
||| `dt = t_B - t_A > 0` and `Q_r(v_B - v_A) = dt^2 - dr^2 - ds^2 > 0`.
public export
isTimelikeFuture3Bool : Vect 3 Integer -> Vect 3 Integer -> Bool
isTimelikeFuture3Bool [tA, rA, sA] [tB, rB, sB] =
  let dt = tB - tA
      dr = rB - rA
      ds = sB - sA
  in (dt > 0) && ((dt * dt - dr * dr - ds * ds) > 0)

||| Proof predicate witnessing future-directed Red Minkowski timelike precedence.
public export
IsTimelikeFuture3 : Vect 3 Integer -> Vect 3 Integer -> Type
IsTimelikeFuture3 vA vB = (isTimelikeFuture3Bool vA vB = True)

||| Total `Dec` recognizer deciding causal timelike orientation `Q_r(vB - vA) > 0 && dt > 0`.
public export
recognizeTimelikePair : (vA, vB : Vect 3 Integer) -> Dec (IsTimelikeFuture3 vA vB)
recognizeTimelikePair vA vB = decideBoolTrue (isTimelikeFuture3Bool vA vB)

||| Erased-proof `Subset` storing a verified future-timelike pair `(vA, vB)`.
public export
TimelikeCausalPair : Type
TimelikeCausalPair = Subset (Vect 3 Integer, Vect 3 Integer) (\(a, b) => IsTimelikeFuture3 a b)

||| Smart constructor packing a causally verified event pair.
public export
toTimelikeCausalPair : (vA, vB : Vect 3 Integer) -> Maybe TimelikeCausalPair
toTimelikeCausalPair vA vB =
  case recognizeTimelikePair vA vB of
    Yes prf => Just (Element (vA, vB) prf)
    No _    => Nothing

||| Proof predicate witnessing stability of an emergent Layer `L` candidate backed
||| by a decidable stability filter over `Box c lPrev` (`Rule 03` §8.5).
public export
IsStableLayerL : (stablePred : Box c lPrev -> Bool) -> Box c lPrev -> Type
IsStableLayerL stablePred b = (stablePred b = True)

||| Total `Dec` recognizer validating Layer `L` stability over `L - 1` constituent multisets.
public export
recognizeStable : (stablePred : Box c lPrev -> Bool) ->
                  (b : Box c lPrev) ->
                  Dec (IsStableLayerL stablePred b)
recognizeStable stablePred b = decideBoolTrue (stablePred b)

||| Erased-proof `Subset` storing a verified Layer `L` assembly.
public export
StableLayer : (c : Type) -> (lPrev : Type) -> (stablePred : Box c lPrev -> Bool) -> Type
StableLayer c lPrev stablePred = Subset (Box c lPrev) (IsStableLayerL stablePred)

||| Smart constructor validating a Layer `L` candidate into `StableLayer`.
public export
toStableLayer : {0 c, lPrev : Type} ->
                (stablePred : Box c lPrev -> Bool) ->
                (b : Box c lPrev) ->
                Maybe (StableLayer c lPrev stablePred)
toStableLayer stablePred b =
  case recognizeStable stablePred b of
    Yes prf => Just (Element b prf)
    No _    => Nothing
