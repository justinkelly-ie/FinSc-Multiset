module Stage0.OnSeq.OnHereditaryMSet

import Data.Nat
import Decidable.Equality
import public Data.Fuel
import public Stage0.Box
import public Stage0.BoxInt
import public Stage0.SignedBit
import public Stage0.HereditaryMSet
import public Stage0.PrimeMultiset
import public Stage0.StructuralFuel
import public Stage0.OnSeq.OnMSet
import public Stage0.OnSeq.FusedStream

%default total

--------------------------------------------------------------------------------
-- 1. ON-SEQUENCE LIFT OF `HereditaryMSet c` (`OnHereditaryMSet`)
--------------------------------------------------------------------------------

||| Unbounded sequence (`Nat -> HereditaryMSet c`) indexed from `start : Nat`.
public export
0 OnHereditaryMSet : (c : Type) -> Type
OnHereditaryMSet c = OnSeq (HereditaryMSet c)

||| Canonical signed integer on-sequence alias (`OnSeq PureMultiset`).
public export
0 OnPureMultiset : Type
OnPureMultiset = OnHereditaryMSet BoxInt

public export
addOnHMSet : MultisetWeight c => OnHereditaryMSet c -> OnHereditaryMSet c -> OnHereditaryMSet c
addOnHMSet = zipWith addHMSet

public export
subOnHMSet : MultisetWeight c => OnHereditaryMSet c -> OnHereditaryMSet c -> OnHereditaryMSet c
subOnHMSet = zipWith subHMSet

public export
negOnHMSet : MultisetWeight c => OnHereditaryMSet c -> OnHereditaryMSet c
negOnHMSet = Stage0.OnSeq.OnMSet.map negHMSet

public export
hadamardOnHMSet : MultisetWeight c => OnHereditaryMSet c -> OnHereditaryMSet c -> OnHereditaryMSet c
hadamardOnHMSet = zipWith hadamardHMSet

public export
mulOnHMSet : MultisetWeight c => OnHereditaryMSet c -> OnHereditaryMSet c -> OnHereditaryMSet c
mulOnHMSet = zipWith mulHMSet

public export
hyperOpOnHMSet : MultisetWeight c =>
                 (level : Nat) ->
                 OnHereditaryMSet c ->
                 OnHereditaryMSet c ->
                 OnHereditaryMSet c
hyperOpOnHMSet lvl = zipWith (hyperOp lvl)

public export
scaleOnHMSet : MultisetWeight c => c -> OnHereditaryMSet c -> OnHereditaryMSet c
scaleOnHMSet s = Stage0.OnSeq.OnMSet.map (scaleHMSet s)

public export
freezeOnHMSetToSigned : OnPureMultiset -> OnHereditaryMSet SignedBit
freezeOnHMSetToSigned = Stage0.OnSeq.OnMSet.map freezeToSignedPhase

public export
coolOnHMSetToParity : OnHereditaryMSet SignedBit -> OnHereditaryMSet MultisetBit
coolOnHMSetToParity = Stage0.OnSeq.OnMSet.map coolToParityPhase

public export
supportOnHMSet : OnPureMultiset -> OnHereditaryMSet MultisetBit
supportOnHMSet = Stage0.OnSeq.OnMSet.map toSupportMSet

public export
supportStatsOnHMSet : MultisetWeight c => OnHereditaryMSet c -> OnSeq SupportStats
supportStatsOnHMSet = Stage0.OnSeq.OnMSet.map (\(MkHMSet box) => collectSupportStats box)

public export
selfFuelOnHMSet : MultisetWeight c => OnHereditaryMSet c -> OnSeq (AnyGohFuel, Nat)
selfFuelOnHMSet = Stage0.OnSeq.OnMSet.map selfFuelOfHMSet

--------------------------------------------------------------------------------
-- 2. COINDUCTIVE `InfFuel` BRIDGED TO IDRIS 2 `Data.Fuel`
--------------------------------------------------------------------------------

||| Productive total coinductive fuel stream (avoids `Data.Fuel.forever`,
||| which is marked non-terminating in Idris 2 0.8.0 because `More` is `Lazy`).
public export
data InfFuel : Type where
  InfDry  : InfFuel
  InfMore : Inf InfFuel -> InfFuel

||| Unbounded self-sustaining `InfFuel` stream.
public export
openInfFuel : InfFuel
openInfFuel = InfMore openInfFuel

||| Demand-driven finite slice from `InfFuel` directly into Idris 2's `Data.Fuel`.
public export
sliceInfToDataFuel : Nat -> InfFuel -> Fuel
sliceInfToDataFuel Z     _            = Dry
sliceInfToDataFuel (S _) InfDry       = Dry
sliceInfToDataFuel (S k) (InfMore nf) = More (sliceInfToDataFuel k nf)

||| Converts a bounded `GohFuel cap` envelope into Idris 2's `Data.Fuel`.
public export
gohToDataFuel : GohFuel cap -> Fuel
gohToDataFuel f = limit (gohSteps f)

--------------------------------------------------------------------------------
-- 3. CONSTRUCTIVE `GohPrimeSum` FUEL SPLITTING (`recognition-rule.md`)
--------------------------------------------------------------------------------

||| Combines two certified prime `GohFuel` budgets sequentially (`gohSteps` gains
||| boundary headroom over monolithic `gohFuelForCapacity (p + q)`).
public export
primeSumGohFuel : {p, q, n : Nat} -> GohPrimeSum p q n -> GohFuel n
primeSumGohFuel (MkGohPrimeSum {p} {q} _ _ prf) =
  rewrite sym prf in sequentialFuel (gohFuelForCapacity p) (gohFuelForCapacity q)

||| Witness that `n` decomposes into a pair of 13-smooth `GohPrime` capacities `p + q = n`.
public export
data HasGohPrimeSum : (n : Nat) -> Type where
  MkHasGohPrimeSum : (p : Nat) -> (q : Nat) -> GohPrime p -> GohPrime q -> (p + q = n) -> HasGohPrimeSum n

||| Converts a recognized `HasGohPrimeSum n` into a `Stage0.PrimeMultiset.GohPrimeSum`.
public export
toGohPrimeSum : {n : Nat} -> (s : HasGohPrimeSum n) -> (p : Nat ** q : Nat ** GohPrimeSum p q n)
toGohPrimeSum (MkHasGohPrimeSum p q prP prQ eqPrf) = (p ** q ** MkGohPrimeSum prP prQ eqPrf)

public export
refuteSecondPrf : (p, n : Nat) ->
                  (p + 2  = n -> Void) -> (p + 3  = n -> Void) ->
                  (p + 5  = n -> Void) -> (p + 7  = n -> Void) ->
                  (p + 11 = n -> Void) -> (p + 13 = n -> Void) ->
                  {q : Nat} -> GohPrime q -> (p + q = n) -> Void
refuteSecondPrf _ _ c2  _   _   _   _   _   Prime2  eqPrf = c2  eqPrf
refuteSecondPrf _ _ _   c3  _   _   _   _   Prime3  eqPrf = c3  eqPrf
refuteSecondPrf _ _ _   _   c5  _   _   _   Prime5  eqPrf = c5  eqPrf
refuteSecondPrf _ _ _   _   _   c7  _   _   Prime7  eqPrf = c7  eqPrf
refuteSecondPrf _ _ _   _   _   _   c11 _   Prime11 eqPrf = c11 eqPrf
refuteSecondPrf _ _ _   _   _   _   _   c13 Prime13 eqPrf = c13 eqPrf

public export
checkGohSecondFor : (p : Nat) -> (prP : GohPrime p) -> (n : Nat) ->
                    Dec (q : Nat ** (GohPrime q, p + q = n))
checkGohSecondFor p prP n =
  case decEq (p + 2) n of
    Yes prf => Yes (2 ** (Prime2, prf))
    No c2 =>
      case decEq (p + 3) n of
        Yes prf => Yes (3 ** (Prime3, prf))
        No c3 =>
          case decEq (p + 5) n of
            Yes prf => Yes (5 ** (Prime5, prf))
            No c5 =>
              case decEq (p + 7) n of
                Yes prf => Yes (7 ** (Prime7, prf))
                No c7 =>
                  case decEq (p + 11) n of
                    Yes prf => Yes (11 ** (Prime11, prf))
                    No c11 =>
                      case decEq (p + 13) n of
                        Yes prf => Yes (13 ** (Prime13, prf))
                        No c13 => No (\(_ ** (prQ, eqPrf)) => refuteSecondPrf p n c2 c3 c5 c7 c11 c13 prQ eqPrf)

public export
refuteFirstPrf : (n : Nat) ->
                 ((q : Nat ** (GohPrime q, 2  + q = n)) -> Void) ->
                 ((q : Nat ** (GohPrime q, 3  + q = n)) -> Void) ->
                 ((q : Nat ** (GohPrime q, 5  + q = n)) -> Void) ->
                 ((q : Nat ** (GohPrime q, 7  + q = n)) -> Void) ->
                 ((q : Nat ** (GohPrime q, 11 + q = n)) -> Void) ->
                 ((q : Nat ** (GohPrime q, 13 + q = n)) -> Void) ->
                 {p, q : Nat} -> GohPrime p -> GohPrime q -> (p + q = n) -> Void
refuteFirstPrf _ c2  _   _   _   _   _   Prime2  prQ eqPrf = c2  (_ ** (prQ, eqPrf))
refuteFirstPrf _ _   c3  _   _   _   _   Prime3  prQ eqPrf = c3  (_ ** (prQ, eqPrf))
refuteFirstPrf _ _   _   c5  _   _   _   Prime5  prQ eqPrf = c5  (_ ** (prQ, eqPrf))
refuteFirstPrf _ _   _   _   c7  _   _   Prime7  prQ eqPrf = c7  (_ ** (prQ, eqPrf))
refuteFirstPrf _ _   _   _   _   c11 _   Prime11 prQ eqPrf = c11 (_ ** (prQ, eqPrf))
refuteFirstPrf _ _   _   _   _   _   c13 Prime13 prQ eqPrf = c13 (_ ** (prQ, eqPrf))

||| Total constructive `Dec` recognizer deciding whether `n` splits into two
||| 13-smooth `GohPrime` capacities `p + q = n`.
public export
recognizeGohPrimeSum : (n : Nat) -> Dec (HasGohPrimeSum n)
recognizeGohPrimeSum n =
  case checkGohSecondFor 2 Prime2 n of
    Yes (q ** (prQ, prf)) => Yes (MkHasGohPrimeSum 2 q Prime2 prQ prf)
    No c2 =>
      case checkGohSecondFor 3 Prime3 n of
        Yes (q ** (prQ, prf)) => Yes (MkHasGohPrimeSum 3 q Prime3 prQ prf)
        No c3 =>
          case checkGohSecondFor 5 Prime5 n of
            Yes (q ** (prQ, prf)) => Yes (MkHasGohPrimeSum 5 q Prime5 prQ prf)
            No c5 =>
              case checkGohSecondFor 7 Prime7 n of
                Yes (q ** (prQ, prf)) => Yes (MkHasGohPrimeSum 7 q Prime7 prQ prf)
                No c7 =>
                  case checkGohSecondFor 11 Prime11 n of
                    Yes (q ** (prQ, prf)) => Yes (MkHasGohPrimeSum 11 q Prime11 prQ prf)
                    No c11 =>
                      case checkGohSecondFor 13 Prime13 n of
                        Yes (q ** (prQ, prf)) => Yes (MkHasGohPrimeSum 13 q Prime13 prQ prf)
                        No c13 => No (\(MkHasGohPrimeSum _ _ prP prQ eqPrf) => refuteFirstPrf n c2 c3 c5 c7 c11 c13 prP prQ eqPrf)

||| Recursive 13-smooth `GohPrime` sum partition witness for arbitrary `n : Nat`.
public export
data GohPrimePartition : (n : Nat) -> Type where
  PartZero  : GohPrimePartition 0
  PartUnit  : GohPrimePartition 1
  PartPrime : (p : Nat) -> GohPrime p -> GohPrimePartition p
  PartAdd   : (p : Nat) -> GohPrime p -> {rem : Nat} -> GohPrimePartition rem -> GohPrimePartition (p + rem)

||| Lowers any `GohPrimePartition n` to a sequential `GohFuel n` envelope.
public export
partitionFuel : {n : Nat} -> GohPrimePartition n -> GohFuel n
partitionFuel PartZero              = gohFuelForCapacity 0
partitionFuel PartUnit              = gohFuelForCapacity 1
partitionFuel (PartPrime p _)       = gohFuelForCapacity p
partitionFuel (PartAdd p _ rest)    = sequentialFuel (gohFuelForCapacity p) (partitionFuel rest)

||| Total structural builder decomposing any capacity `n` (including macroscopic `210+`)
||| into certified 13-smooth `GohPrime` segments (preferring exact 2-prime Goldbach pairs
||| when available, and chunking larger inputs by `Prime13`).
public export
buildGohPrimePartition : (n : Nat) -> GohPrimePartition n
buildGohPrimePartition 0  = PartZero
buildGohPrimePartition 1  = PartUnit
buildGohPrimePartition 2  = PartPrime 2 Prime2
buildGohPrimePartition 3  = PartPrime 3 Prime3
buildGohPrimePartition 4  = PartAdd 2 Prime2 (PartPrime 2 Prime2)
buildGohPrimePartition 5  = PartAdd 2 Prime2 (PartPrime 3 Prime3)
buildGohPrimePartition 6  = PartAdd 3 Prime3 (PartPrime 3 Prime3)
buildGohPrimePartition 7  = PartAdd 2 Prime2 (PartPrime 5 Prime5)
buildGohPrimePartition 8  = PartAdd 3 Prime3 (PartPrime 5 Prime5)
buildGohPrimePartition 9  = PartAdd 2 Prime2 (PartPrime 7 Prime7)
buildGohPrimePartition 10 = PartAdd 3 Prime3 (PartPrime 7 Prime7)
buildGohPrimePartition 11 = PartPrime 11 Prime11
buildGohPrimePartition 12 = PartAdd 5 Prime5 (PartPrime 7 Prime7)
buildGohPrimePartition 13 = PartAdd 2 Prime2 (PartPrime 11 Prime11)
buildGohPrimePartition 14 = PartAdd 3 Prime3 (PartPrime 11 Prime11)
buildGohPrimePartition (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S k))))))))))))))) =
  case recognizeGohPrimeSum (15 + k) of
    Yes (MkHasGohPrimeSum p q prP prQ eqPrf) =>
      rewrite sym eqPrf in PartAdd p prP (PartPrime q prQ)
    No _ =>
      PartAdd 13 Prime13 (buildGohPrimePartition (S (S k)))

||| Generalized 13-smooth `GohPrime` partitioned fuel step count valid for all `n : Nat`.
public export
decomposedPrimeFuelNat : (n : Nat) -> Nat
decomposedPrimeFuelNat n = gohSteps (partitionFuel (buildGohPrimePartition n))

||| Evaluates `gohSteps` using certified 13-smooth `GohPrime` splitting for arbitrary `n : Nat`
||| (`4 -> 8`, `8 -> 15`, `24 -> 39`, `210 -> 340`).
public export
primeSplitFuelNat : (n : Nat) -> Nat
primeSplitFuelNat = decomposedPrimeFuelNat

--------------------------------------------------------------------------------
-- 4. SUPPORT STATS ALIASES (UPGRADED STAGE 0 VS. LEGACY HEIGHT-ONLY)
--------------------------------------------------------------------------------

||| Alias pointing directly to `Stage0.HereditaryMSet.collectSupportStats`
||| (now recursively inspects multi-axis coordinate weights via `maxWeightInBox`).
public export
collectRecursiveStats : MultisetWeight c => HereditaryMSet c -> SupportStats
collectRecursiveStats (MkHMSet b) = collectSupportStats b

||| Legacy single-pass collector truncating multi-node inner keys to `boxHeight`
||| (kept purely as a negative-control baseline in `Stage1.FuelProbe`).
public export
legacyHeightOnlyStats : MultisetWeight c => Box c (HereditaryMSet c) -> SupportStats
legacyHeightOnlyStats BoxLeaf = emptySupportStats
legacyHeightOnlyStats (BoxNode _ left (MkHMSet innerBox) w right) =
  let lStats     = legacyHeightOnlyStats left
      rStats     = legacyHeightOnlyStats right
      absW       = weightMagnitude w
      childDeg   = case innerBox of
                     BoxLeaf => 0
                     BoxNode _ BoxLeaf (MkHMSet BoxLeaf) expW BoxLeaf =>
                       weightMagnitude expW
                     _ => boxHeight innerBox
      selfNnz    = if isZero w then 0 else 1
      mergedNnz  = lStats.nnz + selfNnz + rStats.nnz
      mergedMass = lStats.totalMass + absW + rStats.totalMass
      mergedMax  = fuelMax lStats.maxDeg (fuelMax childDeg rStats.maxDeg)
  in MkSupportStats mergedNnz mergedMass mergedMax

--------------------------------------------------------------------------------
-- 5. PLUGGABLE STATIC/BOUNDED `FuelPolicy` PRESETS FOR A/B PROBING
--------------------------------------------------------------------------------

||| Controls whether `YieldExhausted` stops an asymmetric left-to-right zipper
||| (`AsymmetricZipperFreeze`) or freezes entire symmetric radial shells (`SymmetricRadialFreeze`).
public export
data FreezeStrategy : Type where
  AsymmetricZipperFreeze : FreezeStrategy
  SymmetricRadialFreeze  : FreezeStrategy

public export
Eq FreezeStrategy where
  AsymmetricZipperFreeze == AsymmetricZipperFreeze = True
  SymmetricRadialFreeze  == SymmetricRadialFreeze  = True
  _                      == _                      = False

public export
Show FreezeStrategy where
  show AsymmetricZipperFreeze = "AsymmetricZipperFreeze"
  show SymmetricRadialFreeze  = "SymmetricRadialFreeze"

||| Pluggable Stage 0/1 static/bounded fuel sizer policy for A/B probing against
||| the uncapped `InfFuel` -> `Data.Fuel` streaming oracle (`Stage1.FuelProbe`).
public export
record FuelPolicy where
  constructor MkFuelPolicy
  policyName      : String
  useRecursiveDeg : Bool
  freezeStrategy  : FreezeStrategy
  sizeSingle      : (cap : Nat) -> (treeHeight : Nat) -> SupportStats -> (GohFuel cap, Nat)
  sizeBinary      : InteractionMode -> (cap : Nat) -> (hA : Nat) -> (hB : Nat) -> SupportStats -> SupportStats -> (GohFuel cap, Nat)

private
treeBoundForMode : InteractionMode -> Nat -> Nat -> Nat
treeBoundForMode AdditiveMode     hA hB = fastNatPower2 hA + fastNatPower2 hB
treeBoundForMode IntersectionMode hA hB = fastNatPower2 hA + fastNatPower2 hB
treeBoundForMode ConvolutionalMode hA hB = fastNatPower2 (hA + hB)
treeBoundForMode CaretationMode   hA hB = fastNatPower2 (hA + hB) + boundaryBracketOverhead

||| Permanent negative regression control reproducing the old unfixed behavior:
||| adds `+ stats.totalMass` into `stepBudget`, truncates multi-axis keys to
||| `boxHeight`, and freezes asymmetrically left-to-right.
public export
legacyMassBloatedPolicy : FuelPolicy
legacyMassBloatedPolicy =
  MkFuelPolicy
    { policyName = "legacyMassBloated"
    , useRecursiveDeg = False
    , freezeStrategy = AsymmetricZipperFreeze
    , sizeSingle = \cap, h, stats =>
        let boundedCap = min cap (stats.nnz + S stats.maxDeg)
            yf         = MkGohFuel (gohFuelNat boundedCap)
            sb         = gohSteps yf + fastNatPower2 h + stats.totalMass + stats.nnz
        in (yf, sb)
    , sizeBinary = \mode, cap, hA, hB, sA, sB =>
        let comb       = combineSupportStats mode sA sB
            boundedCap = min cap (comb.nnz + S comb.maxDeg)
            yf         = MkGohFuel (gohFuelNat boundedCap)
            sb         = gohSteps yf + treeBoundForMode mode hA hB + comb.totalMass + comb.nnz
        in (yf, sb)
    }

||| Structural-only `stepBudget` without `+ stats.totalMass`, keeping legacy
||| left-to-right `AsymmetricZipperFreeze` and legacy `boxHeight` stats.
public export
structuralOnlyPolicy : FuelPolicy
structuralOnlyPolicy =
  MkFuelPolicy
    { policyName = "structuralOnly"
    , useRecursiveDeg = False
    , freezeStrategy = AsymmetricZipperFreeze
    , sizeSingle = \cap, h, stats => mkBudgetFromStats cap (fastNatPower2 h) stats
    , sizeBinary = \mode, cap, hA, hB, sA, sB =>
        mkBudgetFromStats cap (treeBoundForMode mode hA hB) (combineSupportStats mode sA sB)
    }

||| Mirrors the upgraded production `Stage0.HereditaryMSet` + `FusedStream`
||| defaults: structural `mkBudgetFromStats` (zero `totalMass` bloat),
||| multi-axis `collectSupportStats`, and `SymmetricRadialFreeze`.
public export
currentHMSetPolicy : FuelPolicy
currentHMSetPolicy =
  MkFuelPolicy
    { policyName = "currentHMSet"
    , useRecursiveDeg = True
    , freezeStrategy = SymmetricRadialFreeze
    , sizeSingle = \cap, h, stats => mkBudgetFromStats cap (fastNatPower2 h) stats
    , sizeBinary = \mode, cap, hA, hB, sA, sB =>
        mkBudgetFromStats cap (treeBoundForMode mode hA hB) (combineSupportStats mode sA sB)
    }

||| Explicit structural + symmetric policy alias matching upgraded `currentHMSetPolicy`.
public export
symmetricStructuralPolicy : FuelPolicy
symmetricStructuralPolicy =
  { policyName := "symmetricStructural" } currentHMSetPolicy

||| Static-test `FuelPolicy` injecting `primeSplitFuelNat` into
||| `Stage0.HereditaryMSet.mkBudgetFromStatsWith` alongside recursive
||| `collectSupportStats` and `SymmetricRadialFreeze`.
public export
primeSplitFuelPolicy : FuelPolicy
primeSplitFuelPolicy =
  MkFuelPolicy
    { policyName = "primeSplitFuel"
    , useRecursiveDeg = True
    , freezeStrategy = SymmetricRadialFreeze
    , sizeSingle = \cap, h, stats =>
        mkBudgetFromStatsWith primeSplitFuelNat cap (fastNatPower2 h) stats
    , sizeBinary = \mode, cap, hA, hB, sA, sB =>
        mkBudgetFromStatsWith primeSplitFuelNat cap (treeBoundForMode mode hA hB) (combineSupportStats mode sA sB)
    }

--------------------------------------------------------------------------------
-- 6. BOUNDED `FuelPolicy` STEPPING & `InfFuel`/`Data.Fuel` STREAM EVOLUTION
--------------------------------------------------------------------------------

||| One observed tick along a bounded `FuelPolicy` `OnHereditaryMSet` trajectory.
public export
record FuelStepSnapshot (cap : Nat) (c : Type) where
  constructor MkFuelStepSnapshot
  tickIdx        : Nat
  state          : HereditaryMSet c
  freezeReason   : FreezeReason
  allocatedYield : Nat
  usedYield      : Nat
  allocatedSteps : Nat
  usedSteps      : Nat
  stats          : SupportStats

||| One observed tick along an unbounded coinductive `InfFuel` -> `Data.Fuel` trajectory
||| (carries zero hardcoded static caps or step limits).
public export
record InfFuelSnapshot (c : Type) where
  constructor MkInfFuelSnapshot
  tickIdx      : Nat
  state        : HereditaryMSet c
  freezeReason : FreezeReason
  usedYield    : Nat
  usedSteps    : Nat
  stats        : SupportStats

private
modeForLevel : Nat -> InteractionMode
modeForLevel Z         = AdditiveMode
modeForLevel (S Z)     = ConvolutionalMode
modeForLevel (S (S _)) = CaretationMode

private
statsForPolicy : MultisetWeight c => FuelPolicy -> HereditaryMSet c -> SupportStats
statsForPolicy pol (MkHMSet b) =
  if pol.useRecursiveDeg then collectSupportStats b else legacyHeightOnlyStats b

private
runHyperOpWithInfFuelCached : MultisetWeight c =>
                              InfFuel ->
                              (level : Nat) ->
                              (HereditaryMSet c, SupportStats) ->
                              (HereditaryMSet c, SupportStats) ->
                              InfFuelSnapshot c
runHyperOpWithInfFuelCached infFuel level (mA, sA) (mB, sB) =
  let needed = S (S (sA.nnz * sB.nnz + 2 * (sA.nnz + sB.nnz) + 4))
      df     = sliceInfToDataFuel needed infFuel
      insertTerm : (HereditaryMSet c, c) -> HereditaryMSet c -> HereditaryMSet c
      insertTerm (k, w) (MkHMSet acc) = MkHMSet (addAtKeyBox k w acc)
      outcome : (HereditaryMSet c, FreezeReason, Nat, Nat)
      outcome = case level of
                  Z => runDecoupledDataFuel df df hyperOpStep insertTerm emptyHMSet (initHyperOpZipState 0 mA mB)
                  S innerLvl => runSymmetricRadialConvDataFuel innerLvl df df mA mB
  in case outcome of
       (outState, reason, yUsed, sUsed) =>
         let outStats = case outState of MkHMSet bOut => collectSupportStats bOut
         in MkInfFuelSnapshot 0 outState reason yUsed sUsed outStats

||| Evaluates `hyperOp level mA mB` polymorphically over any `MultisetWeight c`
||| carrier under `InfFuel` sliced dynamically on demand into Idris 2 `Data.Fuel`.
public export
runHyperOpWithInfFuel : MultisetWeight c =>
                        InfFuel ->
                        (level : Nat) ->
                        HereditaryMSet c ->
                        HereditaryMSet c ->
                        InfFuelSnapshot c
runHyperOpWithInfFuel infFuel level mA@(MkHMSet bA) mB@(MkHMSet bB) =
  runHyperOpWithInfFuelCached infFuel level (mA, collectSupportStats bA) (mB, collectSupportStats bB)

private
stepInfIterate : MultisetWeight c =>
                 InfFuel ->
                 Nat ->
                 (HereditaryMSet c, SupportStats) ->
                 Nat ->
                 InfFuelSnapshot c ->
                 InfFuelSnapshot c
stepInfIterate _ _ _ Z snap = snap
stepInfIterate infFuel level kernelPair (S rem) snap =
  let nextSnap = runHyperOpWithInfFuelCached infFuel level (snap.state, snap.stats) kernelPair
      stamped  = { tickIdx := S snap.tickIdx } nextSnap
  in stepInfIterate infFuel level kernelPair rem stamped

||| Generates an unbounded causal `OnSeq (InfFuelSnapshot c)` driven purely by
||| `InfFuel` -> `Data.Fuel` (zero hardcoded static capacity caps).
public export
evolveOnHMSetInfFuel : MultisetWeight c =>
                       InfFuel ->
                       (level : Nat) ->
                       (seed : HereditaryMSet c) ->
                       (kernel : HereditaryMSet c) ->
                       OnSeq (InfFuelSnapshot c)
evolveOnHMSetInfFuel infFuel level seed kernel =
  let initStats  = case seed of MkHMSet b => collectSupportStats b
      kStats     = case kernel of MkHMSet bk => collectSupportStats bk
      snap0      = MkInfFuelSnapshot 0 seed NaturalCompletion 0 0 initStats
  in MkOnSeq 0 (\t => stepInfIterate infFuel level (kernel, kStats) t snap0)

||| Projects an `InfFuelSnapshot` trajectory down to a pure `OnHereditaryMSet c`.
public export
onInfStates : OnSeq (InfFuelSnapshot c) -> OnHereditaryMSet c
onInfStates = Stage0.OnSeq.OnMSet.map (.state)

private
runFueledHyperOpCached : MultisetWeight c =>
                         FuelPolicy ->
                         (level : Nat) ->
                         (cap : Nat) ->
                         (HereditaryMSet c, SupportStats) ->
                         (HereditaryMSet c, SupportStats, Nat) ->
                         FuelStepSnapshot cap c
runFueledHyperOpCached pol level cap (mA@(MkHMSet bA), sA) (mB, sB, hB) =
  let (yFuel, sBudget) = pol.sizeBinary (modeForLevel level) cap (boxHeight bA) hB sA sB
      allocY = gohSteps yFuel
      allocS = sBudget
      insertTerm : (HereditaryMSet c, c) -> HereditaryMSet c -> HereditaryMSet c
      insertTerm (k, w) (MkHMSet acc) = MkHMSet (addAtKeyBox k w acc)
      sol : SolidifiedCarrier cap (HereditaryMSet c)
      sol = case (pol.freezeStrategy, level) of
              (SymmetricRadialFreeze, S innerLvl) =>
                runSymmetricRadialConv innerLvl yFuel sBudget mA mB
              _ =>
                runDecoupledStream yFuel sBudget hyperOpStep insertTerm emptyHMSet (initHyperOpZipState level mA mB)
      outStats = statsForPolicy pol sol.carrier
  in MkFuelStepSnapshot
       { tickIdx = 0
       , state = sol.carrier
       , freezeReason = sol.freezeReason
       , allocatedYield = allocY
       , usedYield = minus allocY (gohSteps sol.remainingYield)
       , allocatedSteps = allocS
       , usedSteps = minus allocS sol.remainingSteps
       , stats = outStats
       }

||| Runs a single bounded `hyperOp level mA mB` evaluation governed by `FuelPolicy`.
public export
runFueledHyperOpWithPolicy : MultisetWeight c =>
                             FuelPolicy ->
                             (level : Nat) ->
                             (cap : Nat) ->
                             HereditaryMSet c ->
                             HereditaryMSet c ->
                             FuelStepSnapshot cap c
runFueledHyperOpWithPolicy pol level cap mA mB@(MkHMSet bB) =
  let sA = statsForPolicy pol mA
      sB = statsForPolicy pol mB
  in runFueledHyperOpCached pol level cap (mA, sA) (mB, sB, boxHeight bB)

private
stepIterate : MultisetWeight c =>
              FuelPolicy ->
              Nat ->
              (cap : Nat) ->
              (HereditaryMSet c, SupportStats, Nat) ->
              Nat ->
              FuelStepSnapshot cap c ->
              FuelStepSnapshot cap c
stepIterate _ _ _ _ Z snap = snap
stepIterate pol level cap kernelTuple (S rem) snap =
  let nextSnap = runFueledHyperOpCached pol level cap (snap.state, snap.stats) kernelTuple
      stamped  = { tickIdx := S snap.tickIdx } nextSnap
  in stepIterate pol level cap kernelTuple rem stamped

||| Generates an unbounded causal `OnSeq (FuelStepSnapshot cap c)` trajectory
||| evolving `seed` by repeated `runFueledHyperOpWithPolicy policy level cap _ kernel`.
public export
evolveOnHMSet : MultisetWeight c =>
                FuelPolicy ->
                (level : Nat) ->
                (cap : Nat) ->
                (seed : HereditaryMSet c) ->
                (kernel : HereditaryMSet c) ->
                OnSeq (FuelStepSnapshot cap c)
evolveOnHMSet pol level cap seed kernel =
  let initStats      = statsForPolicy pol seed
      kStats         = statsForPolicy pol kernel
      hKer           = hmBoxHeight kernel
      (yInit, sInit) = pol.sizeSingle cap (hmBoxHeight seed) initStats
      snap0          = MkFuelStepSnapshot 0 seed NaturalCompletion (gohSteps yInit) 0 sInit 0 initStats
  in MkOnSeq 0 (\t => stepIterate pol level cap (kernel, kStats, hKer) t snap0)

||| Projects a snapshot trajectory down to a pure `OnHereditaryMSet c`.
public export
onHMSetStates : OnSeq (FuelStepSnapshot cap c) -> OnHereditaryMSet c
onHMSetStates = Stage0.OnSeq.OnMSet.map (.state)

--------------------------------------------------------------------------------
-- 6B. CAUSAL-DIAMOND HORIZON-AWARE EVOLVER & `Dec` RECOGNIZER (`BoundedHorizon T`)
--------------------------------------------------------------------------------

private
halfNatDiamond : Nat -> Nat
halfNatDiamond (S (S k)) = S (halfNatDiamond k)
halfNatDiamond _         = Z

||| Equator yield budget for a symmetric kernel (`kernelNnz` active sites, half-width
||| `kernelRadius`) evolving over horizon `horizonT` to keep the origin exact.
public export
diamondEquatorYield : (horizonT : Nat) -> (kernelNnz : Nat) -> (kernelRadius : Nat) -> Nat
diamondEquatorYield horizonT kernelNnz kernelRadius =
  kernelNnz * (2 * kernelRadius * halfNatDiamond horizonT + 1)

||| Per-tick causal-diamond yield budget at tick `tickS` (`0 <= tickS < horizonT`),
||| shedding modes outside `|x| <= kernelRadius * (horizonT - tickS)` past the midpoint.
public export
diamondTickYield : (horizonT : Nat) -> (kernelNnz : Nat) -> (kernelRadius : Nat) -> (tickS : Nat) -> Nat
diamondTickYield horizonT kernelNnz kernelRadius tickS =
  kernelNnz * (2 * kernelRadius * min tickS (minus horizonT tickS) + 1)

||| Constructive witness that a causal-diamond evolution `(horizonT, kernelNnz, kernelRadius)`
||| fits within `maxPeakYield` at the diamond equator `floor(horizonT / 2)`.
public export
data FitsDiamondBudget : (horizonT : Nat) -> (kernelNnz : Nat) -> (kernelRadius : Nat) -> (maxPeakYield : Nat) -> Type where
  MkFitsDiamondBudget : LTE (diamondEquatorYield horizonT kernelNnz kernelRadius) maxPeakYield
                     -> FitsDiamondBudget horizonT kernelNnz kernelRadius maxPeakYield

||| Total constructive `Dec` recognizer deciding whether a causal diamond horizon fits
||| within `maxPeakYield`.
public export
recognizeDiamondHorizon : (horizonT, kernelNnz, kernelRadius, maxPeakYield : Nat) ->
                          Dec (FitsDiamondBudget horizonT kernelNnz kernelRadius maxPeakYield)
recognizeDiamondHorizon horizonT kernelNnz kernelRadius maxPeakYield =
  case isLTE (diamondEquatorYield horizonT kernelNnz kernelRadius) maxPeakYield of
    Yes ltePrf => Yes (MkFitsDiamondBudget ltePrf)
    No  contra => No (\(MkFitsDiamondBudget ltePrf) => contra ltePrf)

||| Solidified outcome of a finite-horizon causal-diamond or flat-equator evolution.
public export
record CausalDiamondOutcome (horizonT : Nat) (c : Type) where
  constructor MkCausalDiamondOutcome
  finalState     : HereditaryMSet c
  totalUsedYield : Nat
  peakTickYield  : Nat
  finalStats     : SupportStats

private
runHorizonSchedule : MultisetWeight c =>
                     (level : Nat) ->
                     (horizonT : Nat) ->
                     (budFn : Nat -> Nat) ->
                     (seed : HereditaryMSet c) ->
                     (kernel : HereditaryMSet c) ->
                     CausalDiamondOutcome horizonT c
runHorizonSchedule level horizonT budFn seed kernel = go 0 horizonT seed 0 0
  where
    insertTerm : (HereditaryMSet c, c) -> HereditaryMSet c -> HereditaryMSet c
    insertTerm (k, w) (MkHMSet acc) = MkHMSet (addAtKeyBox k w acc)
    stepOnce : Nat -> HereditaryMSet c -> SolidifiedCarrier horizonT (HereditaryMSet c)
    stepOnce yBud st =
      let yf = the (GohFuel horizonT) (MkGohFuel yBud)
      in case level of
           Z          => runDecoupledStream yf (yBud + 64) hyperOpStep insertTerm emptyHMSet (initHyperOpZipState 0 st kernel)
           S innerLvl => runSymmetricRadialConv innerLvl yf (yBud + 64) st kernel
    go : Nat -> Nat -> HereditaryMSet c -> Nat -> Nat -> CausalDiamondOutcome horizonT c
    go _ Z st totY peakY =
      let fStats = case st of MkHMSet b => collectSupportStats b
      in MkCausalDiamondOutcome st totY peakY fStats
    go s (S rem) st totY peakY =
      let yBud  = budFn s
          sol   = stepOnce yBud st
          usedY = minus yBud (gohSteps sol.remainingYield)
      in go (S s) rem sol.carrier (totY + usedY) (max peakY usedY)

||| Evolves `seed` under `kernel` for `horizonT` ticks using the backward light-cone
||| causal-diamond schedule (`diamondTickYield`), recovering the exact origin at `horizonT`
||| while shedding outer modes past the midpoint `s > floor(horizonT / 2)`.
public export
evolveCausalDiamond : MultisetWeight c =>
                      (level : Nat) ->
                      (horizonT : Nat) ->
                      (seed : HereditaryMSet c) ->
                      (kernel : HereditaryMSet c) ->
                      CausalDiamondOutcome horizonT c
evolveCausalDiamond level horizonT seed kernel@(MkHMSet bKer) =
  let kStats = collectSupportStats bKer
      kNnz   = max 1 kStats.nnz
      kRad   = max 1 kStats.maxDeg
  in runHorizonSchedule level horizonT (diamondTickYield horizonT kNnz kRad) seed kernel

||| Evolves `seed` under `kernel` for `horizonT` ticks using a constant flat-equator budget
||| (`diamondEquatorYield`), keeping the origin exact without post-midpoint shedding.
public export
evolveFlatEquator : MultisetWeight c =>
                    (level : Nat) ->
                    (horizonT : Nat) ->
                    (seed : HereditaryMSet c) ->
                    (kernel : HereditaryMSet c) ->
                    CausalDiamondOutcome horizonT c
evolveFlatEquator level horizonT seed kernel@(MkHMSet bKer) =
  let kStats = collectSupportStats bKer
      kNnz   = max 1 kStats.nnz
      kRad   = max 1 kStats.maxDeg
  in runHorizonSchedule level horizonT (\_ => diamondEquatorYield horizonT kNnz kRad) seed kernel

--------------------------------------------------------------------------------
-- 7. PURE QTT 0 `Refl` AUDITS FOR PRIME FUEL SPLITS
--------------------------------------------------------------------------------

||| Audit 1: Goldbach split `2 + 2 = 4` yields `8` GohFuel steps vs. `7` monolithic steps.
public export
0 prfPrimeSum2_2GainsStep :
  ( Stage0.HereditaryMSet.gohSteps (Stage0.OnSeq.OnHereditaryMSet.primeSumGohFuel Stage0.PrimeMultiset.gohPrimeSum2_2)
  , Stage0.HereditaryMSet.gohFuelNat 4
  ) = (8, 7)
prfPrimeSum2_2GainsStep = Refl

||| Audit 2: Goldbach split `3 + 5 = 8` yields `15` GohFuel steps vs. `13` monolithic steps.
public export
0 prfPrimeSum3_5GainsTwoSteps :
  ( Stage0.HereditaryMSet.gohSteps (Stage0.OnSeq.OnHereditaryMSet.primeSumGohFuel Stage0.PrimeMultiset.gohPrimeSum3_5)
  , Stage0.HereditaryMSet.gohFuelNat 8
  ) = (15, 13)
prfPrimeSum3_5GainsTwoSteps = Refl

||| Audit 3: Generalized 13-smooth prime-chunk partition scales cleanly to Primorial 210 (`340 > 316`).
public export
0 prfDecomposedPrime210 :
  Stage0.OnSeq.OnHereditaryMSet.decomposedPrimeFuelNat 210 = 340
prfDecomposedPrime210 = Refl

||| Audit 4: Equator yield for `horizonT = 12` with `[1, 2, 1]` (`nnz=3, rad=1`) equals `39`.
public export
0 prfDiamondEquator12 :
  Stage0.OnSeq.OnHereditaryMSet.diamondEquatorYield 12 3 1 = 39
prfDiamondEquator12 = Refl
