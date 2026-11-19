module Stage1.QuantumManyBodyProbe

import Data.List
import Data.Nat
import Decidable.Equality
import public Stage0.Box
import public Stage0.BoxInt
import public Stage0.SignedFraction
import public Stage1.FuelProbe

%default total

private
iterateN : Nat -> (a -> a) -> a -> a
iterateN Z     _ x = x
iterateN (S k) f x = iterateN k f (f x)

private
powInt : Integer -> Nat -> Integer
powInt _ Z     = 1
powInt b (S k) = b * powInt b k

--------------------------------------------------------------------------------
-- 1. PROBE I: MANY-BODY QUANTUM STATISTICS, RATIONAL BELL/CHSH & U(1) GAUGE
--------------------------------------------------------------------------------

||| Constructive witness that a Gaussian integer `(a, b)` defines a Pythagorean
||| rational phase on the circle of squared radius `rSq` (`a^2 + b^2 = rSq`).
public export
data IsPythagoreanPhase : (a, b, rSq : Integer) -> Type where
  MkPythagoreanPhase : (a * a + b * b = rSq) -> IsPythagoreanPhase a b rSq

||| Total constructive `Dec` recognizer for discrete rational Pythagorean phases.
public export
recognizePythagoreanPhase : (a, b, rSq : Integer) -> Dec (IsPythagoreanPhase a b rSq)
recognizePythagoreanPhase a b rSq =
  case decEq (a * a + b * b) rSq of
    Yes prf   => Yes (MkPythagoreanPhase prf)
    No contra => No (\(MkPythagoreanPhase p) => contra p)

||| Two-particle signed integer state on a 1D chain: `((x1, spin1), (x2, spin2))`
||| where `False = L` and `True = R`. Uses exact Black/Red cancellation.
public export
PairSpinor1D : Type
PairSpinor1D = Box BoxInt ((Integer, Bool), (Integer, Bool))

||| Single 2-particle discrete-time Hadamard walk step applying `[[1, 1], [1, -1]]`
||| and chiral shifts (`L -> x - 1`, `R -> x + 1`) independently to particle 1
||| and then particle 2, preserving particle-exchange symmetry.
public export
stepHadamardPair1D : PairSpinor1D -> PairSpinor1D
stepHadamardPair1D st =
  let mid : PairSpinor1D
      mid = foldBox (\((x1, s1), p2), (MkBoxInt w), acc =>
                      if w == 0
                        then acc
                        else
                          let a1 = addAtKeyBox ((x1 - 1, False), p2) (intToBoxInt w) acc
                              wR = if s1 then negate w else w
                          in addAtKeyBox ((x1 + 1, True), p2) (intToBoxInt wR) a1)
                    (the PairSpinor1D BoxLeaf)
                    st
  in foldBox (\(p1, (x2, s2)), (MkBoxInt w), acc =>
               if w == 0
                 then acc
                 else
                   let a1 = addAtKeyBox (p1, (x2 - 1, False)) (intToBoxInt w) acc
                       wR = if s2 then negate w else w
                   in addAtKeyBox (p1, (x2 + 1, True)) (intToBoxInt wR) a1)
             (the PairSpinor1D BoxLeaf)
             mid

private
record PairAccum where
  constructor MkPairAccum
  totQ2  : Integer
  diagQ2 : Integer
  sameQ2 : Integer

private
record PairStats where
  constructor MkPairStats
  q2       : Integer
  diagPos  : MSetFraction
  sameFull : MSetFraction

private
pairMetrics : PairSpinor1D -> PairStats
pairMetrics st =
  let res = foldBox (\((x1, s1), (x2, s2)), (MkBoxInt w), acc =>
                      let p  = w * w
                          d2 = if x1 == x2 then p else 0
                          s2 = if (x1 == x2) && (s1 == s2) then p else 0
                      in MkPairAccum (acc.totQ2 + p) (acc.diagQ2 + d2) (acc.sameQ2 + s2))
                    (MkPairAccum 0 0 0)
                    st
      den  = integerToNat (max (the Integer 1) res.totQ2)
      diag = reduceMSF (mkMSF (intToBoxInt res.diagQ2) den)
      same = reduceMSF (mkMSF (intToBoxInt res.sameQ2) den)
  in MkPairStats res.totQ2 diag same

private
record HOMStatsEval where
  constructor MkHOMStatsEval
  bosonDiag1    : MSetFraction
  fermionDiag1  : MSetFraction
  distDiag1     : MSetFraction
  bosonDiag6    : MSetFraction
  fermionDiag6  : MSetFraction
  distDiag6     : MSetFraction
  unitary6Ok    : Bool
  dip1Ok        : Bool
  pauliOk       : Bool
  bunching6Ok   : Bool

private
evalHOMStats : HOMStatsEval
evalHOMStats =
  let boson0   = setBox ((the Integer 0, False), (the Integer 0, True)) (intToBoxInt 1)
                   (setBox ((the Integer 0, True), (the Integer 0, False)) (intToBoxInt 1)
                     (the PairSpinor1D BoxLeaf))
      fermion0 = setBox ((the Integer 0, False), (the Integer 0, True)) (intToBoxInt 1)
                   (setBox ((the Integer 0, True), (the Integer 0, False)) (intToBoxInt (-1))
                     (the PairSpinor1D BoxLeaf))
      dist0    = setBox ((the Integer 0, False), (the Integer 0, True)) (intToBoxInt 1)
                   (the PairSpinor1D BoxLeaf)

      b1 = stepHadamardPair1D boson0
      b2 = stepHadamardPair1D b1
      b4 = iterateN 2 stepHadamardPair1D b2
      b6 = iterateN 2 stepHadamardPair1D b4

      f1 = stepHadamardPair1D fermion0
      f2 = stepHadamardPair1D f1
      f4 = iterateN 2 stepHadamardPair1D f2
      f6 = iterateN 2 stepHadamardPair1D f4

      d1 = stepHadamardPair1D dist0
      d6 = iterateN 5 stepHadamardPair1D d1

      sb1 = pairMetrics b1
      sb6 = pairMetrics b6
      sf1 = pairMetrics f1
      sf2 = pairMetrics f2
      sf4 = pairMetrics f4
      sf6 = pairMetrics f6
      sd1 = pairMetrics d1
      sd6 = pairMetrics d6

      uniOk   = andAll [sb6.q2 == 8192, sf6.q2 == 8192, sd6.q2 == 4096]
      dipOk   = andAll [ sb1.diagPos == oneMSF
                       , sf1.diagPos == zeroMSF
                       , sd1.diagPos == mkMSF 1 2
                       ]
      pauliOk = andAll [ sf1.sameFull == zeroMSF
                       , sf2.sameFull == zeroMSF
                       , sf4.sameFull == zeroMSF
                       , sf6.sameFull == zeroMSF
                       ]
      b6Ok    = andAll [ msfLT sf6.diagPos sd6.diagPos
                       , msfLT sd6.diagPos sb6.diagPos
                       ]
  in MkHOMStatsEval sb1.diagPos sf1.diagPos sd1.diagPos sb6.diagPos sf6.diagPos sd6.diagPos
       uniOk dipOk pauliOk b6Ok

||| Exact rational Born-rule spin correlator `P(same) - P(diff)` on the
||| entangled integer Bell state `|Phi+> = |00> + |11>` under orthogonal bases
||| `R(cA, sA)` and `R(cB, sB)`.
public export
chshCorrPhiPlus : (cA, sA, cB, sB : Integer) -> MSetFraction
chshCorrPhiPlus cA sA cB sB =
  let a00  = cA * cB + sA * sB
      a01  = negate (cA * sB) + sA * cB
      a10  = negate (sA * cB) + cA * sB
      a11  = sA * sB + cA * cB
      same = a00 * a00 + a11 * a11
      diff = a01 * a01 + a10 * a10
  in reduceMSF (mkMSF (intToBoxInt (same - diff)) (integerToNat (max (the Integer 1) (same + diff))))

||| Exact rational Born-rule spin correlator on the separable product state `|00>`.
public export
chshCorrSep00 : (cA, sA, cB, sB : Integer) -> MSetFraction
chshCorrSep00 cA sA cB sB =
  let a00  = cA * cB
      a01  = negate (cA * sB)
      a10  = negate (sA * cB)
      a11  = sA * sB
      same = a00 * a00 + a11 * a11
      diff = a01 * a01 + a10 * a10
  in reduceMSF (mkMSF (intToBoxInt (same - diff)) (integerToNat (max (the Integer 1) (same + diff))))

private
record CHSHEval where
  constructor MkCHSHEval
  sEntangled : MSetFraction
  sSeparable : MSetFraction
  chshOk     : Bool

private
evalCHSH : CHSHEval
evalCHSH =
  let eAB   = chshCorrPhiPlus 1 0 12 5
      eABp  = chshCorrPhiPlus 1 0 12 (-5)
      eApB  = chshCorrPhiPlus 1 1 12 5
      eApBp = chshCorrPhiPlus 1 1 12 (-5)
      sEnt  = reduceMSF (subMSF (addMSF (addMSF eAB eABp) eApB) eApBp)

      sAB   = chshCorrSep00 1 0 12 5
      sABp  = chshCorrSep00 1 0 12 (-5)
      sApB  = chshCorrSep00 1 1 12 5
      sApBp = chshCorrSep00 1 1 12 (-5)
      sSep  = reduceMSF (subMSF (addMSF (addMSF sAB sABp) sApB) sApBp)

      ok = andAll [ sEnt == mkMSF 478 169
                  , msfGT sEnt (mkMSF 2 1)
                  , sSep == mkMSF 238 169
                  , msfLT sSep (mkMSF 2 1)
                  ]
  in MkCHSHEval sEnt sSep ok

||| Exact Gaussian integer `(re, im) in Z[i]` for discrete `U(1)` gauge phases.
public export
GaussInt : Type
GaussInt = (Integer, Integer)

private
gMul : GaussInt -> GaussInt -> GaussInt
gMul (a, b) (c, d) = (a * c - b * d, a * d + b * c)

private
gAdd : GaussInt -> GaussInt -> GaussInt
gAdd (a, b) (c, d) = (a + c, b + d)

private
gSub : GaussInt -> GaussInt -> GaussInt
gSub (a, b) (c, d) = (a - c, b - d)

private
gConj : GaussInt -> GaussInt
gConj (a, b) = (a, negate b)

private
gNorm : GaussInt -> Integer
gNorm (a, b) = a * a + b * b

||| Evaluates destructive interference probabilities `(P+, P-)` on a closed
||| Aharonov-Bohm plaquette threaded by Gaussian-integer flux `flux` (scale 5)
||| under independent local vertex gauge transformations `g1`, `g3`.
public export
evalABPlaquette : (flux, g1, g3 : GaussInt) -> (MSetFraction, MSetFraction)
evalABPlaquette flux g1 g3 =
  let g1n    = gNorm g1
      g3n    = gNorm g3
      top0   = gMul (gMul flux (gConj g1)) g1
      top    = (fst top0 * g3n, snd top0 * g3n)
      bot0   = gMul (gMul (5, 0) (gConj g3)) g3
      bot    = (fst bot0 * g1n, snd bot0 * g1n)
      pPlus  = gNorm (gAdd top bot)
      pMinus = gNorm (gSub top bot)
      den    = integerToNat (max (the Integer 1) (pPlus + pMinus))
  in ( reduceMSF (mkMSF (intToBoxInt pPlus) den)
     , reduceMSF (mkMSF (intToBoxInt pMinus) den)
     )

private
record ABGaugeEval where
  constructor MkABGaugeEval
  probPlusFlux0   : MSetFraction
  probPlusFlux345 : MSetFraction
  probPlusFluxPi2 : MSetFraction
  probPlusFluxPi  : MSetFraction
  gaugeInvOk      : Bool
  phaseDecOk      : Bool

private
evalABGauge : ABGaugeEval
evalABGauge =
  let idG = (the Integer 1, the Integer 0)
      g1  = (the Integer 3, the Integer 4)
      g3  = (the Integer 12, the Integer 5)

      (p0A, p0B) = evalABPlaquette (5, 0) idG idG
      (g0A, g0B) = evalABPlaquette (5, 0) g1 g3

      (p3A, p3B) = evalABPlaquette (3, 4) idG idG
      (g3A, g3B) = evalABPlaquette (3, 4) g1 g3

      (p9A, p9B) = evalABPlaquette (0, 5) idG idG
      (g9A, g9B) = evalABPlaquette (0, 5) g1 g3

      (pPA, pPB) = evalABPlaquette (-5, 0) idG idG
      (gPA, gPB) = evalABPlaquette (-5, 0) g1 g3

      gOk = andAll [ p0A == oneMSF,   p0B == zeroMSF,  p0A == g0A, p0B == g0B
                   , p3A == mkMSF 4 5, p3B == mkMSF 1 5, p3A == g3A, p3B == g3B
                   , p9A == mkMSF 1 2, p9B == mkMSF 1 2, p9A == g9A, p9B == g9B
                   , pPA == zeroMSF,  pPB == oneMSF,   pPA == gPA, pPB == gPB
                   ]

      decOk = andAll
                [ case recognizePythagoreanPhase 3 4 25 of
                    Yes (MkPythagoreanPhase _) => True
                    No  _                      => False
                , case recognizePythagoreanPhase 12 5 169 of
                    Yes (MkPythagoreanPhase _) => True
                    No  _                      => False
                , case recognizePythagoreanPhase 1 1 2 of
                    Yes (MkPythagoreanPhase _) => True
                    No  _                      => False
                , case recognizePythagoreanPhase 3 3 25 of
                    Yes _ => False
                    No  _ => True
                ]
  in MkABGaugeEval p0A p3A p9A pPA gOk decOk

public export
record ManyBodyGaugeReport where
  constructor MkManyBodyGaugeReport
  homBosonDiag1      : MSetFraction
  homFermionDiag1    : MSetFraction
  homDistDiag1       : MSetFraction
  homBosonDiag6      : MSetFraction
  homFermionDiag6    : MSetFraction
  homDistDiag6       : MSetFraction
  homPauliOk         : Bool
  chshEntangled      : MSetFraction
  chshSeparable      : MSetFraction
  chshOk             : Bool
  abFlux0Plus        : MSetFraction
  abFlux345Plus      : MSetFraction
  abFluxPi2Plus      : MSetFraction
  abFluxPiPlus       : MSetFraction
  abGaugeInvOk       : Bool
  phaseDecOk         : Bool
  passesManyBody     : Bool

||| Probe I: Tests two-particle Hong-Ou-Mandel bosonic bunching vs. fermionic
||| Pauli exclusion (`PairSpinor1D`), exact Pythagorean Bell/CHSH violation (`478/169 > 2`),
||| and local gauge-invariant Aharonov-Bohm interference over Gaussian integers `Z[i]`.
export
probeManyBodyAndGauge : ManyBodyGaugeReport
probeManyBodyAndGauge =
  let hom = evalHOMStats
      ch  = evalCHSH
      ab  = evalABGauge
      homOk = andAll [hom.unitary6Ok, hom.dip1Ok, hom.pauliOk, hom.bunching6Ok]
      passOk = andAll [homOk, ch.chshOk, ab.gaugeInvOk, ab.phaseDecOk]
  in MkManyBodyGaugeReport
       hom.bosonDiag1 hom.fermionDiag1 hom.distDiag1
       hom.bosonDiag6 hom.fermionDiag6 hom.distDiag6
       homOk
       ch.sEntangled ch.sSeparable ch.chshOk
       ab.probPlusFlux0 ab.probPlusFlux345 ab.probPlusFluxPi2 ab.probPlusFluxPi
       ab.gaugeInvOk ab.phaseDecOk passOk

--------------------------------------------------------------------------------
-- 2. PROBE J: 2+1D SPLIT-STEP DIRAC WALK & ROTATIONAL ISOTROPY (Z^2 vs A_2)
--------------------------------------------------------------------------------

||| Two-component signed integer spinor over a 2D integer grid `(x, y)`.
public export
Spinor2D : Type
Spinor2D = (Box BoxInt (Integer, Integer), Box BoxInt (Integer, Integer))

||| Split-step 2+1D Dirac walk (`U = S_y * C * S_x * C`), scaling `Q2` by `(a^2 + c^2)^2` per tick.
public export
stepDirac2D : (a, b, c, d : Integer) -> Spinor2D -> Spinor2D
stepDirac2D a b c d (psi0, psi1) =
  let stepAxis : Integer -> Integer -> Spinor2D -> Spinor2D
      stepAxis dx dy (s0, s1) =
        let (m0A, m1A) =
              foldBox (\(x, y), (MkBoxInt w), (acc0, acc1) =>
                        if w == 0
                          then (acc0, acc1)
                          else ( addAtKeyBox (x - dx, y - dy) (intToBoxInt (a * w)) acc0
                               , addAtKeyBox (x + dx, y + dy) (intToBoxInt (c * w)) acc1
                               ))
                      (the (Box BoxInt (Integer, Integer)) BoxLeaf, the (Box BoxInt (Integer, Integer)) BoxLeaf)
                      s0
        in foldBox (\(x, y), (MkBoxInt w), (acc0, acc1) =>
                     if w == 0
                       then (acc0, acc1)
                       else ( addAtKeyBox (x - dx, y - dy) (intToBoxInt (b * w)) acc0
                            , addAtKeyBox (x + dx, y + dy) (intToBoxInt (d * w)) acc1
                            ))
                   (m0A, m1A)
                   s1
  in stepAxis 0 1 (stepAxis 1 0 (psi0, psi1))

private
record Accum2D where
  constructor MkAccum2D
  m0 : Integer
  m2 : Integer
  m4 : Integer
  q4 : Integer

private
record Spinor2DStats where
  constructor MkSpinor2DStats
  q2      : Integer
  var     : MSetFraction
  anisoA4 : MSetFraction

private
moments2DSpinor : Spinor2D -> Spinor2DStats
moments2DSpinor (psi0, psi1) =
  let addPt : (Integer, Integer) -> BoxInt -> Accum2D -> Accum2D
      addPt (x, y) (MkBoxInt w) acc =
        let p  = w * w
            x2 = x * x
            y2 = y * y
            r2 = x2 + y2
            a4 = x2 * x2 + y2 * y2 - 6 * x2 * y2
        in MkAccum2D (acc.m0 + p) (acc.m2 + p * r2) (acc.m4 + p * r2 * r2) (acc.q4 + p * a4)
      s1   = foldBox addPt (MkAccum2D 0 0 0 0) psi0
      s2   = foldBox addPt s1 psi1
      var  = reduceMSF (mkMSF (intToBoxInt s2.m2) (integerToNat (max (the Integer 1) s2.m0)))
      a4   = reduceMSF (mkMSF (intToBoxInt s2.q4) (integerToNat (max (the Integer 1) s2.m4)))
  in MkSpinor2DStats s2.m0 var a4

private
stepDiffZ2 : Box BoxInt (Integer, Integer) -> Box BoxInt (Integer, Integer)
stepDiffZ2 =
  foldBox (\(x, y), (MkBoxInt w), acc =>
            if w == 0
              then acc
              else
                let a0 = addAtKeyBox (x, y)     (intToBoxInt (4 * w)) acc
                    a1 = addAtKeyBox (x + 1, y) (intToBoxInt w) a0
                    a2 = addAtKeyBox (x - 1, y) (intToBoxInt w) a1
                    a3 = addAtKeyBox (x, y + 1) (intToBoxInt w) a2
                in addAtKeyBox (x, y - 1) (intToBoxInt w) a3)
          BoxLeaf

private
stepDiffA2 : Box BoxInt (Integer, Integer) -> Box BoxInt (Integer, Integer)
stepDiffA2 =
  foldBox (\(u, v), (MkBoxInt w), acc =>
            if w == 0
              then acc
              else
                let a0 = addAtKeyBox (u, v)         (intToBoxInt (2 * w)) acc
                    a1 = addAtKeyBox (u + 1, v)     (intToBoxInt w) a0
                    a2 = addAtKeyBox (u - 1, v)     (intToBoxInt w) a1
                    a3 = addAtKeyBox (u, v + 1)     (intToBoxInt w) a2
                    a4 = addAtKeyBox (u, v - 1)     (intToBoxInt w) a3
                    a5 = addAtKeyBox (u + 1, v - 1) (intToBoxInt w) a4
                in addAtKeyBox (u - 1, v + 1) (intToBoxInt w) a5)
          BoxLeaf

private
record AccumDiff2D where
  constructor MkAccumDiff2D
  num4 : Integer
  den4 : Integer

private
quadA4Z2 : Box BoxInt (Integer, Integer) -> MSetFraction
quadA4Z2 b =
  let res = foldBox (\(x, y), (MkBoxInt w), acc =>
                      let x2 = x * x
                          y2 = y * y
                          r2 = x2 + y2
                          q4 = x2 * x2 + y2 * y2 - 6 * x2 * y2
                      in MkAccumDiff2D (acc.num4 + w * q4) (acc.den4 + w * r2 * r2))
                    (MkAccumDiff2D 0 0)
                    b
  in reduceMSF (mkMSF (intToBoxInt res.num4) (integerToNat (max (the Integer 1) res.den4)))

private
quadA4A2 : Box BoxInt (Integer, Integer) -> MSetFraction
quadA4A2 b =
  let res = foldBox (\(u, v), (MkBoxInt w), acc =>
                      let x  = 2 * u + v
                          x2 = x * x
                          v2 = v * v
                          q4 = x2 * x2 + 9 * v2 * v2 - 18 * x2 * v2
                          r2 = u * u + u * v + v2
                      in MkAccumDiff2D (acc.num4 + w * q4) (acc.den4 + 16 * w * r2 * r2))
                    (MkAccumDiff2D 0 0)
                    b
  in reduceMSF (mkMSF (intToBoxInt res.num4) (integerToNat (max (the Integer 1) res.den4)))

private
record Dirac2DEval where
  constructor MkDirac2DEval
  hadVar8    : MSetFraction
  hadVRat84  : MSetFraction
  hadA4_8    : MSetFraction
  heavyVar8  : MSetFraction
  heavyVRat84 : MSetFraction
  heavyA4_8  : MSetFraction
  dirac2DOk  : Bool

private
evalDirac2D : Dirac2DEval
evalDirac2D =
  let s0 = ( setBox (the (Integer, Integer) (0, 0)) (intToBoxInt 1) BoxLeaf
           , setBox (the (Integer, Integer) (0, 0)) (intToBoxInt 1) BoxLeaf
           )
      h4 = iterateN 4 (stepDirac2D 1 1 1 (-1)) s0
      h8 = iterateN 4 (stepDirac2D 1 1 1 (-1)) h4
      sh4 = moments2DSpinor h4
      sh8 = moments2DSpinor h8
      hVR = reduceMSF (divMSF sh8.var sh4.var)

      d4 = iterateN 4 (stepDirac2D 3 4 4 (-3)) s0
      d8 = iterateN 4 (stepDirac2D 3 4 4 (-3)) d4
      sd4 = moments2DSpinor d4
      sd8 = moments2DSpinor d8
      dVR = reduceMSF (divMSF sd8.var sd4.var)

      ok = andAll [ sh8.q2 == 2 * powInt 4 8
                  , sd8.q2 == 2 * powInt 625 8
                  , msfGT hVR (mkMSF 35 10)
                  , msfGT dVR (mkMSF 35 10)
                  , msfGT sh8.anisoA4 (mkMSF 25 100)
                  , msfGT sd8.anisoA4 (mkMSF (-1) 100)
                  , msfLT sd8.anisoA4 (mkMSF 1 100)
                  ]
  in MkDirac2DEval sh8.var hVR sh8.anisoA4 sd8.var dVR sd8.anisoA4 ok

private
record DiffIsoEval where
  constructor MkDiffIsoEval
  z2A4_1 : MSetFraction
  z2A4_4 : MSetFraction
  z2A4_8 : MSetFraction
  a2A4_1 : MSetFraction
  a2A4_4 : MSetFraction
  a2A4_8 : MSetFraction
  isoOk  : Bool

private
evalDiffIsotropy : DiffIsoEval
evalDiffIsotropy =
  let init = setBox (the (Integer, Integer) (0, 0)) (intToBoxInt 1) BoxLeaf
      z1 = stepDiffZ2 init
      z2 = stepDiffZ2 z1
      z4 = iterateN 2 stepDiffZ2 z2
      z8 = iterateN 4 stepDiffZ2 z4

      a1 = stepDiffA2 init
      a2 = stepDiffA2 a1
      a4 = iterateN 2 stepDiffA2 a2
      a8 = iterateN 4 stepDiffA2 a4

      qz1 = quadA4Z2 z1
      qz2 = quadA4Z2 z2
      qz4 = quadA4Z2 z4
      qz8 = quadA4Z2 z8

      qa1 = quadA4A2 a1
      qa2 = quadA4A2 a2
      qa4 = quadA4A2 a4
      qa8 = quadA4A2 a8

      ok = andAll [ qz1 == oneMSF, qz2 == mkMSF 1 2, qz4 == mkMSF 1 4, qz8 == mkMSF 1 8
                  , qa1 == zeroMSF, qa2 == zeroMSF, qa4 == zeroMSF, qa8 == zeroMSF
                  ]
  in MkDiffIsoEval qz1 qz4 qz8 qa1 qa4 qa8 ok

public export
record Isotropy2DReport where
  constructor MkIsotropy2DReport
  had2DVar8        : MSetFraction
  had2DVRat84      : MSetFraction
  had2DA4_8        : MSetFraction
  heavy2DVar8      : MSetFraction
  heavy2DVRat84    : MSetFraction
  heavy2DA4_8      : MSetFraction
  z2A4_1           : MSetFraction
  z2A4_4           : MSetFraction
  z2A4_8           : MSetFraction
  a2A4_1           : MSetFraction
  a2A4_4           : MSetFraction
  a2A4_8           : MSetFraction
  passesIsotropy2D : Bool

||| Probe J: Tests dynamical rotational/quadrupole isotropy `A_4` across a 2+1D
||| split-step Hadamard vs. 3-4-5 Dirac quantum walk and compares Square `Z^2`
||| (`A_4 = 1/t`) vs. Hexagonal `A_2` (`A_4 = 0` identically) lattice diffusion.
export
probeDirac2DAndIsotropy : Isotropy2DReport
probeDirac2DAndIsotropy =
  let d = evalDirac2D
      i = evalDiffIsotropy
      ok = andAll [d.dirac2DOk, i.isoOk]
  in MkIsotropy2DReport
       d.hadVar8 d.hadVRat84 d.hadA4_8
       d.heavyVar8 d.heavyVRat84 d.heavyA4_8
       i.z2A4_1 i.z2A4_4 i.z2A4_8
       i.a2A4_1 i.a2A4_4 i.a2A4_8
       ok

--------------------------------------------------------------------------------
-- 3. COMPILE-TIME QTT 0 `Refl` AUDITS
--------------------------------------------------------------------------------

||| Audit 1: Exact rational Bell/CHSH violation (`478/169 > 2`).
public export
0 prfChshBellViolation : (478 > 2 * 169) = True
prfChshBellViolation = Refl

||| Audit 2: Exact rational CHSH compatibility with Tsirelson bound (`(478/169)^2 < 8`).
public export
0 prfChshTsirelsonBound : (478 * 478 < 8 * 169 * 169) = True
prfChshTsirelsonBound = Refl

||| Hexagonal `A_2` tick-1 quadrupole anisotropy sum over the 6 unit vectors.
public export
hexA2QuadTick1 : Integer
hexA2QuadTick1 =
  let term : (Integer, Integer) -> Integer
      term (u, v) =
        let x  = 2 * u + v
            x2 = x * x
            v2 = v * v
        in x2 * x2 + 9 * v2 * v2 - 18 * x2 * v2
  in sum (map term [(1, 0), (-1, 0), (0, 1), (0, -1), (1, -1), (-1, 1)])

||| Audit 3: Exact cancellation of rank-4 quadrupole anisotropy on the `A_2` lattice.
public export
0 prfHexA2IsotropyTick1 : Stage1.QuantumManyBodyProbe.hexA2QuadTick1 = 0
prfHexA2IsotropyTick1 = Refl
