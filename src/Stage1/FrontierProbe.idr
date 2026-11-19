module Stage1.FrontierProbe

import Data.Nat
import Decidable.Equality
import public Stage0.Box
import public Stage0.BoxInt
import public Stage0.SignedFraction
import public Stage0.HereditaryMSet
import public Stage1.Views
import public Stage1.Bridge.LaurentAntiMSetBridge
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
-- 1. WAVE 1 (PROBE F): SIGNED 1+1D HADAMARD QUANTUM & MASSIVE DIRAC WALKS
--------------------------------------------------------------------------------

||| Exact integer 2x2 scaled unitary matrix witness:
||| columns `(a, c)` and `(b, d)` are orthogonal with equal quadrance `scaleSq`.
public export
data IsIntegerUnitary2x2 : (a, b, c, d, scaleSq : Integer) -> Type where
  MkIntegerUnitary2x2 : (a * a + c * c = scaleSq)
                     -> (b * b + d * d = scaleSq)
                     -> (a * b + c * d = 0)
                     -> IsIntegerUnitary2x2 a b c d scaleSq

||| Total constructive `Dec` recognizer for scaled 2x2 integer unitary coins.
public export
recognizeIntegerUnitary2x2 : (a, b, c, d, scaleSq : Integer) ->
                             Dec (IsIntegerUnitary2x2 a b c d scaleSq)
recognizeIntegerUnitary2x2 a b c d scaleSq =
  case decEq (a * a + c * c) scaleSq of
    No c1 => No (\(MkIntegerUnitary2x2 p1 _ _) => c1 p1)
    Yes p1 =>
      case decEq (b * b + d * d) scaleSq of
        No c2 => No (\(MkIntegerUnitary2x2 _ p2 _) => c2 p2)
        Yes p2 =>
          case decEq (a * b + c * d) 0 of
            No c3 => No (\(MkIntegerUnitary2x2 _ _ p3) => c3 p3)
            Yes p3 => Yes (MkIntegerUnitary2x2 p1 p2 p3)

||| Two-component signed integer spinor `(psiL, psiR)` over 1D discrete space.
public export
Spinor1D : Type
Spinor1D = (Box BoxInt Integer, Box BoxInt Integer)

||| Single discrete-time 1+1D coined walk step with coin `[[a, b], [c, d]]`,
||| followed by chiral shifts `L -> x - 1`, `R -> x + 1`.
||| `addAtKeyBox` performs exact Black/Red zero-pruning annihilation automatically.
public export
stepCoinWalk1D : (a, b, c, d : Integer) -> Spinor1D -> Spinor1D
stepCoinWalk1D a b c d (psiL, psiR) =
  let (l1, r1) = foldBox (\x, (MkBoxInt w), (accL, accR) =>
                           if w == 0
                             then (accL, accR)
                             else ( addAtKeyBox (x - 1) (intToBoxInt (a * w)) accL
                                  , addAtKeyBox (x + 1) (intToBoxInt (c * w)) accR
                                  ))
                         (BoxLeaf, BoxLeaf)
                         psiL
  in foldBox (\x, (MkBoxInt w), (accL, accR) =>
               if w == 0
                 then (accL, accR)
                 else ( addAtKeyBox (x - 1) (intToBoxInt (b * w)) accL
                      , addAtKeyBox (x + 1) (intToBoxInt (d * w)) accR
                      ))
             (l1, r1)
             psiR

||| Massless Hadamard quantum walk step (`[[1, 1], [1, -1]]`, `Q2 * 2` per tick, `v_max = 1/sqrt(2)`).
public export
stepHadamard1D : Spinor1D -> Spinor1D
stepHadamard1D = stepCoinWalk1D 1 1 1 (-1)

||| Heavy massive Pythagorean 3-4-5 Dirac walk step (`[[3, 4], [4, -3]]`, `Q2 * 25` per tick, `m_eff = 4/5`, `v_max = 3/5`).
public export
stepDiracHeavy345 : Spinor1D -> Spinor1D
stepDiracHeavy345 = stepCoinWalk1D 3 4 4 (-3)

||| Light massive Pythagorean 3-4-5 Dirac walk step (`[[4, 3], [3, -4]]`, `Q2 * 25` per tick, `m_eff = 3/5`, `v_max = 4/5`).
public export
stepDiracLight345 : Spinor1D -> Spinor1D
stepDiracLight345 = stepCoinWalk1D 4 3 3 (-4)

||| Canonical massive Pythagorean 3-4-5 Dirac walk step (alias for `stepDiracHeavy345`).
public export
stepDirac345 : Spinor1D -> Spinor1D
stepDirac345 = stepDiracHeavy345

private
boxQ2 : Box BoxInt Integer -> Integer
boxQ2 = foldBox (\_, (MkBoxInt w), acc => acc + w * w) (the Integer 0)

||| Total Euclidean L2 quadrance `sum_x (psiL(x)^2 + psiR(x)^2)` of a 1D spinor.
public export
spinorQ2 : Spinor1D -> Integer
spinorQ2 (psiL, psiR) = boxQ2 psiL + boxQ2 psiR

||| Total L1 amplitude sum `sum_x (|psiL(x)| + |psiR(x)|)` of a 1D spinor.
public export
spinorL1 : Spinor1D -> Integer
spinorL1 (psiL, psiR) =
  let l1 = foldBox (\_, (MkBoxInt w), acc => acc + abs w) (the Integer 0) psiL
      r1 = foldBox (\_, (MkBoxInt w), acc => acc + abs w) (the Integer 0) psiR
  in l1 + r1

||| Net signed sum `sum_x (psiL(x) + psiR(x))` of a 1D spinor.
public export
spinorSignedSum : Spinor1D -> Integer
spinorSignedSum (psiL, psiR) =
  let sL = foldBox (\_, (MkBoxInt w), acc => acc + w) (the Integer 0) psiL
      sR = foldBox (\_, (MkBoxInt w), acc => acc + w) (the Integer 0) psiR
  in sL + sR

||| Signed chirality polarization `(||psiR||_2^2 - ||psiL||_2^2) / Q2` as an exact `MSetFraction`.
public export
spinorChirality : Spinor1D -> MSetFraction
spinorChirality (psiL, psiR) =
  let qL = boxQ2 psiL
      qR = boxQ2 psiR
  in reduceMSF (mkMSF (intToBoxInt (qR - qL)) (integerToNat (max (the Integer 1) (qR + qL))))

||| Exact quantum probability variance `<x^2>` and kurtosis `<x^4> / <x^2>^2`
||| under the L2 amplitude-squared measure `wL(x)^2 + wR(x)^2`.
public export
spinorVarianceAndKurtosis : Spinor1D -> (MSetFraction, MSetFraction)
spinorVarianceAndKurtosis (psiL, psiR) =
  let addMoms : Integer -> BoxInt -> (Integer, (Integer, Integer)) -> (Integer, (Integer, Integer))
      addMoms x (MkBoxInt w) (a0, (a2, a4)) =
        let p  = w * w
            x2 = x * x
        in (a0 + p, (a2 + p * x2, a4 + p * x2 * x2))
      s1   = foldBox addMoms (the Integer 0, (the Integer 0, the Integer 0)) psiL
      s2   = foldBox addMoms s1 psiR
      m0   = fst s2
      m2   = fst (snd s2)
      m4   = snd (snd s2)
      var  = reduceMSF (mkMSF (intToBoxInt m2) (integerToNat (max (the Integer 1) m0)))
      kurt = reduceMSF (mkMSF (intToBoxInt (m4 * m0)) (integerToNat (max (the Integer 1) (m2 * m2))))
  in (var, kurt)

||| Embeds a 1D `Box BoxInt Integer` into a scalar Laurent `PureMultiset` for `DualChannelView`.
public export
box1DToPureMSet : Box BoxInt Integer -> PureMultiset
box1DToPureMSet b =
  MkHMSet (foldBox (\x, w, acc => addAtKeyBox (signedKeyM x) w acc) BoxLeaf b)

public export
record QuantumDiracReport where
  constructor MkQuantumDiracReport
  hadQ2_16             : Integer
  hadExactUnitary      : Bool
  hadL1_16             : Integer
  hadSignedSum16       : Integer
  hadInterferenceOk    : Bool
  hadVarRatio16        : MSetFraction
  hadKurt16            : MSetFraction
  ballisticOk          : Bool
  diracExactUnitary    : Bool
  diracChirality1      : MSetFraction
  diracChirality2      : MSetFraction
  diracChirality3      : MSetFraction
  diracChirality4      : MSetFraction
  var12Heavy           : MSetFraction
  var12Hadamard        : MSetFraction
  var12Light           : MSetFraction
  zitterbewegungOk     : Bool
  subLightMassOk       : Bool
  coinDecOk            : Bool
  passesQuantumProbe   : Bool

private
record DiracEvalMetrics where
  constructor MkDiracEvalMetrics
  q12HeavyOk : Bool
  q12LightOk : Bool
  c1         : MSetFraction
  c2         : MSetFraction
  c3         : MSetFraction
  c4         : MSetFraction
  var12Heavy : MSetFraction
  var12Light : MSetFraction

private
evalDiracMetrics : DiracEvalMetrics
evalDiracMetrics =
  let d0     = (setBox (the Integer 0) (intToBoxInt 1) BoxLeaf, the (Box BoxInt Integer) BoxLeaf)
      d1     = stepDiracHeavy345 d0
      d2     = stepDiracHeavy345 d1
      d3     = stepDiracHeavy345 d2
      d4     = stepDiracHeavy345 d3
      d12H   = iterateN 8 stepDiracHeavy345 d4
      q12HOk = (spinorQ2 d12H == powInt 25 12)
      c1     = spinorChirality d1
      c2     = spinorChirality d2
      c3     = spinorChirality d3
      c4     = spinorChirality d4
      (v12H, _) = spinorVarianceAndKurtosis d12H

      l12    = iterateN 12 stepDiracLight345 d0
      q12LOk = (spinorQ2 l12 == powInt 25 12)
      (v12L, _) = spinorVarianceAndKurtosis l12
  in MkDiracEvalMetrics q12HOk q12LOk c1 c2 c3 c4 v12H v12L

||| Probe F: Tests exact L2 unitarity, destructive Black/Red interference (`DualChannelView`),
||| ballistic spreading (`z ~ 1.0`, bimodal kurtosis `< 2`) on the 1+1D Hadamard walk, and
||| Zitterbewegung chirality oscillation + relativistic mass-dispersion ordering across the
||| heavy (`m_eff=4/5`, `v_max=3/5`) and light (`m_eff=3/5`, `v_max=4/5`) 3-4-5 Dirac walks.
export
probeQuantumDiracWalk : QuantumDiracReport
probeQuantumDiracWalk =
  let h0  = (setBox (the Integer 0) (intToBoxInt 1) BoxLeaf, setBox (the Integer 0) (intToBoxInt 1) BoxLeaf)
      h8  = iterateN 8 stepHadamard1D h0
      h12 = iterateN 4 stepHadamard1D h8
      h16 = iterateN 4 stepHadamard1D h12

      q2H16    = spinorQ2 h16
      expQ2    = 2 * powInt 2 16
      hUniOk   = (q2H16 == expQ2)
      l1H16    = spinorL1 h16
      sSum16   = spinorSignedSum h16
      dcView   = splitChannels (box1DToPureMSet (fst h16))
      interfOk = andAll [ l1H16 < q2H16
                        , l1H16 == 1484
                        , sSum16 == 512
                        , dcView.posChannel /= emptyHMSet
                        , dcView.negChannel /= emptyHMSet
                        ]

      (var8, _)      = spinorVarianceAndKurtosis h8
      (var12H, _)    = spinorVarianceAndKurtosis h12
      (var16, kH16)  = spinorVarianceAndKurtosis h16
      vRat           = reduceMSF (divMSF var16 var8)
      ballOk         = andAll [ msfGT vRat (mkMSF 38 10)
                              , msfLT kH16 (mkMSF 16 10)
                              ]

      dMetrics = evalDiracMetrics
      dUniOk   = andAll [dMetrics.q12HeavyOk, dMetrics.q12LightOk]
      zitterOk = andAll [ msfGT dMetrics.c1 zeroMSF
                        , msfLT dMetrics.c2 zeroMSF
                        , msfLT dMetrics.c3 dMetrics.c2
                        , msfGT dMetrics.c4 dMetrics.c3
                        ]
      subLtOk  = andAll [ msfLT dMetrics.var12Heavy var12H
                        , msfLT var12H dMetrics.var12Light
                        , msfLT dMetrics.var12Light (mkMSF 144 1)
                        ]

      coinOk = andAll
                 [ case recognizeIntegerUnitary2x2 1 1 1 (-1) 2 of
                     Yes (MkIntegerUnitary2x2 _ _ _) => True
                     No  _                           => False
                 , case recognizeIntegerUnitary2x2 3 4 4 (-3) 25 of
                     Yes (MkIntegerUnitary2x2 _ _ _) => True
                     No  _                           => False
                 , case recognizeIntegerUnitary2x2 4 3 3 (-4) 25 of
                     Yes (MkIntegerUnitary2x2 _ _ _) => True
                     No  _                           => False
                 , case recognizeIntegerUnitary2x2 1 1 1 1 2 of
                     Yes _ => False
                     No  _ => True
                 ]

      passOk = andAll [hUniOk, interfOk, ballOk, dUniOk, zitterOk, subLtOk, coinOk]
  in MkQuantumDiracReport q2H16 hUniOk l1H16 sSum16 interfOk vRat kH16 ballOk
       dUniOk dMetrics.c1 dMetrics.c2 dMetrics.c3 dMetrics.c4
       dMetrics.var12Heavy var12H dMetrics.var12Light
       zitterOk subLtOk coinOk passOk

--------------------------------------------------------------------------------
-- 2. WAVE 2 (PROBE G): 3+1D INTEGER LORENTZ GROUP SO+(3,1; Z) & MANDELSTAM
--------------------------------------------------------------------------------

public export
Vec4I : Type
Vec4I = (Integer, Integer, Integer, Integer)

public export
Mat4I : Type
Mat4I = (Vec4I, Vec4I, Vec4I, Vec4I)

||| Red Minkowski bilinear form `t1*t2 - x1*x2 - y1*y2 - z1*z2` in 3+1D.
public export
redDot4 : Vec4I -> Vec4I -> Integer
redDot4 (t1, x1, y1, z1) (t2, x2, y2, z2) =
  t1 * t2 - x1 * x2 - y1 * y2 - z1 * z2

||| Blue Euclidean spatial quadrance `x^2 + y^2 + z^2` in 3+1D.
public export
blueQuad4 : Vec4I -> Integer
blueQuad4 (_, x, y, z) = x * x + y * y + z * z

||| Strict forward chronological timelike precedence in 3+1D Red Minkowski space.
public export
causalPrecedes4 : Vec4I -> Vec4I -> Bool
causalPrecedes4 (t1, x1, y1, z1) (t2, x2, y2, z2) =
  let d = (t2 - t1, x2 - x1, y2 - y1, z2 - z1)
  in (t2 > t1) && (redDot4 d d > 0)

||| Vector sum and difference in 3+1D.
public export
addVec4 : Vec4I -> Vec4I -> Vec4I
addVec4 (t1, x1, y1, z1) (t2, x2, y2, z2) = (t1 + t2, x1 + x2, y1 + y2, z1 + z2)

public export
subVec4 : Vec4I -> Vec4I -> Vec4I
subVec4 (t1, x1, y1, z1) (t2, x2, y2, z2) = (t1 - t2, x1 - x2, y1 - y2, z1 - z2)

||| Exact integer boost in `SO+(3,1; Z)` generated by two spacelike hyperplane
||| reflections along `(1, 1, 1, 0)` and `(1, 0, 1, 1)`.
public export
lorentzBoost4D : Vec4I -> Vec4I
lorentzBoost4D (t, x, y, z) =
  ( 5 * t - 2 * x - 4 * y - 2 * z
  , 2 * t -     x - 2 * y
  , 4 * t - 2 * x - 3 * y - 2 * z
  , 2 * t         - 2 * y -     z
  )

||| Explicit 4-column representation of `lorentzBoost4D`.
public export
boost4DMat : Mat4I
boost4DMat =
  ( ( 5,  2,  4,  2)
  , (-2, -1, -2,  0)
  , (-4, -2, -3, -2)
  , (-2,  0, -2, -1)
  )

||| Canonical Minkowski Gram inner-product list `[c0.c0, c1.c1, c2.c2, c3.c3, off-diags]`.
public export
lorentzGramList : Mat4I -> List Integer
lorentzGramList (c0, c1, c2, c3) =
  [ redDot4 c0 c0, redDot4 c1 c1, redDot4 c2 c2, redDot4 c3 c3
  , redDot4 c0 c1, redDot4 c0 c2, redDot4 c0 c3
  , redDot4 c1 c2, redDot4 c1 c3, redDot4 c2 c3
  ]

||| Orthochronous `g_00 > 0` check for a 4D transformation matrix.
public export
mat4T00Pos : Mat4I -> Bool
mat4T00Pos ((t00, _, _, _), _, _, _) = t00 > 0

||| Constructive witness that `m` preserves the 3+1D Minkowski form and future cone.
public export
data IsOrthochronousLorentz4D : (m : Mat4I) -> Type where
  MkOrthochronousLorentz4D : (lorentzGramList m = [1, -1, -1, -1, 0, 0, 0, 0, 0, 0])
                          -> (mat4T00Pos m = True)
                          -> IsOrthochronousLorentz4D m

||| Total constructive `Dec` recognizer for `SO+(3,1; Z)` / `O+(3,1; Z)` matrices.
public export
recognizeLorentz4D : (m : Mat4I) -> Dec (IsOrthochronousLorentz4D m)
recognizeLorentz4D m =
  case decEq (lorentzGramList m) [1, -1, -1, -1, 0, 0, 0, 0, 0, 0] of
    No cGram => No (\(MkOrthochronousLorentz4D pG _) => cGram pG)
    Yes pGram =>
      case decEq (mat4T00Pos m) True of
        No cTime => No (\(MkOrthochronousLorentz4D _ pT) => cTime pT)
        Yes pTime => Yes (MkOrthochronousLorentz4D pGram pTime)

public export
record Lorentz4DReport where
  constructor MkLorentz4DReport
  redTimelike          : Integer
  redTimelikeBoosted   : Integer
  blueTimelike         : Integer
  blueTimelikeBoosted  : Integer
  nullDopplerShiftOk   : Bool
  spacelikeSimultFlip  : Bool
  causalOrderPreserved : Bool
  mandelstamS          : Integer
  mandelstamT          : Integer
  mandelstamU          : Integer
  mandelstamBoostedOk  : Bool
  lorentzDecOk         : Bool
  passesLorentz4DProbe : Bool

private
evalMandelstam2to2 : (Integer, Integer, Integer, Bool)
evalMandelstam2to2 =
  let p1  = (5,  3,  4, 0)
      p2  = (5, -3, -4, 0)
      p3  = (5,  0,  3, 4)
      p4  = (5,  0, -3, -4)
      bp1 = lorentzBoost4D p1
      bp2 = lorentzBoost4D p2
      bp3 = lorentzBoost4D p3
      bp4 = lorentzBoost4D p4
      qS  = addVec4 p1 p2
      qT  = subVec4 p1 p3
      qU  = subVec4 p1 p4
      s   = redDot4 qS qS
      t   = redDot4 qT qT
      u   = redDot4 qU qU
      bs  = redDot4 (addVec4 bp1 bp2) (addVec4 bp1 bp2)
      bt  = redDot4 (subVec4 bp1 bp3) (subVec4 bp1 bp3)
      bu  = redDot4 (subVec4 bp1 bp4) (subVec4 bp1 bp4)
      ok  = andAll [ redDot4 p1 p1 == 0, redDot4 p2 p2 == 0
                   , redDot4 p3 p3 == 0, redDot4 p4 p4 == 0
                   , s == 100, t == -26, u == -74
                   , s + t + u == 0
                   , bs == s, bt == t, bu == u
                   ]
  in (s, t, u, ok)

||| Probe G: Tests full 3+1D `SO+(3,1; Z)` Lorentz invariance across timelike, null Doppler
||| redshift, spacelike simultaneity flip, chronological causal precedence, and 2->2
||| massless Mandelstam `(s, t, u)` conservation & boost invariance.
export
probeLorentz4D : Lorentz4DReport
probeLorentz4D =
  let vTime  = (5, 1, 2, 1)
      bvTime = lorentzBoost4D vTime
      rTime  = redDot4 vTime vTime
      rBTime = redDot4 bvTime bvTime
      bTime  = blueQuad4 vTime
      bBTime = blueQuad4 bvTime

      vNull1  = (3, 1, 2, 2)
      bvNull1 = lorentzBoost4D vNull1
      vNull2  = (5, 3, 4, 0)
      bvNull2 = lorentzBoost4D vNull2
      nullOk  = andAll [ redDot4 vNull1 vNull1 == 0, redDot4 bvNull1 bvNull1 == 0
                       , blueQuad4 vNull1 == 9, blueQuad4 bvNull1 == 1
                       , redDot4 vNull2 vNull2 == 0, redDot4 bvNull2 bvNull2 == 0
                       , blueQuad4 vNull2 == 25, blueQuad4 bvNull2 == 9
                       ]

      vSpc   = (2, 3, 1, 1)
      bvSpc  = lorentzBoost4D vSpc
      spcOk  = andAll [ redDot4 vSpc vSpc == -7
                      , redDot4 bvSpc bvSpc == -7
                      , fst vSpc > 0
                      , fst bvSpc < 0
                      ]

      evA     = (1, 0, 0, 0)
      evB     = (5, 1, 2, 1)
      causOk  = andAll [ causalPrecedes4 evA evB
                       , causalPrecedes4 (lorentzBoost4D evA) (lorentzBoost4D evB)
                       ]

      (sM, tM, uM, mandOk) = evalMandelstam2to2

      badMat : Mat4I
      badMat = ((5, 2, 4, 2), (-2, -1, -2, 0), (-4, -2, -3, -2), (-2, 0, -2, 0))
      decOk  = andAll
                 [ case recognizeLorentz4D boost4DMat of
                     Yes (MkOrthochronousLorentz4D _ _) => True
                     No  _                              => False
                 , case recognizeLorentz4D badMat of
                     Yes _ => False
                     No  _ => True
                 ]

      passOk = andAll [ rTime == 19, rBTime == 19
                      , bTime == 6, bBTime == 150
                      , nullOk, spcOk, causOk, mandOk, decOk
                      ]
  in MkLorentz4DReport rTime rBTime bTime bBTime nullOk spcOk causOk sM tM uM mandOk decOk passOk

--------------------------------------------------------------------------------
-- 3. WAVE 3 (PROBE H): BACKGROUND-FREE HEREDITARY GEOMETRY (d_s /= d_H)
--------------------------------------------------------------------------------

||| Exact natural power `3^n`.
public export
pow3Nat : Nat -> Nat
pow3Nat Z     = 1
pow3Nat (S k) = 3 * pow3Nat k

||| Constructive witness that a Sierpinski gasket at generation `gen` satisfies
||| the exact topological vertex formula `2 * V = 3^(gen + 1) + 3`.
public export
data SatisfiesGasketVolume : (gen, vCount : Nat) -> Type where
  MkGasketVolume : (2 * vCount = pow3Nat (S gen) + 3) -> SatisfiesGasketVolume gen vCount

||| Total constructive `Dec` recognizer for rewritten gasket vertex counts.
public export
recognizeGasketVertexLaw : (gen, vCount : Nat) -> Dec (SatisfiesGasketVolume gen vCount)
recognizeGasketVertexLaw gen vCount =
  case decEq (2 * vCount) (pow3Nat (S gen) + 3) of
    Yes prf   => Yes (MkGasketVolume prf)
    No contra => No (\(MkGasketVolume prf) => contra prf)

private
normEdge : Nat -> Nat -> (Nat, Nat)
normEdge u v = if u <= v then (u, v) else (v, u)

private
lookupOrAllocMid : Nat -> Nat ->
                   (Box BoxInt (Nat, Nat), Nat) ->
                   (Nat, Box BoxInt (Nat, Nat), Nat)
lookupOrAllocMid u v (midBox, nxt) =
  let key      = normEdge u v
      existing = unwrapBox (lookupBox key midBox)
  in if existing > 0
       then (minus (integerToNat existing) 1, midBox, nxt)
       else
         let enc = intToBoxInt (natToInteger (S nxt))
         in (nxt, setBox key enc midBox, S nxt)

private
subdivideRingStep : (List (Nat, Nat), Nat) -> (List (Nat, Nat), Nat)
subdivideRingStep (edges, nxt) = go edges nxt []
  where
    go : List (Nat, Nat) -> Nat -> List (Nat, Nat) -> (List (Nat, Nat), Nat)
    go []            n acc = (acc, n)
    go ((u, v) :: es) n acc = go es (S n) ((u, n) :: (n, v) :: acc)

private
subdivideGasketStep : (List (Nat, (Nat, Nat)), Nat) -> (List (Nat, (Nat, Nat)), Nat)
subdivideGasketStep (tris, nxt) = go tris BoxLeaf nxt []
  where
    go : List (Nat, (Nat, Nat)) ->
         Box BoxInt (Nat, Nat) ->
         Nat ->
         List (Nat, (Nat, Nat)) ->
         (List (Nat, (Nat, Nat)), Nat)
    go [] _ n acc = (acc, n)
    go ((a, (b, c)) :: rest) midBox n acc =
      let (ab, m1, n1) = lookupOrAllocMid a b (midBox, n)
          (bc, m2, n2) = lookupOrAllocMid b c (m1, n1)
          (ca, m3, n3) = lookupOrAllocMid c a (m2, n2)
          t1 = (a,  (ab, ca))
          t2 = (ab, (b,  bc))
          t3 = (ca, (bc, c))
      in go rest m3 n3 (t1 :: t2 :: t3 :: acc)

private
dedupTrisEdges : List (Nat, (Nat, Nat)) -> List (Nat, Nat)
dedupTrisEdges tris =
  let eBox = foldl (\acc, (a, (b, c)) =>
                     setBox (normEdge c a) (intToBoxInt 1)
                       (setBox (normEdge b c) (intToBoxInt 1)
                         (setBox (normEdge a b) (intToBoxInt 1) acc)))
                   (the (Box BoxInt (Nat, Nat)) BoxLeaf)
                   tris
  in foldBox (\e, w, acc => if isZero w then acc else e :: acc) [] eBox

private
buildDegreeBox : List (Nat, Nat) -> Box BoxInt Nat
buildDegreeBox =
  foldl (\acc, (u, v) =>
          addAtKeyBox u (intToBoxInt 1) (addAtKeyBox v (intToBoxInt 1) acc))
        BoxLeaf

||| Coordinate-free graph diffusion (`mass * 8` per tick, `stay = 8 - deg(v)`,
||| `1` per incident edge) over an undirected vertex/edge multiset.
public export
stepGraphWalk : Box BoxInt Nat -> List (Nat, Nat) -> Box BoxInt Nat -> Box BoxInt Nat
stepGraphWalk degBox edges st =
  let stayBox = foldBox (\v, (MkBoxInt w), acc =>
                          if w == 0
                            then acc
                            else
                              let deg = unwrapBox (lookupBox v degBox)
                              in addAtKeyBox v (intToBoxInt (w * (8 - deg))) acc)
                        BoxLeaf
                        st
  in foldl (\acc, (u, v) =>
             let wu = lookupBox u st
                 wv = lookupBox v st
                 a1 = if isZero wu then acc else addAtKeyBox v wu acc
             in if isZero wv then a1 else addAtKeyBox u wv a1)
           stayBox
           edges

private
returnRatioGraph : Nat -> Box BoxInt Nat -> MSetFraction
returnRatioGraph startV b =
  let w0   = lookupBox startV b
      totM = foldBox (\_, (MkBoxInt w), acc => acc + integerToNat (abs w)) (the Nat 0) b
  in reduceMSF (mkMSF w0 totM)

private
walkGraphPowers8_16_32 : Nat -> List (Nat, Nat) -> (MSetFraction, MSetFraction)
walkGraphPowers8_16_32 startV edges =
  let degBox = buildDegreeBox edges
      s0     = setBox startV (intToBoxInt 1) BoxLeaf
      s8     = iterateN 8  (stepGraphWalk degBox edges) s0
      s16    = iterateN 8  (stepGraphWalk degBox edges) s8
      s32    = iterateN 16 (stepGraphWalk degBox edges) s16
      d816   = reduceMSF (divMSF (returnRatioGraph startV s16) (returnRatioGraph startV s8))
      d1632  = reduceMSF (divMSF (returnRatioGraph startV s32) (returnRatioGraph startV s16))
  in (effDimPower2 d816, effDimPower2 d1632)

public export
record EmergentGeometryReport where
  constructor MkEmergentGeometryReport
  ringVerts           : Nat
  ringEdges           : Nat
  gasketVerts         : Nat
  gasketEdges         : Nat
  ringPow8to16        : MSetFraction
  ringPow16to32       : MSetFraction
  gasketPow8to16      : MSetFraction
  gasketPow16to32     : MSetFraction
  gasketDecOk         : Bool
  passesEmergentProbe : Bool

||| Probe H: Rewrites coordinate-free 1D ring bisection (`d_H = 1, d_s = 1`) and
||| Sierpinski gasket subdivision (`d_H = log2(3) ~ 1.585`) for 4 generations, then
||| runs coordinate-free adjacency diffusion to verify `2^{d_s}(Ring) < 2^{d_s}(Gasket) < 3 = 2^{d_H}`
||| (proving `d_s ~ 1.365 != d_H ~ 1.585` purely from relational multiset topology).
export
probeEmergentGeometry : EmergentGeometryReport
probeEmergentGeometry =
  let (rEdges, rVerts) = iterateN 4 subdivideRingStep ([(0, 1), (1, 2), (2, 0)], 3)
      (gTris,  gVerts) = iterateN 4 subdivideGasketStep ([(0, (1, 2))], 3)
      gEdges           = dedupTrisEdges gTris
      gEdgeCount       = length gEdges

      (eR816, eR1632) = walkGraphPowers8_16_32 0 rEdges
      (eG816, eG1632) = walkGraphPowers8_16_32 3 gEdges

      decOk = andAll
                [ case recognizeGasketVertexLaw 4 gVerts of
                    Yes (MkGasketVolume _) => True
                    No  _                  => False
                , case recognizeGasketVertexLaw 4 122 of
                    Yes _ => False
                    No  _ => True
                ]

      passOk = andAll
                 [ rVerts == 48
                 , length rEdges == 48
                 , gVerts == 123
                 , gEdgeCount == 243
                 , decOk
                 , msfLT eR816 eG816
                 , msfLT eG816 (mkMSF 3 1)
                 , msfLT eR1632 eG1632
                 , msfLT eG1632 (mkMSF 3 1)
                 , msfGT eG816 (mkMSF 24 10)
                 , msfGT eG1632 (mkMSF 24 10)
                 ]
  in MkEmergentGeometryReport rVerts (length rEdges) gVerts gEdgeCount
       eR816 eR1632 eG816 eG1632 decOk passOk

--------------------------------------------------------------------------------
-- 4. COMPILE-TIME QTT 0 `Refl` AUDITS
--------------------------------------------------------------------------------

||| Audit 1: Exact 3+1D Minkowski Gram identity for `boost4DMat`.
public export
0 prfLorentzGram4D :
  Stage1.FrontierProbe.lorentzGramList Stage1.FrontierProbe.boost4DMat
    = [1, -1, -1, -1, 0, 0, 0, 0, 0, 0]
prfLorentzGram4D = Refl

||| Audit 2: Exact generation-4 Sierpinski gasket topological vertex formula.
public export
0 prfGasketVol4 :
  2 * 123 = Stage1.FrontierProbe.pow3Nat 5 + 3
prfGasketVol4 = Refl
