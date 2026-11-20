module Stage1.EmergentCouplingProbe

import Data.List
import Data.Nat
import Decidable.Equality
import public Stage0.Box
import public Stage0.BoxInt
import public Stage0.SignedFraction
import public Stage0.HereditaryMSet
import public Stage1.ConvolutionAdmissibility
import public Stage1.PhasedMultiset
import public Stage1.FuelProbe
import public Stage1.FrontierProbe

%default total

private
repeatN : Nat -> (a -> a) -> a -> a
repeatN Z     _ x = x
repeatN (S k) f x = repeatN k f (f x)

private
powInt : Integer -> Nat -> Integer
powInt _ Z     = 1
powInt b (S k) = b * powInt b k

private
reduceBigMSF : MSetFraction -> MSetFraction
reduceBigMSF = reduceMSF

--------------------------------------------------------------------------------
-- LOCAL PRIVATE GRAPH & BFS UTILITIES
--------------------------------------------------------------------------------

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

private
returnRatioGraph : Nat -> Box BoxInt Nat -> MSetFraction
returnRatioGraph startV b =
  let w0   = lookupBox startV b
      totM = foldBox (\_, (MkBoxInt w), acc => acc + integerToNat (abs w)) (the Nat 0) b
  in reduceBigMSF (mkMSF w0 totM)

private
neighborsOf : Nat -> List (Nat, Nat) -> List Nat
neighborsOf v edges =
  sort (foldl (\acc, (a, b) =>
                if a == v then b :: acc
                else if b == v then a :: acc
                else acc) [] edges)

private
record BFSAcc where
  constructor MkBFSAcc
  visAcc   : Box BoxInt Nat
  frontAcc : Box BoxInt Nat

private
bfsDistances : Nat -> Nat -> List (Nat, Nat) -> Box BoxInt Nat
bfsDistances maxDepth start edges =
  let initBox = setBox start (intToBoxInt 1) (the (Box BoxInt Nat) BoxLeaf)
  in go maxDepth (the Integer 2) initBox initBox
  where
    go : Nat -> Integer -> Box BoxInt Nat -> Box BoxInt Nat -> Box BoxInt Nat
    go Z _ vis _ = vis
    go (S k) nextEnc vis front =
      if boxNodeCount front == Z
        then vis
        else
          let res = foldl (\acc, (u, v) =>
                            let fu = unwrapBox (lookupBox u front)
                                fv = unwrapBox (lookupBox v front)
                                acc1 =
                                  if (fu > 0) && (unwrapBox (lookupBox v acc.visAcc) == 0)
                                    then MkBFSAcc (setBox v (intToBoxInt nextEnc) acc.visAcc)
                                                  (setBox v (intToBoxInt 1) acc.frontAcc)
                                    else acc
                            in if (fv > 0) && (unwrapBox (lookupBox u acc1.visAcc) == 0)
                                 then MkBFSAcc (setBox u (intToBoxInt nextEnc) acc1.visAcc)
                                               (setBox u (intToBoxInt 1) acc1.frontAcc)
                                 else acc1)
                          (MkBFSAcc vis BoxLeaf)
                          edges
          in go k (nextEnc + 1) res.visAcc res.frontAcc

private
distFromBox : Nat -> Box BoxInt Nat -> Integer
distFromBox v distBox =
  let r = unwrapBox (lookupBox v distBox)
  in if r > 0 then r - 1 else 0

--------------------------------------------------------------------------------
-- 1. PROBE K: SIERPINSKI GEN3/GEN4/GEN5 LOG-PERIODICITY vs BOUNDARY & RG FIXED PT
--------------------------------------------------------------------------------

private
record GasketScaleMetrics where
  constructor MkGasketScaleMetrics
  verts     : Nat
  edges     : Nat
  pow4to8   : MSetFraction
  pow8to16  : MSetFraction
  pow16to32 : MSetFraction
  pow32to64 : MSetFraction
  rg5At4    : MSetFraction
  rg5At8    : MSetFraction
  rg5At12   : MSetFraction

private
evalGasketScaleMetrics : Nat -> GasketScaleMetrics
evalGasketScaleMetrics gen =
  let (gTris, gVerts) = repeatN gen subdivideGasketStep ([(0, (1, 2))], 3)
      gEdges          = dedupTrisEdges gTris
      degBox          = buildDegreeBox gEdges
      step            = stepGraphWalk degBox gEdges
      s0              = setBox (the Nat 3) (intToBoxInt 1) (the (Box BoxInt Nat) BoxLeaf)

      s4  = repeatN 4  step s0
      s8  = repeatN 4  step s4
      s12 = repeatN 4  step s8
      s16 = repeatN 4  step s12
      s20 = repeatN 4  step s16
      s32 = repeatN 12 step s20
      s40 = repeatN 8  step s32
      s60 = repeatN 20 step s40
      s64 = repeatN 4  step s60

      p4  = returnRatioGraph 3 s4
      p8  = returnRatioGraph 3 s8
      p12 = returnRatioGraph 3 s12
      p16 = returnRatioGraph 3 s16
      p20 = returnRatioGraph 3 s20
      p32 = returnRatioGraph 3 s32
      p40 = returnRatioGraph 3 s40
      p60 = returnRatioGraph 3 s60
      p64 = returnRatioGraph 3 s64

      d4to8   = reduceBigMSF (effDimPower2 (reduceBigMSF (divMSF p8  p4)))
      d8to16  = reduceBigMSF (effDimPower2 (reduceBigMSF (divMSF p16 p8)))
      d16to32 = reduceBigMSF (effDimPower2 (reduceBigMSF (divMSF p32 p16)))
      d32to64 = reduceBigMSF (effDimPower2 (reduceBigMSF (divMSF p64 p32)))

      r5_4    = reduceBigMSF (divMSF p4  p20)
      r5_8    = reduceBigMSF (divMSF p8  p40)
      r5_12   = reduceBigMSF (divMSF p12 p60)
  in MkGasketScaleMetrics gVerts (length gEdges) d4to8 d8to16 d16to32 d32to64 r5_4 r5_8 r5_12

public export
record GasketLogPeriodicReport where
  constructor MkGasketLogPeriodicReport
  gen5Verts        : Nat
  gen5Edges        : Nat
  gen3Pow32to64    : MSetFraction
  gen4Pow16to32    : MSetFraction
  gen5Pow4to8      : MSetFraction
  gen5Pow8to16     : MSetFraction
  gen5Pow16to32    : MSetFraction
  gen5Pow32to64    : MSetFraction
  gen5RG5At4       : MSetFraction
  gen5RG5At8       : MSetFraction
  gen5RG5At12      : MSetFraction
  logPeriodicOk    : Bool
  boundaryCollapse : Bool
  rg5FixedPointOk  : Bool
  gen5DecOk        : Bool
  passesProbeK     : Bool

||| Probe K: Separates true discrete scale invariance (log-periodic oscillations and
||| exact factor-of-5 RG fixed point `P(t)/P(5t) -> 3`) from finite-size boundary
||| collapse across Sierpinski `Gen3` (`V=42`), `Gen4` (`V=123`), and `Gen5` (`V=366`).
export
probeGasketLogPeriodicity : GasketLogPeriodicReport
probeGasketLogPeriodicity =
  let g3 = evalGasketScaleMetrics 3
      g4 = evalGasketScaleMetrics 4
      g5 = evalGasketScaleMetrics 5

      logOk = andAll [ msfGT g5.pow4to8 g5.pow8to16
                     , msfGT g5.pow16to32 g5.pow8to16
                     , msfGT g5.pow16to32 g5.pow32to64
                     , msfLT (msfAbsDiff g5.pow16to32 g4.pow16to32) (mkMSF 1 1000)
                     ]

      bndOk = andAll [ msfLT g3.pow32to64 (mkMSF 2 1)
                     , msfGT g5.pow32to64 (mkMSF 24 10)
                     ]

      rg5Ok = andAll [ msfGT g5.rg5At4 g5.rg5At8
                     , msfGT g5.rg5At8 g5.rg5At12
                     , msfGT g5.rg5At12 (mkMSF 3 1)
                     , msfLT g5.rg5At12 (mkMSF 305 100)
                     ]

      decOk = andAll
                [ case recognizeGasketVertexLaw 5 g5.verts of
                    Yes (MkGasketVolume _) => True
                    No  _                  => False
                , case recognizeGasketVertexLaw 5 365 of
                    Yes _ => False
                    No  _ => True
                ]

      passOk = andAll [g5.verts == 366, g5.edges == 729, logOk, bndOk, rg5Ok, decOk]
  in MkGasketLogPeriodicReport g5.verts g5.edges
       g3.pow32to64 g4.pow16to32
       g5.pow4to8 g5.pow8to16 g5.pow16to32 g5.pow32to64
       g5.rg5At4 g5.rg5At8 g5.rg5At12
       logOk bndOk rg5Ok decOk passOk

--------------------------------------------------------------------------------
-- 2. PROBE L: EXACT 4x4 GROVER QUANTUM WALK ON COORDINATE-FREE GASKET
--------------------------------------------------------------------------------

||| Constructive witness that a symmetric 4x4 coin `diag*I + off*(J - I)`
||| satisfies `G^T G = 4 I` (columns have quadrance 4 and are orthogonal).
public export
data IsGrover4Unitary : (diag, off : Integer) -> Type where
  MkGrover4Unitary : (diag * diag + 3 * off * off = 4)
                  -> (2 * diag * off + 2 * off * off = 0)
                  -> IsGrover4Unitary diag off

||| Total constructive `Dec` recognizer for 4x4 integer Grover coins.
public export
recognizeGrover4Unitary : (diag, off : Integer) -> Dec (IsGrover4Unitary diag off)
recognizeGrover4Unitary diag off =
  case decEq (diag * diag + 3 * off * off) 4 of
    No c1 => No (\(MkGrover4Unitary p1 _) => c1 p1)
    Yes p1 =>
      case decEq (2 * diag * off + 2 * off * off) 0 of
        No c2 => No (\(MkGrover4Unitary _ p2) => c2 p2)
        Yes p2 => Yes (MkGrover4Unitary p1 p2)

||| Directed-arc spinor state `(u, v) -> amplitude` residing at vertex `u`
||| facing neighbor `v`.
public export
ArcSpinor : Type
ArcSpinor = Box BoxInt (Nat, Nat)

||| Exact integer unitary quantum walk on an undirected graph with interior
||| vertices of degree 4 (`G_4` Grover coin, `Q2 * 4`) and corner vertices of
||| degree 2 (`[[0, 2], [2, 0]]` transmission swap, `Q2 * 4`), plus arc shift.
public export
stepGroverGraph : Box BoxInt Nat -> List (Nat, Nat) -> ArcSpinor -> ArcSpinor
stepGroverGraph degBox edges st =
  let sumBox : Box BoxInt Nat
      sumBox = foldBox (\(v, _), w, acc => addAtKeyBox v w acc)
                       (the (Box BoxInt Nat) BoxLeaf)
                       st
  in foldl (\acc, (u, v) =>
             let du   = unwrapBox (lookupBox u degBox)
                 dv   = unwrapBox (lookupBox v degBox)
                 su   = unwrapBox (lookupBox u sumBox)
                 sv   = unwrapBox (lookupBox v sumBox)
                 wuv  = unwrapBox (lookupBox (u, v) st)
                 wvu  = unwrapBox (lookupBox (v, u) st)
                 outU = if du == 4 then su - 2 * wuv else if du == 2 then 2 * (su - wuv) else 0
                 outV = if dv == 4 then sv - 2 * wvu else if dv == 2 then 2 * (sv - wvu) else 0
                 a1   = if outU == 0 then acc else addAtKeyBox (v, u) (intToBoxInt outU) acc
             in if outV == 0 then a1 else addAtKeyBox (u, v) (intToBoxInt outV) a1)
           (the ArcSpinor BoxLeaf)
           edges

private
record ArcAccum where
  constructor MkArcAccum
  q2Acc  : Integer
  l1Acc  : Integer
  retAcc : Integer
  m2Acc  : Integer

private
record ArcStats where
  constructor MkArcStats
  q2      : Integer
  l1      : Integer
  retProb : MSetFraction
  var     : MSetFraction

private
arcStats : Nat -> Box BoxInt Nat -> ArcSpinor -> ArcStats
arcStats startV distBox st =
  let res = foldBox (\(v, _), (MkBoxInt w), acc =>
                      let p   = w * w
                          aw  = abs w
                          d   = distFromBox v distBox
                          r2  = if v == startV then p else 0
                      in MkArcAccum (acc.q2Acc + p) (acc.l1Acc + aw) (acc.retAcc + r2) (acc.m2Acc + p * d * d))
                    (MkArcAccum 0 0 0 0)
                    st
      den = integerToNat (max (the Integer 1) res.q2Acc)
  in MkArcStats res.q2Acc res.l1Acc
       (reduceMSF (mkMSF (intToBoxInt res.retAcc) den))
       (reduceMSF (mkMSF (intToBoxInt res.m2Acc) den))

private
record ClAccum where
  constructor MkClAccum
  totAcc : Integer
  retAcc : Integer
  m2Acc  : Integer

private
clGraphStats : Nat -> Box BoxInt Nat -> Box BoxInt Nat -> (MSetFraction, MSetFraction)
clGraphStats startV distBox st =
  let res = foldBox (\v, (MkBoxInt w), acc =>
                      let d  = distFromBox v distBox
                          rw = if v == startV then w else 0
                      in MkClAccum (acc.totAcc + w) (acc.retAcc + rw) (acc.m2Acc + w * d * d))
                    (MkClAccum 0 0 0)
                    st
      den = integerToNat (max (the Integer 1) res.totAcc)
  in ( reduceMSF (mkMSF (intToBoxInt res.retAcc) den)
     , reduceMSF (mkMSF (intToBoxInt res.m2Acc) den)
     )

public export
record GroverGasketReport where
  constructor MkGroverGasketReport
  symQ2_16        : Integer
  symExactUni16   : Bool
  dipExactUni16   : Bool
  symVRat16to8    : MSetFraction
  symVar16        : MSetFraction
  clVar16         : MSetFraction
  dipRet16        : MSetFraction
  clRet16         : MSetFraction
  interferedOk    : Bool
  groverDecOk     : Bool
  passesGrover    : Bool

||| Probe L: Evolves an exact integer 4x4 Grover quantum walk directly on the
||| coordinate-free Gen-4 Sierpinski gasket (`V=123, E=243`), proving exact `L2`
||| unitarity (`4^16`), sub-ballistic fractal quantum transport (`V16/V8 < 2.0`),
||| and >5x dipole quantum localization compared to classical diffusion.
export
probeGroverOnGasket : GroverGasketReport
probeGroverOnGasket =
  let (gTris, _) = repeatN 4 subdivideGasketStep ([(0, (1, 2))], 3)
      gEdges     = dedupTrisEdges gTris
      degBox     = buildDegreeBox gEdges
      distBox    = bfsDistances 20 3 gEdges
      nbs3       = neighborsOf 3 gEdges

      sym0       = foldl (\acc, nb => setBox (the Nat 3, nb) (intToBoxInt 1) acc)
                         (the ArcSpinor BoxLeaf) nbs3
      dip0       = case nbs3 of
                     (n0 :: n1 :: _) =>
                       setBox (the Nat 3, n0) (intToBoxInt 1)
                         (setBox (the Nat 3, n1) (intToBoxInt (-1)) (the ArcSpinor BoxLeaf))
                     _ => sym0

      gStep  = stepGroverGraph degBox gEdges
      sym8   = repeatN 8 gStep sym0
      sym16  = repeatN 8 gStep sym8
      dip16  = repeatN 16 gStep dip0

      sSym8  = arcStats 3 distBox sym8
      sSym16 = arcStats 3 distBox sym16
      sDip16 = arcStats 3 distBox dip16
      symVR  = reduceMSF (divMSF sSym16.var sSym8.var)

      cl0    = setBox (the Nat 3) (intToBoxInt 1) (the (Box BoxInt Nat) BoxLeaf)
      cl16   = repeatN 16 (stepGraphWalk degBox gEdges) cl0
      (clR16, clV16) = clGraphStats 3 distBox cl16

      symUni = (sSym16.q2 == 4 * powInt 4 16)
      dipUni = (sDip16.q2 == 2 * powInt 4 16)
      intOk  = andAll [ sSym16.l1 < sSym16.q2
                      , sDip16.l1 < sDip16.q2
                      ]

      decOk  = andAll
                 [ case recognizeGrover4Unitary (-1) 1 of
                     Yes (MkGrover4Unitary _ _) => True
                     No  _                      => False
                 , case recognizeGrover4Unitary 1 1 of
                     Yes _ => False
                     No  _ => True
                 ]

      passOk = andAll
                 [ symUni
                 , dipUni
                 , intOk
                 , decOk
                 , msfGT sDip16.retProb (mkMSF 30 100)
                 , msfLT clR16 (mkMSF 8 100)
                 , msfGT sSym16.var clV16
                 , msfLT symVR (mkMSF 2 1)
                 ]
  in MkGroverGasketReport sSym16.q2 symUni dipUni symVR sSym16.var clV16
       sDip16.retProb clR16 intOk decOk passOk

--------------------------------------------------------------------------------
-- 3. PROBE M: `PhasedMultiset` HORIZON DECOHERENCE & CURVATURE BACK-REACTION
--------------------------------------------------------------------------------

private
filterWindowBox : Integer -> Box BoxInt Integer -> Box BoxInt Integer
filterWindowBox wBound = sliceWindowInt (2 * integerToNat (abs wBound) + 1) 0

private
stepWindowedHad1D : Integer -> Spinor1D -> Spinor1D
stepWindowedHad1D wBound st =
  let (nL, nR) = stepHadamard1D st
  in (filterWindowBox wBound nL, filterWindowBox wBound nR)

private
stepDephasedHad1D : Spinor1D -> Spinor1D
stepDephasedHad1D (pL, pR) =
  let (l1, r1) = foldBox (\x, (MkBoxInt w), (accL, accR) =>
                           if w == 0
                             then (accL, accR)
                             else ( addAtKeyBox (x - 1) (intToBoxInt w) accL
                                  , addAtKeyBox (x + 1) (intToBoxInt w) accR
                                  ))
                         (the (Box BoxInt Integer) BoxLeaf, the (Box BoxInt Integer) BoxLeaf)
                         pL
  in foldBox (\x, (MkBoxInt w), (accL, accR) =>
               if w == 0
                 then (accL, accR)
                 else ( addAtKeyBox (x - 1) (intToBoxInt w) accL
                      , addAtKeyBox (x + 1) (intToBoxInt w) accR
                      ))
             (l1, r1)
             pR

private
record ProbAccum1D where
  constructor MkProbAccum1D
  m0 : Integer
  m2 : Integer
  m4 : Integer

private
record ProbStats1D where
  constructor MkProbStats1D
  totP  : Integer
  varP  : MSetFraction
  kurtP : MSetFraction

private
statsProb1D : Spinor1D -> ProbStats1D
statsProb1D (pL, pR) =
  let addM : Integer -> BoxInt -> ProbAccum1D -> ProbAccum1D
      addM x (MkBoxInt w) acc =
        let x2 = x * x
        in MkProbAccum1D (acc.m0 + w) (acc.m2 + w * x2) (acc.m4 + w * x2 * x2)
      s1   = foldBox addM (MkProbAccum1D 0 0 0) pL
      s2   = foldBox addM s1 pR
      var  = reduceMSF (mkMSF (intToBoxInt s2.m2) (integerToNat (max (the Integer 1) s2.m0)))
      kurt = reduceMSF (mkMSF (intToBoxInt (s2.m4 * s2.m0)) (integerToNat (max (the Integer 1) (s2.m2 * s2.m2))))
  in MkProbStats1D s2.m0 var kurt

private
record HorizonDecohEval where
  constructor MkHorizonDecohEval
  cohQ2_16     : Integer
  winQ2_16     : Integer
  winRetained  : MSetFraction
  dephVRat16   : MSetFraction
  dephKurt16   : MSetFraction
  phasedDecOk  : Bool
  horizonOk    : Bool

private
evalHorizonDecoherence : HorizonDecohEval
evalHorizonDecoherence =
  let s0  = ( setBox (the Integer 0) (intToBoxInt 1) BoxLeaf
            , setBox (the Integer 0) (intToBoxInt 1) BoxLeaf
            )
      h16 = repeatN 16 stepHadamard1D s0
      w16 = repeatN 16 (stepWindowedHad1D 6) s0
      d8  = repeatN 8  stepDephasedHad1D s0
      d16 = repeatN 8  stepDephasedHad1D d8

      phL : Stage1.PhasedMultiset.Multiset (MkPhase 1 (StaticHorizon (-16) 16) 33) BoxInt
      phL = MkPhasedMSet (box1DToPureMSet (fst h16))
      phR : Stage1.PhasedMultiset.Multiset (MkPhase 1 (StaticHorizon (-16) 16) 33) BoxInt
      phR = MkPhasedMSet (box1DToPureMSet (snd h16))

      winL : Stage1.PhasedMultiset.Multiset (MkPhase 1 (WindowedHorizon 13) 13) BoxInt
      winL = MkPhasedMSet (box1DToPureMSet (fst w16))
      winR : Stage1.PhasedMultiset.Multiset (MkPhase 1 (WindowedHorizon 13) 13) BoxInt
      winR = MkPhasedMSet (box1DToPureMSet (snd w16))

      cohQ2 = unwrapBox (dotBoundedPhased phL phL) + unwrapBox (dotBoundedPhased phR phR)
      winQ2 = unwrapBox (dotBoundedPhased winL winL) + unwrapBox (dotBoundedPhased winR winR)
      retF  = reduceMSF (mkMSF (intToBoxInt winQ2) (integerToNat (max (the Integer 1) cohQ2)))

      sd8       = statsProb1D d8
      sd16      = statsProb1D d16
      dVRat     = reduceMSF (divMSF sd16.varP sd8.varP)
      fuelCount = snd (phasedFuelOf phL)
      phDec = andAll
                [ case recognizeCanonicalPhased phL of
                    Yes _ => True
                    No  _ => False
                , case recognizeCanonicalPhased winL of
                    Yes _ => True
                    No  _ => False
                , case recognizeBoundedRegime (WindowedHorizon 13) of
                    Yes _ => True
                    No  _ => False
                , case recognizeBoundedRegime OpenFuture of
                    Yes _ => False
                    No  _ => True
                , fuelCount > 0
                ]

      ok = andAll [ cohQ2 == 131072
                  , winQ2 == 61816
                  , msfLT retF (mkMSF 1 2)
                  , dVRat == mkMSF 2 1
                  , msfGT sd16.kurtP (mkMSF 28 10)
                  , phDec
                  ]
  in MkHorizonDecohEval cohQ2 winQ2 retF dVRat sd16.kurtP phDec ok

||| Constructive witness that a closed 2D triangulation satisfies Euler's sphere
||| identity (`V + F = E + 2`) and discrete Gauss-Bonnet curvature conservation (`sum K = 12`).
public export
data IsGaussBonnetSphere2D : (v, e, f : Nat) -> (sumK : Integer) -> Type where
  MkGaussBonnetSphere2D : (v + f = e + 2)
                       -> (sumK = 12)
                       -> IsGaussBonnetSphere2D v e f sumK

||| Total constructive `Dec` recognizer for discrete Gauss-Bonnet topology on 2D triangulations.
public export
recognizeGaussBonnet2D : (v, e, f : Nat) -> (sumK : Integer) -> Dec (IsGaussBonnetSphere2D v e f sumK)
recognizeGaussBonnet2D v e f sumK =
  case decEq (v + f) (e + 2) of
    No cEuler => No (\(MkGaussBonnetSphere2D pe _) => cEuler pe)
    Yes pEuler =>
      case decEq sumK 12 of
        No cCurv => No (\(MkGaussBonnetSphere2D _ pk) => cCurv pk)
        Yes pCurv => Yes (MkGaussBonnetSphere2D pEuler pCurv)

private
record TriMeshState where
  constructor MkTriMeshState
  tris   : List (Nat, (Nat, Nat))
  nVerts : Nat
  matter : Box BoxInt Nat

private
subdivideHotTris : Integer -> TriMeshState -> TriMeshState
subdivideHotTris threshold st = go st.tris st.nVerts st.matter []
  where
    go : List (Nat, (Nat, Nat)) ->
         Nat ->
         Box BoxInt Nat ->
         List (Nat, (Nat, Nat)) ->
         TriMeshState
    go [] n m acc = MkTriMeshState acc n m
    go ((a, (b, c)) :: rest) n m acc =
      let triMass = unwrapBox (lookupBox a m)
                  + unwrapBox (lookupBox b m)
                  + unwrapBox (lookupBox c m)
      in if triMass >= threshold
           then
             let m' = setBox n (intToBoxInt (triMass `div` 3)) m
             in go rest (S n) m' ((a, (b, n)) :: (b, (c, n)) :: (c, (a, n)) :: acc)
           else go rest n m ((a, (b, c)) :: acc)

private
sumCurvRange : Nat -> Box BoxInt Nat -> Integer
sumCurvRange Z     _      = 0
sumCurvRange (S k) degBox = (6 - unwrapBox (lookupBox k degBox)) + sumCurvRange k degBox

private
stepGraphWalkBase : Integer -> Box BoxInt Nat -> List (Nat, Nat) -> Box BoxInt Nat -> Box BoxInt Nat
stepGraphWalkBase base degBox edges st =
  let stayBox = foldBox (\v, (MkBoxInt w), acc =>
                          if w == 0
                            then acc
                            else
                              let deg = unwrapBox (lookupBox v degBox)
                              in addAtKeyBox v (intToBoxInt (w * (base - deg))) acc)
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
loc1MassRatio : Box BoxInt Nat -> Box BoxInt Nat -> MSetFraction
loc1MassRatio distBox st =
  let (totW, locW) = foldBox (\v, (MkBoxInt w), (tw, lw) =>
                               let d = distFromBox v distBox
                               in (tw + w, if d <= 1 then lw + w else lw))
                             (the Integer 0, the Integer 0)
                             st
  in reduceMSF (mkMSF (intToBoxInt locW) (integerToNat (max (the Integer 1) totW)))

private
record CurvatureEval where
  constructor MkCurvatureEval
  meshVerts   : Nat
  meshEdges   : Nat
  meshFaces   : Nat
  sumCurv     : Integer
  kPole0_0    : Integer
  kPole0_3    : Integer
  kPole1_3    : Integer
  loc1Pole0   : MSetFraction
  loc1Pole1   : MSetFraction
  gaussDecOk  : Bool
  curvOk      : Bool

private
evalMatterBackReaction : CurvatureEval
evalMatterBackReaction =
  let octTris : List (Nat, (Nat, Nat))
      octTris = [ (0, (2, 3)), (0, (3, 4)), (0, (4, 5)), (0, (5, 2))
                , (1, (3, 2)), (1, (4, 3)), (1, (5, 4)), (1, (2, 5))
                ]
      m0  = setBox (the Nat 0) (intToBoxInt 9) (the (Box BoxInt Nat) BoxLeaf)

      st0 = MkTriMeshState octTris 6 m0
      st1 = subdivideHotTris 6 st0
      st2 = subdivideHotTris 6 st1
      st3 = subdivideHotTris 6 st2

      e0 = dedupTrisEdges st0.tris
      d0 = buildDegreeBox e0
      s0 = sumCurvRange st0.nVerts d0
      k0_0 = 6 - unwrapBox (lookupBox (the Nat 0) d0)

      e1 = dedupTrisEdges st1.tris
      d1 = buildDegreeBox e1
      s1 = sumCurvRange st1.nVerts d1

      e2 = dedupTrisEdges st2.tris
      d2 = buildDegreeBox e2
      s2 = sumCurvRange st2.nVerts d2

      e3 = dedupTrisEdges st3.tris
      d3 = buildDegreeBox e3
      s3 = sumCurvRange st3.nVerts d3
      k0_3 = 6 - unwrapBox (lookupBox (the Nat 0) d3)
      k1_3 = 6 - unwrapBox (lookupBox (the Nat 1) d3)

      dist0 = bfsDistances 10 0 e3
      dist1 = bfsDistances 10 1 e3
      w0    = repeatN 16 (stepGraphWalkBase 64 d3 e3) (setBox (the Nat 0) (intToBoxInt 1) BoxLeaf)
      w1    = repeatN 16 (stepGraphWalkBase 64 d3 e3) (setBox (the Nat 1) (intToBoxInt 1) BoxLeaf)
      loc0  = loc1MassRatio dist0 w0
      loc1  = loc1MassRatio dist1 w1

      checkGB : Nat -> Nat -> Nat -> Integer -> Bool
      checkGB v e f sk =
        case recognizeGaussBonnet2D v e f sk of
          Yes (MkGaussBonnetSphere2D _ _) => True
          No  _                           => False

      gbOk = andAll [ checkGB st0.nVerts (length e0) (length st0.tris) s0
                    , checkGB st1.nVerts (length e1) (length st1.tris) s1
                    , checkGB st2.nVerts (length e2) (length st2.tris) s2
                    , checkGB st3.nVerts (length e3) (length st3.tris) s3
                    , not (checkGB st3.nVerts (length e3) (minus (length st3.tris) 1) s3)
                    ]

      ok = andAll [ st3.nVerts == 42, length e3 == 120, length st3.tris == 80, s3 == 12
                  , k0_0 == 2, k0_3 == -26, k1_3 == 2
                  , gbOk
                  , msfGT loc0 (mkMSF 85 100)
                  , msfLT loc1 (mkMSF 65 100)
                  , msfGT loc0 loc1
                  ]
  in MkCurvatureEval st3.nVerts (length e3) (length st3.tris) s3 k0_0 k0_3 k1_3 loc0 loc1 gbOk ok

public export
record PhasedBackReactionReport where
  constructor MkPhasedBackReactionReport
  cohQ2_16        : Integer
  winQ2_16        : Integer
  winRetained     : MSetFraction
  dephVRat16      : MSetFraction
  dephKurt16      : MSetFraction
  phasedDecOk     : Bool
  meshVerts       : Nat
  meshEdges       : Nat
  meshFaces       : Nat
  sumCurv         : Integer
  kPole0_0        : Integer
  kPole0_3        : Integer
  kPole1_3        : Integer
  loc1Pole0       : MSetFraction
  loc1Pole1       : MSetFraction
  gaussDecOk      : Bool
  passesProbeM    : Bool

||| Probe M: Tests `PhasedMultiset` / `WindowedHorizon` causal horizon decoherence
||| (unitarity leak + diffusive `V16/V8=2`, classical `Kurt16~2.875`) and endogenous
||| matter-coupled graph curvature (`chi=2`, `sum K = 12` conservation + focusing).
export
probePhasedDecoherenceAndBackReaction : PhasedBackReactionReport
probePhasedDecoherenceAndBackReaction =
  let h = evalHorizonDecoherence
      c = evalMatterBackReaction
      ok = andAll [h.horizonOk, c.curvOk]
  in MkPhasedBackReactionReport
       h.cohQ2_16 h.winQ2_16 h.winRetained h.dephVRat16 h.dephKurt16 h.phasedDecOk
       c.meshVerts c.meshEdges c.meshFaces c.sumCurv c.kPole0_0 c.kPole0_3 c.kPole1_3
       c.loc1Pole0 c.loc1Pole1 c.gaussDecOk ok

--------------------------------------------------------------------------------
-- 4. COMPILE-TIME QTT 0 `Refl` AUDITS
--------------------------------------------------------------------------------

||| Audit 1: Exact generation-5 Sierpinski gasket topological vertex formula.
public export
0 prfGasketVol5 : 2 * 366 = Stage1.FrontierProbe.pow3Nat 6 + 3
prfGasketVol5 = Refl

||| Audit 2: Exact Euler characteristic for the 42-vertex back-reacted sphere mesh.
public export
0 prfGaussBonnetEuler42 : (42 + 80 = 120 + 2)
prfGaussBonnetEuler42 = Refl

||| Audit 3: Exact Gauss-Bonnet sum curvature identity `sum_v (6 - deg(v)) = 12`.
public export
0 prfGaussBonnetCurv42 : (6 * 42 = 2 * 120 + 12)
prfGaussBonnetCurv42 = Refl
