module Stage1.DynamicInteractionProbe

import Data.List
import Data.Nat
import Decidable.Equality
import public Stage0.Box
import public Stage0.BoxInt
import public Stage0.SignedFraction
import public Stage0.HereditaryMSet
import public Stage1.Bridge.LaurentAntiMSetBridge
import public Stage1.ConvolutionAdmissibility
import public Stage1.PhasedMultiset
import public Stage1.FuelProbe
import public Stage1.QuantumManyBodyProbe
import public Stage1.EmergentCouplingProbe

%default total

private
repeatStep : Nat -> (a -> a) -> a -> a
repeatStep Z     _ x = x
repeatStep (S k) f x = repeatStep k f (f x)

private
powInt : Integer -> Nat -> Integer
powInt _ Z     = 1
powInt b (S k) = b * powInt b k

private
reduceBigMSF : MSetFraction -> MSetFraction
reduceBigMSF = reduceMSF

--------------------------------------------------------------------------------
-- 1. PROBE N: CONTACT-INTERACTING 2-PARTICLE SCATTERING VIA MAXEL ALGEBRA
--------------------------------------------------------------------------------

||| Cartesian outer product `><` on signed coordinate multisets, building an
||| exact separable two-particle product state `|psi1> >< |psi2>`.
public export
outerPairBox : Ord a => Ord b => Box BoxInt a -> Box BoxInt b -> Box BoxInt (a, b)
outerPairBox = tensorBox

||| Maxel transposition swapping pair coordinates `(a, b) -> (b, a)`.
public export
transposePairMaxel : Ord a => Ord b => Box BoxInt (a, b) -> Box BoxInt (b, a)
transposePairMaxel = transposeBox

||| Pixel-fusion Maxel multiplication contracting matching inner keys `b1 == b2`
||| (`[a, b1] * [b2, c] -> [a, c]`) with automatic zero-pruning annihilation.
public export
composePairMaxel : Ord a => Ord b => Ord c =>
                   Box BoxInt (a, b) -> Box BoxInt (b, c) -> Box BoxInt (a, c)
composePairMaxel = composeBox

private
diagMaskOf : PairSpinor1D -> PairSpinor1D
diagMaskOf =
  foldBox (\k@((x1, _), (x2, _)), w, acc =>
            if unwrapBox w == 0 || x1 /= x2
              then acc
              else setBox k (intToBoxInt 1) acc)
          BoxLeaf

||| Unitary contact-reflection interaction `psi - 2 * (psi .*. Delta)` inverting
||| Black/Red polarity on the coincidence diagonal `x1 == x2`.
public export
applyContactMask : PairSpinor1D -> PairSpinor1D
applyContactMask psi =
  let delta = diagMaskOf psi
  in subBox psi (scaleBox (intToBoxInt 2) (hadamardBox psi delta))

||| Single discrete-time 2-particle walk step with coin `[[a, b], [c, d]]` and
||| chiral shifts applied to both particles, followed optionally by contact reflection.
public export
stepPairCoin1D : (a, b, c, d : Integer) -> Bool -> PairSpinor1D -> PairSpinor1D
stepPairCoin1D a b c d useContact st =
  let mid : PairSpinor1D
      mid = foldBox (\((x1, s1), p2), (MkBoxInt w), acc =>
                      if w == 0
                        then acc
                        else
                          let cL = if s1 then b else a
                              cR = if s1 then d else c
                              a1 = addAtKeyBox ((x1 - 1, False), p2) (intToBoxInt (cL * w)) acc
                          in addAtKeyBox ((x1 + 1, True), p2) (intToBoxInt (cR * w)) a1)
                    (the PairSpinor1D BoxLeaf)
                    st
      moved : PairSpinor1D
      moved = foldBox (\(p1, (x2, s2)), (MkBoxInt w), acc =>
                        if w == 0
                          then acc
                          else
                            let cL = if s2 then b else a
                                cR = if s2 then d else c
                                a1 = addAtKeyBox (p1, (x2 - 1, False)) (intToBoxInt (cL * w)) acc
                            in addAtKeyBox (p1, (x2 + 1, True)) (intToBoxInt (cR * w)) a1)
                      (the PairSpinor1D BoxLeaf)
                      mid
  in if useContact then applyContactMask moved else moved

||| Exact rational Born purity `Tr(rho_1^2) = ||Psi * Psi^T||_2^2 / Q2^2` where `1`
||| certifies a separable product state and `< 1` proves dynamical entanglement.
public export
pairPurity : PairSpinor1D -> MSetFraction
pairPurity psi =
  let q2     = unwrapBox (dotBox psi psi)
      rho1   = composePairMaxel psi (transposePairMaxel psi)
      trRho2 = unwrapBox (dotBox rho1 rho1)
      den    = integerToNat (max (the Integer 1) (q2 * q2))
  in reduceBigMSF (mkMSF (intToBoxInt trRho2) den)

private
record PairDiagAccum where
  constructor MkPairDiagAccum
  nearQ2Acc : Integer
  sep2Acc   : Integer

private
record PairDiagStats where
  constructor MkPairDiagStats
  q2       : Integer
  diagFrac : MSetFraction
  nearFrac : MSetFraction
  meanSep2 : MSetFraction

private
pairDiagStats : PairSpinor1D -> PairDiagStats
pairDiagStats psi =
  let q2      = unwrapBox (dotBox psi psi)
      diagBox = hadamardBox psi (diagMaskOf psi)
      diagQ2  = unwrapBox (dotBox diagBox diagBox)
      acc     = foldBox (\((x1, _), (x2, _)), (MkBoxInt w), st =>
                          let p   = w * w
                              dx  = x1 - x2
                              nr  = if abs dx <= 2 then p else 0
                          in MkPairDiagAccum (st.nearQ2Acc + nr) (st.sep2Acc + p * dx * dx))
                        (MkPairDiagAccum 0 0)
                        psi
      den = integerToNat (max (the Integer 1) q2)
  in MkPairDiagStats q2
       (reduceBigMSF (mkMSF (intToBoxInt diagQ2) den))
       (reduceBigMSF (mkMSF (intToBoxInt acc.nearQ2Acc) den))
       (reduceBigMSF (mkMSF (intToBoxInt acc.sep2Acc) den))

private
relDistPureMSet : PairSpinor1D -> PureMultiset
relDistPureMSet psi =
  MkHMSet (foldBox (\((x1, _), (x2, _)), (MkBoxInt w), acc =>
                     if w == 0
                       then acc
                       else addAtKeyBox (signedKeyM (x1 - x2)) (intToBoxInt (w * w)) acc)
                   BoxLeaf
                   psi)

private
doublonWindowMask : Stage1.PhasedMultiset.Multiset (MkPhase 1 (WindowedHorizon 5) 5) BoxInt
doublonWindowMask =
  let b = foldl (\acc, k => addAtKeyBox (signedKeyM k) (intToBoxInt 1) acc)
                BoxLeaf
                [the Integer (-2), -1, 0, 1, 2]
  in MkPhasedMSet (MkHMSet b)

private
record PhasedWindowCheck where
  constructor MkPhasedWindowCheck
  windowedDoublonFrac : MSetFraction
  phasedReflectOk     : Bool
  phasedSliceOk       : Bool

private
verifyPhasedContactAndWindow : PairSpinor1D -> MSetFraction -> PhasedWindowCheck
verifyPhasedContactAndWindow dirCont8 expectedNear =
  let relM = relDistPureMSet dirCont8
      phStatic : Stage1.PhasedMultiset.Multiset (MkPhase 1 (StaticHorizon (-16) 16) 33) BoxInt
      phStatic = MkPhasedMSet relM
      phOpen   : Stage1.PhasedMultiset.Multiset (MkPhase 1 OpenFuture 65) BoxInt
      phOpen   = MkPhasedMSet relM
      phCore   : Stage1.PhasedMultiset.Multiset (MkPhase 1 (WindowedHorizon 5) 5) BoxInt
      phCore   = hadamardSlicePhased phOpen doublonWindowMask

      totW     = unwrapBox (sumBoundedPhased phStatic)
      winW     = unwrapBox (sumBoundedPhased phCore)
      winFrac  = reduceBigMSF (mkMSF (intToBoxInt winW) (integerToNat (max (the Integer 1) totW)))

      orig : Stage1.PhasedMultiset.Multiset (MkPhase 1 (StaticHorizon (-4) 4) 9) BoxInt
      orig = MkPhasedMSet (MkHMSet (setBox (signedKeyM 0) (intToBoxInt 3)
                                    (setBox (signedKeyM 1) (intToBoxInt 4) BoxLeaf)))
      mask : Stage1.PhasedMultiset.Multiset (MkPhase 1 (StaticHorizon (-4) 4) 9) BoxInt
      mask = MkPhasedMSet (MkHMSet (setBox (signedKeyM 0) (intToBoxInt 1) BoxLeaf))
      refl = contactReflectPhased orig mask

      reflOk = andAll [ unwrapBox (dotBoundedPhased refl refl) == unwrapBox (dotBoundedPhased orig orig)
                      , unwrapBox (dotBoundedPhased refl orig) == 7
                      ]
      slcOk  = andAll [ winFrac == expectedNear
                      , case recognizeCanonicalPhased phCore of
                          Yes _ => True
                          No  _ => False
                      ]
  in MkPhasedWindowCheck winFrac reflOk slcOk

private
record CollideEval where
  constructor MkCollideEval
  freePur1  : MSetFraction
  freePur8  : MSetFraction
  contPur1  : MSetFraction
  contPur8  : MSetFraction
  collideOk : Bool

private
evalCollidingEntanglement : CollideEval
evalCollidingEntanglement =
  let p1 = setBox (the (Integer, Bool) (-1, True)) (intToBoxInt 1) BoxLeaf
      p2 = setBox (the (Integer, Bool) (1, False)) (intToBoxInt 1) BoxLeaf
      s0 = outerPairBox p1 p2

      f1 = stepPairCoin1D 1 1 1 (-1) False s0
      f8 = repeatStep 7 (stepPairCoin1D 1 1 1 (-1) False) f1
      c1 = stepPairCoin1D 1 1 1 (-1) True s0
      c8 = repeatStep 7 (stepPairCoin1D 1 1 1 (-1) True) c1

      fp1 = pairPurity f1
      fp8 = pairPurity f8
      cp1 = pairPurity c1
      cp8 = pairPurity c8

      qExp = powInt 4 8
      ok = andAll [ unwrapBox (dotBox f8 f8) == qExp
                  , unwrapBox (dotBox c8 c8) == qExp
                  , fp1 == oneMSF
                  , fp8 == oneMSF
                  , cp1 == mkMSF 1 2
                  , msfLT cp8 (mkMSF 30 100)
                  ]
  in MkCollideEval fp1 fp8 cp1 cp8 ok

private
record DoublonEval where
  constructor MkDoublonEval
  hadFreeNear  : MSetFraction
  hadContNear  : MSetFraction
  hadContPur   : MSetFraction
  dirFreeNear  : MSetFraction
  dirContNear  : MSetFraction
  dirFreeSep2  : MSetFraction
  dirContSep2  : MSetFraction
  alignFreeSep : MSetFraction
  alignContSep : MSetFraction
  phasedWinOk  : Bool
  phasedReflOk : Bool
  doublonOk    : Bool

private
evalDoublonBinding : DoublonEval
evalDoublonBinding =
  let pL  = setBox (the (Integer, Bool) (0, False)) (intToBoxInt 1) BoxLeaf
      pR  = setBox (the (Integer, Bool) (0, True))  (intToBoxInt 1) BoxLeaf
      opp = outerPairBox pL pR
      aln = outerPairBox pL pL

      hf8 = repeatStep 8 (stepPairCoin1D 1 1 1 (-1) False) opp
      hc8 = repeatStep 8 (stepPairCoin1D 1 1 1 (-1) True)  opp
      df8 = repeatStep 8 (stepPairCoin1D 3 4 4 (-3) False) opp
      dc8 = repeatStep 8 (stepPairCoin1D 3 4 4 (-3) True)  opp
      af8 = repeatStep 8 (stepPairCoin1D 1 1 1 (-1) False) aln
      ac8 = repeatStep 8 (stepPairCoin1D 1 1 1 (-1) True)  aln

      shf = pairDiagStats hf8
      shc = pairDiagStats hc8
      sdf = pairDiagStats df8
      sdc = pairDiagStats dc8
      saf = pairDiagStats af8
      sac = pairDiagStats ac8
      pHc = pairPurity hc8

      pw = verifyPhasedContactAndWindow dc8 sdc.nearFrac

      ok = andAll [ shf.q2 == powInt 4 8
                  , shc.q2 == powInt 4 8
                  , sdf.q2 == powInt 625 8
                  , sdc.q2 == powInt 625 8
                  , msfGT shc.nearFrac (mkMSF 50 100)
                  , msfLT shf.nearFrac (mkMSF 35 100)
                  , msfLT shc.meanSep2 shf.meanSep2
                  , msfLT pHc (mkMSF 25 100)
                  , msfGT sdc.nearFrac (mkMSF 70 100)
                  , msfLT sdf.nearFrac (mkMSF 45 100)
                  , msfLT sdc.meanSep2 (mkMSF 16 1)
                  , msfLT sdc.meanSep2 sdf.meanSep2
                  , msfGT sac.meanSep2 saf.meanSep2
                  , pw.phasedSliceOk
                  , pw.phasedReflectOk
                  ]
  in MkDoublonEval shf.nearFrac shc.nearFrac pHc sdf.nearFrac sdc.nearFrac
       sdf.meanSep2 sdc.meanSep2 saf.meanSep2 sac.meanSep2 pw.phasedSliceOk pw.phasedReflectOk ok

public export
record ContactScatteringReport where
  constructor MkContactScatteringReport
  collFreePur1    : MSetFraction
  collFreePur8    : MSetFraction
  collContPur1    : MSetFraction
  collContPur8    : MSetFraction
  hadFreeNear8    : MSetFraction
  hadContNear8    : MSetFraction
  hadContPur8     : MSetFraction
  dirFreeNear8    : MSetFraction
  dirContNear8    : MSetFraction
  dirFreeSep2     : MSetFraction
  dirContSep2     : MSetFraction
  alignFreeSep2   : MSetFraction
  alignContSep2   : MSetFraction
  phasedWindowOk  : Bool
  phasedReflectOk : Bool
  passesProbeN    : Bool

||| Probe N: Tests dynamical entanglement generation from separable collisions,
||| spin-dependent molecular doublon binding vs. aligned-spin repulsion via Maxel
||| pixel contraction (`composePairMaxel`), `applyContactMask`, and `WindowedHorizon` slicing.
export
probeContactScattering : ContactScatteringReport
probeContactScattering =
  let c  = evalCollidingEntanglement
      d  = evalDoublonBinding
      ok = andAll [c.collideOk, d.doublonOk]
  in MkContactScatteringReport
       c.freePur1 c.freePur8 c.contPur1 c.contPur8
       d.hadFreeNear d.hadContNear d.hadContPur
       d.dirFreeNear d.dirContNear d.dirFreeSep2 d.dirContSep2
       d.alignFreeSep d.alignContSep d.phasedWinOk d.phasedReflOk ok

--------------------------------------------------------------------------------
-- 2. PROBE O: SIMPLEX-STAGGERED G_3 QUANTUM BACK-REACTION & UV SCALE SPECTRUM
--------------------------------------------------------------------------------

||| Constructive witness that a 3x3 symmetric integer Grover coin `diag*I + off*(J - I)`
||| satisfies `G_3^T G_3 = 9 I` (column quadrance 9 and mutual orthogonality).
public export
data IsGrover3Unitary : (diag, off : Integer) -> Type where
  MkGrover3Unitary : (diag * diag + 2 * off * off = 9)
                  -> (2 * diag * off + off * off = 0)
                  -> IsGrover3Unitary diag off

||| Total constructive `Dec` recognizer for 3x3 integer Grover coins.
public export
recognizeGrover3Unitary : (diag, off : Integer) -> Dec (IsGrover3Unitary diag off)
recognizeGrover3Unitary diag off =
  case decEq (diag * diag + 2 * off * off) 9 of
    No c1 => No (\(MkGrover3Unitary p1 _) => c1 p1)
    Yes p1 =>
      case decEq (2 * diag * off + off * off) 0 of
        No c2 => No (\(MkGrover3Unitary _ p2) => c2 p2)
        Yes p2 => Yes (MkGrover3Unitary p1 p2)

||| Oriented simplicial triangle face tagged with its `RetroBoundedHorizon` UV subdivision depth.
public export
record UVTri where
  constructor MkUVTri
  vA      : Nat
  vB      : Nat
  vC      : Nat
  uvDepth : Nat

||| Quantum amplitude carried on oriented half-edges `(u, v)`.
public export
HalfEdgeSpinor : Type
HalfEdgeSpinor = Box BoxInt (Nat, Nat)

||| Single simplex-staggered quantum walk tick:
||| 1. Apply the 3x3 integer Grover coin `G_3` (`2*S - 3*w`, scaling `Q2 * 9`)
|||    locally within every triangle `(a, b, c)`.
||| 2. Shift across shared edges via `transposePairMaxel` (`(u, v) -> (v, u)`).
||| Exact unitarity holds for arbitrary triangulations and vertex degrees.
public export
stepG3HalfEdgeWalk : List UVTri -> HalfEdgeSpinor -> HalfEdgeSpinor
stepG3HalfEdgeWalk tris st =
  let coined : HalfEdgeSpinor
      coined = foldl (\acc, (MkUVTri a b c _) =>
                       let w1 = unwrapBox (lookupBox (a, b) st)
                           w2 = unwrapBox (lookupBox (b, c) st)
                           w3 = unwrapBox (lookupBox (c, a) st)
                       in if (w1 == 0) && (w2 == 0) && (w3 == 0)
                            then acc
                            else
                              let s  = w1 + w2 + w3
                                  o1 = 2 * s - 3 * w1
                                  o2 = 2 * s - 3 * w2
                                  o3 = 2 * s - 3 * w3
                                  a1 = if o1 == 0 then acc else addAtKeyBox (a, b) (intToBoxInt o1) acc
                                  a2 = if o2 == 0 then a1  else addAtKeyBox (b, c) (intToBoxInt o2) a1
                              in if o3 == 0 then a2 else addAtKeyBox (c, a) (intToBoxInt o3) a2)
                     (the HalfEdgeSpinor BoxLeaf)
                     tris
  in transposePairMaxel coined

private
record UVMeshState where
  constructor MkUVMeshState
  uvTris   : List UVTri
  uvNVerts : Nat

private
subdivideByBornUV : Nat -> Integer -> Integer -> UVMeshState -> HalfEdgeSpinor -> UVMeshState
subdivideByBornUV uvCap threshNum threshDen mesh st =
  let q2Tot = unwrapBox (dotBox st st)
  in go mesh.uvTris mesh.uvNVerts [] q2Tot
  where
    go : List UVTri -> Nat -> List UVTri -> Integer -> UVMeshState
    go [] nv acc _ = MkUVMeshState (reverse acc) nv
    go (tri@(MkUVTri a b c d) :: rest) nv acc q2Tot =
      let w1  = unwrapBox (lookupBox (a, b) st)
          w2  = unwrapBox (lookupBox (b, c) st)
          w3  = unwrapBox (lookupBox (c, a) st)
          q2T = w1 * w1 + w2 * w2 + w3 * w3
      in if (d < uvCap) && (q2T * threshDen >= q2Tot * threshNum)
           then
             let t1 = MkUVTri c a nv (S d)
                 t2 = MkUVTri b c nv (S d)
                 t3 = MkUVTri a b nv (S d)
             in go rest (S nv) (t1 :: t2 :: t3 :: acc) q2Tot
           else go rest nv (tri :: acc) q2Tot

private
uvNormEdge : Nat -> Nat -> (Nat, Nat)
uvNormEdge u v = if u <= v then (u, v) else (v, u)

private
uvTrisEdges : List UVTri -> List (Nat, Nat)
uvTrisEdges tris =
  let eBox = foldl (\acc, (MkUVTri a b c _) =>
                     setBox (uvNormEdge c a) (intToBoxInt 1)
                       (setBox (uvNormEdge b c) (intToBoxInt 1)
                         (setBox (uvNormEdge a b) (intToBoxInt 1) acc)))
                   (the (Box BoxInt (Nat, Nat)) BoxLeaf)
                   tris
  in foldBox (\e, w, acc => if isZero w then acc else e :: acc) [] eBox

private
uvDegreeBox : List (Nat, Nat) -> Box BoxInt Nat
uvDegreeBox =
  foldl (\acc, (u, v) =>
          addAtKeyBox u (intToBoxInt 1) (addAtKeyBox v (intToBoxInt 1) acc))
        BoxLeaf

private
uvSumCurvRange : Nat -> Box BoxInt Nat -> Integer
uvSumCurvRange Z     _      = 0
uvSumCurvRange (S k) degBox = (6 - unwrapBox (lookupBox k degBox)) + uvSumCurvRange k degBox

private
record UVBFSAcc where
  constructor MkUVBFSAcc
  visAcc   : Box BoxInt Nat
  frontAcc : Box BoxInt Nat

private
uvBfsDist : Nat -> Nat -> List (Nat, Nat) -> Box BoxInt Nat
uvBfsDist maxDepth start edges =
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
                                    then MkUVBFSAcc (setBox v (intToBoxInt nextEnc) acc.visAcc)
                                                    (setBox v (intToBoxInt 1) acc.frontAcc)
                                    else acc
                            in if (fv > 0) && (unwrapBox (lookupBox u acc1.visAcc) == 0)
                                 then MkUVBFSAcc (setBox u (intToBoxInt nextEnc) acc1.visAcc)
                                                 (setBox u (intToBoxInt 1) acc1.frontAcc)
                                 else acc1)
                          (MkUVBFSAcc vis BoxLeaf)
                          edges
          in go k (nextEnc + 1) res.visAcc res.frontAcc

private
uvDistFromBox : Nat -> Box BoxInt Nat -> Integer
uvDistFromBox v distBox =
  let r = unwrapBox (lookupBox v distBox)
  in if r > 0 then r - 1 else 0

private
uvSpectrumPhased : List UVTri ->
                   Stage1.PhasedMultiset.Multiset (MkPhase 1 (RetroBoundedHorizon 3) 4) BoxInt
uvSpectrumPhased tris =
  let b = foldl (\acc, (MkUVTri _ _ _ d) =>
                  addAtKeyBox (signedKeyM (negate (natToInteger d))) (intToBoxInt 1) acc)
                BoxLeaf
                tris
  in MkPhasedMSet (MkHMSet b)

private
pole0ProbAt : HalfEdgeSpinor -> MSetFraction
pole0ProbAt st =
  let q2   = unwrapBox (dotBox st st)
      at0  = foldBox (\(u, _), (MkBoxInt w), acc => if u == 0 then acc + w * w else acc)
                     (the Integer 0)
                     st
  in reduceBigMSF (mkMSF (intToBoxInt at0) (integerToNat (max (the Integer 1) q2)))

private
northHemisphereProb : List UVTri -> HalfEdgeSpinor -> MSetFraction
northHemisphereProb tris st =
  let edges = uvTrisEdges tris
      d0    = uvBfsDist 12 0 edges
      d1    = uvBfsDist 12 1 edges
      q2    = unwrapBox (dotBox st st)
      nQ2   = foldBox (\(u, _), (MkBoxInt w), acc =>
                        if uvDistFromBox u d0 < uvDistFromBox u d1
                          then acc + w * w
                          else acc)
                      (the Integer 0)
                      st
  in reduceBigMSF (mkMSF (intToBoxInt nQ2) (integerToNat (max (the Integer 1) q2)))

private
record WalkTrajectoryEval where
  constructor MkWalkTrajectoryEval
  finalQ2_10      : Integer
  at0Tick10       : MSetFraction
  avgNorth7to12   : MSetFraction
  finalVerts      : Nat
  finalEdges      : Nat
  finalFaces      : Nat
  finalSumK       : Integer
  finalKPole0     : Integer
  finalKPole1     : Integer
  uvFaceTotal     : Integer
  uvDepth2Count   : Integer
  gbDecOk         : Bool

private
octInitMesh : UVMeshState
octInitMesh =
  MkUVMeshState
    [ MkUVTri 0 2 3 0, MkUVTri 0 3 4 0, MkUVTri 0 4 5 0, MkUVTri 0 5 2 0
    , MkUVTri 1 3 2 0, MkUVTri 1 4 3 0, MkUVTri 1 5 4 0, MkUVTri 1 2 5 0
    ]
    6

private
runTrajLoop : Nat -> Nat -> Bool -> UVMeshState -> HalfEdgeSpinor ->
              Integer -> MSetFraction -> MSetFraction -> WalkTrajectoryEval
runTrajLoop Z _ _ mesh _ q2_10 at0_10 northSum =
  let edges    = uvTrisEdges mesh.uvTris
      degBox   = uvDegreeBox edges
      fCount   = length mesh.uvTris
      eCount   = length edges
      sK       = uvSumCurvRange mesh.uvNVerts degBox
      k0       = 6 - unwrapBox (lookupBox (the Nat 0) degBox)
      k1       = 6 - unwrapBox (lookupBox (the Nat 1) degBox)
      avgN     = reduceBigMSF (divMSF northSum (mkMSF 6 1))
      uvSpec   = uvSpectrumPhased mesh.uvTris
      uvTot    = unwrapBox (sumBoundedPhased uvSpec)
      uvD2     = case uvSpec of
                   MkPhasedMSet (MkHMSet b) => unwrapBox (lookupBox (signedKeyM (-2)) b)
      gbOk     = case recognizeGaussBonnet2D mesh.uvNVerts eCount fCount sK of
                   Yes (MkGaussBonnetSphere2D _ _) => True
                   No  _                           => False
  in MkWalkTrajectoryEval q2_10 at0_10 avgN mesh.uvNVerts eCount fCount sK k0 k1 uvTot uvD2 gbOk
runTrajLoop (S rem) tick isDynamic mesh st q2_10 at0_10 northSum =
  let st1   = stepG3HalfEdgeWalk mesh.uvTris st
      mesh1 = if isDynamic && (tick == 2 || tick == 4 || tick == 6)
                then subdivideByBornUV 3 1 8 mesh st1
                else mesh
      q2Now = if tick == 10 then unwrapBox (dotBox st1 st1) else q2_10
      a0Now = if tick == 10 then pole0ProbAt st1 else at0_10
      nSum' = if tick >= 7
                then reduceBigMSF (addMSF northSum (northHemisphereProb mesh1.uvTris st1))
                else northSum
  in runTrajLoop rem (S tick) isDynamic mesh1 st1 q2Now a0Now nSum'

public export
record QuantumBackReactionReport where
  constructor MkQuantumBackReactionReport
  symDynQ2_10        : Integer
  dipDynQ2_10        : Integer
  symStatAt0_10      : MSetFraction
  symDynAt0_10       : MSetFraction
  avgNorthSymStat    : MSetFraction
  avgNorthSymDyn     : MSetFraction
  avgNorthDipStat    : MSetFraction
  avgNorthDipDyn     : MSetFraction
  symVerts           : Nat
  symEdges           : Nat
  symFaces           : Nat
  symSumK            : Integer
  symKPole0          : Integer
  symKPole1          : Integer
  symUVDepth2Faces   : Integer
  dipVerts           : Nat
  dipKPole0          : Integer
  dipKPole1          : Integer
  grover3AndRegimeOk : Bool
  passesProbeO       : Bool

||| Probe O: Tests two-way Born quantum-to-geometry back-reaction using an exact
||| integer 3x3 Grover coin `G_3` (`Q2 * 9`) on oriented triangles + `transposePairMaxel`,
||| `RetroBoundedHorizon` UV scale tracking, Discrete Gauss-Bonnet invariance (`chi=2, sumK=12`),
||| and interference-sculpted curvature wells (`Pole0-Sym` vs. `Pole0-Dipole`).
export
probeSimplexBackReaction : QuantumBackReactionReport
probeSimplexBackReaction =
  let sym0 : HalfEdgeSpinor
      sym0 = setBox (the (Nat, Nat) (0, 2)) (intToBoxInt 1)
               (setBox (the (Nat, Nat) (0, 3)) (intToBoxInt 1)
                 (setBox (the (Nat, Nat) (0, 4)) (intToBoxInt 1)
                   (setBox (the (Nat, Nat) (0, 5)) (intToBoxInt 1) BoxLeaf)))

      dip0 : HalfEdgeSpinor
      dip0 = setBox (the (Nat, Nat) (0, 2)) (intToBoxInt 1)
               (setBox (the (Nat, Nat) (0, 3)) (intToBoxInt (-1)) BoxLeaf)

      symStat = runTrajLoop 12 1 False octInitMesh sym0 0 zeroMSF zeroMSF
      symDyn  = runTrajLoop 12 1 True  octInitMesh sym0 0 zeroMSF zeroMSF
      dipStat = runTrajLoop 12 1 False octInitMesh dip0 0 zeroMSF zeroMSF
      dipDyn  = runTrajLoop 12 1 True  octInitMesh dip0 0 zeroMSF zeroMSF

      g3RegOk = andAll
                  [ case recognizeGrover3Unitary (-1) 2 of
                      Yes (MkGrover3Unitary _ _) => True
                      No  _                      => False
                  , case recognizeGrover3Unitary 1 2 of
                      Yes _ => False
                      No  _ => True
                  , case recognizeCanConvolve (BoundedHorizon 12) (RetroBoundedHorizon 3) of
                      Yes _ => True
                      No  _ => False
                  , case recognizeCanConvolve OpenFuture (RetroBoundedHorizon 3) of
                      Yes _ => False
                      No  _ => True
                  ]

      passOk = andAll
                 [ symDyn.finalQ2_10 == 4 * powInt 9 10
                 , dipDyn.finalQ2_10 == 2 * powInt 9 10
                 , msfGT symStat.at0Tick10 (mkMSF 95 100)
                 , msfLT symDyn.at0Tick10  (mkMSF 50 100)
                 , msfGT symDyn.avgNorth7to12 symStat.avgNorth7to12
                 , symDyn.finalVerts == 14
                 , symDyn.finalEdges == 36
                 , symDyn.finalFaces == 24
                 , symDyn.finalSumK == 12
                 , symDyn.finalKPole0 == -6
                 , symDyn.finalKPole1 == 2
                 , symDyn.uvFaceTotal == 24
                 , symDyn.uvDepth2Count > 0
                 , symDyn.gbDecOk
                 , dipDyn.finalVerts == 12
                 , dipDyn.finalEdges == 30
                 , dipDyn.finalFaces == 20
                 , dipDyn.finalSumK == 12
                 , dipDyn.finalKPole0 == 0
                 , dipDyn.finalKPole1 == 0
                 , dipDyn.gbDecOk
                 , msfLT dipDyn.avgNorth7to12 dipStat.avgNorth7to12
                 , g3RegOk
                 ]
  in MkQuantumBackReactionReport
       symDyn.finalQ2_10 dipDyn.finalQ2_10
       symStat.at0Tick10 symDyn.at0Tick10
       symStat.avgNorth7to12 symDyn.avgNorth7to12
       dipStat.avgNorth7to12 dipDyn.avgNorth7to12
       symDyn.finalVerts symDyn.finalEdges symDyn.finalFaces
       symDyn.finalSumK symDyn.finalKPole0 symDyn.finalKPole1
       symDyn.uvDepth2Count dipDyn.finalVerts dipDyn.finalKPole0 dipDyn.finalKPole1
       g3RegOk passOk

--------------------------------------------------------------------------------
-- 3. COMPILE-TIME QTT 0 `Refl` AUDITS
--------------------------------------------------------------------------------

||| Audit 1: Finite forward epoch + retrograde UV horizon convolves into compact `StaticHorizon [-3, 12]`.
public export
0 prfBoundRetroConv :
  admissibleConvolution (BoundedHorizon 12) (RetroBoundedHorizon 3) = Just (StaticHorizon (-3) 12)
prfBoundRetroConv = Refl

||| Audit 2: Opposing unbounded `OpenFuture` + `RetroBoundedHorizon` convolution is statically blocked (`Nothing`).
public export
0 prfOpenRetroBlocked :
  admissibleConvolution OpenFuture (RetroBoundedHorizon 3) = Nothing
prfOpenRetroBlocked = Refl

||| Audit 3: Exact 3x3 integer Grover coin column quadrance identity (`(-1)^2 + 2^2 + 2^2 = 9`).
public export
0 prfGrover3Norm : ((-1) * (-1) + 2 * 2 + 2 * 2 = 9)
prfGrover3Norm = Refl

||| Audit 4: Exact 3x3 integer Grover coin off-diagonal orthogonality (`2*(-1)*2 + 2^2 = 0`).
public export
0 prfGrover3Ortho : (2 * (-1) * 2 + 2 * 2 = 0)
prfGrover3Ortho = Refl
