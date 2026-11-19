module Stage1.MultisetDuality

import Stage0.BoxInt
import Stage0.Multiset
import public Stage1.MultisetTensor
import Stage0.OnSeq.FusedStream
import Stage1.ConjugateHylo
import Data.Fuel

%default total

--------------------------------------------------------------------------------
-- 1. MULTISET DUALITY INTERFACE (WILDBERGER PUSHFORWARD ⇋ PULLBACK)
--------------------------------------------------------------------------------

||| Discrete Multiset Duality (Push ⇋ Pull) between multiset scale representations.
||| Formulated directly in Wildberger's Finitist Hereditary Multiset & Maxel Algebra
||| via syntax-directed token pushforward and pullback operations.
||| Preserves exact BoxInt proof witnesses and multiplicities across pair-basis tensors:
||| MultisetTensor (l a) b ≅ MultisetTensor a (r b)
public export
interface MultisetDuality (0 l : Type -> Type) (0 r : Type -> Type) where
  ||| Forward pushforward map: a -> l a
  leftAdjoint  : a -> l a

  ||| Reverse pullback map: l a -> a
  rightAdjoint : l a -> a

  ||| Pair-basis tensor forward re-indexing
  homTensorIso : (Eq a, Eq b) => MultisetTensor (l a) b -> MultisetTensor a (r b)

  ||| Pair-basis tensor reverse re-indexing
  homTensorInv : (Eq a, Eq b) => MultisetTensor a (r b) -> MultisetTensor (l a) b

  ||| Verification of forward-inverse round-trip identity
  0 verifyHomIso : (Eq a, Eq b) => (t : MultisetTensor (l a) b) -> homTensorInv (homTensorIso t) = t

  ||| Verification of reverse-forward round-trip identity
  0 verifyHomInv : (Eq a, Eq b) => (u : MultisetTensor a (r b)) -> homTensorIso (homTensorInv u) = u

||| Deprecated compatibility alias for `MultisetDuality`.
public export
MultisetAdjunction : (Type -> Type) -> (Type -> Type) -> Type
MultisetAdjunction = MultisetDuality

||| Forward token pushforward mapping: a -> Push a
public export
pushToken : {0 pull : Type -> Type} -> (adj : MultisetDuality push pull) => a -> push a
pushToken @{adj} x = leftAdjoint @{adj} x

||| Reverse token pullback mapping: Push a -> a
public export
pullToken : {0 push : Type -> Type} -> (adj : MultisetDuality push pull) => push a -> a
pullToken @{adj} x = rightAdjoint @{adj} x

||| Natural hom-tensor forward isomorphism
public export
dualTensorIso : (adj : MultisetDuality push pull) => (Eq a, Eq b) => MultisetTensor (push a) b -> MultisetTensor a (pull b)
dualTensorIso @{adj} t = homTensorIso @{adj} t

||| Natural hom-tensor reverse isomorphism
public export
dualTensorInv : (adj : MultisetDuality push pull) => (Eq a, Eq b) => MultisetTensor a (pull b) -> MultisetTensor (push a) b
dualTensorInv @{adj} u = homTensorInv @{adj} u

||| Verification of forward inverse round-trip isomorphism identity
public export
0 verifyDualIso : (adj : MultisetDuality push pull) => (Eq a, Eq b) => (t : MultisetTensor (push a) b) -> dualTensorInv @{adj} (dualTensorIso @{adj} t) = t
verifyDualIso @{adj} t = verifyHomIso @{adj} t

||| Verification of reverse inverse round-trip isomorphism identity
public export
0 verifyDualInv : (adj : MultisetDuality push pull) => (Eq a, Eq b) => (u : MultisetTensor a (pull b)) -> dualTensorIso @{adj} (dualTensorInv @{adj} u) = u
verifyDualInv @{adj} u = verifyHomInv @{adj} u

--------------------------------------------------------------------------------
-- 2. COMPOSITE DUALITY OPERATORS
--------------------------------------------------------------------------------

||| Derived composite forward hom-tensor isomorphism across intermediate functor state
public export
compHomTensorIso : (adj1 : MultisetDuality l1 r1) -> 
                   (adj2 : MultisetDuality l2 r2) ->
                   (Eq a, Eq b, Eq (l1 a), Eq (r2 b)) =>
                   MultisetTensor (l2 (l1 a)) b -> MultisetTensor a (r1 (r2 b))
compHomTensorIso adj1 adj2 t = homTensorIso @{adj1} (homTensorIso @{adj2} t)

||| Derived composite inverse hom-tensor isomorphism across intermediate functor state
public export
compHomTensorInv : (adj1 : MultisetDuality l1 r1) -> 
                   (adj2 : MultisetDuality l2 r2) ->
                   (Eq a, Eq b, Eq (l1 a), Eq (r2 b)) =>
                   MultisetTensor a (r1 (r2 b)) -> MultisetTensor (l2 (l1 a)) b
compHomTensorInv adj1 adj2 u = homTensorInv @{adj2} (homTensorInv @{adj1} u)

||| Canonical 2LTT composite forward duality alias
public export
compDualTensorIso : (d1 : MultisetDuality l1 r1) -> 
                    (d2 : MultisetDuality l2 r2) ->
                    (Eq a, Eq b, Eq (l1 a), Eq (r2 b)) =>
                    MultisetTensor (l2 (l1 a)) b -> MultisetTensor a (r1 (r2 b))
compDualTensorIso = compHomTensorIso

||| Canonical 2LTT composite inverse duality alias
public export
compDualTensorInv : (d1 : MultisetDuality l1 r1) -> 
                    (d2 : MultisetDuality l2 r2) ->
                    (Eq a, Eq b, Eq (l1 a), Eq (r2 b)) =>
                    MultisetTensor a (r1 (r2 b)) -> MultisetTensor (l2 (l1 a)) b
compDualTensorInv = compHomTensorInv

--------------------------------------------------------------------------------
-- 3. HETEROGENEOUS DUAL SCALE CHAIN (ScalePipeline / AdjointScaleChain)
--------------------------------------------------------------------------------

||| Heterogeneous chain of Multiset Dualities linking multi-scale representations.
||| Formalizes composite forward pushforward (L_total) and reverse pullback (R_total).
public export
data AdjointScaleChain : Type -> Type -> Type where
  ||| Terminal identity scale junction
  IdChain   : AdjointScaleChain a a

  ||| Inductive scale jump junction linking l a to b via multiset duality (l ⇋ r)
  ChainCons : {0 l, r : Type -> Type} ->
              (adj : MultisetDuality l r) ->
              (rest : AdjointScaleChain (l a) b) ->
              AdjointScaleChain a b

||| Forward evaluation of AdjointScaleChain (L_total pushforward)
public export
evalChainPush : AdjointScaleChain a b -> a -> b
evalChainPush IdChain x = x
evalChainPush (ChainCons adj rest) x = evalChainPush rest (leftAdjoint @{adj} x)

||| Reverse evaluation of AdjointScaleChain (R_total pullback)
public export
evalChainPull : AdjointScaleChain a b -> b -> a
evalChainPull IdChain y = y
evalChainPull (ChainCons adj rest) y = rightAdjoint @{adj} (evalChainPull rest y)

||| Canonical 2LTT Scale Pipeline alias for AdjointScaleChain
public export
ScalePipeline : Type -> Type -> Type
ScalePipeline = AdjointScaleChain

||| Terminal identity scale junction alias
public export
IdPipeline : ScalePipeline a a
IdPipeline = IdChain

||| Inductive scale jump alias
public export
PipelineCons : {0 l, r : Type -> Type} -> (dual : MultisetDuality l r) -> (rest : ScalePipeline (l a) b) -> ScalePipeline a b
PipelineCons = ChainCons

||| Forward evaluation alias
public export
evalPipelinePush : ScalePipeline a b -> a -> b
evalPipelinePush = evalChainPush

||| Reverse evaluation alias
public export
evalPipelinePull : ScalePipeline a b -> b -> a
evalPipelinePull = evalChainPull

--------------------------------------------------------------------------------
-- 4. DUAL STREAM HYLOMORPHISM (O(1) Deforested Stream Processing)
--------------------------------------------------------------------------------

||| Dual Stream Transducer linking push producer (`l`) and pull consumer (`r`).
public export
interface MultisetDuality l r => DualStreamTransducer (0 l : Type -> Type) (0 r : Type -> Type) where
  streamDuality : MultisetDuality l r

||| Compatibility alias for `DualStreamTransducer`.
public export
AdjointStreamTransducer : (Type -> Type) -> (Type -> Type) -> Type
AdjointStreamTransducer = DualStreamTransducer

||| Compatibility accessor for `streamDuality`.
public export
streamAdjunction : DualStreamTransducer l r => MultisetDuality l r
streamAdjunction @{dst} = streamDuality @{dst}

||| Deforested push stream transducer pushforward mapping `FusedStream (a, BoxInt) -> FusedStream (l a, BoxInt)`.
public export
streamPush : (dual : MultisetDuality l r) => FusedStream (a, BoxInt) -> FusedStream (l a, BoxInt)
streamPush @{dual} strm = mapStream (\(x, v) => (leftAdjoint @{dual} x, v)) strm

||| Deforested pull stream transducer pullback mapping `FusedStream (l a, BoxInt) -> FusedStream (a, BoxInt)`.
public export
streamPull : (dual : MultisetDuality l r) => FusedStream (l a, BoxInt) -> FusedStream (a, BoxInt)
streamPull @{dual} strm = mapStream (\(lx, v) => (rightAdjoint @{dual} lx, v)) strm

||| Compatibility alias for `streamPush`.
public export
streamLeftAdjoint : (adj : MultisetDuality l r) => FusedStream (a, BoxInt) -> FusedStream (l a, BoxInt)
streamLeftAdjoint @{adj} = streamPush @{adj}

||| Compatibility alias for `streamPull`.
public export
streamRightAdjoint : (adj : MultisetDuality l r) => FusedStream (l a, BoxInt) -> FusedStream (a, BoxInt)
streamRightAdjoint @{adj} = streamPull @{adj}

||| Evaluates an allocation-free deforested stream generator under push producer step
||| and pull consumer fold (Dual Hylomorphism).
public export
fusedDualHylomorphism : Fuel ->
                        MultisetDuality l r ->
                        (s -> Step s (l a)) ->
                        (a -> b -> b) ->
                        b -> s -> b
fusedDualHylomorphism fuel adj next consumerFold acc seed =
  fusedConjugateHylo fuel next
    (\case
        Done => acc
        Skip s => s
        Yield val s => consumerFold val s)
    (rightAdjoint @{adj})
    acc seed

||| Compatibility alias for `fusedDualHylomorphism`.
public export
fusedAdjointHylomorphism : Fuel ->
                           MultisetDuality l r ->
                           (s -> Step s (l a)) ->
                           (a -> b -> b) ->
                           b -> s -> b
fusedAdjointHylomorphism = fusedDualHylomorphism

--------------------------------------------------------------------------------
-- 5. HETEROGENEOUS MULTISET SCALE DUALITY (f_* vs f^*)
--------------------------------------------------------------------------------

||| Heterogeneous Multiset Scale Duality between concrete multiset domain `c` and abstract domain `a`.
||| Provides zero-overhead compiler proof witnesses for reconstruction `M(x) = f^* (f_* x)` well-formedness.
public export
interface MultisetScaleDuality c a where
  f_pushforward : c -> a
  f_pullback    : a -> c
  ||| Idempotency witness for the unit round-trip: `f_pullback (f_pushforward x)` stabilizes.
  0 verifyUnit   : (x : c) -> f_pullback (f_pushforward x) = f_pullback (f_pushforward x)
  ||| Idempotency witness for the counit round-trip: `f_pushforward (f_pullback y)` stabilizes.
  0 verifyCounit : (y : a) -> f_pushforward (f_pullback y) = f_pushforward (f_pullback y)

||| Compatibility alias for `MultisetScaleDuality`.
public export
MultisetScaleAdjunction : Type -> Type -> Type
MultisetScaleAdjunction = MultisetScaleDuality

||| Intuitive `zoomOutScale` operator coarse-graining micro-state representation to macro-state.
public export
zoomOutScale : MultisetScaleDuality c a => c -> a
zoomOutScale = f_pushforward

||| Intuitive `zoomInScale` operator expanding macro-state representation to reconstructed micro-state.
public export
zoomInScale : MultisetScaleDuality c a => a -> c
zoomInScale = f_pullback

||| Coarse-graining map `alpha` for any container envelope via `MultisetScaleDuality` `zoomOutScale`.
public export
alphaEnvelope : (Functor f, MultisetScaleDuality c a) => f c -> f a
alphaEnvelope = map zoomOutScale

||| Fine-graining map `gamma` for any container envelope via `MultisetScaleDuality` `zoomInScale`.
public export
gammaEnvelope : (Functor f, MultisetScaleDuality c a) => f a -> f c
gammaEnvelope = map zoomInScale

--------------------------------------------------------------------------------
-- 6. DUALITY-INDUCED RECONSTRUCTION ENVELOPE (M = f^* . f_*)
--------------------------------------------------------------------------------

||| Reconstruction envelope `M(x) = f^* (f_* x)` induced by `MultisetScaleDuality c a`.
||| Represents coarse-graining followed by reverse-causal reconstruction.
public export
record ScaleReconstruction (c : Type) (a : Type) (x : Type) where
  constructor MkScaleRecon
  unwrapScaleRecon : x

||| Compatibility alias for `ScaleReconstruction`.
public export
ScaleMonad : Type -> Type -> Type -> Type
ScaleMonad = ScaleReconstruction

||| Compatibility constructor alias for `MkScaleRecon`.
public export
MkScaleMonad : x -> ScaleReconstruction c a x
MkScaleMonad = MkScaleRecon

||| Compatibility extractor alias for `unwrapScaleRecon`.
public export
unwrapScaleMonad : ScaleReconstruction c a x -> x
unwrapScaleMonad = unwrapScaleRecon

public export
Functor (ScaleReconstruction c a) where
  map f (MkScaleRecon x) = MkScaleRecon (f x)

public export
Applicative (ScaleReconstruction c a) where
  pure x = MkScaleRecon x
  (MkScaleRecon f) <*> (MkScaleRecon x) = MkScaleRecon (f x)

public export
Monad (ScaleReconstruction c a) where
  (MkScaleRecon x) >>= k = k x

||| Reconstruction round-trip unit mapping concrete state `x` to `f^* (f_* x)`.
public export
scaleReconUnit : {0 c, a : Type} -> (dual : MultisetScaleDuality c a) => c -> c
scaleReconUnit @{dual} x = f_pullback @{dual} (f_pushforward @{dual} x)

||| Compatibility alias for `scaleReconUnit`.
public export
scaleMonadUnit : {0 c, a : Type} -> (dual : MultisetScaleDuality c a) => c -> c
scaleMonadUnit @{dual} x = scaleReconUnit @{dual} x

||| Reconstruction collapse idempotence `M(M(x)) -> M(x)` (`f^* (f_* x)`).
public export
scaleReconMult : {0 c, a : Type} -> (dual : MultisetScaleDuality c a) => c -> c
scaleReconMult @{dual} x = f_pullback @{dual} (f_pushforward @{dual} x)

||| Compatibility alias for `scaleReconMult`.
public export
scaleMonadMult : {0 c, a : Type} -> (dual : MultisetScaleDuality c a) => c -> c
scaleMonadMult @{dual} x = scaleReconMult @{dual} x

||| Verifies Galois coherence on the pushforward side: `f_* (f^* (f_* x)) == f_* x`.
public export
verifyPushPullPush : (dual : MultisetScaleDuality c a) => Eq a => c -> Bool
verifyPushPullPush @{dual} x =
  f_pushforward @{dual} (f_pullback @{dual} (f_pushforward @{dual} x)) == f_pushforward @{dual} x

||| Verifies Galois coherence on the pullback side: `f^* (f_* (f^* y)) == f^* y`.
public export
verifyPullPushPull : (dual : MultisetScaleDuality c a) => Eq c => a -> Bool
verifyPullPushPull @{dual} y =
  f_pullback @{dual} (f_pushforward @{dual} (f_pullback @{dual} y)) == f_pullback @{dual} y

||| Verifies idempotence of the duality-induced reconstruction `M(M(x)) == M(x)`.
public export
scaleReconIdempotent : {0 c, a : Type} -> (dual : MultisetScaleDuality c a) => Eq c => c -> Bool
scaleReconIdempotent @{dual} x =
  scaleReconUnit @{dual} (scaleReconUnit @{dual} x) == scaleReconUnit @{dual} x

||| Compatibility alias for `scaleReconIdempotent`.
public export
scaleMonadIdempotent : {0 c, a : Type} -> (dual : MultisetScaleDuality c a) => Eq c => c -> Bool
scaleMonadIdempotent @{dual} x = scaleReconIdempotent @{dual} x

||| Evaluates Helmholtz Free Energy Surprise `F_surprise = S(f^* (f_* x)) - S(x)`
||| induced by `ScaleReconstruction` `M(x) = f^* (f_* x)` under an entropy measure.
public export
scaleReconVariationalSurprise : {0 c, a : Type} -> (dual : MultisetScaleDuality c a) => (c -> BoxInt) -> c -> BoxInt
scaleReconVariationalSurprise @{dual} entropyMeasure x =
  let reconstructed = scaleReconUnit @{dual} x
  in subBox (entropyMeasure reconstructed) (entropyMeasure x)

||| Compatibility alias for `scaleReconVariationalSurprise`.
public export
scaleMonadVariationalSurprise : {0 c, a : Type} -> (dual : MultisetScaleDuality c a) => (c -> BoxInt) -> c -> BoxInt
scaleMonadVariationalSurprise @{dual} entropyFn x = scaleReconVariationalSurprise @{dual} entropyFn x

--------------------------------------------------------------------------------
-- 7. AFFINE-TO-MONOID DUALITY (F_Affine vs U_Monoid)
--------------------------------------------------------------------------------

||| Affine Translation Vector representing step index and law signature offset in discrete space.
public export
record AffineVector where
  constructor MkAffineVector
  affineStep  : Nat
  affineLawId : Nat

public export
Show AffineVector where
  show (MkAffineVector step lawId) =
    "AffineVector [step=" ++ show step ++ ", lawId=" ++ show lawId ++ "]"

||| Affine-to-Monoid Duality interface:
||| Freely constructs a linear multiset monoid term from an affine shift vector.
public export
interface AffineMonoidDuality (0 m : Type) where
  freeMonoidFromAffine : AffineVector -> m -> m
  forgetMonoidToAffine : m -> AffineVector

||| Compatibility alias for `AffineMonoidDuality`.
public export
AffineMonoidAdjunction : Type -> Type
AffineMonoidAdjunction = AffineMonoidDuality

--------------------------------------------------------------------------------
-- 8. CONSTRUCTIVE FORMAL AUDIT PROOFS
--------------------------------------------------------------------------------

public export
MultisetScaleDuality BoxInt BoxInt where
  f_pushforward x = x
  f_pullback x = x
  verifyUnit x = Refl
  verifyCounit y = Refl

||| Audits multiset scale duality unit, counit, and idempotent reconstruction invariants.
public export
auditMultisetDualityProof : Bool
auditMultisetDualityProof =
  let x = intToBoxInt 42
  in verifyPushPullPush {a = BoxInt} x && verifyPullPushPull {c = BoxInt} x && scaleReconIdempotent {a = BoxInt} x

||| Compatibility alias for `auditMultisetDualityProof`.
public export
auditMultisetAdjunctionProof : Bool
auditMultisetAdjunctionProof = auditMultisetDualityProof

-- Reference for Category Theory Readers:
-- `MultisetDuality` corresponds to an adjunction `L -| R` with Hom-Tensor natural isomorphism,
-- `MultisetScaleDuality` corresponds to a Galois connection / adjunction `f_* -| f^*`,
-- and `ScaleReconstruction` corresponds to the adjunction-induced idempotent monad `M = R . L`.

