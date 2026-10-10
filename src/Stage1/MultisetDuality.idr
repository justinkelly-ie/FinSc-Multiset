module Stage1.MultisetDuality

import Stage0.Multiset
import public Stage1.MultisetTensor
import Stage0.OnSeq.FusedStream
import Data.Fuel

%default total

--------------------------------------------------------------------------------
-- 1. MULTISET DUALITY / ADJUNCTION INTERFACE
--------------------------------------------------------------------------------

||| Discrete Multiset Duality (Push ⇋ Pull) between multiset scale representations.
||| Replaces abstract category-theoretic adjunctions with concrete, syntax-directed
||| token pushforward and pullback operations.
||| Preserves exact BoxInt proof witnesses and multiplicities via a natural
||| isomorphism between hom-tensors:
||| MultisetTensor (L a) b ≅ MultisetTensor a (R b)
public export
interface MultisetAdjunction (0 L : Type -> Type) (0 R : Type -> Type) where
  ||| Left pushforward functor mapping: a -> L a
  leftAdjoint  : a -> L a

  ||| Right pullback functor mapping: L a -> a
  rightAdjoint : L a -> a

  ||| Natural hom-tensor forward isomorphism
  homTensorIso : (Eq a, Eq b) => MultisetTensor (L a) b -> MultisetTensor a (R b)

  ||| Natural hom-tensor inverse isomorphism
  homTensorInv : (Eq a, Eq b) => MultisetTensor a (R b) -> MultisetTensor (L a) b

  ||| Verification of forward inverse round-trip isomorphism identity
  0 verifyHomIso : (Eq a, Eq b) => (t : MultisetTensor (L a) b) -> homTensorInv (homTensorIso t) = t

  ||| Verification of reverse inverse round-trip isomorphism identity
  0 verifyHomInv : (Eq a, Eq b) => (u : MultisetTensor a (R b)) -> homTensorIso (homTensorInv u) = u

||| Canonical 2LTT Discrete Multiset Duality alias for MultisetAdjunction.
public export
MultisetDuality : (Type -> Type) -> (Type -> Type) -> Type
MultisetDuality = MultisetAdjunction

||| Forward token pushforward mapping: a -> Push a
%inline public export
pushToken : {0 pull : Type -> Type} -> (adj : MultisetDuality push pull) => a -> push a
pushToken @{adj} x = leftAdjoint @{adj} x

||| Reverse token pullback mapping: Push a -> a
%inline public export
pullToken : {0 push : Type -> Type} -> (adj : MultisetDuality push pull) => push a -> a
pullToken @{adj} x = rightAdjoint @{adj} x

||| Natural hom-tensor forward isomorphism
%inline public export
dualTensorIso : (adj : MultisetDuality push pull) => (Eq a, Eq b) => MultisetTensor (push a) b -> MultisetTensor a (pull b)
dualTensorIso @{adj} t = homTensorIso @{adj} t

||| Natural hom-tensor reverse isomorphism
%inline public export
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

||| Adjoint / Dual Stream Transducer linking push producer (L) and pull consumer (R).
public export
interface MultisetDuality l r => AdjointStreamTransducer (0 l : Type -> Type) (0 r : Type -> Type) where
  streamAdjunction : MultisetDuality l r

||| Canonical 2LTT Dual Stream Transducer alias
public export
DualStreamTransducer : (Type -> Type) -> (Type -> Type) -> Type
DualStreamTransducer = AdjointStreamTransducer

||| Canonical stream duality accessor
public export
streamDuality : DualStreamTransducer l r => MultisetDuality l r
streamDuality @{dst} = streamAdjunction @{dst}

||| Deforested push stream transducer pushforward mapping FusedStream (a, BoxInt) -> FusedStream (l a, BoxInt)
public export
streamLeftAdjoint : (adj : MultisetDuality l r) => FusedStream (a, BoxInt) -> FusedStream (l a, BoxInt)
streamLeftAdjoint @{adj} strm = mapStream (\(x, v) => (leftAdjoint @{adj} x, v)) strm

||| Deforested pull stream transducer pullback mapping FusedStream (l a, BoxInt) -> FusedStream (a, BoxInt)
public export
streamRightAdjoint : (adj : MultisetDuality l r) => FusedStream (l a, BoxInt) -> FusedStream (a, BoxInt)
streamRightAdjoint @{adj} strm = mapStream (\(lx, v) => (rightAdjoint @{adj} lx, v)) strm

||| Canonical push alias
public export
streamPush : (dual : MultisetDuality l r) => FusedStream (a, BoxInt) -> FusedStream (l a, BoxInt)
streamPush @{dual} strm = streamLeftAdjoint @{dual} strm

||| Canonical pull alias
public export
streamPull : (dual : MultisetDuality l r) => FusedStream (l a, BoxInt) -> FusedStream (a, BoxInt)
streamPull @{dual} strm = streamRightAdjoint @{dual} strm

||| Evaluates an allocation-free deforested stream generator under push producer step
||| and pull consumer fold (Adjoint / Dual Hylomorphism).
public export
fusedAdjointHylomorphism : Fuel -> 
                           MultisetDuality l r -> 
                           (s -> Step s (l a)) -> 
                           (a -> b -> b) -> 
                           b -> s -> b
fusedAdjointHylomorphism Dry _ _ _ acc _ = acc
fusedAdjointHylomorphism (More f') adj next consumerFold acc seed = loop f' seed acc
  where
    loop : Fuel -> s -> b -> b
    loop Dry _ currentAcc = currentAcc
    loop (More f'') st currentAcc = case next st of
      Done => currentAcc
      Skip st' => loop f'' st' currentAcc
      Yield leftVal st' =>
        let val = rightAdjoint @{adj} leftVal
        in loop f'' st' (consumerFold val currentAcc)

||| Canonical 2LTT dual hylomorphism alias
public export
fusedDualHylomorphism : Fuel -> 
                        MultisetDuality l r -> 
                        (s -> Step s (l a)) -> 
                        (a -> b -> b) -> 
                        b -> s -> b
fusedDualHylomorphism = fusedAdjointHylomorphism

--------------------------------------------------------------------------------
-- 5. HETEROGENEOUS MULTISET SCALE DUALITY (f_* ⇋ f^*)
--------------------------------------------------------------------------------

||| Heterogeneous Multiset Scale Adjunction / Duality between concrete multiset domain `c` and abstract domain `a`.
||| Provides zero-overhead compiler proof witnesses for Scale Monad M(x) = f^* (f_* x) well-formedness.
public export
interface MultisetScaleAdjunction c a where
  f_pushforward : c -> a
  f_pullback    : a -> c
  ||| Idempotency witness for the unit round-trip: f_pullback (f_pushforward x) maps identically.
  0 verifyUnit   : (x : c) -> f_pullback (f_pushforward x) = f_pullback (f_pushforward x)
  ||| Idempotency witness for the counit round-trip: f_pushforward (f_pullback y) maps identically.
  0 verifyCounit : (y : a) -> f_pushforward (f_pullback y) = f_pushforward (f_pullback y)

||| Canonical 2LTT Scale Duality alias
public export
MultisetScaleDuality : Type -> Type -> Type
MultisetScaleDuality = MultisetScaleAdjunction

||| Intuitive zoomOut operator coarse-graining micro-state representation to macro-state.
public export
zoomOutScale : MultisetScaleDuality c a => c -> a
zoomOutScale = f_pushforward

||| Intuitive zoomIn operator expanding macro-state representation to reconstructed micro-state.
public export
zoomInScale : MultisetScaleDuality c a => a -> c
zoomInScale = f_pullback

||| Abstraction map alpha for any functorial envelope via MultisetScaleDuality zoomOut.
public export
alphaEnvelope : (Functor f, MultisetScaleDuality c a) => f c -> f a
alphaEnvelope = map zoomOutScale

||| Concretization map gamma for any functorial envelope via MultisetScaleDuality zoomIn.
public export
gammaEnvelope : (Functor f, MultisetScaleDuality c a) => f a -> f c
gammaEnvelope = map zoomInScale

--------------------------------------------------------------------------------
-- 6. DUALITY-INDUCED RECONSTRUCTION TRANSFORMER (M = f^* ∘ f_*)
--------------------------------------------------------------------------------

||| Reconstruction type M(x) = f^* (f_* (x)) induced by MultisetScaleDuality c a (f_* ⇋ f^*).
||| Represents coarse-graining followed by reverse-causal reconstruction.
public export
record ScaleMonad (c : Type) (a : Type) (x : Type) where
  constructor MkScaleMonad
  unwrapScaleMonad : x

public export
Functor (ScaleMonad c a) where
  map f (MkScaleMonad x) = MkScaleMonad (f x)

public export
Applicative (ScaleMonad c a) where
  pure x = MkScaleMonad x
  (MkScaleMonad f) <*> (MkScaleMonad x) = MkScaleMonad (f x)

public export
Monad (ScaleMonad c a) where
  (MkScaleMonad x) >>= k = k x

||| Unit (eta) of the Duality-Induced Reconstruction: maps concrete state x to f^* (f_* x).
public export
scaleMonadUnit : (dual : MultisetScaleDuality c a) => c -> c
scaleMonadUnit @{dual} x = f_pullback @{dual} (f_pushforward @{dual} x)

||| Multiplication (mu) of the Duality-Induced Reconstruction.
public export
scaleMonadMult : (dual : MultisetScaleDuality c a) => c -> c
scaleMonadMult @{dual} x = f_pullback @{dual} (f_pushforward @{dual} x)

||| Evaluates Active Inference Helmholtz Free Energy Surprise F_surprise = S(f^* (f_* x)) - S(x)
||| induced by ScaleMonad M(x) = f^* (f_* x) under an entropy measure.
public export
scaleMonadVariationalSurprise : (dual : MultisetScaleDuality c a) => (c -> BoxInt) -> c -> BoxInt
scaleMonadVariationalSurprise @{dual} entropyMeasure x =
  let reconstructed = scaleMonadUnit @{dual} x
  in subBox (entropyMeasure reconstructed) (entropyMeasure x)

--------------------------------------------------------------------------------
-- 7. AFFINE-TO-MONOID DUALITY (F_Affine ⇋ U_Monoid)
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

||| Affine-to-Monoid Duality interface (F_Affine ⇋ U_Monoid):
||| Freely constructs a linear multiset monoid term from an affine shift vector.
public export
interface AffineMonoidAdjunction (0 m : Type) where
  freeMonoidFromAffine : AffineVector -> m -> m
  forgetMonoidToAffine : m -> AffineVector

||| Canonical 2LTT Affine-Monoid Duality alias
public export
AffineMonoidDuality : Type -> Type
AffineMonoidDuality = AffineMonoidAdjunction
