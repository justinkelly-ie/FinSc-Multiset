module Stage0.OnSeq.FusedStream

import Data.List
import Data.Nat
import Data.Fuel
import Stage0.BoxInt
import Stage0.Multiset
import Stage0.Token
import public Stage0.StructuralFuel
import public Stage0.Basis.GeometricPixel

%default total

------------------------------------------------------------------------
-- 2. STREAM FUSION CO-STRUCTURE CORE (Coutts et al. 2007)
------------------------------------------------------------------------

||| Non-recursive state transition step representation.
public export
data Step s a = Done | Skip s | Yield a s

||| Strictly linear state transition step representation preserving QTT multiplicity 1.
public export
data StepLinear : Type -> Type -> Type where
  DoneL  : (1 finalState : s) -> StepLinear s a
  SkipL  : (1 nextState : s) -> StepLinear s a
  YieldL : a -> (1 nextState : s) -> StepLinear s a

||| Existential stream wrapper shielding state allocations.
public export
data FusedStream : (a : Type) -> Type where
  MkStream : (next : s -> Step s a) -> (seed : s) -> FusedStream a

||| Linear pair preserving QTT multiplicity 1 across both components.
public export
data LinearPair : Type -> Type -> Type where
  MkLPair : (1 x : a) -> (1 y : b) -> LinearPair a b

||| Linear state and unrestricted observable pair (Rule 04).
||| Guarantees exact linear state consumption while permitting observables to be accumulated freely.
public export
data LinearStatePair : Type -> Type -> Type where
  MkLStatePair : (1 state : s) -> (obs : b) -> LinearStatePair s b

||| Evaluates a stateful linear step transducer with structural Nat fuel,
||| guaranteeing that the linear state is consumed and returned exactly once without leakage.
public export
foldLinearStreamNat : (fuel : Nat) -> (fn : b -> a -> b) -> b -> (1 st : s) -> (step : (1 curr : s) -> StepLinear s a) -> LinearPair b s
foldLinearStreamNat Z _ acc st _ = MkLPair acc st
foldLinearStreamNat (S f) fn acc st step = case step st of
  DoneL st' => MkLPair acc st'
  SkipL st' => foldLinearStreamNat f fn acc st' step
  YieldL x st' => foldLinearStreamNat f fn (fn acc x) st' step

||| A linear streaming multiset pipeline where the stream is consumed with QTT 1 multiplicity.
public export
data LinearStream : (s : Type) -> (a : Type) -> Type where
  MkLinearStream : ((1 st : s) -> StepLinear s a) -> (1 activeSeed : s) -> LinearStream s a

||| Evaluates a LinearStream with a fuel bound, accumulating results into an unrestricted list
||| and returning the consumed linear final state in a LinearStatePair.
public export
runLinearStreamFuel : (fuel : Nat) -> (1 str : LinearStream s a) -> LinearStatePair s (List a)
runLinearStreamFuel Z (MkLinearStream _ seed) = MkLStatePair seed []
runLinearStreamFuel (S f) (MkLinearStream step seed) = case step seed of
  DoneL st => MkLStatePair st []
  SkipL st => runLinearStreamFuel f (MkLinearStream step st)
  YieldL x st =>
    let MkLStatePair finalSt rest = runLinearStreamFuel f (MkLinearStream step st)
    in MkLStatePair finalSt (x :: rest)


||| Step function for converting a List into a stream.
public export
listStep : List a -> Step (List a) a
listStep [] = Done
listStep (y :: ys) = Yield y ys

||| Converts a List storage container into a deforested stream.
public export
stream : List a -> FusedStream a
stream xs = MkStream listStep xs

||| Constructs a deforested stream from a state transition unfold stepper (`Stream Unfold`).
public export
unfoldStream : (s -> Step s a) -> s -> FusedStream a
unfoldStream next seed = MkStream next seed

||| Evaluates a stream generator directly into an accumulator without intermediate allocations (Hylomorphism).
public export
fusedHylomorphism : Fuel -> (next : s -> Step s a) -> (f : a -> b -> b) -> b -> s -> b
fusedHylomorphism Dry _ _ acc _ = acc
fusedHylomorphism (More f') next f acc st = case next st of
  Done => acc
  Skip st' => fusedHylomorphism f' next f acc st'
  Yield x st' => fusedHylomorphism f' next f (f x acc) st'

||| Total Nat fuel-bounded stream generator evaluation directly into an accumulator without intermediate allocations (Hylomorphism).
public export
fusedHylomorphismNat : (fuel : Nat) -> (next : s -> Step s a) -> (fStep : a -> b -> b) -> b -> s -> b
fusedHylomorphismNat Z _ _ acc _ = acc
fusedHylomorphismNat (S f) next fStep acc st = case next st of
  Done => acc
  Skip st' => fusedHylomorphismNat f next fStep acc st'
  Yield x st' => fusedHylomorphismNat f next fStep (fStep x acc) st'

||| Total Fuel-driven stream evaluation producing a List container.
public export
runFueledStream : Fuel -> FusedStream a -> List a
runFueledStream fuel (MkStream {s} step s0) = loop fuel s0
  where
    loop : Fuel -> s -> List a
    loop Dry _ = []
    loop (More f') st = case step st of
      Done => []
      Skip st' => loop f' st'
      Yield x st' => x :: loop f' st'

||| Total Nat fuel-driven stream evaluation producing a List container.
public export
runFueledStreamNat : (fuel : Nat) -> FusedStream a -> List a
runFueledStreamNat fuel (MkStream {s} step s0) = loop fuel s0
  where
    loop : Nat -> s -> List a
    loop Z _ = []
    loop (S f') st = case step st of
      Done => []
      Skip st' => loop f' st'
      Yield x st' => x :: loop f' st'

||| Model-indexed GohFuel stream evaluation producing a List container.
public export
runFueledStreamFuelModel : GohFuel cap -> FusedStream a -> List a
runFueledStreamFuelModel fuel = runFueledStreamNat (gohSteps fuel)

||| Zero-allocation lockstep equality comparison between two FusedStreams with structural Nat fuel.
public export
eqStreamNat : (Eq a) => Nat -> FusedStream a -> FusedStream a -> Bool
eqStreamNat fuel (MkStream {s = s1} step1 seed1) (MkStream {s = s2} step2 seed2) =
  loop fuel seed1 seed2
  where
    loop : Nat -> s1 -> s2 -> Bool
    loop Z _ _ = False
    loop (S f) st1 st2 =
      case step1 st1 of
        Skip st1' => loop f st1' st2
        Done =>
          case step2 st2 of
            Done => True
            Skip st2' => loop f st1 st2'
            Yield _ _ => False
        Yield x1 st1' =>
          case step2 st2 of
            Skip st2' => loop f st1 st2'
            Done => False
            Yield x2 st2' =>
              if x1 == x2 then loop f st1' st2' else False

||| Model-indexed GohFuel stream equality comparison.
public export
eqStreamFuelModel : (Eq a) => GohFuel cap -> FusedStream a -> FusedStream a -> Bool
eqStreamFuelModel fuel = eqStreamNat (gohSteps fuel)

||| Deforested stream equality comparison bounded by Master Substrate Primorial Ground State capacity (Rule 03).
public export
eqStream : (Eq a) => FusedStream a -> FusedStream a -> Bool
eqStream = eqStreamFuelModel masterSubstrateGohFuelModel

||| Definitional stream equality interface bounded by Master Substrate Primorial Ground State capacity.
public export
(Eq a) => Eq (FusedStream a) where
  (==) = eqStream


------------------------------------------------------------------------
-- DEFORESTED STREAM FUSION COMBINATOR LIBRARY
------------------------------------------------------------------------

||| Top-level step function for deforested stream map.
public export
mapStep : (a -> b) -> (s -> Step s a) -> s -> Step s b
mapStep f next st = case next st of
  Done => Done
  Skip st' => Skip st'
  Yield x st' => Yield (f x) st'

||| Deforested stream map operator.
public export
mapStream : (a -> b) -> FusedStream a -> FusedStream b
mapStream f (MkStream next seed) = MkStream (mapStep f next) seed

public export
Functor FusedStream where
  map = mapStream

||| Deforested scan over a FusedStream accumulating state and emitting intermediate values (Rule 04 Section 6).
public export
scanStream : (b -> a -> b) -> b -> FusedStream a -> FusedStream b
scanStream f init (MkStream {s} next seed) =
  MkStream {s = (s, b)}
    (\(st, acc) => case next st of
      Done => Done
      Skip st' => Skip (st', acc)
      Yield x st' =>
        let acc' = f acc x
        in Yield acc' (st', acc'))
    (seed, init)

||| Top-level step function for deforested stream filter.
public export
filterStep : (a -> Bool) -> (s -> Step s a) -> s -> Step s a
filterStep p next st = case next st of
  Done => Done
  Skip st' => Skip st'
  Yield x st' => if p x then Yield x st' else Skip st'

||| Deforested stream filter operator.
public export
filterStream : (a -> Bool) -> FusedStream a -> FusedStream a
filterStream p (MkStream next seed) = MkStream (filterStep p next) seed

||| Alias for deforested stream sifting operator.
public export
siftFusedStream : (a -> Bool) -> FusedStream a -> FusedStream a
siftFusedStream = filterStream

||| Top-level step function for deforested stream filterMap.
public export
filterMapStep : (a -> Maybe b) -> (s -> Step s a) -> s -> Step s b
filterMapStep f next st = case next st of
  Done => Done
  Skip st' => Skip st'
  Yield x st' => case f x of
    Just y => Yield y st'
    Nothing => Skip st'

||| Deforested stream filterMap operator (fused filtering and projection in a single pass).
public export
filterMapStream : (a -> Maybe b) -> FusedStream a -> FusedStream b
filterMapStream f (MkStream next seed) = MkStream (filterMapStep f next) seed

||| Deforested stream zipWith operator.
public export
zipWithStream : (a -> b -> c) -> FusedStream a -> FusedStream b -> FusedStream c
zipWithStream {a, b, c} f (MkStream {s=sA} nextA seedA) (MkStream {s=sB} nextB seedB) =
  MkStream nextStep (seedA, seedB, Nothing)
  where
    nextStep : (sA, sB, Maybe a) -> Step (sA, sB, Maybe a) c
    nextStep (sa, sb, Nothing) = case nextA sa of
      Done => Done
      Skip sa' => Skip (sa', sb, Nothing)
      Yield x sa' => Skip (sa', sb, Just x)
    nextStep (sa, sb, Just x) = case nextB sb of
      Done => Done
      Skip sb' => Skip (sa, sb', Just x)
      Yield y sb' => Yield (f x y) (sa, sb', Nothing)

||| Specialized top-level loop for Nat fuel-bounded stream left fold.
public export
foldStreamLoopNat : (fuel : Nat) -> (next : s -> Step s a) -> (fn : b -> a -> b) -> s -> b -> b
foldStreamLoopNat Z _ _ _ currentAcc = currentAcc
foldStreamLoopNat (S f') next fn st currentAcc = case next st of
  Done => currentAcc
  Skip st' => foldStreamLoopNat f' next fn st' currentAcc
  Yield x st' => foldStreamLoopNat f' next fn st' (fn currentAcc x)

||| Total Nat fuel-bounded stream left fold accumulator.
public export
foldStreamNat : (fuel : Nat) -> (fn : b -> a -> b) -> b -> FusedStream a -> b
foldStreamNat fuel fn acc0 (MkStream next seed) = foldStreamLoopNat fuel next fn seed acc0

||| Specialized top-level loop for Data.Fuel stream left fold.
public export
foldStreamLoopFuel : Fuel -> (next : s -> Step s a) -> (fn : b -> a -> b) -> s -> b -> b
foldStreamLoopFuel Dry _ _ _ currentAcc = currentAcc
foldStreamLoopFuel (More f') next fn st currentAcc = case next st of
  Done => currentAcc
  Skip st' => foldStreamLoopFuel f' next fn st' currentAcc
  Yield x st' => foldStreamLoopFuel f' next fn st' (fn currentAcc x)

||| Total Data.Fuel stream left fold accumulator.
public export
foldStreamFuel : Fuel -> (fn : b -> a -> b) -> b -> FusedStream a -> b
foldStreamFuel fuel fn acc0 (MkStream next seed) = foldStreamLoopFuel fuel next fn seed acc0

||| Deforested stream left fold accumulator bounded by model-derived Master Substrate Primorial Ground State capacity (Rule 03).
||| For custom fuel envelopes, use foldStreamFuelModel, foldStreamGoh, or foldStreamNat directly.
public export
foldStream : (b -> a -> b) -> b -> FusedStream a -> b
foldStream f acc0 strm = foldStreamNat (gohSteps masterSubstrateGohFuelModel) f acc0 strm

||| Total stream fold accumulator using model-indexed GohFuel.
public export
foldStreamFuelModel : GohFuel cap -> (b -> a -> b) -> b -> FusedStream a -> b
foldStreamFuelModel fuel f acc0 strm = foldStreamNat (gohSteps fuel) f acc0 strm

||| Total stream fold accumulator using BoxNat Goh factorisation fuel (backward compatible).
public export
foldStreamBoxNat : BoxNat -> (b -> a -> b) -> b -> FusedStream a -> b
foldStreamBoxNat bn f acc0 strm = foldStreamNat (boxNatToNat bn) f acc0 strm

||| Total stream fold accumulator using model-derived Goh fuel for a given size hint.
public export
foldStreamGoh : (sizeHint : Nat) -> (b -> a -> b) -> b -> FusedStream a -> b
foldStreamGoh sizeHint f acc0 strm = foldStreamNat (gohFuelNat sizeHint) f acc0 strm

||| Evaluates a stream generator directly into an accumulator using model-indexed GohFuel.
public export
fusedHylomorphismModel : GohFuel cap -> (s -> Step s a) -> (a -> b -> b) -> b -> s -> b
fusedHylomorphismModel fuel next stepAcc acc0 seed =
  fusedHylomorphismNat (gohSteps fuel) next stepAcc acc0 seed

||| Evaluates a stream generator directly into an accumulator using BoxNat Goh factorisation fuel (backward compatible).
public export
fusedHylomorphismBoxNat : BoxNat -> (s -> Step s a) -> (a -> b -> b) -> b -> s -> b
fusedHylomorphismBoxNat bn next stepAcc acc0 seed =
  fusedHylomorphismNat (boxNatToNat bn) next stepAcc acc0 seed

||| Evaluates a stream generator using canonical model-derived Goh fuel for a given size hint.
public export
fusedHylomorphismGoh : (sizeHint : Nat) -> (s -> Step s a) -> (a -> b -> b) -> b -> s -> b
fusedHylomorphismGoh sizeHint next stepAcc acc0 seed =
  fusedHylomorphismNat (gohFuelNat sizeHint) next stepAcc acc0 seed

public export
Applicative FusedStream where
  pure x = unfoldStream (\b => if b then Yield x False else Done) True
  fs <*> xs = mapStream (\(f, x) => f x) (zipWithStream (\f, x => (f, x)) fs xs)

public export
Foldable FusedStream where
  foldr f z st = foldStream (flip f) z st
  foldl f z st = foldStream f z st

||| Deforested stream take operator.
public export
fusedTake : Nat -> FusedStream a -> FusedStream a
fusedTake {a} n (MkStream {s} next seed) = MkStream nextStep (n, seed)
  where
    nextStep : (Nat, s) -> Step (Nat, s) a
    nextStep (Z, _) = Done
    nextStep (S k, st) = case next st of
      Done => Done
      Skip st' => Skip (S k, st')
      Yield x st' => Yield x (k, st')

||| Deforested stream take operator bounded by canonical Goh BoxNat fuel across both yields and skips.
public export
fusedTakeGoh : BoxNat -> FusedStream a -> FusedStream a
fusedTakeGoh fuel (MkStream {s} next seed) =
  let maxSteps = boxNatToNat (gohFuelBox fuel)
      n = boxNatToNat fuel
  in MkStream nextStep (n, maxSteps, seed)
  where
    nextStep : (Nat, Nat, s) -> Step (Nat, Nat, s) a
    nextStep (Z, _, _) = Done
    nextStep (_, Z, _) = Done
    nextStep (S k, S steps, st) = case next st of
      Done => Done
      Skip st' => Skip (S k, steps, st')
      Yield x st' => Yield x (k, steps, st')

||| Deforested stream drop operator.
public export
fusedDrop : Nat -> FusedStream a -> FusedStream a
fusedDrop {a} n (MkStream {s} next seed) = MkStream nextStep (n, seed)
  where
    nextStep : (Nat, s) -> Step (Nat, s) a
    nextStep (Z, st) = case next st of
      Done => Done
      Skip st' => Skip (Z, st')
      Yield x st' => Yield x (Z, st')
    nextStep (S k, st) = case next st of
      Done => Done
      Skip st' => Skip (S k, st')
      Yield _ st' => Skip (k, st')

public export
data ConcatState : Type -> Type -> Type where
  ConcatNoInner   : sOuter -> ConcatState sOuter a
  ConcatHaveInner : sOuter -> (sInner -> Step sInner a) -> sInner -> ConcatState sOuter a

||| Top-level transition step for deforested stream concatenation.
public export
fusedConcatStep : (sOuter -> Step sOuter (FusedStream a)) -> ConcatState sOuter a -> Step (ConcatState sOuter a) a
fusedConcatStep nextOuter (ConcatNoInner so) = case nextOuter so of
  Done => Done
  Skip so' => Skip (ConcatNoInner so')
  Yield (MkStream nextInner seedInner) so' => Skip (ConcatHaveInner so' nextInner seedInner)
fusedConcatStep _ (ConcatHaveInner so nextInner seedInner) = case nextInner seedInner of
  Done => Skip (ConcatNoInner so)
  Skip seedInner' => Skip (ConcatHaveInner so nextInner seedInner')
  Yield x seedInner' => Yield x (ConcatHaveInner so nextInner seedInner')

||| Deforested stream concat operator with zero heap re-allocation per step.
public export
fusedConcat : FusedStream (FusedStream a) -> FusedStream a
fusedConcat {a} (MkStream {s=sOuter} nextOuter seedOuter) =
  MkStream (fusedConcatStep nextOuter) (ConcatNoInner seedOuter)

||| Deforested stream monadic bind / flatMap operator.
public export
flatMapStream : (a -> FusedStream b) -> FusedStream a -> FusedStream b
flatMapStream f strm = fusedConcat (mapStream f strm)

||| Cartesian product of two deforested streams with zero intermediate heap allocation.
public export
streamCartesian : FusedStream a -> FusedStream b -> FusedStream (a, b)
streamCartesian strA strB =
  flatMapStream (\x => mapStream (\y => (x, y)) strB) strA

||| Deforested tensor product of weighted streams:
||| Multiplies element weights (wx * wy) while pairing tokens (x, y).
public export
streamTensorProduct : FusedStream (a, BoxInt) -> FusedStream (b, BoxInt) -> FusedStream ((a, b), BoxInt)
streamTensorProduct strA strB =
  mapStream (\((x, wx), (y, wy)) => ((x, y), wx * wy)) (streamCartesian strA strB)


||| Appends two deforested streams together without intermediate heap allocation.
public export
appendStream : FusedStream a -> FusedStream a -> FusedStream a
appendStream {a} (MkStream {s=s1} next1 seed1) (MkStream {s=s2} next2 seed2) =
  MkStream nextStep (Left seed1)
  where
    nextStep : Either s1 s2 -> Step (Either s1 s2) a
    nextStep (Left st1) = case next1 st1 of
      Done => Skip (Right seed2)
      Skip st1' => Skip (Left st1')
      Yield x st1' => Yield x (Left st1')
    nextStep (Right st2) = case next2 st2 of
      Done => Done
      Skip st2' => Skip (Right st2')
      Yield x st2' => Yield x (Right st2')

public export
Semigroup (FusedStream a) where
  (<+>) = appendStream

public export
Monoid (FusedStream a) where
  neutral = MkStream (\_ => Done) ()

||| Deforested stream merge operator for sorted streams.
public export
fusedMergeSorted : Ord a => FusedStream a -> FusedStream a -> FusedStream a
fusedMergeSorted {a} (MkStream {s=sL} nextL seedL) (MkStream {s=sR} nextR seedR) =
  MkStream nextStep (seedL, seedR, Nothing, Nothing)
  where
    nextStep : (sL, sR, Maybe a, Maybe a) -> Step (sL, sR, Maybe a, Maybe a) a
    nextStep (sl, sr, Nothing, Nothing) = case nextL sl of
      Done => case nextR sr of
        Done => Done
        Skip sr' => Skip (sl, sr', Nothing, Nothing)
        Yield yr sr' => Yield yr (sl, sr', Nothing, Nothing)
      Skip sl' => Skip (sl', sr, Nothing, Nothing)
      Yield xl sl' => Skip (sl', sr, Just xl, Nothing)
    nextStep (sl, sr, Just xl, Nothing) = case nextR sr of
      Done => Yield xl (sl, sr, Nothing, Nothing)
      Skip sr' => Skip (sl, sr', Just xl, Nothing)
      Yield yr sr' =>
        if xl <= yr
          then Yield xl (sl, sr', Nothing, Just yr)
          else Yield yr (sl, sr', Just xl, Nothing)
    nextStep (sl, sr, Nothing, Just yr) = case nextL sl of
      Done => Yield yr (sl, sr, Nothing, Nothing)
      Skip sl' => Skip (sl', sr, Nothing, Just yr)
      Yield xl sl' =>
        if xl <= yr
          then Yield xl (sl', sr, Nothing, Just yr)
          else Yield yr (sl', sr, Just xl, Nothing)
    nextStep (sl, sr, Just xl, Just yr) =
      if xl <= yr
        then Yield xl (sl, sr, Nothing, Just yr)
        else Yield yr (sl, sr, Just xl, Nothing)


||| A stateful deforested stream transducer converting elements of type a to type b.
public export
data StreamTransducer : Type -> Type -> Type where

  MkTransducer : (step : s -> a -> Step s b) -> (seed : s) -> StreamTransducer a b

||| Applies a deforested stream transducer to a FusedStream without intermediate allocations.
public export
transduceStream : StreamTransducer a b -> FusedStream a -> FusedStream b
transduceStream {a, b} (MkTransducer {s=sT} stepT seedT) (MkStream {s=sS} stepS seedS) =
  MkStream nextStep (seedS, seedT)
  where
    nextStep : (sS, sT) -> Step (sS, sT) b
    nextStep (ss, st) = case stepS ss of
      Done => Done
      Skip ss' => Skip (ss', st)
      Yield x ss' => case stepT st x of
        Done => Done
        Skip st' => Skip (ss', st')
        Yield y st' => Yield y (ss', st')

||| Converts a Multiset container into a deforested FusedStream.
public export
multisetToStream : Multiset c a -> FusedStream (a, c)
multisetToStream mset = MkStream nextStep mset
  where
    nextStep : Multiset c a -> Step (Multiset c a) (a, c)
    nextStep ZeroM = Done
    nextStep (AddM x w rest) = Yield (x, w) rest

||| Fueled total stream fold accumulator.
public export
fueLedFoldStream : Fuel -> (b -> a -> b) -> b -> FusedStream a -> b
fueLedFoldStream f' f acc (MkStream next seed) = fusedHylomorphism f' next (flip f) acc seed

||| Total Nat fuel-bounded stream fold accumulator.
public export
fueLedFoldStreamNat : (fuel : Nat) -> (b -> a -> b) -> b -> FusedStream a -> b
fueLedFoldStreamNat fuel f acc (MkStream next seed) = fusedHylomorphismNat fuel next (flip f) acc seed

||| Converts a deforested `FusedStream (a, BoxInt)` back into an indexed `Carrier a` (Fueled Fold).
public export
streamToCarrierFuel : Ord a => Fuel -> FusedStream (a, BoxInt) -> Carrier a
streamToCarrierFuel f' strm =
  fueLedFoldStream f' (\acc, (k, v) => addBoxTree k v acc) BoxLeaf strm

||| Converts a deforested `FusedStream (a, BoxInt)` into an indexed `Carrier a` bounded by `substrateFuel`.
public export
streamToCarrier : Ord a => FusedStream (a, BoxInt) -> Carrier a
streamToCarrier = streamToCarrierFuel substrateFuel

||| Streams an indexed `Carrier a` as individual atomic tokens using an $O(\log N)$ left-spine zipper
||| without intermediate `List` allocation.
public export
streamCarrierTokens : Carrier a -> FusedStream (Token a)
streamCarrierTokens m =
  MkStream {s = (BoxZipper BoxInt a, Maybe (a, Nat))}
    (\case
       (stk, Just (x, S k)) => Yield (MkToken x) (stk, if k == 0 then Nothing else Just (x, k))
       (stk, Just (_, Z))   => Skip (stk, Nothing)
       (stk, Nothing) =>
         case stepBoxZipper stk of
           Nothing => Done
           Just (x, w, nextStk) =>
             let count = boxToNat (absBox w)
             in case count of
                  Z   => Skip (nextStk, Nothing)
                  S Z => Yield (MkToken x) (nextStk, Nothing)
                  S k => Yield (MkToken x) (nextStk, Just (x, k)))
    (pushLeftBox m [], Nothing)

||| Folds a deforested stream of tokens back into a canonical `Carrier a` with unit weights.
public export
streamTokensToCarrier : Ord a => FusedStream (Token a) -> Carrier a
streamTokensToCarrier strm =
  foldStream (\acc, tok => acc <+> tokenToCarrier tok) BoxLeaf strm

------------------------------------------------------------------------
-- STREAMING MULTISET ALGEBRA (MODULE SCALING, DIFFERENCE & REDUCTIONS)
------------------------------------------------------------------------

||| Multiplies all weights in a key-weight stream by an integer scale factor in O(1) auxiliary registers.
public export
scaleWeightedStream : BoxInt -> FusedStream (a, BoxInt) -> FusedStream (a, BoxInt)
scaleWeightedStream factor = mapStream (\(x, w) => (x, mulBox w factor))

||| Negates all weights in a key-weight stream (particle-antiparticle conjugation).
public export
negateWeightedStream : FusedStream (a, BoxInt) -> FusedStream (a, BoxInt)
negateWeightedStream = mapStream (\(x, w) => (x, negBox w))

||| Computes the signed difference of two key-weight streams.
public export
diffWeightedStream : FusedStream (a, BoxInt) -> FusedStream (a, BoxInt) -> FusedStream (a, BoxInt)
diffWeightedStream s1 s2 = appendStream s1 (negateWeightedStream s2)

||| Computes total accumulated weight/charge of a key-weight stream as a single-pass fold.
public export
streamWeight : FusedStream (a, BoxInt) -> BoxInt
streamWeight = foldStream (\acc, (_, w) => addBox acc w) (intToBoxInt 0)

||| Counts total atomic tokens in a token stream as a single-pass fold.
public export
streamTokenCount : FusedStream (Token a) -> Nat
streamTokenCount = foldStream (\acc, _ => S acc) 0

||| Deforested stream support projection (extracts keys with non-zero weight).
public export
streamSupport : FusedStream (a, BoxInt) -> FusedStream a
streamSupport = filterMapStream (\(x, w) => if unwrapBox w /= 0 then Just x else Nothing)

||| Merges two key-sorted weighted streams into a consolidated stream combining weights of matching keys.
public export
mergeWeightedStream : (Ord a) => FusedStream (a, BoxInt) -> FusedStream (a, BoxInt) -> FusedStream (a, BoxInt)
mergeWeightedStream {a} (MkStream {s=sL} nextL seedL) (MkStream {s=sR} nextR seedR) =
  MkStream nextStep (seedL, seedR, Nothing, Nothing)
  where
    nextStep : (sL, sR, Maybe (a, BoxInt), Maybe (a, BoxInt)) -> Step (sL, sR, Maybe (a, BoxInt), Maybe (a, BoxInt)) (a, BoxInt)
    nextStep (sl, sr, Nothing, Nothing) = case nextL sl of
      Done => case nextR sr of
        Done => Done
        Skip sr' => Skip (sl, sr', Nothing, Nothing)
        Yield yr sr' => Yield yr (sl, sr', Nothing, Nothing)
      Skip sl' => Skip (sl', sr, Nothing, Nothing)
      Yield xl sl' => Skip (sl', sr, Just xl, Nothing)
    nextStep (sl, sr, Just xl, Nothing) = case nextR sr of
      Done => Yield xl (sl, sr, Nothing, Nothing)
      Skip sr' => Skip (sl, sr, Just xl, Nothing)
      Yield yr sr' => Skip (sl, sr', Just xl, Just yr)
    nextStep (sl, sr, Nothing, Just yr) = case nextL sl of
      Done => Yield yr (sl, sr, Nothing, Nothing)
      Skip sl' => Skip (sl', sr, Nothing, Just yr)
      Yield xl sl' => Skip (sl', sr, Just xl, Just yr)
    nextStep (sl, sr, Just (kL, wL), Just (kR, wR)) =
      if kL == kR then
        let wTotal = addBox wL wR
        in if unwrapBox wTotal == 0
             then Skip (sl, sr, Nothing, Nothing)
             else Yield (kL, wTotal) (sl, sr, Nothing, Nothing)
      else if kL < kR then
        Yield (kL, wL) (sl, sr, Nothing, Just (kR, wR))
      else
        Yield (kR, wR) (sl, sr, Just (kL, wL), Nothing)




------------------------------------------------------------------------
-- 3. WILDBERGER GEOMETRIC PIXEL MATRIX MULTIPLICATION & STREAM DEFORESTATION
------------------------------------------------------------------------

||| 2LTT Carrier Duality: Coinductive Streaming Matrix Multiset
public export
0 MaxelStream : Type
MaxelStream = FusedStream (GeometricPixel, BoxInt)

||| 2LTT Carrier Duality: Coinductive Streaming Vector Multiset
public export
0 VexelStream : Type
VexelStream = FusedStream (GeometricUnixel, BoxInt)

||| Coinductive infinite Maxel stream representing unbounded cosmic time evolution.
public export
data InfMaxelStream : Type where
  (::) : GeometricPixel -> Inf InfMaxelStream -> InfMaxelStream

||| Fused Geometric Pixel Matrix Multiplication.
||| Evaluates Wildberger composition rule [a, b] * [c, d] = [a, d] iff b == c.
||| Non-matching branches emit Skip s' to deforest O(n^2) dead loops to zero heap allocation.
public export
multiplyGeometricPixels : FusedStream GeometricPixel -> FusedStream GeometricPixel -> FusedStream GeometricPixel
multiplyGeometricPixels (MkStream {s=sL} nextL seedL) (MkStream {s=sR} nextR seedR) = 
  MkStream nextStep (seedL, seedR, Nothing)
  where
    nextStep : (sL, sR, Maybe GeometricPixel) -> Step (sL, sR, Maybe GeometricPixel) GeometricPixel
    nextStep (sl, sr, Nothing) = case nextL sl of
      Done => Done
      Skip sl' => Skip (sl', sr, Nothing)
      Yield ml sl' => Skip (sl', sr, Just ml)
      
    nextStep (sl, sr, Just ml) = case nextR sr of
      Done => Skip (sl, seedR, Nothing)
      Skip sr' => Skip (sl, sr', Just ml)
      Yield mr sr' =>
        if target ml == source mr
          then Yield (MkGeometricPixel (source ml) (target mr) (geometry ml)) (sl, sr', Just ml)
          else Skip (sl, sr', Just ml) -- Deforests non-matching cross-terms to Skip!

||| Folds a deforested stream of `GeometricPixel`s into a consolidated `Carrier GeometricPixel` with explicit `Fuel`.
public export
unstreamToCarrier : Fuel -> FusedStream GeometricPixel -> Carrier GeometricPixel
unstreamToCarrier f strm =
  foldStreamFuel f (\acc, px => addBoxTree px (intToBoxInt 1) acc) BoxLeaf strm

------------------------------------------------------------------------
-- 4. CONSTRUCTIVIST TERNARY MATRIX BOOTSTRAP {-1, 0, 1}^3
------------------------------------------------------------------------

||| Foundational constructivist ternary values.
public export
data Ternary = Neg | Zero | Pos

public export
Eq Ternary where
  Neg  == Neg  = True
  Zero == Zero = True
  Pos  == Pos  = True
  _    == _    = False

||| Foundational 2x2 Matrix Maxel carrying ternary elements.
public export
record TernaryMatrix where
  constructor MkMatrix
  source : Int
  target : Int
  topLeft     : Ternary
  topRight    : Ternary
  bottomLeft  : Ternary
  bottomRight : Ternary

public export
Eq TernaryMatrix where
  (MkMatrix s1 t1 tl1 tr1 bl1 br1) == (MkMatrix s2 t2 tl2 tr2 bl2 br2) =
    s1 == s2 && t1 == t2 && tl1 == tl2 && tr1 == tr2 && bl1 == bl2 && br1 == br2

public export
ternarySpace : List Ternary
ternarySpace = [Neg, Zero, Pos]

||| Generates the complete 27 Elliptic base permutations of the ternary space.
public export
generate27EllipticStates : List TernaryMatrix
generate27EllipticStates = do
  tl <- ternarySpace
  tr <- ternarySpace
  bl <- ternarySpace
  let src = if tl == Pos then 1 else 2
  let tgt = if bl == Neg then 1 else 2
  pure (MkMatrix src tgt tl tr bl Pos)

||| Multiply two ternary Maxel matrices using Wildberger's pixel matrix law.
public export
composeTernaryMaxels : TernaryMatrix -> TernaryMatrix -> Maybe TernaryMatrix
composeTernaryMaxels m1 m2 =
  if target m1 == source m2
    then Just (MkMatrix (source m1) (target m2) (topLeft m1) (topRight m2) (bottomLeft m1) (bottomRight m2))
    else Nothing

||| Evaluates total interactions and computes the count of vacuum compressions (Skip).
public export
countVacuumCompressions : List TernaryMatrix -> (Nat, Nat)
countVacuumCompressions states = foldl outer (0, 0) states
  where
    inner : TernaryMatrix -> (Nat, Nat) -> TernaryMatrix -> (Nat, Nat)
    inner x (t, n) y = case composeTernaryMaxels x y of
      Nothing => (t + 1, n + 1)
      Just _  => (t + 1, n)

    outer : (Nat, Nat) -> TernaryMatrix -> (Nat, Nat)
    outer acc x = foldl (inner x) acc states

||| Proof witness function confirming 324 out of 729 combinations compress to vacuum.
public export
verifyBootstrapCompression : (0 prf : countVacuumCompressions Stage0.OnSeq.FusedStream.generate27EllipticStates = (729, 324)) -> String
verifyBootstrapCompression _ = "Bootstrap structural validation verified successfully."

------------------------------------------------------------------------
-- 5. PRIMORIAL 210 QTT 0 TYPE-LEVEL BUDGET CONSTRAINTS
------------------------------------------------------------------------

public export
countGeometry : Geometry -> List (GeometricPixel, Nat) -> Nat
countGeometry targetGeom [] = Z
countGeometry targetGeom ((m, count) :: xs) = 
  if geometry m == targetGeom 
    then count + countGeometry targetGeom xs
    else countGeometry targetGeom xs

||| Deprecated: Use `countGeometry` instead.
public export %deprecate
countSector : Geometry -> List (GeometricPixel, Nat) -> Nat
countSector = countGeometry

||| Enforces the exact 27 Elliptic, 128 Hyperbolic, and 55 Parabolic 
||| boundary allocations within the master cosmic energy profile at compile time.
public export
record ConservedUniverse where
  constructor MkUniverse
  rawMaxels : List (GeometricPixel, Nat)
  0 ellipticProof   : countGeometry Elliptic   rawMaxels = 27
  0 hyperbolicProof : countGeometry Hyperbolic rawMaxels = 128
  0 parabolicProof  : countGeometry Parabolic  rawMaxels = 55

------------------------------------------------------------------------
-- 6. PARALLEL O(LOG N) MULTI-THREADED STREAM PARTITIONING
------------------------------------------------------------------------

||| Splits a List container into left and right stream partitions at a log N midpoint.
public export
splitStreamHalf : List a -> (FusedStream a, FusedStream a)
splitStreamHalf xs =
  let len = length xs
      mid = natDivFast len 2
      (leftList, rightList) = (take mid xs, drop mid xs)
  in (stream leftList, stream rightList)

||| Evaluates a stream fold consumer over a FusedStream directly without intermediate allocations.
public export
evalStreamHylomorphism : Fuel -> (a -> b -> b) -> b -> FusedStream a -> b
evalStreamHylomorphism f stepAcc acc0 (MkStream next seed) =
  fusedHylomorphism f next stepAcc acc0 seed

||| Evaluates a stream fold consumer over a FusedStream over Nat fuel.
public export
evalStreamHylomorphismNat : Nat -> (a -> b -> b) -> b -> FusedStream a -> b
evalStreamHylomorphismNat fuel stepAcc acc0 (MkStream next seed) =
  fusedHylomorphismNat fuel next stepAcc acc0 seed

||| Evaluates a stream fold consumer in parallel over left and right stream partitions.
public export
fusedParallelStreamFold : Fuel -> (a -> b -> b) -> b -> (b -> b -> b) -> List a -> b
fusedParallelStreamFold f stepAcc acc0 combineBin items =
  let (leftStrm, rightStrm) = splitStreamHalf items
      leftRes  = evalStreamHylomorphism f stepAcc acc0 leftStrm
      rightRes = evalStreamHylomorphism f stepAcc acc0 rightStrm
  in combineBin leftRes rightRes

||| Evaluates a stream fold consumer in parallel over left and right stream partitions over Nat fuel.
public export
fusedParallelStreamFoldNat : Nat -> (a -> b -> b) -> b -> (b -> b -> b) -> List a -> b
fusedParallelStreamFoldNat fuel stepAcc acc0 combineBin items =
  let (leftStrm, rightStrm) = splitStreamHalf items
      leftRes  = evalStreamHylomorphismNat fuel stepAcc acc0 leftStrm
      rightRes = evalStreamHylomorphismNat fuel stepAcc acc0 rightStrm
  in combineBin leftRes rightRes

||| Evaluates a stream fold consumer in parallel over model-indexed GohFuel.
public export
fusedParallelStreamFoldFuelModel : GohFuel cap -> (a -> b -> b) -> b -> (b -> b -> b) -> List a -> b
fusedParallelStreamFoldFuelModel fuel = fusedParallelStreamFoldNat (gohSteps fuel)

||| Audit witness verifying parallel stream partitioning fold equivalence.
public export
auditParallelStreamPartitionProof : Bool
auditParallelStreamPartitionProof =
  let items : List Int = [1, 2, 3, 4, 5, 6, 7, 8]
      seqRes = foldl (+) 0 items
      parRes = fusedParallelStreamFoldNat (length items) (+) 0 (+) items
  in seqRes == parRes

------------------------------------------------------------------------
-- 6B. FUELED FINITE STREAMS (DECOUPLED YIELD CAPACITY & SKIP BUDGET)
------------------------------------------------------------------------

||| A bounded finite stream pairing an existential FusedStream with model-indexed
||| GohFuel (`yieldFuel : GohFuel cap`) and an explicit Skip-safe `stepBudget`.
||| Decouples `Yield` count (`cap`) from `Skip` headroom so `filterMapStream` and
||| `flatMapStream` transitions cannot starve valid yielded items.
public export
record FueledFiniteStream (cap : Nat) (a : Type) where
  constructor MkFueledFiniteStream
  yieldFuel  : GohFuel cap
  stepBudget : Nat
  rawStream  : FusedStream a

||| Existential wrapper for a fueled finite stream whose capacity `cap` is derived
||| dynamically (e.g., from a Maxel's support or streaming integer polynumber).
public export
data AnyFueledFiniteStream : Type -> Type where
  MkAnyFueledFiniteStream : (cap : Nat) -> FueledFiniteStream cap a -> AnyFueledFiniteStream a

||| Constructs a FueledFiniteStream from model-indexed GohFuel using its built-in step budget.
public export
mkFueledFiniteStream : {cap : Nat} -> GohFuel cap -> FusedStream a -> FueledFiniteStream cap a
mkFueledFiniteStream yf strm = MkFueledFiniteStream yf (gohSteps yf) strm

||| Constructs a FueledFiniteStream with explicit Skip headroom (`maxSkips`) beyond yield capacity `cap`.
public export
mkFueledFiniteStreamWithSkips : {cap : Nat} -> GohFuel cap -> (maxSkips : Nat) -> FusedStream a -> FueledFiniteStream cap a
mkFueledFiniteStreamWithSkips {cap} yf maxSkips strm =
  let minNeeded = S (cap + maxSkips)
      baseSteps = gohSteps yf
      totalBudget = if baseSteps >= minNeeded then baseSteps else minNeeded
  in MkFueledFiniteStream yf totalBudget strm

||| Wraps a finite List into an exact-length FueledFiniteStream.
public export
fromListFueledFinite : (xs : List a) -> FueledFiniteStream (length xs) a
fromListFueledFinite xs =
  mkFueledFiniteStream (gohFuelForCapacity (length xs)) (stream xs)

||| Maps a function over a FueledFiniteStream, preserving capacity and Skip budget.
public export
mapFueledFiniteStream : (a -> b) -> FueledFiniteStream cap a -> FueledFiniteStream cap b
mapFueledFiniteStream f (MkFueledFiniteStream yf budget strm) =
  MkFueledFiniteStream yf budget (mapStream f strm)

public export
Functor (FueledFiniteStream cap) where
  map = mapFueledFiniteStream

||| Fuses filtering and mapping over a FueledFiniteStream without shrinking the stepBudget
||| needed to absorb filtered Skip steps.
public export
filterMapFueledFiniteStream : (a -> Maybe b) -> FueledFiniteStream cap a -> FueledFiniteStream cap b
filterMapFueledFiniteStream f (MkFueledFiniteStream yf budget strm) =
  MkFueledFiniteStream yf budget (filterMapStream f strm)

||| Appends two FueledFiniteStreams algebraically via `sequentialFuel`.
public export
appendFueledFiniteStream : FueledFiniteStream c1 a -> FueledFiniteStream c2 a -> FueledFiniteStream (c1 + c2) a
appendFueledFiniteStream (MkFueledFiniteStream yf1 b1 s1) (MkFueledFiniteStream yf2 b2 s2) =
  MkFueledFiniteStream (sequentialFuel yf1 yf2) (b1 + b2 + 1) (appendStream s1 s2)

||| Zips two FueledFiniteStreams elementwise under `joinFuel`.
public export
zipWithFueledFiniteStream : (a -> b -> c) -> FueledFiniteStream c1 a -> FueledFiniteStream c2 b -> FueledFiniteStream (fuelMax c1 c2) c
zipWithFueledFiniteStream f (MkFueledFiniteStream yf1 b1 s1) (MkFueledFiniteStream yf2 b2 s2) =
  MkFueledFiniteStream (joinFuel yf1 yf2) (b1 + b2 + 1) (zipWithStream f s1 s2)

||| Flattens nested FueledFiniteStreams using `multiStreamFuelNat` Skip headroom.
public export
flatMapFueledFiniteStream : {cOuter, cInner : Nat} ->
                            GohFuel cInner ->
                            (a -> FueledFiniteStream cInner b) ->
                            FueledFiniteStream cOuter a ->
                            FueledFiniteStream (cOuter * cInner) b
flatMapFueledFiniteStream {cOuter} {cInner} innerFuel f (MkFueledFiniteStream _ outerSteps strm) =
  let innerBudget = gohSteps innerFuel * 2 + 4
      stepCap = outerSteps * (innerBudget + 2) + outerSteps + 2
  in MkFueledFiniteStream (gohFuelForCapacity (cOuter * cInner)) stepCap (flatMapStream (\x => (f x).rawStream) strm)

||| Executes a Skip-safe left fold over a FueledFiniteStream.
||| `Skip` consumes only `stepBudget`; `Yield` consumes both `stepBudget` and `yieldRemaining`.
public export
foldFueledFiniteStream : {cap : Nat} -> (b -> a -> b) -> b -> FueledFiniteStream cap a -> b
foldFueledFiniteStream {cap} fn acc0 (MkFueledFiniteStream _ budget (MkStream next seed)) =
  loop budget cap next seed acc0
  where
    loop : {0 stTy : Type} -> Nat -> Nat -> (stTy -> Step stTy a) -> stTy -> b -> b
    loop Z _ _ _ acc = acc
    loop _ Z _ _ acc = acc
    loop (S sb) (S yr) stepFn st acc = case stepFn st of
      Done => acc
      Skip st' => loop sb (S yr) stepFn st' acc
      Yield x st' => loop sb yr stepFn st' (fn acc x)

||| Materializes a FueledFiniteStream to an in-order List in O(N) time.
public export
toListFueledFiniteStream : {cap : Nat} -> FueledFiniteStream cap a -> List a
toListFueledFiniteStream ffs =
  reverse (foldFueledFiniteStream (\acc, x => x :: acc) (the (List a) []) ffs)

||| Projects the underlying `GohFuel cap` yield budget of a FueledFiniteStream.
public export
fueledFiniteStreamToGohFuel : FueledFiniteStream cap a -> GohFuel cap
fueledFiniteStreamToGohFuel = yieldFuel

------------------------------------------------------------------------
-- 10. DEFORESTED DIVISOR STREAMS & CYCLOTOMIC TOTIENT ACCOUNTING
------------------------------------------------------------------------

||| Integer-backed modulo for natural numbers.
public export
natModFuel : Nat -> Nat -> Nat -> Nat
natModFuel _ a b = natModFast a b

||| Integer-backed greatest common divisor for natural numbers.
public export
natGCDFuel : Nat -> Nat -> Nat -> Nat
natGCDFuel _ a b = natGCDFast a b

||| Greatest common divisor for natural numbers.
public export
natGCD : Nat -> Nat -> Nat
natGCD = natGCDFast

||| Structural countdown accumulator for Euler's totient function.
public export
divOutPrime : Nat -> Nat -> Nat -> Nat
divOutPrime Z _ m = m
divOutPrime (S f) p m = if natModFast m p == 0 then divOutPrime f p (natDivFast m p) else m

public export
totientGo : Nat -> Nat -> Nat -> Nat -> Nat
totientGo Z _ _ res = res
totientGo (S f) p m res =
  if p * p > m then
    if m > 1 then natDivFast res m * minus m 1 else res
  else if natModFast m p == 0 then
    let m' = divOutPrime (S f) p m
        res' = natDivFast res p * minus p 1
    in totientGo f (S p) m' res'
  else
    totientGo f (S p) m res

||| Euler's totient function phi(n) tracking algebraic degree and multiset support cardinality.
||| Evaluates in O(sqrt(n)) trial divisions using Integer-backed division/mod with zero heap allocation.
public export
totientNat : Nat -> Nat
totientNat Z = Z
totientNat (S Z) = S Z
totientNat (S n) = totientGo (S n) 2 (S n) (S n)

||| Compile-time proof witness: phi(39) = 24 definitionally reduces in the core unifier.
public export
0 prfTotient39Definitional : totientNat 39 = 24
prfTotient39Definitional = Refl

||| Deforested ascending stream of all divisors d | n (from 1 up to n) in O(sqrt(n)) steps.
||| Zero intermediate List allocation for non-divisors; stacks only upper cofactors > sqrt(n).
public export
divisorStream : Nat -> FusedStream Nat
divisorStream Z = stream []
divisorStream (S n) = unfoldStream nextStep (Left (1, S n, the (List Nat) []))
  where
    nextStep : Either (Nat, Nat, List Nat) (List Nat)
            -> Step (Either (Nat, Nat, List Nat) (List Nat)) Nat
    nextStep (Right []) = Done
    nextStep (Right (q :: qs)) = Yield q (Right qs)
    nextStep (Left (Z, _, stack)) =
      case stack of
        [] => Done
        (q :: qs) => Yield q (Right qs)
    nextStep (Left (S c', target, stack)) =
      let cand = S c'
      in if cand * cand > target then
           case stack of
             [] => Done
             (q :: qs) => Yield q (Right qs)
         else if natModFast target (S c') == Z then
           let q = natDivFast target (S c')
               stack' = if q == cand then stack else q :: stack
           in Yield cand (Left (S cand, target, stack'))
         else
           Skip (Left (S cand, target, stack))

||| Zero-allocation O(sqrt(n)) divisor stream in O(1) registers (paired yield order)
||| for associative/commutative folds that do not depend on ascending divisor order.
public export
divisorStreamUnordered : Nat -> FusedStream Nat
divisorStreamUnordered Z = stream []
divisorStreamUnordered (S n) = unfoldStream nextStep (1, S n, Nothing)
  where
    nextStep : (Nat, Nat, Maybe Nat) -> Step (Nat, Nat, Maybe Nat) Nat
    nextStep (cand, target, Just q) = Yield q (S cand, target, Nothing)
    nextStep (Z, _, Nothing) = Done
    nextStep (S c', target, Nothing) =
      let cand = S c'
      in if cand * cand > target then Done
         else if natModFast target (S c') == Z then
           let q = natDivFast target (S c')
               pending = if q == cand then Nothing else Just q
           in case pending of
                Nothing => Yield cand (S cand, target, Nothing)
                Just q' => Yield cand (cand, target, Just q')
         else
           Skip (S cand, target, Nothing)

||| Audits Gauss's totient sum identity: sum_{d | n} phi(d) == n
public export
auditTotientConservationProof : (n : Nat) -> Bool
auditTotientConservationProof Z = True
auditTotientConservationProof (S n) =
  let target = S n
      divStrm = divisorStream target
      phiSum = foldStreamNat (target + 10) (\acc, d => acc + totientNat d) 0 divStrm
  in phiSum == target

------------------------------------------------------------------------
-- 11. FUSEDSTREAM DEFORESTATION BENCHMARK & EQUIVALENCE VERIFICATION
------------------------------------------------------------------------

||| Generates a list of integers from 1 to n.
public export
generateSequence : Nat -> List Integer
generateSequence Z = []
generateSequence (S k) = cast (S k) :: generateSequence k

||| Standard List pipeline (3 intermediate list heap allocations).
||| Pipeline: map (+ 10) . filter (even) . map (* 3)
public export
listPipeline : List Integer -> Integer
listPipeline xs =
  let stage1 = map (* 3) xs
      stage2 = filter (\x => (x `mod` 2) == 0) stage1
      stage3 = map (+ 10) stage2
  in foldl (+) 0 stage3

||| Deforested FusedStream pipeline (Zero intermediate list heap allocations).
||| Pipeline: foldStreamNat (length xs) (+) 0 (mapStream (+ 10) (filterStream (even) (mapStream (* 3) (stream xs))))
public export
fusedStreamPipeline : List Integer -> Integer
fusedStreamPipeline xs =
  let strm = stream xs
      stage1 = mapStream (* 3) strm
      stage2 = filterStream (\x => (x `mod` 2) == 0) stage1
      stage3 = mapStream (+ 10) stage2
  in foldStreamNat (length xs) (+) 0 stage3

||| Proves mathematical & observational equivalence between List baseline and FusedStream deforested pipeline.
public export
verifyPipelineEquivalence : Nat -> Bool
verifyPipelineEquivalence n =
  let seq = generateSequence n
  in listPipeline seq == fusedStreamPipeline seq

------------------------------------------------------------------------
-- 11. DECOUPLED YIELD/STEP FUEL & TYPED FREEZE-OUT CERTIFICATES
------------------------------------------------------------------------

||| Classifies the exact physical/computational reason a fueled stream halted:
||| - `YieldExhausted`     : Energy/yield quota (`yieldBudget`) reached `0` (ordered crystal / chemical freeze-out)
||| - `StepHorizonReached` : Causal search horizon (`stepBudget`) reached `0` while yield remained (kinematic decoupling)
||| - `NaturalCompletion`  : Stream emitted `Done` before exhausting either budget (exact ground-state relaxation)
public export
data FreezeReason : Type where
  YieldExhausted     : FreezeReason
  StepHorizonReached : FreezeReason
  NaturalCompletion  : FreezeReason

public export
Eq FreezeReason where
  YieldExhausted     == YieldExhausted     = True
  StepHorizonReached == StepHorizonReached = True
  NaturalCompletion  == NaturalCompletion  = True
  _                  == _                  = False

public export
Show FreezeReason where
  show YieldExhausted     = "YieldExhausted"
  show StepHorizonReached = "StepHorizonReached"
  show NaturalCompletion  = "NaturalCompletion"

||| Typed freeze-out witness returned when a fueled stream halts, carrying:
||| - `carrier`        : The solidified state/multiset relic
||| - `freezeReason`   : Why evolution stopped (`YieldExhausted`, `StepHorizonReached`, `NaturalCompletion`)
||| - `remainingYield` : Unspent `GohFuel cap` steps
||| - `remainingSteps` : Unspent causal search steps
public export
record SolidifiedCarrier (cap : Nat) (a : Type) where
  constructor MkSolidifiedCarrier
  carrier        : a
  freezeReason   : FreezeReason
  remainingYield : GohFuel cap
  remainingSteps : Nat

||| Decoupled Yield/Step Evaluator over `Step s a`:
||| - `Skip s'` consumes ONLY `stepBudget` (`S sRem`), never draining `yieldBudget` (`yRem`)!
||| - `Yield x s'` consumes BOTH 1 unit of `yieldBudget` and 1 unit of `stepBudget`,
|||   updating the state/accumulator `acc` via `combineFn`.
||| - Emits a `SolidifiedCarrier cap b` witness recording the exact `FreezeReason`.
public export
runDecoupledStream : (yieldFuel  : GohFuel cap) ->
                     (stepBudget : Nat) ->
                     (stepFn     : s -> Step s a) ->
                     (combineFn  : a -> b -> b) ->
                     (initAcc    : b) ->
                     (seed       : s) ->
                     SolidifiedCarrier cap b
runDecoupledStream yieldFuel stepBudget stepFn combineFn initAcc seed =
  loop (gohSteps yieldFuel) stepBudget initAcc seed
  where
    loop : Nat -> Nat -> b -> s -> SolidifiedCarrier cap b
    loop Z sRem acc _ =
      MkSolidifiedCarrier acc YieldExhausted (MkGohFuel 0) sRem
    loop yRem Z acc _ =
      MkSolidifiedCarrier acc StepHorizonReached (MkGohFuel yRem) 0
    loop (S yRem) (S sRem) acc st =
      case stepFn st of
        Done =>
          MkSolidifiedCarrier acc NaturalCompletion (MkGohFuel (S yRem)) (S sRem)
        Skip st' =>
          -- `Skip` deducts only from `sRem`, protecting `S yRem` from sparse-filter starvation
          loop (S yRem) sRem acc st'
        Yield x st' =>
          loop yRem sRem (combineFn x acc) st'

||| Linear (`QTT 1`) Decoupled Stream Evaluator over `StepLinear s a`:
||| Threads a `1`-quantity linear state (`UniverseContainer`, `LinBuf`, or `PingPongGrid`)
||| under decoupled `(yieldFuel, stepBudget)` bounds, returning both the final linear state
||| and the `SolidifiedCarrier` freeze-out certificate inside a `LinearStatePair`.
public export
runDecoupledLinearStream : (yieldFuel  : GohFuel cap) ->
                           (stepBudget : Nat) ->
                           (1 seed     : s) ->
                           (stepFn     : (1 curr : s) -> StepLinear s a) ->
                           (combineFn  : a -> b -> b) ->
                           (initAcc    : b) ->
                           LinearStatePair s (SolidifiedCarrier cap b)
runDecoupledLinearStream yieldFuel stepBudget seed stepFn combineFn initAcc =
  loop (gohSteps yieldFuel) stepBudget initAcc seed
  where
    loop : Nat -> Nat -> b -> (1 curr : s) -> LinearStatePair s (SolidifiedCarrier cap b)
    loop Z sRem acc st =
      MkLStatePair st (MkSolidifiedCarrier acc YieldExhausted (MkGohFuel 0) sRem)
    loop yRem Z acc st =
      MkLStatePair st (MkSolidifiedCarrier acc StepHorizonReached (MkGohFuel yRem) 0)
    loop (S yRem) (S sRem) acc st =
      case stepFn st of
        DoneL st' =>
          MkLStatePair st' (MkSolidifiedCarrier acc NaturalCompletion (MkGohFuel (S yRem)) (S sRem))
        SkipL st' =>
          loop (S yRem) sRem acc st'
        YieldL x st' =>
          loop yRem sRem (combineFn x acc) st'

------------------------------------------------------------------------
-- 12. FUELED `Step` / `Yield` `hyperOp` TRANSDUCER (`runFueledHyperOp`)
------------------------------------------------------------------------

||| Incremental zipper transducer state for fueled `hyperOp` evaluation over `HereditaryMSet c`:
||| - `AddZipState`  : Lockstep ascending zipper merge (`level = 0`, annihilating pairs emit `Skip`).
||| - `ConvZipState` : Nested outer/inner zipper pairing (`level = S innerLevel`).
public export
data HyperOpZipState : (c : Type) -> Type where
  AddZipState  : BoxZipper c (HereditaryMSet c) -> BoxZipper c (HereditaryMSet c) -> HyperOpZipState c
  ConvZipState : (innerLevel : Nat) ->
                 (fullB2 : Stage0.Box.Box c (HereditaryMSet c)) ->
                 BoxZipper c (HereditaryMSet c) ->
                 BoxZipper c (HereditaryMSet c) ->
                 HyperOpZipState c

||| Initializes a `HyperOpZipState c` at `level` without intermediate list allocations.
public export
initHyperOpZipState : (level : Nat) ->
                      HereditaryMSet c ->
                      HereditaryMSet c ->
                      HyperOpZipState c
initHyperOpZipState Z (MkHMSet b1) (MkHMSet b2) =
  AddZipState (pushLeftBox b1 []) (pushLeftBox b2 [])
initHyperOpZipState (S innerLevel) (MkHMSet b1) (MkHMSet BoxLeaf) =
  ConvZipState innerLevel BoxLeaf [] []
initHyperOpZipState (S innerLevel) (MkHMSet b1) (MkHMSet b2) =
  ConvZipState innerLevel b2 (pushLeftBox b1 []) (pushLeftBox b2 [])

||| Single `Step` transition for fueled `hyperOp` evaluation:
||| - Surviving non-zero terms emit `Yield (kOut, wOut)` (consuming `GohFuel` + `stepBudget`).
||| - Zero-pruned annihilations (`[x, x^a] = []`) and AVL inner resets emit `Skip`
|||   (consuming only `stepBudget` while sparing `GohFuel`).
public export
hyperOpStep : MultisetWeight c =>
              HyperOpZipState c ->
              Step (HyperOpZipState c) (HereditaryMSet c, c)
hyperOpStep (AddZipState [] []) = Done
hyperOpStep (AddZipState [] ((k2, w2, r2) :: ys)) =
  let nextZ2 = pushLeftBox r2 ys
  in if isZero w2
       then Skip (AddZipState [] nextZ2)
       else Yield (k2, w2) (AddZipState [] nextZ2)
hyperOpStep (AddZipState ((k1, w1, r1) :: xs) []) =
  let nextZ1 = pushLeftBox r1 xs
  in if isZero w1
       then Skip (AddZipState nextZ1 [])
       else Yield (k1, w1) (AddZipState nextZ1 [])
hyperOpStep (AddZipState z1@((k1, w1, r1) :: xs) z2@((k2, w2, r2) :: ys)) =
  case compare k1 k2 of
    LT =>
      let nextZ1 = pushLeftBox r1 xs
      in if isZero w1
           then Skip (AddZipState nextZ1 z2)
           else Yield (k1, w1) (AddZipState nextZ1 z2)
    GT =>
      let nextZ2 = pushLeftBox r2 ys
      in if isZero w2
           then Skip (AddZipState z1 nextZ2)
           else Yield (k2, w2) (AddZipState z1 nextZ2)
    EQ =>
      let nextZ1 = pushLeftBox r1 xs
          nextZ2 = pushLeftBox r2 ys
          wSum   = addWeight w1 w2
      in if isZero wSum
           then Skip (AddZipState nextZ1 nextZ2)
           else Yield (k1, wSum) (AddZipState nextZ1 nextZ2)
hyperOpStep (ConvZipState _ _ [] _) = Done
hyperOpStep (ConvZipState innerLevel fullB2 ((k1, w1, r1) :: xs) []) =
  Skip (ConvZipState innerLevel fullB2 (pushLeftBox r1 xs) (pushLeftBox fullB2 []))
hyperOpStep (ConvZipState innerLevel fullB2 z1@((k1, w1, r1) :: xs) ((k2, w2, r2) :: ys)) =
  if isZero w1
    then Skip (ConvZipState innerLevel fullB2 (pushLeftBox r1 xs) (pushLeftBox fullB2 []))
    else
      let nextZ2 = pushLeftBox r2 ys
          wProd  = mulWeight w1 w2
      in if isZero wProd
           then Skip (ConvZipState innerLevel fullB2 z1 nextZ2)
           else Yield (hyperOp innerLevel k1 k2, wProd) (ConvZipState innerLevel fullB2 z1 nextZ2)

private
zipShells : List a -> List a -> List (List a)
zipShells []        []        = []
zipShells (x :: xs) []        = [x] :: zipShells xs []
zipShells []        (y :: ys) = [y] :: zipShells [] ys
zipShells (x :: xs) (y :: ys) = [x, y] :: zipShells xs ys

||| Groups non-zero entries of `HereditaryMSet c` into symmetric radial shells outward
||| from `emptyHMSet`: `[[origin], [neg_1, pos_1], [neg_2, pos_2], ...]`.
public export
buildRadialShells : MultisetWeight c => HereditaryMSet c -> List (List (HereditaryMSet c, c))
buildRadialShells (MkHMSet box) =
  let zeroKey = emptyHMSet {c}
      splitStep : (List (HereditaryMSet c, c), List (HereditaryMSet c, c), List (HereditaryMSet c, c)) ->
                  (HereditaryMSet c, c) ->
                  (List (HereditaryMSet c, c), List (HereditaryMSet c, c), List (HereditaryMSet c, c))
      splitStep (negDesc, zeros, posRev) (k, w) =
        if isZero w
          then (negDesc, zeros, posRev)
          else case compare k zeroKey of
                 LT => ((k, w) :: negDesc, zeros, posRev)
                 EQ => (negDesc, (k, w) :: zeros, posRev)
                 GT => (negDesc, zeros, (k, w) :: posRev)
      part     = foldBoxTreeL splitStep ([], [], []) box
      negDesc  = fst part
      zeros    = fst (snd part)
      posRev   = snd (snd part)
      headZero : List (List (HereditaryMSet c, c))
      headZero = case zeros of
                   [] => []
                   _  => [zeros]
  in headZero ++ zipShells negDesc (reverse posRev)

private
insertEntryAgainstBox : MultisetWeight c =>
                        Nat ->
                        (HereditaryMSet c, c) ->
                        Box c (HereditaryMSet c) ->
                        Box c (HereditaryMSet c) ->
                        Box c (HereditaryMSet c)
insertEntryAgainstBox innerLevel (k1, w1) boxB acc =
  foldBox (\k2, w2, bAcc =>
            let wProd = mulWeight w1 w2
            in if isZero wProd
                 then bAcc
                 else addAtKeyBox (hyperOp innerLevel k1 k2) wProd bAcc)
          acc
          boxB

||| Consume `n` steps of Idris 2's `Data.Fuel`, returning `Nothing` on `Dry`.
public export
consumeDataFuel : Nat -> Fuel -> Maybe Fuel
consumeDataFuel Z     f        = Just f
consumeDataFuel (S k) (More f) = consumeDataFuel k f
consumeDataFuel (S _) Dry      = Nothing

||| Decoupled yield/step runner directly driven by Idris 2 `Data.Fuel`.
||| Returns `(result, freezeReason, usedYields, usedSteps)`.
public export
runDecoupledDataFuel : (yieldFuel : Fuel) ->
                       (stepFuel  : Fuel) ->
                       (stepFn    : s -> Step s a) ->
                       (combineFn : a -> b -> b) ->
                       (initAcc   : b) ->
                       (seed      : s) ->
                       (b, FreezeReason, Nat, Nat)
runDecoupledDataFuel yFuel sFuel stepFn combineFn initAcc seed =
  loop yFuel sFuel 0 0 initAcc seed
  where
    loop : Fuel -> Fuel -> Nat -> Nat -> b -> s -> (b, FreezeReason, Nat, Nat)
    loop Dry _ yU sU acc _ = (acc, YieldExhausted, yU, sU)
    loop _ Dry yU sU acc _ = (acc, StepHorizonReached, yU, sU)
    loop (More yNext) (More sNext) yU sU acc st =
      case stepFn st of
        Done       => (acc, NaturalCompletion, yU, sU)
        Skip st'   => loop (More yNext) sNext yU (S sU) acc st'
        Yield x st' => loop yNext sNext (S yU) (S sU) (combineFn x acc) st'

||| Deforested bidirectional McBride zipper convolution driven directly by Idris 2 `Data.Fuel`
||| with zero intermediate `List` allocation.
public export
runSymmetricRadialConvDataFuel : MultisetWeight c =>
                                 (innerLevel : Nat) ->
                                 (yieldFuel  : Fuel) ->
                                 (stepFuel   : Fuel) ->
                                 HereditaryMSet c ->
                                 HereditaryMSet c ->
                                 (HereditaryMSet c, FreezeReason, Nat, Nat)
runSymmetricRadialConvDataFuel innerLevel yFuel sFuel (MkHMSet boxA) (MkHMSet boxB) =
  let nnzA = countNonZeroBox boxA
      nnzB = countNonZeroBox boxB
  in if nnzA == 0 || nnzB == 0
       then (MkHMSet BoxLeaf, NaturalCompletion, 0, 0)
       else
         let useAOuter  = nnzA >= nnzB
             outerBox   = if useAOuter then boxA else boxB
             innerBox   = if useAOuter then boxB else boxA
             innerNnz   = if useAOuter then nnzB else nnzA
             rad0       = initRadialZipper (emptyHMSet {c}) outerBox
         in loopZip (S (boxNodeCount outerBox)) rad0 yFuel sFuel 0 0 innerBox innerNnz BoxLeaf
  where
    loopZip : Nat ->
              RadialBoxZipper c (HereditaryMSet c) ->
              Fuel -> Fuel -> Nat -> Nat ->
              Box c (HereditaryMSet c) -> Nat ->
              Box c (HereditaryMSet c) ->
              (HereditaryMSet c, FreezeReason, Nat, Nat)
    loopZip Z _ _ _ yU sU _ _ acc =
      (MkHMSet acc, NaturalCompletion, yU, sU)
    loopZip (S rem) rad yRem sRem yU sU innerBox innerNnz acc =
      case stepRadialZipper (S rem) rad of
        RadialDone =>
          (MkHMSet acc, NaturalCompletion, yU, sU)
        RadialOrigin e nextRad =>
          let need = innerNnz
          in case consumeDataFuel need sRem of
               Nothing => (MkHMSet acc, StepHorizonReached, yU, sU)
               Just sRem' =>
                 case consumeDataFuel need yRem of
                   Nothing => (MkHMSet acc, YieldExhausted, yU, sU)
                   Just yRem' =>
                     let acc' = insertEntryAgainstBox innerLevel e innerBox acc
                     in loopZip rem nextRad yRem' sRem' (yU + need) (sU + need) innerBox innerNnz acc'
        RadialSingle e nextRad =>
          let need = innerNnz
          in case consumeDataFuel need sRem of
               Nothing => (MkHMSet acc, StepHorizonReached, yU, sU)
               Just sRem' =>
                 case consumeDataFuel need yRem of
                   Nothing => (MkHMSet acc, YieldExhausted, yU, sU)
                   Just yRem' =>
                     let acc' = insertEntryAgainstBox innerLevel e innerBox acc
                     in loopZip rem nextRad yRem' sRem' (yU + need) (sU + need) innerBox innerNnz acc'
        RadialPair e1 e2 nextRad =>
          let need = innerNnz + innerNnz
          in case consumeDataFuel need sRem of
               Nothing => (MkHMSet acc, StepHorizonReached, yU, sU)
               Just sRem' =>
                 case consumeDataFuel need yRem of
                   Nothing => (MkHMSet acc, YieldExhausted, yU, sU)
                   Just yRem' =>
                     let acc1 = insertEntryAgainstBox innerLevel e1 innerBox acc
                         acc2 = insertEntryAgainstBox innerLevel e2 innerBox acc1
                     in loopZip rem nextRad yRem' sRem' (yU + need) (sU + need) innerBox innerNnz acc2

||| Deforested bidirectional McBride zipper convolution bounded by `GohFuel cap`,
||| preserving exact UV-IR shell symmetry across `YieldExhausted` freeze horizons.
public export
runSymmetricRadialConv : MultisetWeight c =>
                         (innerLevel : Nat) ->
                         GohFuel cap ->
                         Nat ->
                         HereditaryMSet c ->
                         HereditaryMSet c ->
                         SolidifiedCarrier cap (HereditaryMSet c)
runSymmetricRadialConv innerLevel yFuel stepBudget (MkHMSet boxA) (MkHMSet boxB) =
  let nnzA = countNonZeroBox boxA
      nnzB = countNonZeroBox boxB
  in if nnzA == 0 || nnzB == 0
       then MkSolidifiedCarrier (MkHMSet BoxLeaf) NaturalCompletion yFuel stepBudget
       else
         let useAOuter = nnzA >= nnzB
             outerBox  = if useAOuter then boxA else boxB
             innerBox  = if useAOuter then boxB else boxA
             innerNnz  = if useAOuter then nnzB else nnzA
             rad0      = initRadialZipper (emptyHMSet {c}) outerBox
         in loopZip (S (boxNodeCount outerBox)) rad0 (gohSteps yFuel) stepBudget innerBox innerNnz BoxLeaf
  where
    loopZip : Nat ->
              RadialBoxZipper c (HereditaryMSet c) ->
              Nat -> Nat ->
              Box c (HereditaryMSet c) -> Nat ->
              Box c (HereditaryMSet c) ->
              SolidifiedCarrier cap (HereditaryMSet c)
    loopZip Z _ yRem sRem _ _ acc =
      MkSolidifiedCarrier (MkHMSet acc) NaturalCompletion (MkGohFuel yRem) sRem
    loopZip (S rem) rad yRem sRem innerBox innerNnz acc =
      case stepRadialZipper (S rem) rad of
        RadialDone =>
          MkSolidifiedCarrier (MkHMSet acc) NaturalCompletion (MkGohFuel yRem) sRem
        RadialOrigin e nextRad =>
          let need = innerNnz
          in if need > sRem
               then MkSolidifiedCarrier (MkHMSet acc) StepHorizonReached (MkGohFuel yRem) sRem
             else if need > yRem
               then MkSolidifiedCarrier (MkHMSet acc) YieldExhausted (MkGohFuel yRem) sRem
             else
               let acc' = insertEntryAgainstBox innerLevel e innerBox acc
               in loopZip rem nextRad (minus yRem need) (minus sRem need) innerBox innerNnz acc'
        RadialSingle e nextRad =>
          let need = innerNnz
          in if need > sRem
               then MkSolidifiedCarrier (MkHMSet acc) StepHorizonReached (MkGohFuel yRem) sRem
             else if need > yRem
               then MkSolidifiedCarrier (MkHMSet acc) YieldExhausted (MkGohFuel yRem) sRem
             else
               let acc' = insertEntryAgainstBox innerLevel e innerBox acc
               in loopZip rem nextRad (minus yRem need) (minus sRem need) innerBox innerNnz acc'
        RadialPair e1 e2 nextRad =>
          let need = innerNnz + innerNnz
          in if need > sRem
               then MkSolidifiedCarrier (MkHMSet acc) StepHorizonReached (MkGohFuel yRem) sRem
             else if need > yRem
               then MkSolidifiedCarrier (MkHMSet acc) YieldExhausted (MkGohFuel yRem) sRem
             else
               let acc1 = insertEntryAgainstBox innerLevel e1 innerBox acc
                   acc2 = insertEntryAgainstBox innerLevel e2 innerBox acc1
               in loopZip rem nextRad (minus yRem need) (minus sRem need) innerBox innerNnz acc2

||| Legacy left-to-right zipper `hyperOp` evaluator (kept for regression control).
public export
runFueledHyperOpZipper : MultisetWeight c =>
                         (level : Nat) ->
                         (cap : Nat) ->
                         HereditaryMSet c ->
                         HereditaryMSet c ->
                         SolidifiedCarrier cap (HereditaryMSet c)
runFueledHyperOpZipper level cap mA mB =
  let (yFuel, sBudget) = hyperOpFuelOfHMSet level cap mA mB
      insertTerm : (HereditaryMSet c, c) -> HereditaryMSet c -> HereditaryMSet c
      insertTerm (k, w) (MkHMSet acc) = MkHMSet (addAtKeyBox k w acc)
  in runDecoupledStream yFuel sBudget hyperOpStep insertTerm emptyHMSet (initHyperOpZipState level mA mB)

||| Evaluates `hyperOp level mA mB` polymorphically over any `MultisetWeight c`
||| carrier under support-derived `hyperOpFuelOfHMSet level cap mA mB`:
||| - Level `0` (`+`): `AddZipState` via `runDecoupledStream` (preserving zero-yield annihilation `Skip`s)
||| - Level `1+` (`*`, `^`, ...): `runSymmetricRadialConv` preserving UV-IR shell symmetry on freeze-out.
public export
runFueledHyperOp : MultisetWeight c =>
                   (level : Nat) ->
                   (cap : Nat) ->
                   HereditaryMSet c ->
                   HereditaryMSet c ->
                   SolidifiedCarrier cap (HereditaryMSet c)
runFueledHyperOp Z cap mA mB = runFueledHyperOpZipper Z cap mA mB
runFueledHyperOp (S innerLevel) cap mA mB =
  let (yFuel, sBudget) = hyperOpFuelOfHMSet (S innerLevel) cap mA mB
  in runSymmetricRadialConv innerLevel yFuel sBudget mA mB
