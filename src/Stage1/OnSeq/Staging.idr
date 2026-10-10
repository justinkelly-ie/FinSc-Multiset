module Stage1.OnSeq.Staging

import public Stage1.OnSeq
import public Stage0.OnSeq.FusedStream
import Data.SortedMap

%default total

------------------------------------------------------------------------
-- 1. EXPLICIT 2LTT STAGING MODAL COMBINATORS FOR ON-SEQUENCES
------------------------------------------------------------------------

||| 2LTT Type Lifting (⇑OnSeq a): Marks an OnSeq as a Stage 1 meta-level lifted sequence.
public export
0 LiftOnSeq : Type -> Type
LiftOnSeq a = OnSeq a

||| 2LTT Quoting (⟨f⟩): Quotes a raw term generator function (n ↦ f(n)) into a Stage 1 static OnSeq.
public export
quoteOnSeq : Nat -> (Nat -> a) -> LiftOnSeq a
quoteOnSeq start f = MkOnSeq start f

||| 2LTT Splicing (~seq): Splices a Stage 1 static OnSeq down into a Stage 0 deforested FusedStream.
public export
spliceOnSeqToStream : LiftOnSeq a -> (idx : Nat) -> (len : Nat) -> FusedStream a
spliceOnSeqToStream seq idx len = stream (elements (getClip seq idx len))

||| 2LTT Monoid Splicing (~seq ↦ Monoid): Splices a Stage 1 static OnSeq directly down
||| into a Stage 0 consolidated Multiset Monoid map payload.
public export
spliceOnSeqToMonoid : Ord a => LiftOnSeq a -> (idx : Nat) -> (len : Nat) -> SortedMap a Nat
spliceOnSeqToMonoid {a} seq idx len =
  let strm = spliceOnSeqToStream seq idx len
  in foldStreamNat len (\acc, x => case lookup x acc of
                                     Nothing => insert x 1 acc
                                     Just v  => insert x (v + 1) acc)
                       (empty {v=Nat}) strm

------------------------------------------------------------------------
-- 2. EXPLICIT DEFINITIONAL INVERSE LAWS
------------------------------------------------------------------------

||| 2LTT Inverse Law: Splicing term retrieval on a quoted OnSeq yields the exact generator value definitionally (~⟨f⟩(n) ≡ Just (f n)).
public export
0 inverseSpliceQuoteOnSeq : (f : Nat -> a) -> (n : Nat) -> getTerm (quoteOnSeq Z f) n = Just (f n)
inverseSpliceQuoteOnSeq _ Z = Refl
inverseSpliceQuoteOnSeq _ (S k) = Refl

||| QTT 0 Erased Proof: Splicing a quoted constant OnSeq preserves scalar payload invariance.
public export
0 prfConstantOnSeqSpliceInvariance : (x : a) -> (n : Nat) -> getTerm (constant Z x) n = Just x
prfConstantOnSeqSpliceInvariance _ Z = Refl
prfConstantOnSeqSpliceInvariance _ (S k) = Refl
