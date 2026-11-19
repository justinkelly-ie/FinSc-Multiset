module Stage1.OnSeq

import Data.Linear
import public Stage0.BoxInt
import public Stage0.Multiset
import Stage0.SignedFraction
import public Stage0.OnSeq.OnMSet
import public Stage0.OnSeq.FusedStream
import public Stage1.TypeTheory.MultisetLevel

%default total

------------------------------------------------------------------------
-- 1. SPECIALIZED ON-SEQUENCE ALGEBRAS (RE-EXPORTS Stage0.OnSeq.OnMSet)
------------------------------------------------------------------------

||| Pointwise addition of BoxInt on-sequences.
public export
addOnSeqBox : OnSeq BoxInt -> OnSeq BoxInt -> OnSeq BoxInt
addOnSeqBox = zipWith (+)

||| Pointwise multiplication of BoxInt on-sequences.
public export
mulOnSeqBox : OnSeq BoxInt -> OnSeq BoxInt -> OnSeq BoxInt
mulOnSeqBox = zipWith (*)

||| Pointwise addition of MSetFraction on-sequences.
public export
addOnSeqMSF : OnSeq MSetFraction -> OnSeq MSetFraction -> OnSeq MSetFraction
addOnSeqMSF = zipWith addMSF

||| Pointwise multiplication of MSetFraction on-sequences.
public export
mulOnSeqMSF : OnSeq MSetFraction -> OnSeq MSetFraction -> OnSeq MSetFraction
mulOnSeqMSF = zipWith mulMSF

------------------------------------------------------------------------
-- 2. QUANTITATIVE TYPE THEORY (QTT) SEQUENCING
------------------------------------------------------------------------

||| Linearly advance an ongoing sequence by evaluating at term n and stepping the lower bound.
public export
linearStepOnSeq : (1 seq : OnSeq a) -> (n : Nat) -> (Maybe a, OnSeq a)
linearStepOnSeq (MkOnSeq s at) n = (getTerm (MkOnSeq s at) n, MkOnSeq (S (max s n)) at)

------------------------------------------------------------------------
-- 3. EXPLICIT 2LTT STAGING MODAL COMBINATORS FOR ON-SEQUENCES
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

||| Quotes a raw multiset sequence generator function into a Stage 1 static OnSeq payload.
public export
quoteOnSeqMultiset : Nat -> (Nat -> Multiset BoxInt a) -> LiftOnSeq (Multiset BoxInt a)
quoteOnSeqMultiset start f = MkOnSeq start f

||| Splices a Stage 1 static OnSeq multiset sequence directly down into a Stage 0 consolidated Box multiset monoid.
public export
spliceOnSeqToBox : Ord a => LiftOnSeq (Multiset BoxInt a) -> (idx : Nat) -> (len : Nat) -> Carrier a
spliceOnSeqToBox seq idx len =
  let strm = spliceOnSeqToStream seq idx len
  in foldStreamNat len (\acc, m => foldMultiset (\k, w, innerAcc => insertBox k w innerAcc) acc m)
                       emptyBox strm

------------------------------------------------------------------------
-- 4. EXPLICIT DEFINITIONAL INVERSE LAWS & PROOFS
------------------------------------------------------------------------

||| 2LTT Inverse Law: Splicing term retrieval on a quoted OnSeq yields the exact generator value definitionally (~⟨f⟩(n) ≡ Just (f n)).
public export
0 inverseSpliceQuoteOnSeq : (f : Nat -> a) -> (n : Nat) -> getTerm (quoteOnSeq Z f) n = Just (f n)
inverseSpliceQuoteOnSeq _ Z = Refl
inverseSpliceQuoteOnSeq _ (S _) = Refl

||| QTT 0 Erased Proof: Splicing a quoted constant OnSeq preserves scalar payload invariance.
public export
0 prfConstantOnSeqSpliceInvariance : (x : a) -> (n : Nat) -> getTerm (constant Z x) n = Just x
prfConstantOnSeqSpliceInvariance _ Z = Refl
prfConstantOnSeqSpliceInvariance _ (S _) = Refl

||| Splicing term retrieval on a quoted multiset sequence yields the exact generator value definitionally.
public export
0 inverseSpliceQuoteOnSeqMultiset : (f : Nat -> Multiset BoxInt a) -> (n : Nat) -> getTerm (quoteOnSeqMultiset Z f) n = Just (f n)
inverseSpliceQuoteOnSeqMultiset _ Z = Refl
inverseSpliceQuoteOnSeqMultiset _ (S _) = Refl

||| Audits that finite Clip extraction from the identity on-sequence [n>
||| correctly produces the expected elements and length.
public export
auditOnSeqClipExtractionProof : Bool
auditOnSeqClipExtractionProof =
  let clip = getClip (identity 1) 1 4
  in (clip.startIdx == 1) && (clip.elements == [1, 2, 3, 4])

