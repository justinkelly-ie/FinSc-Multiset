module Stage1.OnSeq

import Data.Linear
import public Stage0.BoxInt
import Stage0.SignedFraction
import public Stage0.OnSeq.OnMSet

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
-- 3. CANONICAL COMPILE-TIME PROOFS
------------------------------------------------------------------------

||| Audits that finite Clip extraction from the identity on-sequence [n>
||| correctly produces the expected elements and length.
public export
auditOnSeqClipExtractionProof : Bool
auditOnSeqClipExtractionProof =
  let clip = getClip (identity 1) 1 4
  in (clip.startIdx == 1) && (clip.elements == [1, 2, 3, 4])
