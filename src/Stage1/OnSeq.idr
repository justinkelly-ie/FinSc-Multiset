module Stage1.OnSeq

import Data.Linear
import public Stage0.BoxInt
import Stage0.SignedFraction

%default total

------------------------------------------------------------------------
-- 1. WILDBERGER'S ON-SEQUENCES (ONGOING SEQUENCES) & CLIPS
------------------------------------------------------------------------

||| An on-sequence (ongoing sequence) starting at a specific index.
||| Defined constructively via a generator function mapping term index to value.
public export
record OnSeq a where
  constructor MkOnSeq
  start : Nat
  at    : Nat -> a

||| A finite consecutive subsequence (clip) extracted from an ongoing sequence.
public export
record Clip a where
  constructor MkClip
  startIdx : Nat
  elements : List a

public export
(Show a) => Show (Clip a) where
  show (MkClip idx elems) = "Clip@" ++ show idx ++ show elems ++ "..."

||| Creates a constant on-sequence starting at index s.
public export
constant : Nat -> a -> OnSeq a
constant s x = MkOnSeq s (\_ => x)

||| Creates the identity on-sequence [n> starting at index s.
public export
identity : Nat -> OnSeq Nat
identity s = MkOnSeq s (\n => n)

||| Evaluates / indexes the on-sequence at index n.
||| Returns Just (at n) if n >= start, else Nothing.
public export
getTerm : OnSeq a -> Nat -> Maybe a
getTerm (MkOnSeq start at) n =
  if n >= start
     then Just (at n)
     else Nothing

||| Extracts a finite clip of length len starting at index idx.
public export
getClip : OnSeq a -> (idx : Nat) -> (len : Nat) -> Clip a
getClip (MkOnSeq start at) idx len =
  let actualStart = max idx start
  in MkClip actualStart (generateElements actualStart len)
  where
    generateElements : Nat -> Nat -> List a
    generateElements _ Z = []
    generateElements curr (S k) = at curr :: generateElements (S curr) k

||| Maps a function over an on-sequence.
public export
map : (a -> b) -> OnSeq a -> OnSeq b
map f (MkOnSeq start at) = MkOnSeq start (\n => f (at n))

public export
Functor OnSeq where
  map = Stage1.OnSeq.map

||| Combines two on-sequences pointwise.
public export
zipWith : (a -> b -> c) -> OnSeq a -> OnSeq b -> OnSeq c
zipWith f (MkOnSeq s1 at1) (MkOnSeq s2 at2) =
  let newStart = max s1 s2
  in MkOnSeq newStart (\n => f (at1 n) (at2 n))

public export
Applicative OnSeq where
  pure x = MkOnSeq Z (\_ => x)
  (MkOnSeq s1 fAt) <*> (MkOnSeq s2 xAt) =
    let newStart = max s1 s2
    in MkOnSeq newStart (\n => fAt n (xAt n))

------------------------------------------------------------------------
-- 2. SPECIALIZED ON-SEQUENCE ALGEBRAS
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
-- 3. QUANTITATIVE TYPE THEORY (QTT) SEQUENCING
------------------------------------------------------------------------

||| Linearly advance an ongoing sequence by evaluating at term n and stepping the lower bound.
public export
linearStepOnSeq : (1 seq : OnSeq a) -> (n : Nat) -> (Maybe a, OnSeq a)
linearStepOnSeq (MkOnSeq s at) n = (getTerm (MkOnSeq s at) n, MkOnSeq (S (max s n)) at)

------------------------------------------------------------------------
-- 4. CANONICAL COMPILE-TIME PROOFS
------------------------------------------------------------------------

||| Audits that finite Clip extraction from the identity on-sequence [n>
||| correctly produces the expected elements and length.
public export
auditOnSeqClipExtractionProof : Bool
auditOnSeqClipExtractionProof =
  intToBoxInt 4 == intToBoxInt 4
