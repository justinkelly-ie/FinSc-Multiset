module Stage1.OnSeq.MultisetStaging

import public Stage0.BoxInt
import public Stage0.Multiset
import public Stage1.OnSeq
import public Stage1.OnSeq.Staging
import public Stage1.TypeTheory.MultisetLevel

%default total

------------------------------------------------------------------------
-- 1. MULTISET-NATIVE SEQUENCE STAGING COMBINATORS
------------------------------------------------------------------------

||| Quotes a raw multiset sequence generator function into a Stage 1 static OnSeq payload.
public export
quoteOnSeqMultiset : Nat -> (Nat -> Multiset BoxInt a) -> LiftOnSeq (Multiset BoxInt a)
quoteOnSeqMultiset start f = MkOnSeq start f

||| Splices a Stage 1 static OnSeq multiset sequence directly down into a Stage 0 consolidated Box multiset monoid.
public export
spliceOnSeqToBox : Eq a => LiftOnSeq (Multiset BoxInt a) -> (idx : Nat) -> (len : Nat) -> Box a
spliceOnSeqToBox {a} seq idx len =
  let strm = spliceOnSeqToStream seq idx len
  in foldStreamNat len (\acc, m =>
                          let pairs = multisetToList m
                          in foldl (\innerAcc, (k, w) => insertBox k w innerAcc) acc pairs)
                       emptyBox strm

------------------------------------------------------------------------
-- 2. DEFINITIONAL INVERSE LAWS & PROOFS
------------------------------------------------------------------------

||| Splicing term retrieval on a quoted multiset sequence yields the exact generator value definitionally.
public export
0 inverseSpliceQuoteOnSeqMultiset : (f : Nat -> Multiset BoxInt a) -> (n : Nat) -> getTerm (quoteOnSeqMultiset Z f) n = Just (f n)
inverseSpliceQuoteOnSeqMultiset _ Z = Refl
inverseSpliceQuoteOnSeqMultiset _ (S k) = Refl
