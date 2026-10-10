module Stage0.OnSeq.OnMSet

import Stage0.Multiset
import Stage0.Singleton.Sing
import Stage0.Singleton.Bit

%default total

||| An on-sequence (ongoing sequence) starting at a specific index.
||| Defined via a generator function mapping the term index to the value.
public export
record OnSeq a where
  constructor MkOnSeq
  start : Nat
  at    : Nat -> a

||| A finite consecutive subsequence (clip) extracted from a sequence.
public export
record Clip a where
  constructor MkClip
  startIdx : Nat
  elements : List a

export
(Show a) => Show (Clip a) where
  show (MkClip idx elems) = "Clip@" ++ show idx ++ show elems ++ "..."

||| Creates a constant on-sequence starting at a specific index.
public export
constant : Nat -> a -> OnSeq a
constant s x = MkOnSeq s (\_ => x)

||| Creates the identity on-sequence [n> starting at a specific index (usually 0 or 1).
public export
identity : Nat -> OnSeq Nat
identity s = MkOnSeq s (\n => n)

||| Evaluates/indexes the on-sequence at a specific term index.
||| Returns `Just value` if index >= start, else `Nothing`.
public export
getTerm : OnSeq a -> Nat -> Maybe a
getTerm (MkOnSeq start at) n =
  if n >= start
     then Just (at n)
     else Nothing

||| Extracts a finite clip of a given length starting from the specified index.
||| Returns a Clip starting at max(idx, start).
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
  map = Stage0.OnSeq.OnMSet.map

||| Combines two on-sequences pointwise.
||| The resulting on-sequence starts at the maximum of the two starting indices.
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

-----------------------------------------------------------------------
-- SPECIALIZED ON-SEQUENCES FOR THE MULTISET MATH SUITE
-----------------------------------------------------------------------

||| On-sequence of multisets.
public export
0 OnMSet : (c : Type) -> (a : Type) -> Type
OnMSet c a = OnSeq (Multiset c a)

||| Pointwise addition of two on-sequences of multisets.
public export
addOnMSet : (OnMSet c a) -> (OnMSet c a) -> (OnMSet c a)
addOnMSet = zipWith addMultiset

||| Maps multiset annihilation over an on-sequence of multisets.
public export
annihilateOnMSet : (Eq a, Num c, Eq c) => OnMSet c a -> OnMSet c a
annihilateOnMSet = Stage0.OnSeq.OnMSet.map annihilateMultiset

||| Maps scalar scaling over an on-sequence of multisets.
public export
scaleOnMSet : (Num c, Eq c) => c -> OnMSet c a -> OnMSet c a
scaleOnMSet scalar = Stage0.OnSeq.OnMSet.map (scaleMultiset scalar)

||| Swaps matter and antimatter across the on-sequence.
public export
negateOnMSet : Neg c => OnMSet c a -> OnMSet c a
negateOnMSet = Stage0.OnSeq.OnMSet.map negateMultiset

||| Pointwise subtraction of two on-sequences of multisets.
public export
subOnMSet : Neg c => OnMSet c a -> OnMSet c a -> OnMSet c a
subOnMSet = zipWith subMultiset

||| On-sequence of singletons.
public export
0 OnSing : (a : Type) -> Type
OnSing a = OnSeq (Sing a)
