module Stage0.LMultiset

import Stage0.Multiset
import Data.List
import Data.Linear

%default total

||| A strictly linear dependent signed multiset.
||| The exact elements and their integer multiplicities are tracked in the type signature.
||| The `1` multiplicity guarantees un-forgeable physical conservation and enables O(1) in-place mutation.
public export
data LMultiset : (c : Type) -> (a : Type) -> (contents : List (a, c)) -> Type where
  ||| The vacuum state.
  LEmptyM : LMultiset c a []
  
  ||| Adds an element, strictly consuming the previous state linearly.
  LAddM : {0 rest : List (a, c)} ->
          (item : a) -> 
          (count : c) -> 
          (1 prev : LMultiset c a rest) -> 
          LMultiset c a ((item, count) :: rest)

||| Legacy compatibility alias for LMultiset.
public export
0 LDepMultiset : (c : Type) -> (a : Type) -> (contents : List (a, c)) -> Type
LDepMultiset = LMultiset

||| Tail-recursive helper to freeze a linear multiset into an unrestricted list.
||| The accumulator ensures the linear variable `prev` is consumed in a linear context.
public export
freezeLDepAcc : (acc : List (a, c)) -> (1 m : LMultiset c a contents) -> List (a, c)
freezeLDepAcc acc LEmptyM = acc
freezeLDepAcc acc (LAddM item count prev) = freezeLDepAcc ((item, count) :: acc) prev

||| Freezes a type-level linear multiset back into a standard runtime list.
public export
freezeLDep : {0 contents : List (a, c)} -> (1 m : LMultiset c a contents) -> List (a, c)
freezeLDep m = freezeLDepAcc [] m

||| LUnboxResult: An unrestricted wrapper that preserves the type-level multiset contents.
public export
data LUnboxResult : (c : Type) -> (a : Type) -> List (a, c) -> Type where
  MkLUnboxResult : (x : List (a, c)) -> LUnboxResult c a x

||| Unboxes a linear LMultiset into an unrestricted list of items and counts,
||| preserving its type-level index via structural recursion.
public export
lunboxLMultiset : {0 contents : List (a, c)} -> (1 m : LMultiset c a contents) -> LUnboxResult c a contents
lunboxLMultiset LEmptyM = MkLUnboxResult []
lunboxLMultiset (LAddM item count prev) =
  let MkLUnboxResult prev_un = lunboxLMultiset prev
  in MkLUnboxResult ((item, count) :: prev_un)

||| A linear left fold over an LMultiset, consuming it exactly once.
public export
lfoldl : {0 contents : List (a, c)} ->
         (acc : b) ->
         (f : b -> a -> c -> b) ->
         (1 m : LMultiset c a contents) ->
         b
lfoldl acc f LEmptyM = acc
lfoldl acc f (LAddM item count prev) = lfoldl (f acc item count) f prev

||| A linear right fold over an LMultiset, consuming it exactly once.
public export
lfoldr : {0 contents : List (a, c)} ->
         (f : a -> c -> (1 _ : b) -> b) ->
         (1 acc : b) ->
         (1 m : LMultiset c a contents) ->
         b
lfoldr f acc LEmptyM = acc
lfoldr f acc (LAddM item count prev) = f item count (lfoldr f acc prev)

||| Computes the mapped type index list for lmap.
public export
lmapContents : (a -> b) -> List (a, c) -> List (b, c)
lmapContents f [] = []
lmapContents f ((item, count) :: xs) = (f item, count) :: lmapContents f xs

||| A linear map transforming the values of the multiset in-place.
public export
lmap : {0 contents : List (a, c)} ->
       (f : a -> b) ->
       (1 m : LMultiset c a contents) ->
       LMultiset c b (lmapContents f contents)
lmap f LEmptyM = LEmptyM
lmap f (LAddM item count prev) = LAddM (f item) count (lmap f prev)
