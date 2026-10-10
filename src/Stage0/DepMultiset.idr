module Stage0.DepMultiset

import Stage0.Multiset

%default total

||| A dependently typed signed multiset where the elements and counts are tracked at the type level.
||| Unlike LMultiset, this does not enforce QTT linear (1) constraints.
public export
data DepMultiset : (c : Type) -> (a : Type) -> (contents : Multiset c a) -> Type where
  ||| The vacuum state.
  DepEmptyM : DepMultiset c a ZeroM
  
  ||| Adds an element without linear resource consumption.
  DepAddM : {0 rest : Multiset c a} ->
            (item : a) -> 
            (count : c) -> 
            (prev : DepMultiset c a rest) -> 
            DepMultiset c a (AddM item count rest)

||| Freezes a type-level dependent multiset into a standard runtime multiset.
public export
freezeDep : {0 contents : Multiset c a} -> DepMultiset c a contents -> Multiset c a
freezeDep DepEmptyM = ZeroM
freezeDep (DepAddM item count prev) = AddM item count (freezeDep prev)

||| A standard left fold over a DepMultiset.
public export
depFoldl : {0 contents : Multiset c a} ->
           (acc : b) ->
           (f : b -> a -> c -> b) ->
           DepMultiset c a contents ->
           b
depFoldl acc f DepEmptyM = acc
depFoldl acc f (DepAddM item count prev) = depFoldl (f acc item count) f prev

||| A standard right fold over a DepMultiset.
public export
depFoldr : {0 contents : Multiset c a} ->
           (f : a -> c -> b -> b) ->
           (acc : b) ->
           DepMultiset c a contents ->
           b
depFoldr f acc DepEmptyM = acc
depFoldr f acc (DepAddM item count prev) = f item count (depFoldr f acc prev)

||| Computes the mapped type index multiset for depMap.
public export
depMapContents : (a -> b) -> Multiset c a -> Multiset c b
depMapContents f ZeroM = ZeroM
depMapContents f (AddM item count xs) = AddM (f item) count (depMapContents f xs)

||| A standard map transforming the values of the multiset in-place.
public export
depMap : {0 contents : Multiset c a} ->
         (f : a -> b) ->
         DepMultiset c a contents ->
         DepMultiset c b (depMapContents f contents)
depMap f DepEmptyM = DepEmptyM
depMap f (DepAddM item count prev) = DepAddM (f item) count (depMap f prev)


||| A dependently typed strictly positive, non-empty multiset.
||| Guarantees at least one element at compile time.
public export
data DepMultiset1 : (c : Type) -> (a : Type) -> (contents : Multiset1 c a) -> Type where
  ||| The base single element.
  DepBaseM : (item : a) ->
             (count : c) ->
             DepMultiset1 c a (BaseM item count)
  
  ||| Adds an element to a non-empty multiset.
  DepAddM1 : {0 rest : Multiset1 c a} ->
             (item : a) -> 
             (count : c) -> 
             (prev : DepMultiset1 c a rest) -> 
             DepMultiset1 c a (AddM1 item count rest)

||| Freezes a type-level non-empty dependent multiset into a standard runtime non-empty multiset.
public export
freezeDep1 : {0 contents : Multiset1 c a} -> DepMultiset1 c a contents -> Multiset1 c a
freezeDep1 (DepBaseM item count) = BaseM item count
freezeDep1 (DepAddM1 item count prev) = AddM1 item count (freezeDep1 prev)

||| A standard left fold over a DepMultiset1.
public export
depFoldl1 : {0 contents : Multiset1 c a} ->
            (acc : b) ->
            (f : b -> a -> c -> b) ->
            DepMultiset1 c a contents ->
            b
depFoldl1 acc f (DepBaseM item count) = f acc item count
depFoldl1 acc f (DepAddM1 item count prev) = depFoldl1 (f acc item count) f prev

||| A standard right fold over a DepMultiset1.
public export
depFoldr1 : {0 contents : Multiset1 c a} ->
            (f : a -> c -> b -> b) ->
            (acc : b) ->
            DepMultiset1 c a contents ->
            b
depFoldr1 f acc (DepBaseM item count) = f item count acc
depFoldr1 f acc (DepAddM1 item count prev) = f item count (depFoldr1 f acc prev)

||| Computes the mapped type index multiset for depMap1.
public export
depMapContents1 : (a -> b) -> Multiset1 c a -> Multiset1 c b
depMapContents1 f (BaseM item count) = BaseM (f item) count
depMapContents1 f (AddM1 item count xs) = AddM1 (f item) count (depMapContents1 f xs)

||| A standard map transforming the values of the non-empty multiset in-place.
public export
depMap1 : {0 contents : Multiset1 c a} ->
          (f : a -> b) ->
          DepMultiset1 c a contents ->
          DepMultiset1 c b (depMapContents1 f contents)
depMap1 f (DepBaseM item count) = DepBaseM (f item) count
depMap1 f (DepAddM1 item count prev) = DepAddM1 (f item) count (depMap1 f prev)
