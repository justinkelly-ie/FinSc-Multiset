module Stage0.Singleton.Sing

import public Stage0.BoxInt
import public Stage0.Multiset
import public Stage0.Token

%default total

------------------------------------------------------------------------
-- 1. CANONICAL SINGLETON TYPE
------------------------------------------------------------------------

||| A singleton holding exactly one element of type `a`.
||| An atomic point carrier in the 2LTT multiset ecosystem.
public export
data Sing : (a : Type) -> Type where
  MkSing : a -> Sing a

public export
Eq Void where
  _ == _ = True

public export
Eq a => Eq (Sing a) where
  (MkSing x) == (MkSing y) = x == y

public export
[singOrd] Ord a => Ord (Sing a) where
  compare (MkSing x) (MkSing y) = compare x y

public export
[singShow] Show a => Show (Sing a) where
  show (MkSing x) = "{" ++ show x ++ "}"

public export
Functor Sing where
  map f (MkSing x) = MkSing (f x)

public export
Applicative Sing where
  pure = MkSing
  (MkSing f) <*> (MkSing x) = MkSing (f x)

public export
Monad Sing where
  (MkSing x) >>= f = f x

public export
Foldable Sing where
  foldr f acc (MkSing x) = f x acc
  foldl f acc (MkSing x) = f acc x

------------------------------------------------------------------------
-- 2. WRAPPERS & LEGACY ALIASES
-- Preserves 100% backward compatibility.
------------------------------------------------------------------------

public export
toSing : a -> Sing a
toSing = MkSing

public export
fromSing : Sing a -> a
fromSing (MkSing x) = x

||| A guaranteed-present singleton. Alias for Sing.
public export
Sing1 : Type -> Type
Sing1 = Sing

------------------------------------------------------------------------
-- 3. BRIDGING & ISOMORPHISMS WITH TOKEN
------------------------------------------------------------------------

||| Canonical isomorphism from Sing to Token.
public export
singToToken : Sing a -> Token a
singToToken (MkSing x) = MkToken x

||| Canonical isomorphism from Token to Sing.
public export
tokenToSing : Token a -> Sing a
tokenToSing (MkToken x) = MkSing x

||| Proof witness that Sing -> Token -> Sing is identity.
public export
singTokenRoundTripProof : (s : Sing a) -> tokenToSing (singToToken s) = s
singTokenRoundTripProof (MkSing _) = Refl

||| Proof witness that Token -> Sing -> Token is identity.
public export
tokenSingRoundTripProof : (t : Token a) -> singToToken (tokenToSing t) = t
tokenSingRoundTripProof (MkToken _) = Refl

------------------------------------------------------------------------
-- 4. ADJUNCTION UNIT: INJECTION INTO MULTISET CARRIERS
------------------------------------------------------------------------

||| Unit of the Free Commutative Monoid Adjunction for Sing:
||| Injects a singleton into an algebraic multiset with unit multiplicity 1.
public export
singToMultiset : Num c => Sing a -> Multiset c a
singToMultiset (MkSing x) = AddM x 1 ZeroM

||| Injects a singleton into a BoxInt multiset with exact unit weight 1.
public export
singToBox : Sing a -> Multiset BoxInt a
singToBox (MkSing x) = AddM x (intToBoxInt 1) ZeroM

||| Injects a singleton into a multiset with specified scalar count.
public export
singToMultisetCount : Num c => Sing a -> c -> Multiset c a
singToMultisetCount (MkSing x) cnt = AddM x cnt ZeroM

||| Injects a singleton into a BoxInt multiset with specified BoxInt count.
public export
singToBoxCount : Sing a -> BoxInt -> Multiset BoxInt a
singToBoxCount (MkSing x) cnt = AddM x cnt ZeroM

------------------------------------------------------------------------
-- 5. TRANSITION RELATION
------------------------------------------------------------------------

||| A transition relation between two coordinates.
public export
record SingRelation (a : Type) where
  constructor MkSingRelation
  src : a
  tgt : a

public export
Eq a => Eq (SingRelation a) where
  (MkSingRelation s1 t1) == (MkSingRelation s2 t2) = s1 == s2 && t1 == t2

public export
Show a => Show (SingRelation a) where
  show (MkSingRelation s t) = show s ++ " -> " ++ show t
