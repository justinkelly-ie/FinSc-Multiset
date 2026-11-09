module Stage0.Singleton.Sing

import public Stage0.BoxInt
import public Stage0.Multiset
import public Stage0.Token

%default total

------------------------------------------------------------------------
-- 1. CANONICAL SINGLETON TAXONOMY & MODERNIZATION
--
-- Norman Wildberger originally introduced "Singleton" (Sing) to denote
-- both an atomic 1D point and a polymorphic carrier wrapper.
--
-- In the modernized constructivist taxonomy:
--   1. 0D Scalar Basepoint: Nullexel (Stage1.Basis.CoordCell.Nullexel)
--   2. 1D Geometric Coordinates: Unixel (Stage1.Basis.CoordCell.Unixel)
--   3. Polymorphic Atomic Carrier Tokens: Token a (Stage0.Token.Token)
--
-- Sing is maintained here as a transparent backward-compatibility alias
-- mapping directly to Token a.
------------------------------------------------------------------------

||| Transparent backward-compatibility type alias: Sing a is Token a.
public export
Sing : (a : Type) -> Type
Sing = Token

||| Transparent backward-compatibility constructor alias: MkSing is MkToken.
public export
MkSing : a -> Token a
MkSing = MkToken

public export
Eq Void where
  _ == _ = True

------------------------------------------------------------------------
-- 2. WRAPPERS & LEGACY ALIASES
------------------------------------------------------------------------

public export
toSing : a -> Token a
toSing = MkToken

public export
fromSing : Token a -> a
fromSing (MkToken x) = x

||| A guaranteed-present singleton. Alias for Token.
public export
Sing1 : Type -> Type
Sing1 = Token

------------------------------------------------------------------------
-- 3. BRIDGING & ISOMORPHISMS WITH TOKEN
------------------------------------------------------------------------

||| Canonical isomorphism from Sing (Token) to Token (identity).
public export
singToToken : Token a -> Token a
singToToken = id

||| Canonical isomorphism from Token to Sing (identity).
public export
tokenToSing : Token a -> Token a
tokenToSing = id

||| Proof witness that Sing -> Token -> Sing is identity.
public export
singTokenRoundTripProof : (s : Token a) -> tokenToSing (singToToken s) = s
singTokenRoundTripProof _ = Refl

||| Proof witness that Token -> Sing -> Token is identity.
public export
tokenSingRoundTripProof : (t : Token a) -> singToToken (tokenToSing t) = t
tokenSingRoundTripProof _ = Refl

------------------------------------------------------------------------
-- 4. ADJUNCTION UNIT: INJECTION INTO MULTISET CARRIERS
------------------------------------------------------------------------

||| Unit of the Free Commutative Monoid Adjunction:
||| Injects a singleton token into an algebraic multiset with unit multiplicity 1.
public export
singToMultiset : Num c => Token a -> Multiset c a
singToMultiset = tokenToMultiset

||| Injects a singleton token into a BoxInt multiset with exact unit weight 1.
public export
singToBox : Token a -> Multiset BoxInt a
singToBox = tokenToBox

||| Injects a singleton token into a multiset with specified scalar count.
public export
singToMultisetCount : Num c => Token a -> c -> Multiset c a
singToMultisetCount = tokenToMultisetCount

||| Injects a singleton token into a BoxInt multiset with specified BoxInt count.
public export
singToBoxCount : Token a -> BoxInt -> Multiset BoxInt a
singToBoxCount = tokenToBoxCount

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
