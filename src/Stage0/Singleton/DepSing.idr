module Stage0.Singleton.DepSing

import public Stage0.BoxInt
import public Stage0.Multiset
import public Stage0.DepMultiset
import public Stage0.Token
import public Stage0.Singleton.Sing

%default total

------------------------------------------------------------------------
-- 1. CANONICAL DEPENDENT SINGLETON PRIMITIVE
--
-- DepSing is maintained as a transparent alias to DepToken
-- (Stage0.Token.DepToken).
------------------------------------------------------------------------

||| Transparent backward-compatibility type alias: DepSing is DepToken.
public export
DepSing : (a : Type) -> a -> Type
DepSing = DepToken

||| Transparent constructor alias.
public export
MkDepSing : (x : a) -> DepToken a x
MkDepSing = MkDepToken

------------------------------------------------------------------------
-- 2. WEIGHTED DEPENDENT SINGLETON (DepSingWeighted)
------------------------------------------------------------------------

||| Transparent backward-compatibility type alias: DepSingWeighted is DepTokenWeighted.
public export
DepSingWeighted : (c : Type) -> (a : Type) -> a -> c -> Type
DepSingWeighted = DepTokenWeighted

||| Transparent constructor alias.
public export
MkDepSingWeighted : (x : a) -> (weight : c) -> DepTokenWeighted c a x weight
MkDepSingWeighted = MkDepTokenWeighted

||| Dependent weighted singleton type synonym.
public export
0 SingW : (c : Type) -> (a : Type) -> a -> c -> Type
SingW = DepSingWeighted

||| A dependent singleton where the weight is verified non-zero.
public export
0 SingW1 : (c : Type) -> (Eq c, Num c) => (a : Type) -> a -> c -> Type
SingW1 c a x weight = (DepSingWeighted c a x weight, (weight == 0) = False)

------------------------------------------------------------------------
-- 3. BRIDGING WITH TOKEN & UNTYPED SING
------------------------------------------------------------------------

||| Converts a dependent singleton to an untyped Sing (Token).
public export
depSingToSing : DepToken a x -> Token a
depSingToSing (MkDepToken x) = MkToken x

||| Converts a dependent singleton to an unrestricted Token.
public export
depSingToToken : DepToken a x -> Token a
depSingToToken (MkDepToken x) = MkToken x

||| Converts a dependent singleton to a DepToken (identity).
public export
depSingToDepToken : DepToken a x -> DepToken a x
depSingToDepToken = id

||| Converts a DepToken to a DepSing (identity).
public export
depTokenToDepSing : DepToken a x -> DepToken a x
depTokenToDepSing = id

||| Projects the coordinate Sing and weight from a weighted dependent singleton.
public export
depSingWeightedToSing : DepTokenWeighted c a x w -> (Token a, c)
depSingWeightedToSing (MkDepTokenWeighted x w) = (MkToken x, w)

||| Proof witness that DepSing -> DepToken -> DepSing is identity.
public export
depSingTokenRoundTripProof : (ds : DepToken a x) -> depTokenToDepSing (depSingToDepToken ds) = ds
depSingTokenRoundTripProof (MkDepToken _) = Refl

------------------------------------------------------------------------
-- 4. ADJUNCTION UNIT: INJECTION INTO DEPENDENT MULTISETS
------------------------------------------------------------------------

||| Injects a dependent singleton into a DepMultiset with unit multiplicity 1.
public export
depSingToDepMultiset : Num c => DepToken a x -> DepMultiset c a (AddM x 1 ZeroM)
depSingToDepMultiset (MkDepToken x) = DepAddM x 1 DepEmptyM

||| Injects a dependent singleton into a BoxInt DepMultiset with unit weight MkBoxInt 1.
public export
depSingToBoxDepMultiset : DepToken a x -> DepMultiset BoxInt a (AddM x (intToBoxInt 1) ZeroM)
depSingToBoxDepMultiset (MkDepToken x) = DepAddM x (intToBoxInt 1) DepEmptyM

||| Injects a weighted dependent singleton into a DepMultiset with its type-level weight.
public export
depSingWeightedToDepMultiset : DepTokenWeighted c a x w -> DepMultiset c a (AddM x w ZeroM)
depSingWeightedToDepMultiset (MkDepTokenWeighted x w) = DepAddM x w DepEmptyM
