module Stage0.Singleton.DepSing

import public Stage0.BoxInt
import public Stage0.Multiset
import public Stage0.DepMultiset
import public Stage0.Token
import public Stage0.Singleton.Sing

%default total

------------------------------------------------------------------------
-- 1. CANONICAL DEPENDENT SINGLETON PRIMITIVE
------------------------------------------------------------------------

||| A dependently typed singleton primitive.
||| Tracks coordinate element `x` at the type level.
||| Retained intact for 100% backward compatibility with DepVexel.
public export
data DepSing : (a : Type) -> a -> Type where
  MkDepSing : (x : a) -> DepSing a x

------------------------------------------------------------------------
-- 2. WEIGHTED DEPENDENT SINGLETON (DepSingWeighted)
------------------------------------------------------------------------

||| A dependently typed weighted singleton primitive.
||| Tracks coordinate element `x` and weight `weight` at the type level.
public export
data DepSingWeighted : (c : Type) -> (a : Type) -> a -> c -> Type where
  MkDepSingWeighted : (x : a) -> (weight : c) -> DepSingWeighted c a x weight

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

||| Converts a dependent singleton to an untyped Sing.
public export
depSingToSing : DepSing a x -> Sing a
depSingToSing (MkDepSing x) = MkSing x

||| Converts a dependent singleton to an unrestricted Token.
public export
depSingToToken : DepSing a x -> Token a
depSingToToken (MkDepSing x) = MkToken x

||| Converts a dependent singleton to a DepToken.
public export
depSingToDepToken : DepSing a x -> DepToken a x
depSingToDepToken (MkDepSing x) = MkDepToken x

||| Converts a DepToken to a DepSing.
public export
depTokenToDepSing : DepToken a x -> DepSing a x
depTokenToDepSing (MkDepToken x) = MkDepSing x

||| Projects the coordinate Sing and weight from a weighted dependent singleton.
public export
depSingWeightedToSing : DepSingWeighted c a x w -> (Sing a, c)
depSingWeightedToSing (MkDepSingWeighted x w) = (MkSing x, w)

||| Proof witness that DepSing -> DepToken -> DepSing is identity.
public export
depSingTokenRoundTripProof : (ds : DepSing a x) -> depTokenToDepSing (depSingToDepToken ds) = ds
depSingTokenRoundTripProof (MkDepSing _) = Refl

------------------------------------------------------------------------
-- 4. ADJUNCTION UNIT: INJECTION INTO DEPENDENT MULTISETS
------------------------------------------------------------------------

||| Injects a dependent singleton into a DepMultiset with unit multiplicity 1.
public export
depSingToDepMultiset : Num c => DepSing a x -> DepMultiset c a (AddM x 1 ZeroM)
depSingToDepMultiset (MkDepSing x) = DepAddM x 1 DepEmptyM

||| Injects a dependent singleton into a BoxInt DepMultiset with unit weight MkBoxInt 1.
public export
depSingToBoxDepMultiset : DepSing a x -> DepMultiset BoxInt a (AddM x (intToBoxInt 1) ZeroM)
depSingToBoxDepMultiset (MkDepSing x) = DepAddM x (intToBoxInt 1) DepEmptyM

||| Injects a weighted dependent singleton into a DepMultiset with its type-level weight.
public export
depSingWeightedToDepMultiset : DepSingWeighted c a x w -> DepMultiset c a (AddM x w ZeroM)
depSingWeightedToDepMultiset (MkDepSingWeighted x w) = DepAddM x w DepEmptyM
