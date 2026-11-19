module Stage0.Token

import Data.Linear
import public Stage0.BoxInt
import public Stage0.Multiset
import public Stage0.Interfaces

%default total

------------------------------------------------------------------------
-- 1. CANONICAL CONSTRUCTIVIST TOKEN TYPES
------------------------------------------------------------------------

||| An atomic, indivisible token carrying a basis element of type `a`.
||| Represents the free commutative monoid generator δ_x of weight 1.
public export
record Token (a : Type) where
  constructor MkToken
  element : a

||| A strictly linear token carrying an element of type `a`.
||| Enforces Quantitative Type Theory (QTT) linear resource tracking (Rule 04 §1),
||| guaranteeing at compile time that physical tokens cannot be duplicated, leaked, or dropped.
public export
data LToken : (a : Type) -> Type where
  MkLToken : a -> LToken a

||| A dependently typed token tracking coordinate element `x` at the type level.
public export
data DepToken : (a : Type) -> a -> Type where
  MkDepToken : (x : a) -> DepToken a x

||| A dependently typed weighted token tracking coordinate `x` and multiplicity `w` at the type level.
public export
data DepTokenWeighted : (c : Type) -> (a : Type) -> a -> c -> Type where
  MkDepTokenWeighted : (x : a) -> (weight : c) -> DepTokenWeighted c a x weight

------------------------------------------------------------------------
-- 2. STANDARD INTERFACES FOR TOKEN
------------------------------------------------------------------------

public export
Eq Void where
  _ == _ = True

public export
Eq a => Eq (Token a) where
  (MkToken x) == (MkToken y) = x == y

public export
Ord a => Ord (Token a) where
  compare (MkToken x) (MkToken y) = compare x y

public export
DiscreteCoord a => DiscreteCoord (Token a) where

public export
Show a => Show (Token a) where
  show (MkToken x) = "Token(" ++ show x ++ ")"

public export
Eq a => Eq (LToken a) where
  (MkLToken x) == (MkLToken y) = x == y

public export
Show a => Show (LToken a) where
  show (MkLToken x) = "LToken(" ++ show x ++ ")"

||| Maps a coordinate function over an atomic Token.
public export
mapToken : (a -> b) -> Token a -> Token b
mapToken f (MkToken x) = MkToken (f x)

public export
Functor Token where
  map = mapToken

public export
Applicative Token where
  pure = MkToken
  (MkToken f) <*> (MkToken x) = MkToken (f x)

public export
Monad Token where
  (MkToken x) >>= f = f x

public export
Foldable Token where
  foldr f z (MkToken x) = f x z
  foldl f z (MkToken x) = f z x
  null _ = False
  toList (MkToken x) = [x]
  foldMap f (MkToken x) = f x

||| Converts a dependent token to an untyped Token.
public export
depTokenToToken : DepToken a x -> Token a
depTokenToToken (MkDepToken x) = MkToken x

||| Projects the coordinate Token and weight from a weighted dependent token.
public export
depTokenWeightedToToken : DepTokenWeighted c a x w -> (Token a, c)
depTokenWeightedToToken (MkDepTokenWeighted x w) = (MkToken x, w)

------------------------------------------------------------------------
-- 2B. DIRECTED TOKEN TRANSITION RELATION
------------------------------------------------------------------------

||| A directed transition relation between two coordinates (src -> tgt).
public export
record SingRelation (a : Type) where
  constructor MkSingRelation
  src : a
  tgt : a

public export
TokenRelation : Type -> Type
TokenRelation = SingRelation

public export
MkTokenRelation : a -> a -> SingRelation a
MkTokenRelation = MkSingRelation

public export
Eq a => Eq (SingRelation a) where
  (MkSingRelation s1 t1) == (MkSingRelation s2 t2) = s1 == s2 && t1 == t2

public export
Ord a => Ord (SingRelation a) where
  compare (MkSingRelation s1 t1) (MkSingRelation s2 t2) =
    case compare s1 s2 of
      EQ => compare t1 t2
      c  => c

public export
Show a => Show (SingRelation a) where
  show (MkSingRelation s t) = show s ++ " -> " ++ show t

------------------------------------------------------------------------
-- 3. QTT LINEAR PROTOCOLS & COMBINATORS
------------------------------------------------------------------------

||| Consumes a linear token by applying a transformation to its underlying element.
public export
consumeLToken : (1 tok : LToken a) -> (a -> b) -> b
consumeLToken (MkLToken x) f = f x

||| Produces a linear token from an element.
public export
produceLToken : a -> LToken a
produceLToken = MkLToken

||| Unpacks a linear token into its linear underlying element.
public export
unLToken : (1 tok : LToken a) -> (1 f : (1 _ : a) -> b) -> b
unLToken (MkLToken x) f = f x

public export
LConsumable a => LConsumable (LToken a) where
  lconsume (MkLToken x) = lconsume x

public export
LComonoid a => LComonoid (LToken a) where
  lcomult (MkLToken x) =
    let (x1 # x2) = lcomult x
    in (MkLToken x1 # MkLToken x2)

------------------------------------------------------------------------
-- 4. CANONICAL TOKEN INJECTION INTO MULTISET CARRIERS
------------------------------------------------------------------------

||| Unit basis injection `x |-> [x]` into an algebraic `Multiset c a`.
public export
tokenToMultiset : Num c => Token a -> Multiset c a
tokenToMultiset (MkToken x) = AddM x 1 ZeroM

||| Injects an atomic token into a `Carrier a` with exact unit weight `1`.
public export
tokenToCarrier : Token a -> Carrier a
tokenToCarrier (MkToken x) = singletonCarrier x (intToBoxInt 1)

||| Injects an atomic token into a multiset with specified scalar count.
public export
tokenToMultisetCount : Num c => Token a -> c -> Multiset c a
tokenToMultisetCount (MkToken x) cnt = AddM x cnt ZeroM

||| Injects an atomic token into a `Carrier a` with specified `BoxInt` count.
public export
tokenToCarrierCount : Token a -> BoxInt -> Carrier a
tokenToCarrierCount (MkToken x) cnt = singletonCarrier x cnt

||| Wraps a raw element into an atomic token.
public export
toToken : a -> Token a
toToken = MkToken

||| Projects the underlying basis element from a token.
public export
fromToken : Token a -> a
fromToken (MkToken x) = x

------------------------------------------------------------------------
-- 5. DEPENDENT TOKEN OCCURRENCE PROOF WITNESS (IsToken)
------------------------------------------------------------------------

||| Proof witness that element `x` exists in multiset `m` with multiplicity exactly 1.
||| Enforces that `x` is an atomic token inside the multiset.
public export
data IsToken : (x : a) -> (m : Multiset BoxInt a) -> Type where
  HereToken  : IsToken x (AddM x (MkBoxInt 1) rest)
  ThereToken : IsToken x rest -> IsToken x (AddM y c rest)

||| Canonical witness that a newly created token multiset contains the token.
public export
isTokenWitness : (x : a) -> IsToken x (AddM x (MkBoxInt 1) ZeroM)
isTokenWitness x = HereToken

||| Injects a dependent token into a multiset bundled with its correctness witness.
public export
depTokenToBox : DepToken a x -> (m : Multiset BoxInt a ** IsToken x m)
depTokenToBox (MkDepToken x) = (AddM x (intToBoxInt 1) ZeroM ** HereToken)

------------------------------------------------------------------------
-- 6. UNIVERSAL LINEAR BASIS EXTENSION (liftToken)
------------------------------------------------------------------------

||| Scales a BoxInt multiset by an integer factor.
public export
scaleMultisetInt : Integer -> Multiset BoxInt b -> Multiset BoxInt b
scaleMultisetInt _ ZeroM = ZeroM
scaleMultisetInt 1 m = m
scaleMultisetInt k (AddM y (MkBoxInt v) xs) =
  AddM y (MkBoxInt (k * v)) (scaleMultisetInt k xs)

||| Universal Monoid Extension (Pushforward Homomorphism):
||| Lifts a transformation defined on atomic tokens to a unique linear sum over entire multisets.
||| By the universal property of free commutative monoids, this uniquely determines
||| the linear multiset pushforward from its action on single basis tokens.
public export
liftToken : (Token a -> Multiset BoxInt b) -> Multiset BoxInt a -> Multiset BoxInt b
liftToken f ZeroM = ZeroM
liftToken f (AddM x (MkBoxInt w) rest) =
  if w <= 0 then liftToken f rest
  else let img = f (MkToken x)
           scaled = scaleMultisetInt w img
       in addMultiset scaled (liftToken f rest)

||| Identity Proof: Lifting on the empty multiset definitionally preserves the empty multiset.
public export
liftTokenZeroProof : (f : Token a -> Multiset BoxInt b) -> liftToken f ZeroM = ZeroM
liftTokenZeroProof _ = Refl

||| Linear Basis Extension over Indexed Carriers:
||| Extends a transformation on single coordinate tokens to the full `Carrier a` module
||| by scaling and summing image carriers across positive-weight entries.
public export
liftCarrier : DiscreteCoord b => (Token a -> Carrier b) -> Carrier a -> Carrier b
liftCarrier f m =
  foldBoxTreeL (\acc, (x, w) =>
    if w <= intToBoxInt 0
      then acc
      else addCarrier acc (scaleCarrier w (f (MkToken x)))) BoxLeaf m

||| Identity Proof: Lifting on the empty `BoxLeaf` carrier definitionally yields `BoxLeaf`.
public export
0 liftCarrierNeutralProof : DiscreteCoord b => (f : Token a -> Carrier b) -> liftCarrier f BoxLeaf = BoxLeaf
liftCarrierNeutralProof _ = Refl

------------------------------------------------------------------------
-- 7. SUBSTRATE CAUSAL ACTION TOKEN GENERATOR (Delta S = 1)
------------------------------------------------------------------------

||| An atomic causal action influx token advancing the substrate arrow (Delta S = 1).
public export
record SubstrateActionToken where
  constructor MkActionToken
  actionQuantum : BoxInt

public export
Eq SubstrateActionToken where
  (MkActionToken q1) == (MkActionToken q2) = q1 == q2

public export
Ord SubstrateActionToken where
  compare (MkActionToken q1) (MkActionToken q2) = compare q1 q2

public export
DiscreteCoord SubstrateActionToken where

public export
Show SubstrateActionToken where
  show (MkActionToken q) = "ActionToken(q=" ++ show (unwrapBox q) ++ ")"

||| Canonical unit causal action token carrying exactly 1 quantum of action.
public export
unitActionToken : SubstrateActionToken
unitActionToken = MkActionToken (intToBoxInt 1)

||| Injects an atomic action token into a `Carrier a` at element `geom`.
public export
actionTokenToCarrier : Token SubstrateActionToken -> a -> Carrier a
actionTokenToCarrier (MkToken (MkActionToken q)) geom = singletonCarrier geom q

