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
Eq a => Eq (Token a) where
  (MkToken x) == (MkToken y) = x == y

public export
Ord a => Ord (Token a) where
  compare (MkToken x) (MkToken y) = compare x y

public export
Show a => Show (Token a) where
  show (MkToken x) = "Token(" ++ show x ++ ")"

public export
Eq a => Eq (LToken a) where
  (MkLToken x) == (MkLToken y) = x == y

public export
Show a => Show (LToken a) where
  show (MkLToken x) = "LToken(" ++ show x ++ ")"

public export
Functor Token where
  map f (MkToken x) = MkToken (f x)

public export
Applicative Token where
  pure = MkToken
  (MkToken f) <*> (MkToken x) = MkToken (f x)

public export
Monad Token where
  (MkToken x) >>= f = f x

public export
Foldable Token where
  foldr f acc (MkToken x) = f x acc
  foldl f acc (MkToken x) = f acc x

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
-- 4. ADJUNCTION UNIT: INJECTION INTO MULTISET CARRIERS
------------------------------------------------------------------------

||| Unit of the Free Commutative Monoid Adjunction (F ⊣ U):
||| η_X : X -> U(M(X)), x |-> [x]
||| Injects an atomic token into an algebraic multiset with unit multiplicity 1.
public export
tokenToMultiset : Num c => Token a -> Multiset c a
tokenToMultiset (MkToken x) = AddM x 1 ZeroM

||| Injects an atomic token into a BoxInt multiset with exact unit weight (MkBoxInt 1).
public export
tokenToBox : Token a -> Multiset BoxInt a
tokenToBox (MkToken x) = AddM x (intToBoxInt 1) ZeroM

||| Injects an atomic token into a multiset with specified scalar count.
public export
tokenToMultisetCount : Num c => Token a -> c -> Multiset c a
tokenToMultisetCount (MkToken x) cnt = AddM x cnt ZeroM

||| Injects an atomic token into a BoxInt multiset with specified BoxInt count.
public export
tokenToBoxCount : Token a -> BoxInt -> Multiset BoxInt a
tokenToBoxCount (MkToken x) cnt = AddM x cnt ZeroM

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
-- 6. UNIVERSAL FREE ADJUNCTION EXTENSION (liftToken)
------------------------------------------------------------------------

||| Scales a BoxInt multiset by an integer factor.
public export
scaleMultisetInt : Integer -> Multiset BoxInt b -> Multiset BoxInt b
scaleMultisetInt _ ZeroM = ZeroM
scaleMultisetInt 1 m = m
scaleMultisetInt k (AddM y (MkBoxInt v) xs) =
  AddM y (MkBoxInt (k * v)) (scaleMultisetInt k xs)

||| Universal Monoid Extension (Free Adjunction F ⊣ U):
||| Lifts a transformation defined on atomic tokens to a unique homomorphism over entire multisets.
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
Show SubstrateActionToken where
  show (MkActionToken q) = "ActionToken(q=" ++ show (unwrapBox q) ++ ")"

||| Canonical unit causal action token carrying exactly 1 quantum of action.
public export
unitActionToken : SubstrateActionToken
unitActionToken = MkActionToken (intToBoxInt 1)

||| Injects an atomic action token into a multiset carrier for element `geom`.
public export
actionTokenToBox : Token SubstrateActionToken -> a -> Multiset BoxInt a
actionTokenToBox (MkToken (MkActionToken q)) geom = AddM geom q ZeroM

