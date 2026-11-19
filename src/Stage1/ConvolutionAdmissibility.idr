module Stage1.ConvolutionAdmissibility

import public Data.Maybe
import public Decidable.Equality
import public Stage0.BoxInt

%default total

||| Exhaustive classification of Laurent & Stream support bounds over the integer axis Z:
public export
data LaurentRegime : Type where
  ||| 1. Fixed compact interval [low, high] known at Stage 1 compile time
  StaticHorizon       : (low : Integer) -> (high : Integer) -> LaurentRegime
  ||| 2. Forward causal ray [0, cap] governed by runtime `GohFuel`
  BoundedHorizon      : (cap : Nat) -> LaurentRegime
  ||| 3. Backward UV ray [-cap, 0] governed by runtime `GohFuel`
  RetroBoundedHorizon : (cap : Nat) -> LaurentRegime
  ||| 4. Sliding causal interval [t - win, t] of fixed width `win`
  WindowedHorizon     : (win : Nat) -> LaurentRegime
  ||| 5. Causal ray starting at Tick 0 with no preset upper bound (productive on demand)
  OpenFuture          : LaurentRegime
  ||| 6. Two-sided stream with no preset lower or upper bound (productive in both directions)
  BilateralOpen       : LaurentRegime

public export
Eq LaurentRegime where
  (StaticHorizon l1 h1)     == (StaticHorizon l2 h2)     = l1 == l2 && h1 == h2
  (BoundedHorizon c1)       == (BoundedHorizon c2)       = c1 == c2
  (RetroBoundedHorizon c1)  == (RetroBoundedHorizon c2)  = c1 == c2
  (WindowedHorizon w1)      == (WindowedHorizon w2)      = w1 == w2
  OpenFuture                == OpenFuture                = True
  BilateralOpen             == BilateralOpen             = True
  _                         == _                         = False

public export
DecEq LaurentRegime where
  decEq (StaticHorizon l1 h1) (StaticHorizon l2 h2) =
    case (decEq l1 l2, decEq h1 h2) of
      (Yes Refl, Yes Refl) => Yes Refl
      (No contra, _)       => No (\case Refl => contra Refl)
      (_, No contra)       => No (\case Refl => contra Refl)
  decEq (BoundedHorizon c1) (BoundedHorizon c2) =
    case decEq c1 c2 of
      Yes Refl  => Yes Refl
      No contra => No (\case Refl => contra Refl)
  decEq (RetroBoundedHorizon c1) (RetroBoundedHorizon c2) =
    case decEq c1 c2 of
      Yes Refl  => Yes Refl
      No contra => No (\case Refl => contra Refl)
  decEq (WindowedHorizon w1) (WindowedHorizon w2) =
    case decEq w1 w2 of
      Yes Refl  => Yes Refl
      No contra => No (\case Refl => contra Refl)
  decEq OpenFuture             OpenFuture             = Yes Refl
  decEq BilateralOpen          BilateralOpen          = Yes Refl
  decEq (StaticHorizon _ _)    (BoundedHorizon _)     = No (\case Refl impossible)
  decEq (StaticHorizon _ _)    (RetroBoundedHorizon _) = No (\case Refl impossible)
  decEq (StaticHorizon _ _)    (WindowedHorizon _)    = No (\case Refl impossible)
  decEq (StaticHorizon _ _)    OpenFuture             = No (\case Refl impossible)
  decEq (StaticHorizon _ _)    BilateralOpen          = No (\case Refl impossible)
  decEq (BoundedHorizon _)     (StaticHorizon _ _)    = No (\case Refl impossible)
  decEq (BoundedHorizon _)     (RetroBoundedHorizon _) = No (\case Refl impossible)
  decEq (BoundedHorizon _)     (WindowedHorizon _)    = No (\case Refl impossible)
  decEq (BoundedHorizon _)     OpenFuture             = No (\case Refl impossible)
  decEq (BoundedHorizon _)     BilateralOpen          = No (\case Refl impossible)
  decEq (RetroBoundedHorizon _) (StaticHorizon _ _)   = No (\case Refl impossible)
  decEq (RetroBoundedHorizon _) (BoundedHorizon _)    = No (\case Refl impossible)
  decEq (RetroBoundedHorizon _) (WindowedHorizon _)   = No (\case Refl impossible)
  decEq (RetroBoundedHorizon _) OpenFuture            = No (\case Refl impossible)
  decEq (RetroBoundedHorizon _) BilateralOpen         = No (\case Refl impossible)
  decEq (WindowedHorizon _)    (StaticHorizon _ _)    = No (\case Refl impossible)
  decEq (WindowedHorizon _)    (BoundedHorizon _)     = No (\case Refl impossible)
  decEq (WindowedHorizon _)    (RetroBoundedHorizon _) = No (\case Refl impossible)
  decEq (WindowedHorizon _)    OpenFuture             = No (\case Refl impossible)
  decEq (WindowedHorizon _)    BilateralOpen          = No (\case Refl impossible)
  decEq OpenFuture             (StaticHorizon _ _)    = No (\case Refl impossible)
  decEq OpenFuture             (BoundedHorizon _)     = No (\case Refl impossible)
  decEq OpenFuture             (RetroBoundedHorizon _) = No (\case Refl impossible)
  decEq OpenFuture             (WindowedHorizon _)    = No (\case Refl impossible)
  decEq OpenFuture             BilateralOpen          = No (\case Refl impossible)
  decEq BilateralOpen          (StaticHorizon _ _)    = No (\case Refl impossible)
  decEq BilateralOpen          (BoundedHorizon _)     = No (\case Refl impossible)
  decEq BilateralOpen          (RetroBoundedHorizon _) = No (\case Refl impossible)
  decEq BilateralOpen          (WindowedHorizon _)    = No (\case Refl impossible)
  decEq BilateralOpen          OpenFuture             = No (\case Refl impossible)

||| Non-recursive helper combining a compact `[x, y]` `StaticHorizon` with any `LaurentRegime`.
public export
convolveWithStatic : Integer -> Integer -> LaurentRegime -> LaurentRegime
convolveWithStatic x y (StaticHorizon a b)     = StaticHorizon (x + a) (y + b)
convolveWithStatic x y (BoundedHorizon c)      =
  let span = cast {to = Nat} (abs (y - x))
      posShift = if x >= 0 then cast {to = Nat} x else 0
  in BoundedHorizon (span + posShift + c)
convolveWithStatic x y (RetroBoundedHorizon c) =
  let span = cast {to = Nat} (abs (y - x))
      negShift = if y <= 0 then cast {to = Nat} (-y) else 0
  in RetroBoundedHorizon (span + negShift + c)
convolveWithStatic x y (WindowedHorizon w)     = WindowedHorizon (cast (abs (y - x)) + w)
convolveWithStatic _ _ OpenFuture              = OpenFuture
convolveWithStatic _ _ BilateralOpen           = BilateralOpen

||| Compile-time Cauchy Convolution Admissibility Matrix:
||| Returns `Just outputRegime` when convolution `A * B` has guaranteed finite fiber sums
||| at every degree `n`, and `Nothing` when the fiber accumulation lacks a finite bound.
||| Strictly non-recursive so `%default total` verifies coverage and termination trivially.
public export
admissibleConvolution : LaurentRegime -> LaurentRegime -> Maybe LaurentRegime
-- 1. Compact `StaticHorizon` convolves cleanly with every regime:
admissibleConvolution (StaticHorizon x y) r                 = Just (convolveWithStatic x y r)
admissibleConvolution r                   (StaticHorizon a b) = Just (convolveWithStatic a b r)

-- 2. Same-direction `Bounded` and `OpenFuture` rays (causal power series):
admissibleConvolution (BoundedHorizon c1)      (BoundedHorizon c2)      = Just (BoundedHorizon (c1 + c2))
admissibleConvolution (RetroBoundedHorizon c1) (RetroBoundedHorizon c2) = Just (RetroBoundedHorizon (c1 + c2))
admissibleConvolution (BoundedHorizon _)       OpenFuture               = Just OpenFuture
admissibleConvolution OpenFuture               (BoundedHorizon _)       = Just OpenFuture
admissibleConvolution OpenFuture               OpenFuture               = Just OpenFuture

-- 3. Mixed forward/backward finite rays `[0, c1] * [-c2, 0] = [-c2, c1]` (compact `StaticHorizon`):
admissibleConvolution (BoundedHorizon c1)      (RetroBoundedHorizon c2) = Just (StaticHorizon (- cast c2) (cast c1))
admissibleConvolution (RetroBoundedHorizon c1) (BoundedHorizon c2)      = Just (StaticHorizon (- cast c1) (cast c2))

-- 4. `WindowedHorizon` local causal patches (finite sliding buffer bounds overlap):
admissibleConvolution (WindowedHorizon w1)     (WindowedHorizon w2)     = Just (WindowedHorizon (min w1 w2))
admissibleConvolution (WindowedHorizon w)      (BoundedHorizon c)       = Just (WindowedHorizon (min w c))
admissibleConvolution (BoundedHorizon c)       (WindowedHorizon w)      = Just (WindowedHorizon (min w c))
admissibleConvolution (WindowedHorizon w)      (RetroBoundedHorizon c)  = Just (WindowedHorizon (min w c))
admissibleConvolution (RetroBoundedHorizon c)  (WindowedHorizon w)      = Just (WindowedHorizon (min w c))
admissibleConvolution (WindowedHorizon w)      OpenFuture               = Just (WindowedHorizon w)
admissibleConvolution OpenFuture               (WindowedHorizon w)      = Just (WindowedHorizon w)
admissibleConvolution (WindowedHorizon w)      BilateralOpen            = Just (WindowedHorizon w)
admissibleConvolution BilateralOpen            (WindowedHorizon w)      = Just (WindowedHorizon w)

-- 5. Unbounded opposite-ray / bilateral overlaps (statically disallowed):
admissibleConvolution (RetroBoundedHorizon _)  OpenFuture               = Nothing
admissibleConvolution OpenFuture               (RetroBoundedHorizon _)  = Nothing
admissibleConvolution (BoundedHorizon _)       BilateralOpen            = Nothing
admissibleConvolution BilateralOpen            (BoundedHorizon _)       = Nothing
admissibleConvolution (RetroBoundedHorizon _)  BilateralOpen            = Nothing
admissibleConvolution BilateralOpen            (RetroBoundedHorizon _)  = Nothing
admissibleConvolution OpenFuture               BilateralOpen            = Nothing
admissibleConvolution BilateralOpen            OpenFuture               = Nothing
admissibleConvolution BilateralOpen            BilateralOpen            = Nothing

public export
minInt4 : Integer -> Integer -> Integer -> Integer -> Integer
minInt4 a b c d =
  let ab = if a <= b then a else b
      cd = if c <= d then c else d
  in if ab <= cd then ab else cd

public export
maxInt4 : Integer -> Integer -> Integer -> Integer -> Integer
maxInt4 a b c d =
  let ab = if a >= b then a else b
      cd = if c >= d then c else d
  in if ab >= cd then ab else cd

||| Tight static lower exponent bound under Level-2 caretation (`[l1, h1] * [l2, h2]`).
public export
caretStaticLow : Integer -> Integer -> Integer -> Integer -> Integer
caretStaticLow l1 h1 l2 h2 = minInt4 (l1 * l2) (l1 * h2) (h1 * l2) (h1 * h2)

||| Tight static upper exponent bound under Level-2 caretation (`[l1, h1] * [l2, h2]`).
public export
caretStaticHigh : Integer -> Integer -> Integer -> Integer -> Integer
caretStaticHigh l1 h1 l2 h2 = maxInt4 (l1 * l2) (l1 * h2) (h1 * l2) (h1 * h2)

||| Compile-time admissibility and regime transformation for Level-2+ Dirichlet Caretation (`^`).
||| Static intervals multiply corners, bounded positive/retrograde rays scale degree products,
||| and open unwindowed streams are statically disallowed.
public export
caretRegime : LaurentRegime -> LaurentRegime -> Maybe LaurentRegime
caretRegime (StaticHorizon l1 h1)     (StaticHorizon l2 h2)     =
  Just (StaticHorizon (caretStaticLow l1 h1 l2 h2) (caretStaticHigh l1 h1 l2 h2))
caretRegime (BoundedHorizon c1)       (BoundedHorizon c2)       = Just (BoundedHorizon (c1 * c2))
caretRegime (RetroBoundedHorizon c1)  (RetroBoundedHorizon c2)  = Just (BoundedHorizon (c1 * c2))
caretRegime (WindowedHorizon w1)      (WindowedHorizon w2)      = Just (WindowedHorizon (min w1 w2))
caretRegime _                         _                         = Nothing

||| Tightens a `LaurentRegime` upon promotion to the zero-free positive `Poly*` (`e >= 1`) domain.
public export
polyStarRegime : LaurentRegime -> LaurentRegime
polyStarRegime (StaticHorizon l h)     = StaticHorizon (if l >= 1 then l else 1) (if h >= 1 then h else 1)
polyStarRegime (RetroBoundedHorizon _) = StaticHorizon 1 1
polyStarRegime reg                     = reg

||| Proof alias unlocking type-safe `*` only when `admissibleConvolution rA rB` succeeds.
public export
CanConvolve : LaurentRegime -> LaurentRegime -> Type
CanConvolve rA rB = IsJust (admissibleConvolution rA rB)

||| Constructive `Dec` recognizer deciding Cauchy convolution admissibility (`recognition-rule.md`).
public export
recognizeCanConvolve : (rA, rB : LaurentRegime) -> Dec (CanConvolve rA rB)
recognizeCanConvolve rA rB with (admissibleConvolution rA rB)
  recognizeCanConvolve rA rB | Just x  = Yes ItIsJust
  recognizeCanConvolve rA rB | Nothing = No (\prf => absurd prf)

||| Proof witness holding strictly for compact or bounded Laurent horizons,
||| statically blocking global reductions on open `OpenFuture` and `BilateralOpen` rays (`Rule 08` §1 & §5).
public export
data BoundedRegime : LaurentRegime -> Type where
  BoundedStatic   : {l, h : Integer} -> BoundedRegime (StaticHorizon l h)
  BoundedForward  : {c : Nat} -> BoundedRegime (BoundedHorizon c)
  BoundedRetro    : {c : Nat} -> BoundedRegime (RetroBoundedHorizon c)
  BoundedWindowed : {w : Nat} -> BoundedRegime (WindowedHorizon w)

public export
Uninhabited (BoundedRegime OpenFuture) where
  uninhabited BoundedStatic   impossible
  uninhabited BoundedForward  impossible
  uninhabited BoundedRetro    impossible
  uninhabited BoundedWindowed impossible

public export
Uninhabited (BoundedRegime BilateralOpen) where
  uninhabited BoundedStatic   impossible
  uninhabited BoundedForward  impossible
  uninhabited BoundedRetro    impossible
  uninhabited BoundedWindowed impossible

||| Constructive `Dec` recognizer certifying a `LaurentRegime` is bounded prior to global
||| `sumHMSet`, `totalMass`, or free-energy reductions (`recognition-rule.md`).
public export
recognizeBoundedRegime : (reg : LaurentRegime) -> Dec (BoundedRegime reg)
recognizeBoundedRegime (StaticHorizon _ _)     = Yes BoundedStatic
recognizeBoundedRegime (BoundedHorizon _)      = Yes BoundedForward
recognizeBoundedRegime (RetroBoundedHorizon _) = Yes BoundedRetro
recognizeBoundedRegime (WindowedHorizon _)     = Yes BoundedWindowed
recognizeBoundedRegime OpenFuture              = No absurd
recognizeBoundedRegime BilateralOpen           = No absurd
