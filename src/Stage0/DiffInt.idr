module Stage0.DiffInt

import Data.Nat
import Syntax.PreorderReasoning
import Stage0.BoxNat
import Stage0.BoxInt

%default total

------------------------------------------------------------------------
-- 1. CONSTRUCTIVE DIFFERENCE PAIR INTEGER TYPE
------------------------------------------------------------------------

||| A Constructive Integer represented as an exact difference pair [pos, neg]
||| of BoxNat values, representing the integer (pos - neg).
|||
||| Defined according to Norman Wildberger's constructivism:
||| integers are formal difference pairs of natural tallies, without
||| relying on uninterpreted foreign GMP primitives.
public export
record DiffInt where
  constructor MkDiffInt
  pos : BoxNat
  neg : BoxNat

||| Two difference pairs [p1, n1] and [p2, n2] are algebraically equivalent
||| iff cross-addition holds: p1 + n2 = p2 + n1.
public export
diffIntEquiv : DiffInt -> DiffInt -> Bool
diffIntEquiv (MkDiffInt p1 n1) (MkDiffInt p2 n2) =
  (unwrapBoxNat p1 + unwrapBoxNat n2) == (unwrapBoxNat p2 + unwrapBoxNat n1)

||| Zero difference pair [0, 0].
public export
ZeroDiffInt : DiffInt
ZeroDiffInt = MkDiffInt (MkBoxNat 0) (MkBoxNat 0)

||| Lowercase alias for ZeroDiffInt.
public export
zeroDiffInt : DiffInt
zeroDiffInt = ZeroDiffInt

||| Multiplicative unity difference pair [1, 0].
public export
OneDiffInt : DiffInt
OneDiffInt = MkDiffInt (MkBoxNat 1) (MkBoxNat 0)

||| Lowercase alias for OneDiffInt.
public export
oneDiffInt : DiffInt
oneDiffInt = OneDiffInt

||| Negative unity difference pair [0, 1].
public export
NegOneDiffInt : DiffInt
NegOneDiffInt = MkDiffInt (MkBoxNat 0) (MkBoxNat 1)

||| Lowercase alias for NegOneDiffInt.
public export
negOneDiffInt : DiffInt
negOneDiffInt = NegOneDiffInt

||| Embeds a BoxNat into a non-negative difference pair [n, 0].
public export
boxNatToDiffInt : BoxNat -> DiffInt
boxNatToDiffInt n = MkDiffInt n (MkBoxNat 0)

||| Normalizes a difference pair by subtracting the common minimum:
||| reduces [p, n] to either [p - n, 0] or [0, n - p].
public export
normalizeDiffInt : DiffInt -> DiffInt
normalizeDiffInt (MkDiffInt (MkBoxNat p) (MkBoxNat n)) =
  if p >= n
    then MkDiffInt (MkBoxNat (minus p n)) (MkBoxNat 0)
    else MkDiffInt (MkBoxNat 0) (MkBoxNat (minus n p))

||| Converts a difference pair [p, n] to a signed BoxInt (p - n).
public export
diffIntToBoxInt : DiffInt -> BoxInt
diffIntToBoxInt (MkDiffInt (MkBoxNat p) (MkBoxNat n)) =
  intToBoxInt (cast p - cast n)

||| Lifts a signed BoxInt into a canonical difference pair.
public export
boxIntToDiffInt : BoxInt -> DiffInt
boxIntToDiffInt (MkBoxInt v) =
  if v >= 0
    then MkDiffInt (MkBoxNat (integerToNat v)) (MkBoxNat 0)
    else MkDiffInt (MkBoxNat 0) (MkBoxNat (integerToNat (-v)))

------------------------------------------------------------------------
-- 2. EXACT CONSTRUCTIVE RING ARITHMETIC
------------------------------------------------------------------------

||| Addition of difference pairs: [p1, n1] + [p2, n2] = [p1 + p2, n1 + n2].
public export
addDiffInt : DiffInt -> DiffInt -> DiffInt
addDiffInt (MkDiffInt p1 n1) (MkDiffInt p2 n2) =
  MkDiffInt (boxNatAdd p1 p2) (boxNatAdd n1 n2)

||| Negation of a difference pair: -[p, n] = [n, p].
public export
negDiffInt : DiffInt -> DiffInt
negDiffInt (MkDiffInt p n) = MkDiffInt n p

||| Subtraction of difference pairs: d1 - d2 = d1 + (-d2).
public export
subDiffInt : DiffInt -> DiffInt -> DiffInt
subDiffInt d1 d2 = addDiffInt d1 (negDiffInt d2)

||| Multiplication of difference pairs:
||| (p1 - n1) * (p2 - n2) = (p1*p2 + n1*n2) - (p1*n2 + n1*p2).
public export
mulDiffInt : DiffInt -> DiffInt -> DiffInt
mulDiffInt (MkDiffInt p1 n1) (MkDiffInt p2 n2) =
  let posTerm = boxNatAdd (boxNatMul p1 p2) (boxNatMul n1 n2)
      negTerm = boxNatAdd (boxNatMul p1 n2) (boxNatMul n1 p2)
  in MkDiffInt posTerm negTerm

public export
Eq DiffInt where
  d1 == d2 = diffIntEquiv d1 d2

public export
Show DiffInt where
  show (MkDiffInt (MkBoxNat p) (MkBoxNat n)) =
    "DiffInt[" ++ show p ++ " - " ++ show n ++ " = " ++ show (cast {to=Integer} p - cast {to=Integer} n) ++ "]"

public export
Num DiffInt where
  (+) = addDiffInt
  (*) = mulDiffInt
  fromInteger n = boxIntToDiffInt (MkBoxInt n)

public export
Neg DiffInt where
  negate = negDiffInt
  (-) = subDiffInt

------------------------------------------------------------------------
-- 3. UNIVERSAL COMMUTATIVE RING LEMMAS
------------------------------------------------------------------------

||| Additive identity on the left: 0 + a = a.
public export
0 diffIntAddZeroLeft : (a : DiffInt) -> addDiffInt ZeroDiffInt a = a
diffIntAddZeroLeft (MkDiffInt (MkBoxNat p) (MkBoxNat n)) = Refl

||| Additive identity on the right: a + 0 = a.
public export
0 diffIntAddZeroRight : (a : DiffInt) -> addDiffInt a ZeroDiffInt = a
diffIntAddZeroRight (MkDiffInt p n) =
  cong2 MkDiffInt (boxNatAddZeroRight p) (boxNatAddZeroRight n)

||| Commutativity of addition: a + b = b + a.
public export
0 diffIntAddComm : (a, b : DiffInt) -> addDiffInt a b = addDiffInt b a
diffIntAddComm (MkDiffInt p1 n1) (MkDiffInt p2 n2) =
  cong2 MkDiffInt (boxNatAddComm p1 p2) (boxNatAddComm n1 n2)

||| Associativity of addition: (a + b) + c = a + (b + c).
public export
0 diffIntAddAssoc : (a, b, c : DiffInt) -> addDiffInt (addDiffInt a b) c = addDiffInt a (addDiffInt b c)
diffIntAddAssoc (MkDiffInt p1 n1) (MkDiffInt p2 n2) (MkDiffInt p3 n3) =
  cong2 MkDiffInt (boxNatAddAssoc p1 p2 p3) (boxNatAddAssoc n1 n2 n3)

||| Involution of negation: -(-a) = a.
public export
0 diffIntNegInvolutive : (a : DiffInt) -> negDiffInt (negDiffInt a) = a
diffIntNegInvolutive (MkDiffInt p n) = Refl

||| Commutativity of multiplication: a * b = b * a.
public export
0 diffIntMulComm : (a, b : DiffInt) -> mulDiffInt a b = mulDiffInt b a
diffIntMulComm (MkDiffInt p1 n1) (MkDiffInt p2 n2) =
  let prfPos = Calc $
        |~ boxNatAdd (boxNatMul p1 p2) (boxNatMul n1 n2)
        ~~ boxNatAdd (boxNatMul p2 p1) (boxNatMul n1 n2)
              ...(cong (\x => boxNatAdd x (boxNatMul n1 n2)) (boxNatMulComm p1 p2))
        ~~ boxNatAdd (boxNatMul p2 p1) (boxNatMul n2 n1)
              ...(cong (\y => boxNatAdd (boxNatMul p2 p1) y) (boxNatMulComm n1 n2))
      prfNeg = Calc $
        |~ boxNatAdd (boxNatMul p1 n2) (boxNatMul n1 p2)
        ~~ boxNatAdd (boxNatMul n2 p1) (boxNatMul n1 p2)
              ...(cong (\x => boxNatAdd x (boxNatMul n1 p2)) (boxNatMulComm p1 n2))
        ~~ boxNatAdd (boxNatMul n2 p1) (boxNatMul p2 n1)
              ...(cong (\y => boxNatAdd (boxNatMul n2 p1) y) (boxNatMulComm n1 p2))
        ~~ boxNatAdd (boxNatMul p2 n1) (boxNatMul n2 p1)
              ...(boxNatAddComm (boxNatMul n2 p1) (boxNatMul p2 n1))
  in cong2 MkDiffInt prfPos prfNeg

||| Multiplicative identity on the right: a * 1 = a.
public export
0 diffIntMulOneRight : (a : DiffInt) -> mulDiffInt a OneDiffInt = a
diffIntMulOneRight (MkDiffInt p n) =
  let prfPos = Calc $
        |~ boxNatAdd (boxNatMul p (MkBoxNat 1)) (boxNatMul n (MkBoxNat 0))
        ~~ boxNatAdd p (boxNatMul n (MkBoxNat 0))
              ...(cong (\x => boxNatAdd x (boxNatMul n (MkBoxNat 0))) (boxNatMulOneRight p))
        ~~ boxNatAdd p (MkBoxNat 0)
              ...(cong (\y => boxNatAdd p y) (boxNatMulZeroRight n))
        ~~ p  ...(boxNatAddZeroRight p)
      prfNeg = Calc $
        |~ boxNatAdd (boxNatMul p (MkBoxNat 0)) (boxNatMul n (MkBoxNat 1))
        ~~ boxNatAdd (MkBoxNat 0) (boxNatMul n (MkBoxNat 1))
              ...(cong (\x => boxNatAdd x (boxNatMul n (MkBoxNat 1))) (boxNatMulZeroRight p))
        ~~ boxNatAdd (MkBoxNat 0) n
              ...(cong (\y => boxNatAdd (MkBoxNat 0) y) (boxNatMulOneRight n))
        ~~ n  ...(boxNatAddZeroLeft n)
  in cong2 MkDiffInt prfPos prfNeg

||| Multiplicative zero on the right: a * 0 = 0.
public export
0 diffIntMulZeroRight : (a : DiffInt) -> mulDiffInt a ZeroDiffInt = ZeroDiffInt
diffIntMulZeroRight (MkDiffInt (MkBoxNat p) (MkBoxNat n)) =
  let prfPos = Calc $
        |~ boxNatAdd (boxNatMul (MkBoxNat p) (MkBoxNat 0)) (boxNatMul (MkBoxNat n) (MkBoxNat 0))
        ~~ boxNatAdd (MkBoxNat 0) (boxNatMul (MkBoxNat n) (MkBoxNat 0))
              ...(cong (\x => boxNatAdd x (boxNatMul (MkBoxNat n) (MkBoxNat 0))) (boxNatMulZeroRight (MkBoxNat p)))
        ~~ boxNatAdd (MkBoxNat 0) (MkBoxNat 0)
              ...(cong (\y => boxNatAdd (MkBoxNat 0) y) (boxNatMulZeroRight (MkBoxNat n)))
        ~~ MkBoxNat 0 ...(Refl)
      prfNeg = Calc $
        |~ boxNatAdd (boxNatMul (MkBoxNat p) (MkBoxNat 0)) (boxNatMul (MkBoxNat n) (MkBoxNat 0))
        ~~ boxNatAdd (MkBoxNat 0) (boxNatMul (MkBoxNat n) (MkBoxNat 0))
              ...(cong (\x => boxNatAdd x (boxNatMul (MkBoxNat n) (MkBoxNat 0))) (boxNatMulZeroRight (MkBoxNat p)))
        ~~ boxNatAdd (MkBoxNat 0) (MkBoxNat 0)
              ...(cong (\y => boxNatAdd (MkBoxNat 0) y) (boxNatMulZeroRight (MkBoxNat n)))
        ~~ MkBoxNat 0 ...(Refl)
  in cong2 MkDiffInt prfPos prfNeg

||| Diagonal reflexivity for Nat under boolean equality.
public export
0 natEqRefl : (k : Nat) -> (k == k) = True
natEqRefl Z = Refl
natEqRefl (S k) = natEqRefl k

||| Additive inverse produces an algebraically null difference pair:
||| (p - n) + (-(p - n)) = (p + n, n + p) ~ (0, 0).
public export
0 diffIntAdditiveInverseEquiv : (a : DiffInt) -> diffIntEquiv (addDiffInt a (negDiffInt a)) ZeroDiffInt = True
diffIntAdditiveInverseEquiv (MkDiffInt (MkBoxNat p) (MkBoxNat n)) =
  let 0 prfEq : ((p + n) + 0 = 0 + (n + p))
      prfEq = Calc $
        |~ (p + n) + 0
        ~~ p + n ...(plusZeroRightNeutral (p + n))
        ~~ n + p ...(plusCommutative p n)
        ~~ 0 + (n + p) ..<(plusZeroLeftNeutral (n + p))
  in rewrite prfEq in natEqRefl (0 + (n + p))
