module Stage0.BoxInt

import Data.Nat
import Data.Linear

%default total

------------------------------------------------------------------------
-- 1. BOXINT SCALAR TYPE & MONOMORPHIC ARITHMETIC
------------------------------------------------------------------------

||| A BoxInt is a signed integer wrapped in a discrete box.
||| It represents concrete particle counts, quadrances, and metric entries
||| in Wildberger's Box Arithmetic.
|||
||| 2LTT Staging Operation: Lifting (⇑Int) - Lifts raw integer scalars into 0-defect discrete scalar space.
public export
record BoxInt where
  constructor MkBoxInt
  value : Integer

||| 2LTT Staging Operation: Splicing (~t) - Extracts raw underlying Integer term from boxed representation.
%inline public export
unwrapBox : BoxInt -> Integer
unwrapBox (MkBoxInt v) = v

||| 2LTT Staging Operation: Lifting (⇑Int) - Lifts integer value into boxed discrete representation.
%inline public export
intToBoxInt : Integer -> BoxInt
intToBoxInt n = MkBoxInt n

%inline public export
integerToBoxInt : Integer -> BoxInt
integerToBoxInt n = MkBoxInt n

%inline public export
natToBoxInt : Nat -> BoxInt
natToBoxInt n = MkBoxInt (natToInteger n)

%inline public export
addBox : BoxInt -> BoxInt -> BoxInt
addBox (MkBoxInt a) (MkBoxInt b) = MkBoxInt (a + b)

%inline public export
subBox : BoxInt -> BoxInt -> BoxInt
subBox (MkBoxInt a) (MkBoxInt b) = MkBoxInt (a - b)

public export
addBoxLinear : (1 a : BoxInt) -> (1 b : BoxInt) -> BoxInt
addBoxLinear (MkBoxInt a) (MkBoxInt b) = MkBoxInt (a + b)

public export
subBoxLinear : (1 a : BoxInt) -> (1 b : BoxInt) -> BoxInt
subBoxLinear (MkBoxInt a) (MkBoxInt b) = MkBoxInt (a - b)

%inline public export
mulBox : BoxInt -> BoxInt -> BoxInt
mulBox (MkBoxInt a) (MkBoxInt b) = MkBoxInt (a * b)

%inline public export
boxEq : BoxInt -> BoxInt -> Bool
boxEq (MkBoxInt a) (MkBoxInt b) = case a == b of True => True; False => False

%inline public export
boxLTE : BoxInt -> BoxInt -> Bool
boxLTE (MkBoxInt a) (MkBoxInt b) = case a <= b of True => True; False => False

%inline public export
Num BoxInt where
  (+) (MkBoxInt a) (MkBoxInt b) = MkBoxInt (a + b)
  (*) (MkBoxInt a) (MkBoxInt b) = MkBoxInt (a * b)
  fromInteger n = MkBoxInt n

%inline public export
negBox : BoxInt -> BoxInt
negBox (MkBoxInt a) = MkBoxInt (-a)

%inline public export
Neg BoxInt where
  negate (MkBoxInt a) = MkBoxInt (-a)
  (-) (MkBoxInt a) (MkBoxInt b) = MkBoxInt (a - b)

%inline public export
divBox : BoxInt -> BoxInt -> BoxInt
divBox (MkBoxInt a) (MkBoxInt b) = MkBoxInt (case b of 0 => 0; _ => assert_total (a `div` b))

%inline public export
modBox : BoxInt -> BoxInt -> BoxInt
modBox (MkBoxInt a) (MkBoxInt b) = MkBoxInt (case b of 0 => 0; _ => assert_total (a `mod` b))

public export
Integral BoxInt where
  div (MkBoxInt a) (MkBoxInt b) = MkBoxInt (case b of 0 => 0; _ => assert_total (a `div` b))
  mod (MkBoxInt a) (MkBoxInt b) = MkBoxInt (case b of 0 => 0; _ => assert_total (a `mod` b))

public export
Abs BoxInt where
  abs (MkBoxInt v) = MkBoxInt (case v < 0 of True => -v; False => v)

public export
Cast Nat BoxInt where
  cast = natToBoxInt

public export
Cast Integer BoxInt where
  cast = intToBoxInt

||| Converts BoxInt to Nat, clamping negative values to 0.
||| For absolute-value conversion use absBox first.
%inline public export
boxToNat : BoxInt -> Nat
boxToNat (MkBoxInt v) = if v <= 0 then 0 else integerToNat v

public export
Cast BoxInt Nat where
  cast = boxToNat

||| Returns the absolute value of a BoxInt as a BoxInt.
||| Does not go through boxToNat — safe for negative inputs.
%inline public export
absBox : BoxInt -> BoxInt
absBox (MkBoxInt v) = MkBoxInt (if v < 0 then -v else v)

%inline public export
Eq BoxInt where
  (MkBoxInt a) == (MkBoxInt b) = a == b

public export
Ord BoxInt where
  compare (MkBoxInt a) (MkBoxInt b) = compare a b

public export
Show BoxInt where
  show (MkBoxInt a) = "[" ++ show a ++ "]"

%inline public export
boxAdd : BoxInt -> BoxInt -> BoxInt
boxAdd = addBox

%inline public export
boxSub : BoxInt -> BoxInt -> BoxInt
boxSub = subBox

%inline public export
boxMult : BoxInt -> BoxInt -> BoxInt
boxMult (MkBoxInt a) (MkBoxInt b) = MkBoxInt (a * b)

%inline public export
boxMul : BoxInt -> BoxInt -> BoxInt
boxMul = mulBox

%inline public export
natToBox : Nat -> BoxInt
natToBox = natToBoxInt

public export
record NonZeroBoxInt where
  constructor MkNonZeroBoxInt
  val : BoxInt

public export
toNonZeroBoxInt : BoxInt -> Maybe NonZeroBoxInt
toNonZeroBoxInt b =
  let n = unwrapBox b
  in if n == 0 then Nothing
     else Just (MkNonZeroBoxInt b)
