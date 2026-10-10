module Stage0.Singleton.Bit

import Data.Linear
import Stage0.Interfaces
import public Stage0.BoxInt
import public Stage0.Multiset
import public Stage0.Singleton.Sing

%default total

public export
Bit : Type
Bit = Sing (Multiset BoxInt (Multiset BoxInt Void))

public export
Zero : Bit
Zero = MkSing ZeroM

public export
One : Bit
One = MkSing (AddM ZeroM 1 ZeroM)

public export
isZero : Bit -> Bool
isZero (MkSing ZeroM) = True
isZero _              = False

public export
isOne : Bit -> Bool
isOne (MkSing (AddM _ _ _)) = True
isOne _                     = False

public export
Eq Bit where
  (MkSing ZeroM) == (MkSing ZeroM) = True
  (MkSing ZeroM) == _              = False
  _              == (MkSing ZeroM) = False
  _              == _              = True

public export
Show Bit where
  show b = if isOne b then "1" else "0"

public export
Ord Bit where
  compare x y =
    case (isOne x, isOne y) of
      (False, False) => EQ
      (False, True)  => LT
      (True,  False) => GT
      (True,  True)  => EQ

public export
addBit : Bit -> Bit -> Bit
addBit (MkSing ZeroM) y             = y
addBit x             (MkSing ZeroM) = x
addBit _             _              = Zero

public export
mulBit : Bit -> Bit -> Bit
mulBit (MkSing ZeroM) _             = Zero
mulBit _             (MkSing ZeroM) = Zero
mulBit x             _              = x

public export
negBit : Bit -> Bit
negBit x = addBit One x

public export
Num Bit where
  (+)           = addBit
  (*)           = mulBit
  fromInteger n = if mod n 2 == 0 then Zero else One

public export
Neg Bit where
  negate  = negBit
  (-) x y = addBit x (negBit y)

public export
bitToNat : Bit -> Nat
bitToNat b = if isOne b then S Z else Z

public export
natToBit : Nat -> Bit
natToBit Z         = Zero
natToBit (S Z)     = One
natToBit (S (S k)) = natToBit k

public export
bitToInteger : Bit -> Integer
bitToInteger b = if isOne b then 1 else 0

public export
bitToBoxInt : Bit -> BoxInt
bitToBoxInt b = if isOne b then 1 else 0

public export
boolToBit : Bool -> Bit
boolToBit True  = One
boolToBit False = Zero

public export
normalize : Bit -> Bit
normalize b = if isOne b then One else Zero

public export
Abs Bit where
  abs x = x

public export
LConsumable Bit where
  lconsume (MkSing _) = ()

public export
LComonoid Bit where
  lcomult (MkSing ZeroM) = Builtin.(#) Zero Zero
  lcomult (MkSing m)     = Builtin.(#) (MkSing m) (MkSing m)

public export
LEq Bit where
  lEq (MkSing ZeroM) (MkSing ZeroM) = Builtin.(#) True  (Builtin.(#) Zero Zero)
  lEq (MkSing ZeroM) y              = Builtin.(#) False (Builtin.(#) Zero y)
  lEq x              (MkSing ZeroM) = Builtin.(#) False (Builtin.(#) x    Zero)
  lEq x              y              = Builtin.(#) True  (Builtin.(#) x    y)
