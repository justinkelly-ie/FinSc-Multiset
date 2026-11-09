module Stage0.Singleton.Bit

import Data.Linear
import Stage0.Interfaces
import public Stage0.BoxInt
import public Stage0.Multiset
import public Stage0.Token

%default total

||| Bit is the canonical atomic binary logic carrier in the Multiset Algebra of Boole.
||| Defined directly as an atomic token constructor carrying the von Neumann multiset representation:
||| Zero = MkToken ZeroM ([] = empty multiset)
||| One  = MkToken (AddM ZeroM 1 ZeroM) ([[]] = multiset containing the empty multiset)
public export
data Bit : Type where
  MkToken : Multiset BoxInt (Multiset BoxInt Void) -> Bit

||| Converts an atomic Bit to a generic Token.
public export
bitToToken : Bit -> Token (Multiset BoxInt (Multiset BoxInt Void))
bitToToken (MkToken m) = MkToken m

||| Converts a generic Token over multiset void to an atomic Bit.
public export
tokenToBit : Token (Multiset BoxInt (Multiset BoxInt Void)) -> Bit
tokenToBit (MkToken m) = MkToken m

public export
Zero : Bit
Zero = MkToken ZeroM

public export
One : Bit
One = MkToken (AddM ZeroM 1 ZeroM)

public export
isZero : Bit -> Bool
isZero (MkToken ZeroM) = True
isZero _               = False

public export
isOne : Bit -> Bool
isOne (MkToken (AddM _ _ _)) = True
isOne _                      = False

public export
Eq Bit where
  (MkToken ZeroM) == (MkToken ZeroM) = True
  (MkToken ZeroM) == _               = False
  _               == (MkToken ZeroM) = False
  _               == _               = True

public export
Show Bit where
  show b = if isOne b then "1" else "0"

public export
addBit : Bit -> Bit -> Bit
addBit (MkToken ZeroM) y               = y
addBit x               (MkToken ZeroM) = x
addBit _               _               = Zero

public export
mulBit : Bit -> Bit -> Bit
mulBit (MkToken ZeroM) _               = Zero
mulBit _               (MkToken ZeroM) = Zero
mulBit x               _               = x

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
  lconsume (MkToken _) = ()

public export
LComonoid Bit where
  lcomult (MkToken ZeroM) = Builtin.(#) Zero Zero
  lcomult (MkToken m)     = Builtin.(#) (MkToken m) (MkToken m)

public export
LEq Bit where
  lEq (MkToken ZeroM) (MkToken ZeroM) = Builtin.(#) True  (Builtin.(#) Zero Zero)
  lEq (MkToken ZeroM) y               = Builtin.(#) False (Builtin.(#) Zero y)
  lEq x               (MkToken ZeroM) = Builtin.(#) False (Builtin.(#) x    Zero)
  lEq x               y               = Builtin.(#) True  (Builtin.(#) x    y)
