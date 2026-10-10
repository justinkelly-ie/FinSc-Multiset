module Stage0.Singleton.Bit2

import Data.Linear
import Stage0.Interfaces
import public Stage0.BoxInt
import Stage0.Multiset
import Stage0.DepMultiset

%default total

-----------------------------------------------------------------------
-- BIT2 — BIFIED B₂ OVER DepMultiset 1
--
-- Bit2 uses DepMultiset (a dependently typed multiset whose element
-- contents are tracked at the type level) instead of Sing.
--
-- The representation is a DepMultiset of size 1 whose single element
-- is itself a Multiset, restricted to the two B₂ canonical values:
--
--   Zero2 : element = ZeroM             — []   (the empty multiset)
--   One2  : element = AddM ZeroM 1 ZeroM — [[]] (multiset containing [])
--
-- Type-level index for Zero2:
--   AddM ZeroM             1 ZeroM : Multiset BoxInt (Multiset BoxInt Void)
-- Type-level index for One2:
--   AddM (AddM ZeroM 1 ZeroM) 1 ZeroM : Multiset BoxInt (Multiset BoxInt Void)
-----------------------------------------------------------------------

||| The type-level Multiset index for the Zero2 element.
||| ZeroIdx = { [] → 1 } : Multiset BoxInt (Multiset BoxInt (Multiset BoxInt Void))
||| Stores the Bit-level Zero element: ZeroM : Multiset BoxInt (Multiset BoxInt Void)
public export
ZeroIdx : Multiset BoxInt (Multiset BoxInt (Multiset BoxInt Void))
ZeroIdx = AddM ZeroM 1 ZeroM

||| The type-level Multiset index for the One2 element.
||| OneIdx = { [[]] → 1 } : Multiset BoxInt (Multiset BoxInt (Multiset BoxInt Void))
||| Stores the Bit-level One element: AddM ZeroM 1 ZeroM : Multiset BoxInt (Multiset BoxInt Void)
public export
OneIdx : Multiset BoxInt (Multiset BoxInt (Multiset BoxInt Void))
OneIdx = AddM (AddM ZeroM 1 ZeroM) 1 ZeroM

-----------------------------------------------------------------------
-- CANONICAL CONSTRUCTORS
-----------------------------------------------------------------------

||| The zero element of B₂ as a DepMultiset of size 1.
||| Element: ZeroM = [] (the Bit-level Zero: empty Multiset BoxInt (Multiset BoxInt Void)).
public export
Zero2 : DepMultiset BoxInt (Multiset BoxInt (Multiset BoxInt Void)) ZeroIdx
Zero2 = DepAddM ZeroM 1 DepEmptyM

||| The one element of B₂ as a DepMultiset of size 1.
||| Element: AddM ZeroM 1 ZeroM = [[]] (the Bit-level One: Multiset containing ZeroM).
public export
One2 : DepMultiset BoxInt (Multiset BoxInt (Multiset BoxInt Void)) OneIdx
One2 = DepAddM (AddM ZeroM 1 ZeroM) 1 DepEmptyM

-----------------------------------------------------------------------
-- BIT2 — RUNTIME TYPE
--
-- Since Zero2 and One2 carry different type-level indices they cannot
-- share a single type alias directly. We introduce a runtime Bit2 sum
-- type that erases the index, preserving all the B₂ behaviour.
-----------------------------------------------------------------------

||| A Bit2 is a DepMultiset of size 1 whose single element is either
||| [] (zero) or [[]] (one), with the index erased to a runtime type.
public export
data Bit2 : Type where
  ||| 0 ∈ B₂ — DepMultiset { [] }.
  Bit2Zero : DepMultiset BoxInt (Multiset BoxInt (Multiset BoxInt Void)) ZeroIdx -> Bit2
  ||| 1 ∈ B₂ — DepMultiset { [[]] }.
  Bit2One  : DepMultiset BoxInt (Multiset BoxInt (Multiset BoxInt Void)) OneIdx  -> Bit2

||| The zero Bit2.
public export
b2Zero : Bit2
b2Zero = Bit2Zero Zero2

||| The one Bit2.
public export
b2One : Bit2
b2One = Bit2One One2

-----------------------------------------------------------------------
-- PREDICATES
-----------------------------------------------------------------------

public export
isB2Zero : Bit2 -> Bool
isB2Zero (Bit2Zero _) = True
isB2Zero (Bit2One  _) = False

public export
isB2One : Bit2 -> Bool
isB2One (Bit2One  _) = True
isB2One (Bit2Zero _) = False

-----------------------------------------------------------------------
-- DISPLAY
-----------------------------------------------------------------------

public export
Show Bit2 where
  show b = if isB2One b then "1" else "0"

-----------------------------------------------------------------------
-- ORD / EQ
-----------------------------------------------------------------------

public export
Eq Bit2 where
  (Bit2Zero _) == (Bit2Zero _) = True
  (Bit2One  _) == (Bit2One  _) = True
  _            == _             = False

public export
Ord Bit2 where
  compare (Bit2Zero _) (Bit2Zero _) = EQ
  compare (Bit2Zero _) (Bit2One  _) = LT
  compare (Bit2One  _) (Bit2Zero _) = GT
  compare (Bit2One  _) (Bit2One  _) = EQ

-----------------------------------------------------------------------
-- B₂ ARITHMETIC (mod 2)
-----------------------------------------------------------------------

||| Addition in B₂: exclusive or (XOR).
||| 0+0=0  0+1=1  1+0=1  1+1=0
public export
addBit2 : Bit2 -> Bit2 -> Bit2
addBit2 (Bit2Zero _) y            = y
addBit2 x            (Bit2Zero _) = x
addBit2 (Bit2One  _) (Bit2One  _) = b2Zero

||| Multiplication in B₂: logical AND.
||| 0*0=0  0*1=0  1*0=0  1*1=1
public export
mulBit2 : Bit2 -> Bit2 -> Bit2
mulBit2 (Bit2One _) (Bit2One _) = b2One
mulBit2 _           _           = b2Zero

||| Algebra of Boole complement: ¬x = 1 + x.
||| negate Zero2 = One2, negate One2 = Zero2.
public export
negBit2 : Bit2 -> Bit2
negBit2 x = addBit2 b2One x

-----------------------------------------------------------------------
-- NUM / NEG INSTANCES
-----------------------------------------------------------------------

public export
Num Bit2 where
  (+)         = addBit2
  (*)         = mulBit2
  fromInteger n = if mod n 2 == 0 then b2Zero else b2One

public export
Neg Bit2 where
  negate = negBit2
  (-) x y = addBit2 x (negBit2 y)

-----------------------------------------------------------------------
-- CONVERSION
-----------------------------------------------------------------------

public export
bit2ToNat : Bit2 -> Nat
bit2ToNat (Bit2One  _) = S Z
bit2ToNat (Bit2Zero _) = Z

public export
natToBit2 : Nat -> Bit2
natToBit2 Z         = b2Zero
natToBit2 (S Z)     = b2One
natToBit2 (S (S k)) = natToBit2 k

public export
bit2ToInteger : Bit2 -> Integer
bit2ToInteger (Bit2One  _) = 1
bit2ToInteger (Bit2Zero _) = 0

public export
bit2ToBoxInt : Bit2 -> BoxInt
bit2ToBoxInt (Bit2One  _) = 1
bit2ToBoxInt (Bit2Zero _) = 0

public export
normalizeBit2 : Bit2 -> Bit2
normalizeBit2 (Bit2Zero _) = b2Zero
normalizeBit2 (Bit2One  _) = b2One

-----------------------------------------------------------------------
-- ABSOLUTE VALUE
-----------------------------------------------------------------------

public export
Abs Bit2 where
  abs x = x

-----------------------------------------------------------------------
-- FREEZE: RECOVER THE CARRIED DepMultiset
-----------------------------------------------------------------------

||| Freeze the canonical DepMultiset element out of a Bit2.
||| Returns the runtime Multiset that the DepMultiset tracks.
public export
freezeBit2 : Bit2 -> Multiset BoxInt (Multiset BoxInt (Multiset BoxInt Void))
freezeBit2 (Bit2Zero dm) = freezeDep dm
freezeBit2 (Bit2One  dm) = freezeDep dm

-----------------------------------------------------------------------
-- LINEAR INSTANCES
--
-- Pattern-match on constructors so each linear name is used exactly once.
-----------------------------------------------------------------------

public export
LConsumable Bit2 where
  lconsume (Bit2Zero _) = ()
  lconsume (Bit2One  _) = ()

public export
LComonoid Bit2 where
  lcomult (Bit2Zero _) = Builtin.(#) b2Zero b2Zero
  lcomult (Bit2One  _) = Builtin.(#) b2One  b2One

public export
LEq Bit2 where
  lEq (Bit2Zero _) (Bit2Zero _) = Builtin.(#) True  (Builtin.(#) b2Zero b2Zero)
  lEq (Bit2One  _) (Bit2One  _) = Builtin.(#) True  (Builtin.(#) b2One  b2One)
  lEq (Bit2Zero _) (Bit2One  _) = Builtin.(#) False (Builtin.(#) b2Zero b2One)
  lEq (Bit2One  _) (Bit2Zero _) = Builtin.(#) False (Builtin.(#) b2One  b2Zero)
