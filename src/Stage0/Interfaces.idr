module Stage0.Interfaces

import public Data.Linear
import Data.Fin
import Data.Nat
import Stage0.BoxInt

%default total

-----------------------------------------------------------------------
-- 0. CANONICAL COORDINATE INTERFACE HIERARCHY (07-coordinate-systems.md)
-----------------------------------------------------------------------

||| Level 1: Unstructured discrete coordinate domain supporting pointwise multiset operations
||| (`AddM`, `SubM`, `HadamardM`, `MinM`, `MaxM`) and inner products (`DotStatic`, `DotFinite`, `DotWindow`).
public export
interface Ord k => DiscreteCoord k where

||| Level 2: Closed, bounded finite coordinate universe with a compile-time `cardinality`
||| and `0`-quantity erased bijection proofs to `Fin cardinality`.
public export
interface DiscreteCoord k => FiniteCoord k where
  cardinality : Nat
  toIndex     : k -> Fin cardinality
  fromIndex   : Fin cardinality -> k
  0 leftInv   : (x : k) -> fromIndex (toIndex x) = x
  0 rightInv  : (i : Fin cardinality) -> toIndex (fromIndex i) = i

||| Level 3: Translation-invariant coordinate space or interaction timeline supporting
||| additive Cauchy convolution (`MulStatic`, `MulFinite`, `MulStream`).
public export
interface DiscreteCoord k => MonoidCoord k where
  combine : k -> k -> k
  origin  : k
  0 assoc : (x, y, z : k) -> combine x (combine y z) = combine (combine x y) z

||| Level 4: Reversible or periodic coordinate space supporting periodic Torus wrapping
||| and fast NTT/FFT transforms.
public export
interface MonoidCoord k => GroupCoord k where
  inverse  : k -> k
  0 invLaw : (x : k) -> combine x (inverse x) = Stage0.Interfaces.origin

||| Level 5: Directed relational / adjacency edge coordinate pair `(a, b)` supporting
||| matrix/relational contraction (`MulStatic`, `OuterM`, `ContractR`, `ContractL`).
public export
interface (DiscreteCoord a, DiscreteCoord b) => PairCoord a b where
  edgeSource : (a, b) -> a
  edgeTarget : (a, b) -> b
  mkEdge     : a -> b -> (a, b)

public export
DiscreteCoord Nat where

public export
DiscreteCoord Integer where

public export
DiscreteCoord String where

public export
DiscreteCoord BoxInt where

public export
DiscreteCoord (Fin n) where

public export
(DiscreteCoord a, DiscreteCoord b) => DiscreteCoord (a, b) where

public export
(DiscreteCoord a, DiscreteCoord b) => DiscreteCoord (Either a b) where

public export
(DiscreteCoord a, DiscreteCoord b) => PairCoord a b where
  edgeSource (x, _) = x
  edgeTarget (_, y) = y
  mkEdge x y = (x, y)

public export
{n : Nat} -> FiniteCoord (Fin n) where
  cardinality = n
  toIndex i   = i
  fromIndex i = i
  leftInv _   = Refl
  rightInv _  = Refl

public export
MonoidCoord Nat where
  combine = (+)
  origin  = 0
  assoc x y z = plusAssociative x y z

public export
(MonoidCoord a, MonoidCoord b) => MonoidCoord (a, b) where
  combine (x1, y1) (x2, y2) = (combine x1 x2, combine y1 y2)
  origin = (origin, origin)
  assoc (x1, y1) (x2, y2) (x3, y3) =
    rewrite assoc x1 x2 x3 in
    rewrite assoc y1 y2 y3 in
    Refl

||| Vector/Matrix/Tensor Multiset Algebra interface encompassing the 5 canonical calculus operations:
||| addition (+), subtraction (-), multiplication (*), Hadamard pointwise product (.*),
||| tropical infimum (min), tropical supremum (max), and inner product (dot).
public export
interface MultisetAlgebra a where
  zeroM     : a
  addM      : a -> a -> a
  subM      : a -> a -> a
  subM x y = addM x (scaleM (intToBoxInt (-1)) y)
  scaleM    : BoxInt -> a -> a
  mulM      : a -> a -> a
  mulM = hadamardM
  hadamardM : a -> a -> a
  minM      : a -> a -> a
  maxM      : a -> a -> a
  dotM      : a -> a -> BoxInt

-----------------------------------------------------------------------
-- CANONICAL SYMBOLIC INFIX OPERATORS FOR MULTISET ALGEBRA
-----------------------------------------------------------------------

public export
infixl 7 <.>

||| Inner / Dot product: <.>
public export
(<.>) : MultisetAlgebra a => a -> a -> BoxInt
(<.>) = dotM

public export
infixl 8 .*.

||| Pointwise / Hadamard product: .*.
public export
(.*.) : MultisetAlgebra a => a -> a -> a
(.*.) = hadamardM

public export
infixl 8 /\

||| Tropical infimum / Lattice meet (min): /\
public export
(/\) : MultisetAlgebra a => a -> a -> a
(/\) = minM

public export
infixl 8 \/

||| Tropical supremum / Lattice join (max): \/
public export
(\/) : MultisetAlgebra a => a -> a -> a
(\/) = maxM

public export
infixl 7 ><

public export
implementation (Show a, Show b) => Show (LPair a b) where
  show (x # y) = "(" ++ show x ++ " # " ++ show y ++ ")"

-----------------------------------------------------------------------
-- 1. CORE LINEAR INTERFACES
-----------------------------------------------------------------------

||| LConsumable: A protocol for destroying linear resources.
public export
interface LConsumable a where
  lconsume : (1 _ : a) -> ()

||| LComonoid: A protocol for duplicating linear resources.
public export
interface LConsumable a => LComonoid a where
  lcounit : (1 _ : a) -> ()
  lcounit x = lconsume x
  
  lcomult : (1 _ : a) -> LPair a a

||| LEq: A linear version of Boolean equality.
public export
interface (LComonoid a) => LEq a where
  lEq : (1 _ : a) -> (1 _ : a) -> LPair Bool (LPair a a)

-----------------------------------------------------------------------
-- 2. STANDARD IMPLEMENTATIONS
-----------------------------------------------------------------------

public export
lconsumeNat : (1 _ : Nat) -> ()
lconsumeNat Z = ()
lconsumeNat (S k) = lconsumeNat k

public export
lcomultNat : (1 _ : Nat) -> LPair Nat Nat
lcomultNat Z = Builtin.(#) Z Z
lcomultNat (S k) = let Builtin.(#) k1 k2 = lcomultNat k in Builtin.(#) (S k1) (S k2)

public export
lEqNat : (1 _ : Nat) -> (1 _ : Nat) -> LPair Bool (LPair Nat Nat)
lEqNat Z Z = Builtin.(#) True (Builtin.(#) Z Z)
lEqNat (S k) (S j) = let Builtin.(#) res (Builtin.(#) k1 j1) = lEqNat k j in Builtin.(#) res (Builtin.(#) (S k1) (S j1))
lEqNat Z (S j) = Builtin.(#) False (Builtin.(#) Z (S j))
lEqNat (S k) Z = Builtin.(#) False (Builtin.(#) (S k) Z)

public export
implementation LConsumable Nat where
  lconsume = lconsumeNat

public export
implementation LComonoid Nat where
  lcomult = lcomultNat

public export
implementation LEq Nat where
  lEq = lEqNat

public export
implementation LConsumable () where
  lconsume () = ()

public export
implementation LComonoid () where
  lcomult () = Builtin.(#) () ()

public export
implementation LEq () where
  lEq () () = Builtin.(#) True (Builtin.(#) () ())

public export
implementation LConsumable Bool where
  lconsume True = ()
  lconsume False = ()

public export
implementation LComonoid Bool where
  lcomult True = Builtin.(#) True True
  lcomult False = Builtin.(#) False False

public export
implementation (LConsumable a, LConsumable b) => LConsumable (LPair a b) where
  lconsume (x # y) = case lconsume x of () => lconsume y

public export
implementation (LComonoid a, LComonoid b) => LComonoid (LPair a b) where
  lcomult (x # y) = 
    let Builtin.(#) x1 x2 = lcomult x
        Builtin.(#) y1 y2 = lcomult y
    in Builtin.(#) (x1 # y1) (x2 # y2)

public export
implementation (LEq a, LEq b) => LEq (LPair a b) where
  lEq (l1 # r1) (l2 # r2) = 
    let Builtin.(#) resL (Builtin.(#) l1' l2') = lEq l1 l2
        Builtin.(#) resR (Builtin.(#) r1' r2') = lEq r1 r2
        res = if resL then resR else case lconsume resR of () => False
    in Builtin.(#) res (Builtin.(#) (l1' # r1') (l2' # r2'))
public export
data Ur : Type -> Type where
  MkUr : a -> Ur a
