module Stage0.Interfaces

import public Data.Linear
import Data.Fin
import Data.Fin.Properties
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

------------------------------------------------------------------------
-- Multiplicity Weight & Carrier-Parameterised Multiset Algebra
------------------------------------------------------------------------

||| Algebraic interface required for any multiplicity carrier `c` (`BoxInt`,
||| `SignedBit`, `MultisetBit`) to drive `Box c k` and `HereditaryMSet c`.
public export
interface Ord c => MultisetWeight c where
  zeroWeight : c
  oneWeight  : c
  isZero     : c -> Bool
  addWeight  : c -> c -> c
  negWeight  : c -> c
  mulWeight  : c -> c -> c
  minWeight  : c -> c -> c
  maxWeight  : c -> c -> c
  weightMagnitude : c -> Nat
  weightMagnitude w = if isZero w then 0 else 1

||| Subtraction on any `MultisetWeight c` (`x + (-y)`).
public export
subWeight : MultisetWeight c => c -> c -> c
subWeight x y = addWeight x (negWeight y)

public export
MultisetWeight BoxInt where
  zeroWeight = intToBoxInt 0
  oneWeight  = intToBoxInt 1
  isZero     = boxIsZero
  addWeight  = addBox
  negWeight  = negBox
  mulWeight  = mulBox
  minWeight  = Stage0.BoxInt.minBox
  maxWeight  = Stage0.BoxInt.maxBox
  weightMagnitude (MkBoxInt w) = integerToNat (abs w)

||| Defines how a multiplicity carrier `c` peels off one positive (`Left`)
||| or negative (`Right`) quantum at a time.
public export
interface MultisetWeight c => QuantumCarrier c where
  peelQuantum : c -> Maybe (Either c c)

public export
QuantumCarrier BoxInt where
  peelQuantum (MkBoxInt w) =
    if w > 0 then Just (Left (intToBoxInt (w - 1)))
    else if w < 0 then Just (Right (intToBoxInt (w + 1)))
    else Nothing

||| Carrier-parameterised multiset algebra generalizing `MultisetAlgebra`
||| beyond fixed `BoxInt` weights to any `MultisetWeight c` (`SignedBit`,
||| `MultisetBit`, `BoxInt`). `| a` determines `c` uniquely for overload resolution.
public export
interface MultisetWeight c => WeightedMultisetAlgebra c a | a where
  zeroWM     : a
  addWM      : a -> a -> a
  subWM      : a -> a -> a
  scaleWM    : c -> a -> a
  mulWM      : a -> a -> a
  hadamardWM : a -> a -> a
  minWM      : a -> a -> a
  maxWM      : a -> a -> a
  dotWM      : a -> a -> c
  mulWM = hadamardWM

||| Polymorphic outer product interface shared by Cartesian coordinates (`Box c`)
||| and Kuratowski pairing (`HereditaryMSet c`).
public export
interface MultisetOuter a b out | a, b where
  (><) : a -> b -> out

public export
implementation (Show a, Show b) => Show (LPair a b) where
  show (x # y) = "(" ++ show x ++ " # " ++ show y ++ ")"

public export
joinSumFin : (m, n : Nat) -> Either (Fin m) (Fin n) -> Fin (m + n)
joinSumFin m n (Left i)  = weakenN n i
joinSumFin m n (Right j) = shift m j

public export
splitSumCons : Either (Fin m) (Fin n) -> Either (Fin (S m)) (Fin n)
splitSumCons (Left i)  = Left (FS i)
splitSumCons (Right j) = Right j

public export
splitSumFin : (m, n : Nat) -> Fin (m + n) -> Either (Fin m) (Fin n)
splitSumFin Z     n j      = Right j
splitSumFin (S m) n FZ     = Left FZ
splitSumFin (S m) n (FS k) = splitSumCons (splitSumFin m n k)

public export
0 joinSumSplitCons : (m, n : Nat) -> (sp : Either (Fin m) (Fin n))
                  -> joinSumFin (S m) n (splitSumCons sp) = FS (joinSumFin m n sp)
joinSumSplitCons m n (Left i)  = Refl
joinSumSplitCons m n (Right j) = Refl

public export
0 splitJoinSum : (m, n : Nat) -> (e : Either (Fin m) (Fin n))
              -> splitSumFin m n (joinSumFin m n e) = e
splitJoinSum Z     n (Left i)      = absurd i
splitJoinSum (S m) n (Left FZ)     = Refl
splitJoinSum (S m) n (Left (FS i)) = cong splitSumCons (splitJoinSum m n (Left i))
splitJoinSum Z     n (Right j)     = Refl
splitJoinSum (S m) n (Right j)     = cong splitSumCons (splitJoinSum m n (Right j))

public export
0 joinSplitSum : (m, n : Nat) -> (k : Fin (m + n))
              -> joinSumFin m n (splitSumFin m n k) = k
joinSplitSum Z     n j      = Refl
joinSplitSum (S m) n FZ     = Refl
joinSplitSum (S m) n (FS k) =
  trans (joinSumSplitCons m n (splitSumFin m n k)) (cong FS (joinSplitSum m n k))

public export
pairFinCons : (Fin m, Fin n) -> (Fin (S m), Fin n)
pairFinCons (i, j) = (FS i, j)

public export
pairToFin : (m, n : Nat) -> Fin m -> Fin n -> Fin (m * n)
pairToFin Z     _ i      _ = absurd i
pairToFin (S m) n FZ     j = joinSumFin n (m * n) (Left j)
pairToFin (S m) n (FS i) j = joinSumFin n (m * n) (Right (pairToFin m n i j))

mutual
  public export
  finToPair : (m, n : Nat) -> Fin (m * n) -> (Fin m, Fin n)
  finToPair Z     _ k = absurd k
  finToPair (S m) n k = unpairFinStep m n (splitSumFin n (m * n) k)

  public export
  unpairFinStep : (m, n : Nat) -> Either (Fin n) (Fin (m * n)) -> (Fin (S m), Fin n)
  unpairFinStep m n (Left j)     = (FZ, j)
  unpairFinStep m n (Right rest) = pairFinCons (finToPair m n rest)

public export
0 finPairLeftInv : (m, n : Nat) -> (i : Fin m) -> (j : Fin n)
                -> finToPair m n (pairToFin m n i j) = (i, j)
finPairLeftInv Z     _ i      _ = absurd i
finPairLeftInv (S m) n FZ     j = cong (unpairFinStep m n) (splitJoinSum n (m * n) (Left j))
finPairLeftInv (S m) n (FS i) j =
  trans (cong (unpairFinStep m n) (splitJoinSum n (m * n) (Right (pairToFin m n i j))))
        (cong pairFinCons (finPairLeftInv m n i j))

public export
0 pairFinConsRound : (m, n : Nat) -> (p : (Fin m, Fin n))
                  -> uncurry (pairToFin (S m) n) (pairFinCons p)
                     = joinSumFin n (m * n) (Right (uncurry (pairToFin m n) p))
pairFinConsRound m n (i, j) = Refl

mutual
  public export
  0 unpairFinRound : (m, n : Nat) -> (sp : Either (Fin n) (Fin (m * n)))
                  -> uncurry (pairToFin (S m) n) (unpairFinStep m n sp) = joinSumFin n (m * n) sp
  unpairFinRound m n (Left j)     = Refl
  unpairFinRound m n (Right rest) =
    trans (pairFinConsRound m n (finToPair m n rest))
          (cong (joinSumFin n (m * n) . Right) (finPairRightInv m n rest))

  public export
  0 finPairRightInv : (m, n : Nat) -> (k : Fin (m * n))
                   -> uncurry (pairToFin m n) (finToPair m n k) = k
  finPairRightInv Z     _ k = absurd k
  finPairRightInv (S m) n k =
    trans (unpairFinRound m n (splitSumFin n (m * n) k))
          (joinSplitSum n (m * n) k)

public export
eitherCoordToIndex : FiniteCoord a => FiniteCoord b
                  => Either a b -> Either (Fin (cardinality {k = a})) (Fin (cardinality {k = b}))
eitherCoordToIndex (Left x)  = Left (toIndex x)
eitherCoordToIndex (Right y) = Right (toIndex y)

public export
eitherIndexToCoord : FiniteCoord a => FiniteCoord b
                  => Either (Fin (cardinality {k = a})) (Fin (cardinality {k = b})) -> Either a b
eitherIndexToCoord (Left i)  = Left (fromIndex i)
eitherIndexToCoord (Right j) = Right (fromIndex j)

public export
0 eitherIndexRound : (FiniteCoord a, FiniteCoord b)
                  => (sp : Either (Fin (cardinality {k = a})) (Fin (cardinality {k = b})))
                  -> eitherCoordToIndex {a} {b} (eitherIndexToCoord {a} {b} sp) = sp
eitherIndexRound (Left i)  = cong Left (rightInv i)
eitherIndexRound (Right j) = cong Right (rightInv j)

public export
(FiniteCoord a, FiniteCoord b) => FiniteCoord (Either a b) where
  cardinality = cardinality {k = a} + cardinality {k = b}
  toIndex e = joinSumFin (cardinality {k = a}) (cardinality {k = b}) (eitherCoordToIndex e)
  fromIndex k = eitherIndexToCoord (splitSumFin (cardinality {k = a}) (cardinality {k = b}) k)
  leftInv (Left x) =
    trans (cong eitherIndexToCoord (splitJoinSum (cardinality {k = a}) (cardinality {k = b}) (Left (toIndex x))))
          (cong Left (leftInv x))
  leftInv (Right y) =
    trans (cong eitherIndexToCoord (splitJoinSum (cardinality {k = a}) (cardinality {k = b}) (Right (toIndex y))))
          (cong Right (leftInv y))
  rightInv k =
    trans (cong (joinSumFin (cardinality {k = a}) (cardinality {k = b})) (eitherIndexRound {a} {b} (splitSumFin (cardinality {k = a}) (cardinality {k = b}) k)))
          (joinSplitSum (cardinality {k = a}) (cardinality {k = b}) k)

public export
pairCoordToIndex : FiniteCoord a => FiniteCoord b
                => (a, b) -> (Fin (cardinality {k = a}), Fin (cardinality {k = b}))
pairCoordToIndex (x, y) = (toIndex x, toIndex y)

public export
pairIndexToCoord : FiniteCoord a => FiniteCoord b
                => (Fin (cardinality {k = a}), Fin (cardinality {k = b})) -> (a, b)
pairIndexToCoord (i, j) = (fromIndex i, fromIndex j)

public export
0 pairIndexRound : (FiniteCoord a, FiniteCoord b)
                => (p : (Fin (cardinality {k = a}), Fin (cardinality {k = b})))
                -> pairCoordToIndex {a} {b} (pairIndexToCoord {a} {b} p) = p
pairIndexRound (i, j) = rewrite rightInv {k = a} i in rewrite rightInv {k = b} j in Refl

public export
(FiniteCoord a, FiniteCoord b) => FiniteCoord (a, b) where
  cardinality = cardinality {k = a} * cardinality {k = b}
  toIndex p = uncurry (pairToFin (cardinality {k = a}) (cardinality {k = b})) (pairCoordToIndex p)
  fromIndex k = pairIndexToCoord (finToPair (cardinality {k = a}) (cardinality {k = b}) k)
  leftInv (x, y) =
    rewrite finPairLeftInv (cardinality {k = a}) (cardinality {k = b}) (toIndex x) (toIndex y) in
    rewrite leftInv x in
    rewrite leftInv y in Refl
  rightInv k =
    trans (cong (uncurry (pairToFin (cardinality {k = a}) (cardinality {k = b})))
                (pairIndexRound {a} {b} (finToPair (cardinality {k = a}) (cardinality {k = b}) k)))
          (finPairRightInv (cardinality {k = a}) (cardinality {k = b}) k)

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

-- =========================================================================
-- Canonical Constructive Signed Integer Coordinate (`SignedCoord`)
-- =========================================================================

||| Canonical inductive signed integer coordinate with unique zero (`ZeroZ`).
||| Avoids `-0` ambiguity and non-inductive `Integer` opaque proofs, supporting
||| total constructive `Ord`, `DiscreteCoord`, `MonoidCoord`, and `GroupCoord`.
public export
data SignedCoord : Type where
  ZeroZ : SignedCoord
  PosZ  : Nat -> SignedCoord
  NegZ  : Nat -> SignedCoord

public export
Eq SignedCoord where
  ZeroZ  == ZeroZ  = True
  PosZ a == PosZ b = a == b
  NegZ a == NegZ b = a == b
  _      == _      = False

public export
Ord SignedCoord where
  compare ZeroZ    ZeroZ    = EQ
  compare ZeroZ    (PosZ _) = LT
  compare ZeroZ    (NegZ _) = GT
  compare (PosZ _) ZeroZ    = GT
  compare (PosZ a) (PosZ b) = compare a b
  compare (PosZ _) (NegZ _) = GT
  compare (NegZ _) ZeroZ    = LT
  compare (NegZ _) (PosZ _) = LT
  compare (NegZ a) (NegZ b) = compare b a

public export
Show SignedCoord where
  show ZeroZ    = "0"
  show (PosZ k) = "+" ++ show (S k)
  show (NegZ k) = "-" ++ show (S k)

public export
DiscreteCoord SignedCoord where

public export
DiscreteCoord () where

public export
FiniteCoord () where
  cardinality = 1
  toIndex () = FZ
  fromIndex _ = ()
  leftInv () = Refl
  rightInv FZ = Refl
  rightInv (FS k) = absurd k

public export
MonoidCoord () where
  combine _ _ = ()
  origin = ()
  assoc _ _ _ = Refl

public export
GroupCoord () where
  inverse _ = ()
  invLaw _ = Refl

public export
succZ : SignedCoord -> SignedCoord
succZ ZeroZ        = PosZ Z
succZ (PosZ k)     = PosZ (S k)
succZ (NegZ Z)     = ZeroZ
succZ (NegZ (S k)) = NegZ k

public export
predZ : SignedCoord -> SignedCoord
predZ ZeroZ        = NegZ Z
predZ (PosZ Z)     = ZeroZ
predZ (PosZ (S k)) = PosZ k
predZ (NegZ k)     = NegZ (S k)

0 succPredInv : (z : SignedCoord) -> succZ (predZ z) = z
succPredInv ZeroZ        = Refl
succPredInv (PosZ Z)     = Refl
succPredInv (PosZ (S _)) = Refl
succPredInv (NegZ _)     = Refl

0 predSuccInv : (z : SignedCoord) -> predZ (succZ z) = z
predSuccInv ZeroZ        = Refl
predSuccInv (PosZ _)     = Refl
predSuccInv (NegZ Z)     = Refl
predSuccInv (NegZ (S _)) = Refl

||| Compute `(S a) - (S b)` canonically as a `SignedCoord`.
public export
subS : Nat -> Nat -> SignedCoord
subS Z     Z     = ZeroZ
subS (S a) Z     = PosZ a
subS Z     (S b) = NegZ b
subS (S a) (S b) = subS a b

0 subSDiag : (k : Nat) -> subS k k = ZeroZ
subSDiag Z     = Refl
subSDiag (S k) = subSDiag k

0 subSSuccL : (a, b : Nat) -> subS (S a) b = succZ (subS a b)
subSSuccL Z     Z         = Refl
subSSuccL (S _) Z         = Refl
subSSuccL Z     (S Z)     = Refl
subSSuccL Z     (S (S _)) = Refl
subSSuccL (S a) (S b)     = subSSuccL a b

0 subSSuccR : (a, b : Nat) -> subS a (S b) = predZ (subS a b)
subSSuccR Z     Z         = Refl
subSSuccR Z     (S _)     = Refl
subSSuccR (S Z) Z         = Refl
subSSuccR (S (S _)) Z     = Refl
subSSuccR (S a) (S b)     = subSSuccR a b

public export
addSigned : SignedCoord -> SignedCoord -> SignedCoord
addSigned ZeroZ    y        = y
addSigned x        ZeroZ    = x
addSigned (PosZ a) (PosZ b) = PosZ (S (a + b))
addSigned (NegZ a) (NegZ b) = NegZ (S (a + b))
addSigned (PosZ a) (NegZ b) = subS a b
addSigned (NegZ a) (PosZ b) = subS b a

public export
negSigned : SignedCoord -> SignedCoord
negSigned ZeroZ    = ZeroZ
negSigned (PosZ k) = NegZ k
negSigned (NegZ k) = PosZ k

0 addSignedSuccL : (x, y : SignedCoord) -> addSigned (succZ x) y = succZ (addSigned x y)
addSignedSuccL ZeroZ ZeroZ        = Refl
addSignedSuccL ZeroZ (PosZ _)     = Refl
addSignedSuccL ZeroZ (NegZ Z)     = Refl
addSignedSuccL ZeroZ (NegZ (S _)) = Refl
addSignedSuccL (PosZ _) ZeroZ     = Refl
addSignedSuccL (PosZ _) (PosZ _)  = Refl
addSignedSuccL (PosZ a) (NegZ b)  = subSSuccL a b
addSignedSuccL (NegZ Z) ZeroZ     = Refl
addSignedSuccL (NegZ Z) (PosZ Z)  = Refl
addSignedSuccL (NegZ Z) (PosZ (S _)) = Refl
addSignedSuccL (NegZ Z) (NegZ _)  = Refl
addSignedSuccL (NegZ (S _)) ZeroZ = Refl
addSignedSuccL (NegZ (S a)) (PosZ b) =
  rewrite subSSuccR b a in sym (succPredInv (subS b a))
addSignedSuccL (NegZ (S _)) (NegZ _) = Refl

0 addSignedPredL : (x, y : SignedCoord) -> addSigned (predZ x) y = predZ (addSigned x y)
addSignedPredL x y =
  let h : (addSigned (succZ (predZ x)) y = succZ (addSigned (predZ x) y))
      h = addSignedSuccL (predZ x) y
      h' : (addSigned x y = succZ (addSigned (predZ x) y))
      h' = replace {p = \t => addSigned t y = succZ (addSigned (predZ x) y)} (succPredInv x) h
  in sym (trans (cong predZ h') (predSuccInv (addSigned (predZ x) y)))

0 assocPos : (k : Nat) -> (y, z : SignedCoord)
        -> addSigned (PosZ k) (addSigned y z) = addSigned (addSigned (PosZ k) y) z
assocPos Z y z =
  rewrite addSignedSuccL ZeroZ (addSigned y z) in
  rewrite addSignedSuccL ZeroZ y in
  rewrite addSignedSuccL y z in Refl
assocPos (S k) y z =
  rewrite addSignedSuccL (PosZ k) (addSigned y z) in
  rewrite addSignedSuccL (PosZ k) y in
  rewrite addSignedSuccL (addSigned (PosZ k) y) z in
  cong succZ (assocPos k y z)

0 assocNeg : (k : Nat) -> (y, z : SignedCoord)
        -> addSigned (NegZ k) (addSigned y z) = addSigned (addSigned (NegZ k) y) z
assocNeg Z y z =
  rewrite addSignedPredL ZeroZ (addSigned y z) in
  rewrite addSignedPredL ZeroZ y in
  rewrite addSignedPredL y z in Refl
assocNeg (S k) y z =
  rewrite addSignedPredL (NegZ k) (addSigned y z) in
  rewrite addSignedPredL (NegZ k) y in
  rewrite addSignedPredL (addSigned (NegZ k) y) z in
  cong predZ (assocNeg k y z)

0 addSignedAssoc : (x, y, z : SignedCoord)
              -> addSigned x (addSigned y z) = addSigned (addSigned x y) z
addSignedAssoc ZeroZ    _ _ = Refl
addSignedAssoc (PosZ k) y z = assocPos k y z
addSignedAssoc (NegZ k) y z = assocNeg k y z

0 addSignedInvLaw : (x : SignedCoord) -> addSigned x (negSigned x) = ZeroZ
addSignedInvLaw ZeroZ    = Refl
addSignedInvLaw (PosZ k) = subSDiag k
addSignedInvLaw (NegZ k) = subSDiag k

public export
MonoidCoord SignedCoord where
  combine = addSigned
  origin  = ZeroZ
  assoc   = addSignedAssoc

public export
GroupCoord SignedCoord where
  inverse = negSigned
  invLaw  = addSignedInvLaw

public export
signedToBoxInt : SignedCoord -> BoxInt
signedToBoxInt ZeroZ    = intToBoxInt 0
signedToBoxInt (PosZ k) = intToBoxInt (natToInteger (S k))
signedToBoxInt (NegZ k) = intToBoxInt (negate (natToInteger (S k)))

public export
boxIntToSigned : BoxInt -> SignedCoord
boxIntToSigned (MkBoxInt v) =
  if v == 0 then ZeroZ
  else if v > 0 then PosZ (cast (v - 1))
  else NegZ (cast ((-v) - 1))

-- =========================================================================
-- Modular Cyclic Coordinate Instances on `Fin (S n)`
-- =========================================================================

0 notLTToLTE : (x, y : Nat) -> Not (LT x y) -> LTE y x
notLTToLTE Z     Z     _   = LTEZero
notLTToLTE Z     (S _) neg = void (neg (LTESucc LTEZero))
notLTToLTE (S _) Z     _   = LTEZero
notLTToLTE (S x) (S y) neg = LTESucc (notLTToLTE x y (\lt => neg (LTESucc lt)))

0 ltePlusLeft : (x, y : Nat) -> LTE y (x + y)
ltePlusLeft Z     _ = reflexive
ltePlusLeft (S x) y = lteSuccRight (ltePlusLeft x y)

0 ltePlusRight : (x, y : Nat) -> LTE x (x + y)
ltePlusRight x y = rewrite plusCommutative x y in ltePlusLeft y x

0 sumLtSum : (a, b, m1, m2 : Nat) -> LT a m1 -> LT b m2 -> LT (a + b) (m1 + m2)
sumLtSum Z     b (S m1') m2 _ ltb =
  lteSuccRight (transitive ltb (ltePlusLeft m1' m2))
sumLtSum (S a') b (S m1') m2 (LTESucc lta) ltb =
  LTESucc (sumLtSum a' b m1' m2 lta ltb)

0 minusPlusEq : (a, m : Nat) -> LTE m a -> minus a m + m = a
minusPlusEq a     Z     _             = rewrite minusZeroRight a in rewrite plusZeroRightNeutral a in Refl
minusPlusEq (S a) (S m) (LTESucc prf) =
  rewrite sym (plusSuccRightSucc (minus a m) m) in cong S (minusPlusEq a m prf)

0 lteAddMinusLT : (m1, a, m2 : Nat) -> LTE m1 a -> LT a (m1 + m2) -> LT (minus a m1) m2
lteAddMinusLT Z     a     m2 _             lt           = rewrite minusZeroRight a in lt
lteAddMinusLT (S x) (S y) m2 (LTESucc le)  (LTESucc lt) = lteAddMinusLT x y m2 le lt

0 notSuccLTE : {x : Nat} -> Not (LT x x)
notSuccLTE {x = Z}   lt           = absurd lt
notSuccLTE {x = S _} (LTESucc lt) = notSuccLTE lt

0 plusCancelRight : (a, b, c : Nat) -> a + c = b + c -> a = b
plusCancelRight a b Z     eq = rewrite sym (plusZeroRightNeutral a) in rewrite sym (plusZeroRightNeutral b) in eq
plusCancelRight a b (S c) eq =
  let eq' : (S (a + c) = S (b + c))
      eq' = rewrite plusSuccRightSucc a c in rewrite plusSuccRightSucc b c in eq
  in plusCancelRight a b c (injective eq')

0 remUnique : (m, r1, r2, q1, q2 : Nat)
         -> LT r1 m -> LT r2 m -> r1 + q1 * m = r2 + q2 * m -> r1 = r2
remUnique m r1 r2 Z Z _ _ eq =
  rewrite sym (plusZeroRightNeutral r1) in rewrite sym (plusZeroRightNeutral r2) in eq
remUnique m r1 r2 Z (S q2') lt1 _ eq =
  let eq1 : (r1 = r2 + (m + q2' * m))
      eq1 = rewrite sym (plusZeroRightNeutral r1) in eq
      le1 : LTE m (r2 + (m + q2' * m))
      le1 = transitive (ltePlusRight m (q2' * m)) (ltePlusLeft r2 (m + q2' * m))
      le2 : LTE m r1
      le2 = replace {p = \t => LTE m t} (sym eq1) le1
  in void (notSuccLTE {x = r1} (transitive lt1 le2))
remUnique m r1 r2 (S q1') Z _ lt2 eq =
  let eq1 : (r2 = r1 + (m + q1' * m))
      eq1 = rewrite sym (plusZeroRightNeutral r2) in sym eq
      le1 : LTE m (r1 + (m + q1' * m))
      le1 = transitive (ltePlusRight m (q1' * m)) (ltePlusLeft r1 (m + q1' * m))
      le2 : LTE m r2
      le2 = replace {p = \t => LTE m t} (sym eq1) le1
  in void (notSuccLTE {x = r2} (transitive lt2 le2))
remUnique m r1 r2 (S q1') (S q2') lt1 lt2 eq =
  let eqL : ((r1 + q1' * m) + m = r1 + (m + q1' * m))
      eqL = rewrite plusCommutative m (q1' * m) in sym (plusAssociative r1 (q1' * m) m)
      eqR : ((r2 + q2' * m) + m = r2 + (m + q2' * m))
      eqR = rewrite plusCommutative m (q2' * m) in sym (plusAssociative r2 (q2' * m) m)
      eqC : ((r1 + q1' * m) + m = (r2 + q2' * m) + m)
      eqC = trans eqL (trans eq (sym eqR))
  in remUnique m r1 r2 q1' q2' lt1 lt2 (plusCancelRight (r1 + q1' * m) (r2 + q2' * m) m eqC)

0 finToNatInj : {m : Nat} -> {x, y : Fin m} -> finToNat x = finToNat y -> x = y
finToNatInj {x = FZ}   {y = FZ}   _  = Refl
finToNatInj {x = FZ}   {y = FS _} eq = void (SIsNotZ (sym eq))
finToNatInj {x = FS _} {y = FZ}   eq = void (SIsNotZ eq)
finToNatInj {x = FS _} {y = FS _} eq = cong FS (finToNatInj (injective eq))

public export
0 finToNatNatToFinLT : {m : Nat} -> (k : Nat) -> (0 prf : LT k m)
                    -> finToNat (natToFinLT k @{prf}) = k
finToNatNatToFinLT {m = S _} Z     (LTESucc _)   = Refl
finToNatNatToFinLT {m = S _} (S k) (LTESucc prf) = cong S (finToNatNatToFinLT k prf)

public export
wrapAddMod : (m, a, b : Nat) -> Nat
wrapAddMod m a b = case isLT (a + b) m of
  Yes _ => a + b
  No _  => minus (a + b) m

0 wrapAddModLT : (m, a, b : Nat) -> LT a m -> LT b m -> LT (wrapAddMod m a b) m
wrapAddModLT m a b lta ltb with (isLT (a + b) m)
  _ | Yes lt = lt
  _ | No nlt = lteAddMinusLT m (a + b) m (notLTToLTE (a + b) m nlt) (sumLtSum a b m m lta ltb)

0 wrapAddModSpec : (m, a, b : Nat) -> LT a m -> LT b m
              -> (q : Nat ** wrapAddMod m a b + q * m = a + b)
wrapAddModSpec m a b _ _ with (isLT (a + b) m)
  _ | Yes _  = (Z ** plusZeroRightNeutral (a + b))
  _ | No nlt = (1 **
      let 0 prf = notLTToLTE (a + b) m nlt
      in rewrite plusZeroRightNeutral m in minusPlusEq (a + b) m prf)

0 wrapAddModAssoc : (m, a, b, c : Nat) -> LT a m -> LT b m -> LT c m
               -> wrapAddMod m (wrapAddMod m a b) c = wrapAddMod m a (wrapAddMod m b c)
wrapAddModAssoc m a b c lta ltb ltc =
  let ltab  : LT (wrapAddMod m a b) m
      ltab  = wrapAddModLT m a b lta ltb
      ltbc  : LT (wrapAddMod m b c) m
      ltbc  = wrapAddModLT m b c ltb ltc
      ltlhs : LT (wrapAddMod m (wrapAddMod m a b) c) m
      ltlhs = wrapAddModLT m (wrapAddMod m a b) c ltab ltc
      ltrhs : LT (wrapAddMod m a (wrapAddMod m b c)) m
      ltrhs = wrapAddModLT m a (wrapAddMod m b c) lta ltbc
  in case wrapAddModSpec m a b lta ltb of
       (qab ** eqab) => case wrapAddModSpec m (wrapAddMod m a b) c ltab ltc of
         (ql ** eql) => case wrapAddModSpec m b c ltb ltc of
           (qbc ** eqbc) => case wrapAddModSpec m a (wrapAddMod m b c) lta ltbc of
             (qr ** eqr) =>
               let eqL : (wrapAddMod m (wrapAddMod m a b) c + (ql + qab) * m = (a + b) + c)
                   eqL =
                     rewrite multDistributesOverPlusLeft ql qab m in
                     rewrite plusAssociative (wrapAddMod m (wrapAddMod m a b) c) (ql * m) (qab * m) in
                     rewrite eql in
                     rewrite plusCommutative (wrapAddMod m a b) c in
                     rewrite sym (plusAssociative c (wrapAddMod m a b) (qab * m)) in
                     rewrite eqab in plusCommutative c (a + b)
                   eqR : (wrapAddMod m a (wrapAddMod m b c) + (qr + qbc) * m = (a + b) + c)
                   eqR =
                     rewrite multDistributesOverPlusLeft qr qbc m in
                     rewrite plusAssociative (wrapAddMod m a (wrapAddMod m b c)) (qr * m) (qbc * m) in
                     rewrite eqr in
                     rewrite sym (plusAssociative a (wrapAddMod m b c) (qbc * m)) in
                     rewrite eqbc in plusAssociative a b c
               in remUnique m (wrapAddMod m (wrapAddMod m a b) c) (wrapAddMod m a (wrapAddMod m b c))
                    (ql + qab) (qr + qbc) ltlhs ltrhs (trans eqL (sym eqR))

0 finAddModLT : {n : Nat} -> (x, y : Fin (S n))
           -> LT (wrapAddMod (S n) (finToNat x) (finToNat y)) (S n)
finAddModLT {n} x y =
  wrapAddModLT (S n) (finToNat x) (finToNat y) (elemSmallerThanBound x) (elemSmallerThanBound y)

public export
natToFinClamped : Nat -> (n : Nat) -> Fin (S n)
natToFinClamped Z     _     = FZ
natToFinClamped (S k) Z     = FZ
natToFinClamped (S k) (S m) = FS (natToFinClamped k m)

0 finToNatClampedEq : (k, n : Nat) -> (0 prf : LT k (S n))
                   -> finToNat (natToFinClamped k n) = k
finToNatClampedEq Z     _     _            = Refl
finToNatClampedEq (S _) Z     (LTESucc lt) = absurd lt
finToNatClampedEq (S k) (S m) (LTESucc lt) = cong S (finToNatClampedEq k m lt)

public export
finAddMod : {n : Nat} -> Fin (S n) -> Fin (S n) -> Fin (S n)
finAddMod {n} x y =
  natToFinClamped (wrapAddMod (S n) (finToNat x) (finToNat y)) n

0 finToNatFinAddMod : {n : Nat} -> (x, y : Fin (S n))
                   -> finToNat (finAddMod x y) = wrapAddMod (S n) (finToNat x) (finToNat y)
finToNatFinAddMod {n} x y =
  finToNatClampedEq (wrapAddMod (S n) (finToNat x) (finToNat y)) n (finAddModLT x y)

public export
finNegMod : {n : Nat} -> Fin (S n) -> Fin (S n)
finNegMod {n = _}   FZ     = FZ
finNegMod {n = S _} (FS k) = FS (complement k)

0 finAddModAssoc : {n : Nat} -> (x, y, z : Fin (S n))
              -> finAddMod x (finAddMod y z) = finAddMod (finAddMod x y) z
finAddModAssoc {n} x y z =
  let ltx : LT (finToNat x) (S n)
      ltx = elemSmallerThanBound x
      lty : LT (finToNat y) (S n)
      lty = elemSmallerThanBound y
      ltz : LT (finToNat z) (S n)
      ltz = elemSmallerThanBound z
      eq1 : (wrapAddMod (S n) (finToNat x) (finToNat (finAddMod y z))
           = wrapAddMod (S n) (finToNat x) (wrapAddMod (S n) (finToNat y) (finToNat z)))
      eq1 = cong (wrapAddMod (S n) (finToNat x)) (finToNatFinAddMod y z)
      eq2 : (wrapAddMod (S n) (finToNat (finAddMod x y)) (finToNat z)
           = wrapAddMod (S n) (wrapAddMod (S n) (finToNat x) (finToNat y)) (finToNat z))
      eq2 = cong (\t => wrapAddMod (S n) t (finToNat z)) (finToNatFinAddMod x y)
      core : (wrapAddMod (S n) (finToNat x) (wrapAddMod (S n) (finToNat y) (finToNat z))
            = wrapAddMod (S n) (wrapAddMod (S n) (finToNat x) (finToNat y)) (finToNat z))
      core = sym (wrapAddModAssoc (S n) (finToNat x) (finToNat y) (finToNat z) ltx lty ltz)
      natEq : (wrapAddMod (S n) (finToNat x) (finToNat (finAddMod y z))
             = wrapAddMod (S n) (finToNat (finAddMod x y)) (finToNat z))
      natEq = trans eq1 (trans core (sym eq2))
  in finToNatInj (trans (finToNatFinAddMod x (finAddMod y z))
                        (trans natEq (sym (finToNatFinAddMod (finAddMod x y) z))))

0 finAddModInvLaw : {n : Nat} -> (x : Fin (S n)) -> finAddMod x (finNegMod x) = FZ
finAddModInvLaw {n} FZ =
  case wrapAddModSpec (S n) Z Z (LTESucc LTEZero) (LTESucc LTEZero) of
    (q ** eqq) =>
      let wrapZero : (wrapAddMod (S n) Z Z = Z)
          wrapZero = remUnique (S n) _ Z q Z (finAddModLT {n} FZ FZ) (LTESucc LTEZero) eqq
      in finToNatInj (trans (finToNatFinAddMod {n} FZ FZ) wrapZero)
finAddModInvLaw {n = S m} (FS k) =
  let ltx : LT (finToNat (FS k)) (S (S m))
      ltx = elemSmallerThanBound (FS k)
      lty : LT (finToNat (FS (complement k))) (S (S m))
      lty = elemSmallerThanBound (FS (complement k))
      comp : (S (finToNat k) + finToNat (complement k) = S m)
      comp = complementSpec k
      sumIsMod : (S (finToNat k) + S (finToNat (complement k)) = S (S m))
      sumIsMod =
        rewrite sym (plusSuccRightSucc (S (finToNat k)) (finToNat (complement k))) in
        cong S comp
  in case wrapAddModSpec (S (S m)) (S (finToNat k)) (S (finToNat (complement k))) ltx lty of
       (q ** eqq) =>
         let eqMod : (wrapAddMod (S (S m)) (S (finToNat k)) (S (finToNat (complement k))) + q * S (S m) = Z + 1 * S (S m))
             eqMod = rewrite plusZeroRightNeutral (S (S m)) in trans eqq sumIsMod
             wrapZero : (wrapAddMod (S (S m)) (S (finToNat k)) (S (finToNat (complement k))) = Z)
             wrapZero = remUnique (S (S m)) _ Z q 1 (finAddModLT {n = S m} (FS k) (FS (complement k))) (LTESucc LTEZero) eqMod
         in finToNatInj (trans (finToNatFinAddMod {n = S m} (FS k) (FS (complement k))) wrapZero)

public export
{n : Nat} -> MonoidCoord (Fin (S n)) where
  combine = finAddMod
  origin  = FZ
  assoc   = finAddModAssoc

public export
{n : Nat} -> GroupCoord (Fin (S n)) where
  inverse = finNegMod
  invLaw  = finAddModInvLaw
