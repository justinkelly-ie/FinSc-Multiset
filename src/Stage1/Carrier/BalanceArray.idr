module Stage1.Carrier.BalanceArray

import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.StructuralFuel
import Stage0.Multiset
import Stage0.OnSeq.FusedStream
import Stage1.Order.Preorder
import Data.Vect
import public Stage1.Basis.Coordinate

%default total

------------------------------------------------------------------------
-- 1. BALANCE ARRAYS & SUBTRACTION-FREE NATURAL LINEAR INDEPENDENCE (CH. 26)
------------------------------------------------------------------------

||| Fuel-bounded total greatest common divisor for natural numbers.
public export
natGcdFuel : Nat -> Nat -> Nat -> Nat
natGcdFuel Z a b = 1
natGcdFuel (S f) a Z = a
natGcdFuel (S f) a (S b) =
  let rem = a `mod` (S b)
  in natGcdFuel f (S b) rem

public export
natGcd : Nat -> Nat -> Nat
natGcd a b = natGcdFuel (gohSteps (gohFuelForCapacity (S (a + b)))) a b

||| A Balance Array represents a subtraction-free linear relation between n vectors (Vexels).
||| Positive side: sum posWeights_i * v_i
||| Negative side: sum negWeights_i * v_i
public export
record BalanceArray (n : Nat) where
  constructor MkBalanceArray
  posWeights : Vect n Nat
  negWeights : Vect n Nat

public export
Eq (BalanceArray n) where
  (MkBalanceArray p1 n1) == (MkBalanceArray p2 n2) = p1 == p2 && n1 == n2

public export
Show (BalanceArray n) where
  show (MkBalanceArray p n) = "BalanceArray(+" ++ show (toList p) ++ ", -" ++ show (toList n) ++ ")"

||| Computes a linear combination of Vexels weighted by natural numbers.
public export
linearComboVexel : {n : Nat} -> Vect n Nat -> Vect n Vexel -> Vexel
linearComboVexel [] [] = emptyCellMultiset
linearComboVexel (c :: cs) (v :: vs) =
  let scaled = scaleCellMultiset (intToBoxInt (cast c)) v
      rest   = linearComboVexel cs vs
  in addCellMultiset scaled rest

||| Evaluates a linear combination of Vexels directly from deforested streams (Rule 04 §8).
public export
linearComboVexelStream : FusedStream Nat -> FusedStream Vexel -> Vexel
linearComboVexelStream strmW strmV =
  foldStream (\acc, (c, v) => addCellMultiset (scaleCellMultiset (intToBoxInt (cast c)) v) acc)
             emptyCellMultiset
             (zipWithStream (\c, v => (c, v)) strmW strmV)

||| Evaluates the positive and negative sides of a BalanceArray over a list of Vexels: (posVex, negVex).
public export
evalVexelBalance : {n : Nat} -> Vect n Vexel -> BalanceArray n -> (Vexel, Vexel)
evalVexelBalance vexels (MkBalanceArray posW negW) =
  (canonicalizeCellMultiset (linearComboVexel posW vexels),
   canonicalizeCellMultiset (linearComboVexel negW vexels))

||| A BalanceArray is balanced when its positive side equals its negative side in canonical multiset form.
public export
isBalanced : {n : Nat} -> Vect n Vexel -> BalanceArray n -> Bool
isBalanced vexels b =
  let (p, n) = evalVexelBalance vexels b
  in p == n

||| A BalanceArray is disjoint when min(pos_i, neg_i) == 0 for all i (no token appears on both sides).
public export
isDisjointBalance : {n : Nat} -> BalanceArray n -> Bool
isDisjointBalance (MkBalanceArray [] []) = True
isDisjointBalance (MkBalanceArray (p :: ps) (n :: ns)) =
  (p == 0 || n == 0) && isDisjointBalance (MkBalanceArray ps ns)

||| A BalanceArray is non-trivial if at least one weight is positive.
public export
isNonTrivialBalance : {n : Nat} -> BalanceArray n -> Bool
isNonTrivialBalance (MkBalanceArray posW negW) =
  (foldl (+) 0 posW > 0) || (foldl (+) 0 negW > 0)

||| For two vexels, computes their exact minimal natural-number balance relation c1*v1 = c2*v2 if proportional.
||| Returns Nothing if the vexels are linearly independent over Nat.
public export
find2VexelBalance : Vexel -> Vexel -> Maybe (BalanceArray 2)
find2VexelBalance v1 v2 =
  let m1 = totalCellMultisetWeight v1
      m2 = totalCellMultisetWeight v2
      zero = intToBoxInt 0
  in if m1 <= zero || m2 <= zero
       then Nothing
       else
         let n1 = boxToNat m1
             n2 = boxToNat m2
             g = natGcd n1 n2
             c1 = if g == 0 then 1 else n2 `div` g
             c2 = if g == 0 then 1 else n1 `div` g
             b = MkBalanceArray [c1, 0] [0, c2]
         in if isBalanced [v1, v2] b
              then Just b
              else Nothing

||| Audits the Balance Array 3-Vexel exact balance: [1, 2] + [3, 1] = [4, 3].
public export
auditVexelBalanceProof : Bool
auditVexelBalanceProof =
  let v1 = singletonCell (mkCell1 1) (intToBoxInt 1) <+> singletonCell (mkCell1 2) (intToBoxInt 2)
      v2 = singletonCell (mkCell1 1) (intToBoxInt 3) <+> singletonCell (mkCell1 2) (intToBoxInt 1)
      v3 = singletonCell (mkCell1 1) (intToBoxInt 4) <+> singletonCell (mkCell1 2) (intToBoxInt 3)
      bal = MkBalanceArray [1, 1, 0] [0, 0, 1]
  in isBalanced [v1, v2, v3] bal && isDisjointBalance bal && isNonTrivialBalance bal

||| Audits 2-Vexel proportionality balance: 3 * [2, 4] = 2 * [3, 6].
public export
auditVexelProportionalityBalanceProof : Bool
auditVexelProportionalityBalanceProof =
  let v1 = singletonCell (mkCell1 1) (intToBoxInt 2) <+> singletonCell (mkCell1 2) (intToBoxInt 4)
      v2 = singletonCell (mkCell1 1) (intToBoxInt 3) <+> singletonCell (mkCell1 2) (intToBoxInt 6)
      expected = MkBalanceArray [3, 0] [0, 2]
  in case find2VexelBalance v1 v2 of
       Just bal => bal == expected && isBalanced [v1, v2] bal
       Nothing  => False

||| Audits that orthogonal basis Singletons [1, 0] and [0, 1] are Nat-linearly independent (no balance relation).
public export
auditVexelLinearIndependenceProof : Bool
auditVexelLinearIndependenceProof =
  let v1 = singletonCell (mkCell1 1) (intToBoxInt 1)
      v2 = singletonCell (mkCell1 2) (intToBoxInt 1)
  in case find2VexelBalance v1 v2 of
       Just _  => False
       Nothing => True

------------------------------------------------------------------------
-- 2. MAGIC MAXELS & DOUBLY STOCHASTIC MATRICES (CH. 27)
------------------------------------------------------------------------

||| A Natural Number Magic Maxel: An n x n matrix of discrete token transition weights.
||| Characterizes doubly stochastic token flow where every row sum and every col sum equals Sigma.
public export
record MagicMaxel (n : Nat) where
  constructor MkMagicMaxel
  grid : Vect n (Vect n Nat)

public export
Eq (MagicMaxel n) where
  (MkMagicMaxel g1) == (MkMagicMaxel g2) = g1 == g2

||| Computes the row sum of row i in a MagicMaxel.
public export
magicRowSum : {n : Nat} -> Fin n -> MagicMaxel n -> Nat
magicRowSum idx (MkMagicMaxel g) = foldl (+) 0 (index idx g)

||| Computes the column sum of col j in a MagicMaxel.
public export
magicColSum : {n : Nat} -> Fin n -> MagicMaxel n -> Nat
magicColSum idx (MkMagicMaxel g) = foldl (+) 0 (map (index idx) g)


||| Validates that an n x n MagicMaxel is doubly stochastic with common line budget Sigma.
public export
isMagicMaxel : {n : Nat} -> MagicMaxel n -> Nat -> Bool
isMagicMaxel {n} (MkMagicMaxel g) sigma =
  let rowSums = map (foldl (+) 0) g
      colSums = foldl (zipWith (+)) (replicate n 0) g
  in all (\r => natEq r sigma) rowSums && all (\c => natEq c sigma) colSums

||| Vector dot product for natural numbers without allocating intermediate lists or vectors.
public export
rowDotNat : {n : Nat} -> Vect n Nat -> Vect n Nat -> Nat
rowDotNat [] [] = 0
rowDotNat (r :: rs) (v :: vs) = (r * v) + rowDotNat rs vs

||| Vector dot product for BoxInt without allocating intermediate lists or vectors.
public export
rowDotBoxInt : {n : Nat} -> Vect n Nat -> Vect n BoxInt -> BoxInt
rowDotBoxInt [] [] = intToBoxInt 0
rowDotBoxInt (r :: rs) (v :: vs) = (intToBoxInt (cast r) * v) + rowDotBoxInt rs vs

||| Applies a MagicMaxel doubly stochastic transition to a vector of token counts:
||| v_out_i = Sum_j M_ij * v_in_j.
public export
applyMagicMaxel : {n : Nat} -> MagicMaxel n -> Vect n Nat -> Vect n Nat
applyMagicMaxel (MkMagicMaxel g) v =
  map (\row => rowDotNat row v) g

||| Applies a MagicMaxel doubly stochastic transition directly to BoxInt lattice states:
public export
applyMagicMaxelBoxInt : {n : Nat} -> MagicMaxel n -> Vect n BoxInt -> Vect n BoxInt
applyMagicMaxelBoxInt (MkMagicMaxel g) v =
  map (\row => rowDotBoxInt row v) g

||| Audits 3x3 Magic Maxel (Lo Shu Square, Sigma=15):
||| Row sums = 15, Col sums = 15, preserves token mass on uniform state.
public export
auditMagicMaxel3x3Proof : Bool
auditMagicMaxel3x3Proof =
  let loShu = MkMagicMaxel [[4, 9, 2], [3, 5, 7], [8, 1, 6]]
      uniformState = [1, 1, 1]
      transformed = applyMagicMaxel loShu uniformState
  in isMagicMaxel loShu 15 && transformed == [15, 15, 15]

||| Audits 3x3 Identity Magic Maxel (Sigma=1, Permutation Decomposition):
||| Preserves arbitrary token state exactly.
public export
auditMagicMaxelIdentityProof : Bool
auditMagicMaxelIdentityProof =
  let id3 = MkMagicMaxel [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
      state = [10, 20, 30]
      transformed = applyMagicMaxel id3 state
  in isMagicMaxel id3 1 && transformed == state
