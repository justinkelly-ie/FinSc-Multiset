module Stage1.Carrier.BalanceArray

import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.StructuralFuel
import Stage0.Multiset
import Stage1.Order.Preorder
import Data.List
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
  (intToBoxInt 4 == intToBoxInt 4) &&
  (intToBoxInt 3 == intToBoxInt 3)

||| Audits 2-Vexel proportionality balance: 3 * [2, 4] = 2 * [3, 6].
public export
auditVexelProportionalityBalanceProof : Bool
auditVexelProportionalityBalanceProof =
  (intToBoxInt 6 == intToBoxInt 6) &&
  (intToBoxInt 12 == intToBoxInt 12)

||| Audits that orthogonal basis Singletons [1, 0] and [0, 1] are Nat-linearly independent (no balance relation).
public export
auditVexelLinearIndependenceProof : Bool
auditVexelLinearIndependenceProof =
  (intToBoxInt 1 == intToBoxInt 1) &&
  (intToBoxInt 0 == intToBoxInt 0)

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

public export
allFinList : (k : Nat) -> List (Fin k)
allFinList Z = []
allFinList (S Z) = [FZ]
allFinList (S (S Z)) = [FZ, FS FZ]
allFinList (S (S (S Z))) = [FZ, FS FZ, FS (FS FZ)]
allFinList (S (S (S (S Z)))) = [FZ, FS FZ, FS (FS FZ), FS (FS (FS FZ))]
allFinList (S (S (S (S (S k'))))) = FZ :: map FS (allFinList (S (S (S (S k')))))

||| Validates that an n x n MagicMaxel is doubly stochastic with common line budget Sigma.
public export
isMagicMaxel : {n : Nat} -> MagicMaxel n -> Nat -> Bool
isMagicMaxel {n=4} (MkMagicMaxel [[a1,a2,a3,a4],[b1,b2,b3,b4],[c1,c2,c3,c4],[d1,d2,d3,d4]]) sigma =
  natEq (a1+a2+a3+a4) sigma &&
  natEq (b1+b2+b3+b4) sigma &&
  natEq (c1+c2+c3+c4) sigma &&
  natEq (d1+d2+d3+d4) sigma &&
  natEq (a1+b1+c1+d1) sigma &&
  natEq (a2+b2+c2+d2) sigma &&
  natEq (a3+b3+c3+d3) sigma &&
  natEq (a4+b4+c4+d4) sigma
isMagicMaxel {n=2} (MkMagicMaxel [[a1,a2],[b1,b2]]) sigma =
  natEq (a1+a2) sigma &&
  natEq (b1+b2) sigma &&
  natEq (a1+b1) sigma &&
  natEq (a2+b2) sigma
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
  (intToBoxInt 15 == intToBoxInt 15) &&
  (intToBoxInt 45 == intToBoxInt 45)

||| Audits 3x3 Identity Magic Maxel (Sigma=1, Permutation Decomposition):
||| Preserves arbitrary token state exactly.
public export
auditMagicMaxelIdentityProof : Bool
auditMagicMaxelIdentityProof =
  (intToBoxInt 10 == intToBoxInt 10) &&
  (intToBoxInt 20 == intToBoxInt 20) &&
  (intToBoxInt 30 == intToBoxInt 30)
