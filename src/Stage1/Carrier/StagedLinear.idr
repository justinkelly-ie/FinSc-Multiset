module Stage1.Carrier.StagedLinear

import Data.Fin
import Data.Nat
import Data.Vect
import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.StructuralFuel
import Language.Reflection
import Stage1.TypeTheory.Staging
import Stage1.MultisetTree
import Stage1.Basis.CoordCell
import Stage1.Carrier.CellMultiset

%default total

------------------------------------------------------------------------
-- 1. DIMENSION-INDEXED TYPED VECTORS & MATRICES (VexelN & MaxelN)
------------------------------------------------------------------------

||| A VexelN is a dimension-indexed discrete vector of dimension `n`,
||| holding `n` BoxInt scalar weights for unrolled 2LTT staging.
public export
record VexelN (n : Nat) where
  constructor MkVexelN
  components : Vect n BoxInt

||| Self-documenting type synonym for dense vector.
public export
DenseVexel : (n : Nat) -> Type
DenseVexel = VexelN

public export
Eq (VexelN n) where
  (MkVexelN v1) == (MkVexelN v2) = v1 == v2

public export
{n : Nat} -> Show (VexelN n) where
  show (MkVexelN v) = "Vexel" ++ show n ++ "(" ++ show v ++ ")"

||| Constructor for 2-dimensional VexelN (single qubit state vector).
public export
mkVexel2 : BoxInt -> BoxInt -> VexelN 2
mkVexel2 v0 v1 = MkVexelN [v0, v1]

||| Constructor for 4-dimensional VexelN (two-qubit state vector).
public export
mkVexel4 : BoxInt -> BoxInt -> BoxInt -> BoxInt -> VexelN 4
mkVexel4 v0 v1 v2 v3 = MkVexelN [v0, v1, v2, v3]

||| A MaxelN is a dimension-indexed square discrete matrix of dimension `n` x `n`,
||| holding an n-vector of n-vector BoxInt weights for unrolled 2LTT staging.
public export
record MaxelN (n : Nat) where
  constructor MkMaxelN
  rows : Vect n (Vect n BoxInt)

||| Self-documenting type synonym for dense square matrix.
public export
DenseMaxel : (n : Nat) -> Type
DenseMaxel = MaxelN

public export
Eq (MaxelN n) where
  (MkMaxelN m1) == (MkMaxelN m2) = m1 == m2

public export
{n : Nat} -> Show (MaxelN n) where
  show (MkMaxelN m) = "Maxel" ++ show n ++ "x" ++ show n ++ "(" ++ show m ++ ")"

||| Constructor for 2x2 MaxelN (single qubit unitary gate).
public export
mkMaxel2 : BoxInt -> BoxInt -> BoxInt -> BoxInt -> MaxelN 2
mkMaxel2 m00 m01 m10 m11 = MkMaxelN [[m00, m01], [m10, m11]]

||| Constructor for 4x4 MaxelN (two-qubit unitary gate).
public export
mkMaxel4 : Vect 4 (Vect 4 BoxInt) -> MaxelN 4
mkMaxel4 rs = MkMaxelN rs

||| 2LTT Staged MaxelN-VexelN Contraction:
public export
stagedMaxelNVec : {n : Nat} -> Lift (MaxelN n) -> VexelN n -> Code (VexelN n)
stagedMaxelNVec qm (MkVexelN v) = quote (MkVexelN (stagedUnrollMatVec (rows (splice qm)) v))

||| 2LTT Staged MaxelN Matrix Multiplication:
public export
stagedMaxelNMul : {n : Nat} -> Lift (MaxelN n) -> Lift (MaxelN n) -> Code (MaxelN n)
stagedMaxelNMul qm1 qm2 = quote (MkMaxelN (stagedUnrollMatMul (rows (splice qm1)) (rows (splice qm2))))

||| 2LTT Staged MaxelN Identity Matrix of dimension n:
public export
stagedIdentityMaxelN : (n : Nat) -> MaxelN n
stagedIdentityMaxelN n = MkMaxelN (stagedIdentityMat n)

||| 2LTT Staged MaxelN Power in O(log exp) repeated squarings:
public export
stagedMaxelNPower : (fuel : Nat) -> {n : Nat} -> Lift (MaxelN n) -> Nat -> Code (MaxelN n)
stagedMaxelNPower fuel qm exp = quote (MkMaxelN (stagedFastMatPower fuel (rows (splice qm)) exp))

------------------------------------------------------------------------
-- 2. DENSE-SPARSE CONVERSION BRIDGES
------------------------------------------------------------------------

vectToVexelHelper : Nat -> Vect k BoxInt -> Vexel -> Vexel
vectToVexelHelper _ [] acc = acc
vectToVexelHelper idx (w :: ws) acc =
  if boxIsZero w
    then vectToVexelHelper (S idx) ws acc
    else vectToVexelHelper (S idx) ws (setBoxTree (mkCell1 idx) w acc)

||| Converts a dimension-indexed VexelN into a canonical sparse multiset Vexel (1-indexed).
public export
vexelNToVexel : {n : Nat} -> VexelN n -> Vexel
vexelNToVexel (MkVexelN comps) = vectToVexelHelper 1 comps BoxLeaf

||| Converts a dimension-indexed VexelN into a 0-indexed sparse multiset Vexel (quantum basis).
public export
vexelNToVexel0 : {n : Nat} -> VexelN n -> Vexel
vexelNToVexel0 (MkVexelN comps) = vectToVexelHelper 0 comps BoxLeaf

||| Converts a sparse multiset Vexel into a dimension-indexed VexelN (0-indexed).
public export
vexelToVexelN : (n : Nat) -> Vexel -> VexelN n
vexelToVexelN n v =
  MkVexelN (generateComponents 0 n)
  where
    generateComponents : Nat -> (k : Nat) -> Vect k BoxInt
    generateComponents _ Z = []
    generateComponents idx (S rem) =
      let w = lookupBoxTree (mkCell1 idx) v
      in w :: generateComponents (S idx) rem

||| Converts a sparse multiset Vexel into a dimension-indexed VexelN (1-indexed).
public export
vexelToVexelN1 : (n : Nat) -> Vexel -> VexelN n
vexelToVexelN1 n v =
  MkVexelN (generateComponents 1 n)
  where
    generateComponents : Nat -> (k : Nat) -> Vect k BoxInt
    generateComponents _ Z = []
    generateComponents idx (S rem) =
      let w = lookupBoxTree (mkCell1 idx) v
      in w :: generateComponents (S idx) rem

vectToMaxelRowHelper : Nat -> Nat -> Vect k BoxInt -> Maxel -> Maxel
vectToMaxelRowHelper _ _ [] acc = acc
vectToMaxelRowHelper r c (w :: ws) acc =
  if boxIsZero w
    then vectToMaxelRowHelper r (S c) ws acc
    else vectToMaxelRowHelper r (S c) ws (setCellMultiset (mkPixel r c) w acc)

matToMaxelHelper : Nat -> Nat -> Vect k (Vect n BoxInt) -> Maxel -> Maxel
matToMaxelHelper _ _ [] acc = acc
matToMaxelHelper r c0 (row :: rows) acc =
  let acc' = vectToMaxelRowHelper r c0 row acc
  in matToMaxelHelper (S r) c0 rows acc'

||| Converts a dimension-indexed MaxelN into a canonical sparse multiset Maxel (1-indexed).
public export
maxelNToMaxel : {n : Nat} -> MaxelN n -> Maxel
maxelNToMaxel (MkMaxelN rs) = matToMaxelHelper 1 1 rs BoxLeaf

||| Converts a dimension-indexed MaxelN into a 0-indexed sparse multiset Maxel (quantum basis).
public export
maxelNToMaxel0 : {n : Nat} -> MaxelN n -> Maxel
maxelNToMaxel0 (MkMaxelN rs) = matToMaxelHelper 0 0 rs BoxLeaf
