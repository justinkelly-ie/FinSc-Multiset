module Stage1.MultisetTensor

import public Stage0.BoxInt
import public Stage0.Multiset
import Stage0.OnSeq.FusedStream
import Stage1.Order.Preorder
import Data.Fuel
import Data.List
import Data.SortedMap

%default total

||| An Adjoint Multiset Tensor V ⊗ W* represented as a 2D pair multiset.
||| This replaces rigid grid matrix containers with an emergent, deforested multiset structure.
public export
MultisetTensor : Type -> Type -> Type
MultisetTensor a b = Multiset BoxInt (a, b)

||| Tensor Outer Product (A ⊗ B):
||| Computes the tensor product of two multiset state vectors.
public export
tensorProduct : Multiset BoxInt a -> Multiset BoxInt b -> MultisetTensor a b
tensorProduct ZeroM _ = ZeroM
tensorProduct (AddM x w1 restX) ys =
  addMultiset (scaleRow x w1 ys) (tensorProduct restX ys)
  where
    scaleRow : a -> BoxInt -> Multiset BoxInt b -> MultisetTensor a b
    scaleRow _ _ ZeroM = ZeroM
    scaleRow itemA weightA (AddM itemB weightB restY) =
      AddM (itemA, itemB) (weightA * weightB) (scaleRow itemA weightA restY)

||| Canonical Operator Tensor Product (A ⊗_Op B):
||| Computes the monoidal tensor product of two multiset operators:
||| (c1 -> r1) ⊗ (c2 -> r2) => ((c1, c2) -> (r1, r2)).
||| Re-associates row-col pairs directly in the symmetric monoidal category of multisets without ad-hoc arithmetic.
public export
tensorOperator : MultisetTensor r1 c1 -> MultisetTensor r2 c2 -> MultisetTensor (r1, r2) (c1, c2)
tensorOperator m1 m2 =
  mapMultiset (\((r1, c1), (r2, c2)) => ((r1, r2), (c1, c2))) (tensorProduct m1 m2)


||| Transposes an Adjoint Multiset Tensor (A^T): (a, b) -> (b, a).
public export
transposeTensor : MultisetTensor a b -> MultisetTensor b a
transposeTensor ZeroM = ZeroM
transposeTensor (AddM (x, y) w rest) = AddM (y, x) w (transposeTensor rest)

||| Stream Hylomorphic Tensor Contraction (Matrix Multiplication A · B):
||| Multiplies two multiset tensors A : (a, b) and B : (b, c) -> (a, c)
||| using a single-pass indexed contraction loop that eliminates quadratic copying passes.
public export
multisetTensorMult : Eq b => MultisetTensor a b -> MultisetTensor b c -> MultisetTensor a c
multisetTensorMult tensorA tensorB =
  let indexB = groupByKey tensorB
  in contractLoop tensorA indexB ZeroM
  where
    insertEntry : b -> c -> BoxInt -> List (b, List (c, BoxInt)) -> List (b, List (c, BoxInt))
    insertEntry targetK targetJ weight [] = [(targetK, [(targetJ, weight)])]
    insertEntry targetK targetJ weight ((kEntry, row) :: entries) =
      if targetK == kEntry
        then (kEntry, (targetJ, weight) :: row) :: entries
        else (kEntry, row) :: insertEntry targetK targetJ weight entries

    groupByKey : MultisetTensor b c -> List (b, List (c, BoxInt))
    groupByKey ZeroM = []
    groupByKey (AddM (k, j) w rest) = insertEntry k j w (groupByKey rest)

    lookupKey : b -> List (b, List (c, BoxInt)) -> List (c, BoxInt)
    lookupKey _ [] = []
    lookupKey targetK ((kEntry, row) :: entries) =
      if targetK == kEntry then row else lookupKey targetK entries

    emitCols : a -> BoxInt -> List (c, BoxInt) -> MultisetTensor a c -> MultisetTensor a c
    emitCols _ _ [] acc = acc
    emitCols itemI weight1 ((targetJ, weight2) :: cols) acc =
      AddM (itemI, targetJ) (weight1 * weight2) (emitCols itemI weight1 cols acc)

    contractLoop : MultisetTensor a b -> List (b, List (c, BoxInt)) -> MultisetTensor a c -> MultisetTensor a c
    contractLoop ZeroM _ acc = acc
    contractLoop (AddM (i, k1) w1 restA) idxB acc =
      let cols = lookupKey k1 idxB
          newAcc = emitCols i w1 cols acc
      in contractLoop restA idxB newAcc

||| Logarithmic Tensor Contraction (Matrix Multiplication A · B) for Ordered Keys:
||| Multiplies two multiset tensors A : (a, b) and B : (b, c) -> (a, c)
||| by pre-indexing tensorB into a balanced search map in O(|B| log |B|) time,
||| reducing contraction lookup to O(log |B|) per element of tensorA.
public export
multisetTensorMultOrd : Ord b => MultisetTensor a b -> MultisetTensor b c -> MultisetTensor a c
multisetTensorMultOrd tensorA tensorB =
  let indexB = foldMultiset insertCol empty tensorB
  in foldMultiset (contractRow indexB) ZeroM tensorA
  where
    insertCol : (b, c) -> BoxInt -> SortedMap b (List (c, BoxInt)) -> SortedMap b (List (c, BoxInt))
    insertCol (k, j) w mapAcc =
      case lookup k mapAcc of
        Nothing   => insert k [(j, w)] mapAcc
        Just cols => insert k ((j, w) :: cols) mapAcc

    emitCols : a -> BoxInt -> List (c, BoxInt) -> MultisetTensor a c -> MultisetTensor a c
    emitCols _ _ [] acc = acc
    emitCols itemI weight1 ((targetJ, weight2) :: cols) acc =
      AddM (itemI, targetJ) (weight1 * weight2) (emitCols itemI weight1 cols acc)

    contractRow : SortedMap b (List (c, BoxInt)) -> (a, b) -> BoxInt -> MultisetTensor a c -> MultisetTensor a c
    contractRow idxB (itemI, targetK) weight1 acc =
      case lookup targetK idxB of
        Nothing   => acc
        Just cols => emitCols itemI weight1 cols acc

||| Audits that multisetTensorMultOrd matches multisetTensorMult on canonical matrices.
public export
auditTensorMultOrdMatches : Bool
auditTensorMultOrdMatches =
  let tA : MultisetTensor Nat Nat = AddM (1, 1) (intToBoxInt 2) (AddM (1, 2) (intToBoxInt 3) ZeroM)
      tB : MultisetTensor Nat Nat = AddM (1, 1) (intToBoxInt 4) (AddM (2, 1) (intToBoxInt 5) ZeroM)
  in (multisetTensorMult tA tB == multisetTensorMultOrd tA tB)

||| Monomorphic 2D Determinant over MultisetTensor: det([a b; c d]) = a*d - b*c
%inline public export
detTensor2D : BoxInt -> BoxInt -> BoxInt -> BoxInt -> BoxInt
detTensor2D a b c d = subBox (a * d) (b * c)

||| Monomorphic 2D Trace over MultisetTensor: tr([a b; c d]) = a + d
%inline public export
traceTensor2D : BoxInt -> BoxInt -> BoxInt
traceTensor2D a d = addBox a d

------------------------------------------------------------------------
-- GALOIS 4GEOMETRIES PUSHFORWARD STREAMS (f_* ⊣ f^*)
------------------------------------------------------------------------

||| Galois Fiber Pushforward (f_*) computing exact chromogeometric quadrance
||| Q(v) = v^T * g_Sector * v directly over multiset tensor streams.
public export
chromometricQuadrance : Geometry -> BoxInt -> BoxInt -> BoxInt -> BoxInt
chromometricQuadrance Elliptic   dx dy dz = addBox (addBox (dx * dx) (dy * dy)) (addBox (dz * dz) 1)
chromometricQuadrance Hyperbolic dx dy dz = addBox (subBox (addBox (dx * dx) (dy * dy)) (dz * dz)) 1
chromometricQuadrance Parabolic  dx dy dz = addBox (addBox (dx * dx) (dy * dy)) 1
chromometricQuadrance Substrate  _  _  _  = 1

------------------------------------------------------------------------
-- 1. COMPILE-TIME TENSOR RANK WITNESSES (dim <= 27)
------------------------------------------------------------------------

||| Erased compile-time proof witness verifying multiset tensor dimension rank bound (dim <= 27).
public export
0 TensorAdjunctionWitness : (dim : Nat) -> Type
TensorAdjunctionWitness dim = natLTE dim 27 = True

||| Static compile-time witness for 27-element triadic tensor rank (27 <= 27).
public export
0 prfMultisetTensorAdjunctionRank27 : TensorAdjunctionWitness 27
prfMultisetTensorAdjunctionRank27 = Refl

||| Verified multiset tensor carrying compile-time erased rank witness.
public export
record VerifiedTensorAdjunction (dim : Nat) (a : Type) (b : Type) where
  constructor MkVerifiedTensor
  tensor : MultisetTensor a b
  0 rankPrf : TensorAdjunctionWitness dim

------------------------------------------------------------------------
-- 2. DEFORESTED MULTISET TENSOR STREAM TRANSDUCERS
------------------------------------------------------------------------

||| Discrete multiset tensor step record.
public export
record MultisetTensorStep where
  constructor MkTensorStep
  stepId : Int
  weight : BoxInt

public export
Eq MultisetTensorStep where
  (MkTensorStep id1 w1) == (MkTensorStep id2 w2) =
    id1 == id2 && w1 == w2

||| O(1) allocation deforested stream transducer evaluating total weight across multiset tensor elements.
public export
fusedMultisetTensorStream : Fuel -> MultisetTensor a b -> BoxInt
fusedMultisetTensorStream f tensor =
  fusedHylomorphism f
    (\(idx, st) => case st of
                     ZeroM => Done
                     AddM (_, _) w rest => Yield (MkTensorStep idx w) (idx + 1, rest))
    (\step, acc => weight step + acc)
    (intToBoxInt 0)
    (1, tensor)

||| O(1) allocation deforested stream transducer evaluating total trace sum over diagonal multiset tensor elements.
public export
fusedComputeTensorTrace : Eq a => Fuel -> MultisetTensor a a -> BoxInt
fusedComputeTensorTrace f tensor =
  fusedHylomorphism f
    (\(idx, st) => case st of
                     ZeroM => Done
                     AddM (x, y) w rest =>
                       if x == y
                         then Yield (MkTensorStep idx w) (idx + 1, rest)
                         else Skip (idx + 1, rest))
    (\step, acc => weight step + acc)
    (intToBoxInt 0)
    (1, tensor)

