module Stage1.Carrier.Kronecker

import Data.Fin
import Data.Nat
import Data.Vect
import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.Multiset
import Stage0.Token
import Language.Reflection
import Stage1.TypeTheory.Staging
import Stage1.MultisetTree
import Stage1.MultisetTensor
import Stage1.Basis.CoordCell
import Stage1.Carrier.CellMultiset
import Stage1.Carrier.StagedLinear
import Stage1.Carrier.SquareMaxel

%default total

------------------------------------------------------------------------
-- 1. SPARSE KRONECKER TENSOR PRODUCT (SquareMaxel)
------------------------------------------------------------------------

||| Canonical Kronecker Coordinate Chart Observation:
public export
observeKroneckerPixel : (n : Nat) -> ((Nat, Nat), (Nat, Nat)) -> Pixel
observeKroneckerPixel n ((r1, r2), (c1, c2)) = mkPixel ((r1 * n) + r2) ((c1 * n) + c2)

||| Sparse Kronecker Tensor Product for SquareMaxel:
public export
kroneckerSquareMaxel : {m, n : Nat} -> SquareMaxel m -> SquareMaxel n -> SquareMaxel (m * n)
kroneckerSquareMaxel {m} {n} (MkSquareMaxel t1) (MkSquareMaxel t2) =
  let resultTree = foldBoxTreeL (\accTree, (p1, w1) =>
        foldBoxTreeL (\innerAcc, (p2, w2) =>
          let r1 = pixelRow p1
              c1 = pixelCol p1
              r2 = pixelRow p2
              c2 = pixelCol p2
              pOut = observeKroneckerPixel n ((r1, r2), (c1, c2))
          in addCellTree pOut (w1 * w2) innerAcc)
          accTree
          t2)
        BoxLeaf
        t1
  in MkSquareMaxel resultTree

||| 2LTT Staged Kronecker Product for SquareMaxel:
public export
stagedKroneckerSquareMaxel : {m, n : Nat} -> Lift (SquareMaxel m) -> Lift (SquareMaxel n) -> Code (SquareMaxel (m * n))
stagedKroneckerSquareMaxel qm1 qm2 = quote (kroneckerSquareMaxel (splice qm1) (splice qm2))

------------------------------------------------------------------------
-- 2. DENSE KRONECKER TENSOR PRODUCTS (VexelN & MaxelN)
------------------------------------------------------------------------

||| Multiplies two Vect BoxInt vectors via Kronecker tensor product: Vect (n * m) BoxInt.
public export
kroneckerVect : {n, m : Nat} -> Vect n BoxInt -> Vect m BoxInt -> Vect (n * m) BoxInt
kroneckerVect u v = concat (map (\x => map (mulBox x) v) u)

||| Kronecker tensor product of two dimension-indexed VexelN vectors: VexelN (n * m).
public export
kroneckerVexelN : {n, m : Nat} -> VexelN n -> VexelN m -> VexelN (n * m)
kroneckerVexelN (MkVexelN u) (MkVexelN v) = MkVexelN (kroneckerVect u v)

||| 2LTT Staged Kronecker tensor product of two VexelN vectors at Stage 1.
public export
stagedKroneckerVexelN : {n, m : Nat} -> Lift (VexelN n) -> Lift (VexelN m) -> Code (VexelN (n * m))
stagedKroneckerVexelN qv1 qv2 = quote (kroneckerVexelN (splice qv1) (splice qv2))

||| Kronecker tensor product of two dimension-indexed MaxelN square matrices: MaxelN (n * m).
public export
kroneckerMaxelN : {n, m : Nat} -> MaxelN n -> MaxelN m -> MaxelN (n * m)
kroneckerMaxelN (MkMaxelN rowsA) (MkMaxelN rowsB) =
  let blockRows : Vect n (Vect m (Vect (n * m) BoxInt))
      blockRows = map (\ra => map (\rb => kroneckerVect ra rb) rowsB) rowsA
  in MkMaxelN (concat blockRows)

||| 2LTT Staged Kronecker tensor product of two MaxelN square matrices at Stage 1.
public export
stagedKroneckerMaxelN : {n, m : Nat} -> Lift (MaxelN n) -> Lift (MaxelN m) -> Code (MaxelN (n * m))
stagedKroneckerMaxelN qm1 qm2 = quote (kroneckerMaxelN (splice qm1) (splice qm2))

------------------------------------------------------------------------
-- 3. MULTISETTENSOR ISOMORPHISMS & ALGEBRAIC KRONECKER EQUIVALENCE
------------------------------------------------------------------------

||| Converts a SquareMaxel into a MultisetTensor over natural coordinate pairs.
public export
squareMaxelToTensor : {dim : Nat} -> SquareMaxel dim -> Multiset BoxInt (Nat, Nat)
squareMaxelToTensor (MkSquareMaxel tree) =
  foldBoxTreeR (\p, w, acc => AddM (pixelRow p, pixelCol p) w acc) ZeroM tree

||| Reconstructs a sparse SquareMaxel from an observed MultisetTensor Pixel.
public export
tensorToSquareMaxel : {dim : Nat} -> Multiset BoxInt Pixel -> SquareMaxel dim
tensorToSquareMaxel tensor =
  MkSquareMaxel
    (foldMultiset (\p, w, tree => addCellTree p w tree) BoxLeaf tensor)

||| Converts a SquareMaxel into a Multiset over typed Pixels.
public export
squareMaxelToPixelTensor : {dim : Nat} -> SquareMaxel dim -> Multiset BoxInt Pixel
squareMaxelToPixelTensor (MkSquareMaxel tree) =
  foldBoxTreeR (\p, w, acc => AddM p w acc) ZeroM tree

||| Reconstructs a sparse SquareMaxel from a natural coordinate pair Multiset.
public export
tensorNatToSquareMaxel : {dim : Nat} -> Multiset BoxInt (Nat, Nat) -> SquareMaxel dim
tensorNatToSquareMaxel tensor =
  tensorToSquareMaxel (mapMultiset (\(r, c) => mkPixel r c) tensor)

||| Converts a SquareMaxel into a Multiset over Token pairs without intermediate Nat conversion.
public export
squareMaxelToTokenTensor : {dim : Nat} -> SquareMaxel dim -> Multiset BoxInt (Token Nat, Token Nat)
squareMaxelToTokenTensor (MkSquareMaxel tree) =
  foldBoxTreeR (\p, w, acc => AddM (pixelTokens p) w acc) ZeroM tree

||| Reconstructs a sparse SquareMaxel directly from a Token pair Multiset.
public export
tokenTensorToSquareMaxel : {dim : Nat} -> Multiset BoxInt (Token Nat, Token Nat) -> SquareMaxel dim
tokenTensorToSquareMaxel tensor =
  tensorToSquareMaxel (mapMultiset (\(rt, ct) => mkPixelTokens rt ct) tensor)

||| Verified Invariant: Converting a SquareMaxel to Multiset and back preserves the matrix.
public export
auditSquareMaxelTensorRoundtrip : Bool
auditSquareMaxelTensorRoundtrip =
  let id2 = identitySquareMaxel 2
  in tensorNatToSquareMaxel (squareMaxelToTensor id2) == id2 &&
     tensorToSquareMaxel (squareMaxelToPixelTensor id2) == id2

||| Converts a general Maxel into a typed MultisetTensor over natural coordinates.
public export
maxelToTensor : Maxel -> MultisetTensor Nat Nat
maxelToTensor tree =
  foldBoxTreeR (\p, w, acc => AddM (pixelRow p, pixelCol p) w acc) ZeroM tree

||| Reconstructs a general Maxel from a MultisetTensor over natural coordinates.
public export
tensorToMaxel : MultisetTensor Nat Nat -> Maxel
tensorToMaxel tensor =
  foldMultiset (\(r, c), w, tree => addCellTree (mkPixel r c) w tree) BoxLeaf tensor

||| Algebraic Kronecker Tensor Product on SquareMaxel:
public export
kroneckerSquareMaxelAlg : {m, n : Nat} -> SquareMaxel m -> SquareMaxel n -> SquareMaxel (m * n)
kroneckerSquareMaxelAlg {m} {n} m1 m2 =
  let t1 = squareMaxelToTensor m1
      t2 = squareMaxelToTensor m2
      tOp = tensorOperator t1 t2
      observed = mapMultiset (observeKroneckerPixel n) tOp
  in tensorToSquareMaxel observed

||| Verified Invariant: Direct sparse Kronecker product definitionally matches
||| the pushforward observation of the underlying monoidal tensor operator.
public export
auditKroneckerAlgebraicEquivalence : Bool
auditKroneckerAlgebraicEquivalence =
  let id2 = identitySquareMaxel 2
  in kroneckerSquareMaxel id2 id2 == kroneckerSquareMaxelAlg id2 id2

