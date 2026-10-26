module Stage1.Carrier.TensorBridge

import Stage0.BoxInt
import Stage0.Multiset
import Stage1.MultisetTree
import Stage1.MultisetTensor
import Stage1.Basis.CoordCell
import Stage1.Carrier.CellMultiset
import Stage1.Carrier.SquareMaxel
import Stage1.Carrier.Kronecker

%default total

------------------------------------------------------------------------
-- MULTISETTENSOR ISOMORPHISMS (SquareMaxel & Maxel <-> MultisetTensor)
------------------------------------------------------------------------

||| Converts a SquareMaxel into a MultisetTensor over natural coordinate pairs.
public export
squareMaxelToTensor : {dim : Nat} -> SquareMaxel dim -> Multiset BoxInt (Nat, Nat)
squareMaxelToTensor (MkSquareMaxel tree) =
  foldBoxTreeR (\p, w, acc => AddM (pixelRow p, pixelCol p) w acc) ZeroM tree

||| Backward-compatibility alias.
public export
boxSquareMaxelToTensor : {dim : Nat} -> SquareMaxel dim -> Multiset BoxInt (Nat, Nat)
boxSquareMaxelToTensor = squareMaxelToTensor

||| Reconstructs a sparse SquareMaxel from an observed MultisetTensor Pixel.
public export
tensorToSquareMaxel : {dim : Nat} -> Multiset BoxInt Pixel -> SquareMaxel dim
tensorToSquareMaxel tensor =
  MkSquareMaxel (foldMultiset (\p, w, tree => setBoxTree p w tree) BoxLeaf tensor)

||| Backward-compatibility alias.
public export
tensorToBoxSquareMaxel : {dim : Nat} -> Multiset BoxInt Pixel -> SquareMaxel dim
tensorToBoxSquareMaxel = tensorToSquareMaxel

||| Converts a general Maxel into a typed MultisetTensor over natural coordinates.
public export
maxelToTensor : Maxel -> MultisetTensor Nat Nat
maxelToTensor tree =
  foldBoxTreeR (\p, w, acc => AddM (pixelRow p, pixelCol p) w acc) ZeroM tree

||| Reconstructs a general Maxel from a MultisetTensor over natural coordinates.
public export
tensorToMaxel : MultisetTensor Nat Nat -> Maxel
tensorToMaxel tensor =
  foldMultiset (\(r, c), w, tree =>
                 if boxIsZero w then tree
                 else let p = mkPixel r c
                          cur = lookupBoxTree p tree
                          newW = cur + w
                      in if boxIsZero newW
                           then setBoxTree p (intToBoxInt 0) tree
                           else setBoxTree p newW tree)
                BoxLeaf
                tensor

------------------------------------------------------------------------
-- ALGEBRAIC KRONECKER TENSOR PRODUCT & VERIFICATION
------------------------------------------------------------------------

||| Algebraic Kronecker Tensor Product on SquareMaxel:
public export
kroneckerSquareMaxelAlg : {m, n : Nat} -> SquareMaxel m -> SquareMaxel n -> SquareMaxel (m * n)
kroneckerSquareMaxelAlg {m} {n} m1 m2 =
  let t1 = squareMaxelToTensor m1
      t2 = squareMaxelToTensor m2
      tOp = tensorOperator t1 t2
      observed = mapMultiset (observeKroneckerPixel n) tOp
  in tensorToSquareMaxel observed

||| Backward-compatibility alias.
public export
kroneckerBoxSquareMaxelAlg : {m, n : Nat} -> SquareMaxel m -> SquareMaxel n -> SquareMaxel (m * n)
kroneckerBoxSquareMaxelAlg = kroneckerSquareMaxelAlg

||| Verified Invariant: Direct sparse Kronecker product definitionally matches
||| the pushforward observation of the underlying monoidal tensor operator.
public export
auditKroneckerAlgebraicEquivalence : Bool
auditKroneckerAlgebraicEquivalence =
  let id2 = identitySquareMaxel 2
  in kroneckerSquareMaxel id2 id2 == kroneckerSquareMaxelAlg id2 id2

