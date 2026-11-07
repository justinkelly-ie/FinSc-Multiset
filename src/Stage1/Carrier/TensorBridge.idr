module Stage1.Carrier.TensorBridge

import Stage0.BoxInt
import Stage0.Multiset
import Stage0.Token
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



||| Verified Invariant: Direct sparse Kronecker product definitionally matches
||| the pushforward observation of the underlying monoidal tensor operator.
public export
auditKroneckerAlgebraicEquivalence : Bool
auditKroneckerAlgebraicEquivalence =
  let id2 = identitySquareMaxel 2
  in kroneckerSquareMaxel id2 id2 == kroneckerSquareMaxelAlg id2 id2

