module Stage1.Carrier.TensorBridge

import Stage0.BoxInt
import Stage0.Multiset
import Stage1.MultisetTree
import Stage1.MultisetTensor
import Stage1.Basis.CoordCell
import Stage1.Carrier.CellMultiset
import Stage1.Carrier.SquareMaxel

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
