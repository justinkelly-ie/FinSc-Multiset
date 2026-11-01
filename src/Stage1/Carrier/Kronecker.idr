module Stage1.Carrier.Kronecker

import Data.Fin
import Data.Nat
import Data.Vect
import Stage0.BoxInt
import Stage0.BoxNat
import Language.Reflection
import Stage1.TypeTheory.Staging
import Stage1.MultisetTree
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
              wOut = w1 * w2
          in if unwrapBox wOut == 0
               then innerAcc
               else let cur = lookupBoxTree pOut innerAcc
                        newW = cur + wOut
                    in if unwrapBox newW == 0
                         then setBoxTree pOut (intToBoxInt 0) innerAcc
                         else setBoxTree pOut newW innerAcc)
          accTree
          t2)
        BoxLeaf
        t1
  in compressSquareMaxel (MkSquareMaxel resultTree)

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
