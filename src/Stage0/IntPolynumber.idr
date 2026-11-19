module Stage0.IntPolynumber

import Data.List
import Data.Nat
import Data.Linear
import Stage0.Interfaces
import Stage0.StructuralFuel
import public Stage0.BoxInt
import public Stage0.Multiset

%default total

||| A highly compressed, high-performance representation of Polynomials with BoxInt coefficients.
||| Backed by the unified AVL Carrier (Nat, Nat) keyed by (alpha power, beta power).
public export
IntPolynumber : Type
IntPolynumber = Carrier (Nat, Nat)

||| The zero IntPolynumber.
public export
emptyIntPoly : IntPolynumber
emptyIntPoly = neutral

public export
posTerm : Nat -> Nat -> BoxInt -> IntPolynumber
posTerm alpha beta coeff = singletonCarrier (alpha, beta) coeff

||| Add two IntPolynumbers, automatically annihilating opposites and merging duplicate degrees.
public export
addIntPoly : IntPolynumber -> IntPolynumber -> IntPolynumber
addIntPoly = (<+>)

||| Subtract p2 from p1, automatically annihilating opposites.
public export
subIntPoly : IntPolynumber -> IntPolynumber -> IntPolynumber
subIntPoly = (-)

||| Explicitly annihilates the IntPolynumber (canonical AVL Carrier is already coalesced and zero-pruned).
public export
annihilateIntPoly : IntPolynumber -> IntPolynumber
annihilateIntPoly = id

||| Multiply two IntPolynumbers via MonoidCoord (Nat, Nat) Cauchy convolution.
public export
mulIntPoly : IntPolynumber -> IntPolynumber -> IntPolynumber
mulIntPoly = (*)

||| Scales an IntPolynumber by a BoxInt scalar, pruning zero weights.
public export
scaleIntPoly : BoxInt -> IntPolynumber -> IntPolynumber
scaleIntPoly = scaleCarrier

||| Hadamard (pointwise coefficient) product of two IntPolynumbers.
public export
hadamardIntPoly : IntPolynumber -> IntPolynumber -> IntPolynumber
hadamardIntPoly = (.*.)

||| Tropical infimum (componentwise min) of two IntPolynumbers.
public export
minIntPoly : IntPolynumber -> IntPolynumber -> IntPolynumber
minIntPoly = (/\)

||| Tropical supremum (componentwise max) of two IntPolynumbers.
public export
maxIntPoly : IntPolynumber -> IntPolynumber -> IntPolynumber
maxIntPoly = (\/)

||| Inner product / Frobenius pairing of two IntPolynumbers: sum c1_ij * c2_ij.
public export
dotIntPoly : IntPolynumber -> IntPolynumber -> BoxInt
dotIntPoly = (<.>)

||| Evaluates a bivariate IntPolynumber P(alpha, beta) at BoxInt coordinates (a, b)
||| using O(log d) binary exponentiation.
public export
evalIntPoly : IntPolynumber -> BoxInt -> BoxInt -> BoxInt
evalIntPoly p a b =
  foldBoxTreeL (\acc, ((degA, degB), c) =>
    let powFuel : Nat -> BoxInt -> Nat -> BoxInt
        powFuel Z _ _ = MkBoxInt 1
        powFuel _ _ Z = MkBoxInt 1
        powFuel (S fuel) base exp =
          let (half, isOdd) = natHalfAndOdd exp
              hPow = powFuel fuel (mulBox base base) half
          in if isOdd then mulBox base hPow else hPow
        powA = powFuel (gohSteps (gohFuelForCapacity degA)) a degA
        powB = powFuel (gohSteps (gohFuelForCapacity degB)) b degB
    in addBox acc (mulBox c (mulBox powA powB)))
    (MkBoxInt 0)
    p

||| Raises an IntPolynumber to a natural power n via repeated Cauchy multiplication.
public export
powerIntPoly : IntPolynumber -> Nat -> IntPolynumber
powerIntPoly _ Z = 1
powerIntPoly p (S k) = p * powerIntPoly p k

||| Substitutes alpha -> r and beta -> s into an IntPolynumber P(alpha, beta).
||| Evaluated structurally via AVL fold: sum c_ij * r^i * s^j.
public export
substituteIntPoly : (r : IntPolynumber) -> (s : IntPolynumber) -> IntPolynumber -> IntPolynumber
substituteIntPoly r s p =
  foldBoxTreeL (\acc, ((degA, degB), c) =>
    let termR = powerIntPoly r degA
        termS = powerIntPoly s degB
        scaledTerm = scaleIntPoly c (termR * termS)
    in acc + scaledTerm)
    neutral
    p
