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
||| Instead of unary MSets, we use a Run-Length Encoded dictionary grouped by (alpha power, beta power).
public export
IntPolynumber : Type
IntPolynumber = Multiset BoxInt (Nat, Nat)

||| The zero IntPolynumber.
public export
emptyIntPoly : IntPolynumber
emptyIntPoly = ZeroM

public export
posTerm : Nat -> Nat -> BoxInt -> IntPolynumber
posTerm alpha beta coeff =
  if boxIsZero coeff then ZeroM else AddM (alpha, beta) coeff ZeroM

||| Add two IntPolynumbers, automatically annihilating opposites and merging duplicate degrees.
public export
addIntPoly : IntPolynumber -> IntPolynumber -> IntPolynumber
addIntPoly = unionMultisetBox

||| Subtract p2 from p1, automatically annihilating opposites.
public export
subIntPoly : IntPolynumber -> IntPolynumber -> IntPolynumber
subIntPoly p1 p2 = unionMultisetBox p1 (negateMultiset p2)

||| Explicitly annihilates the IntPolynumber, compressing it by merging terms.
public export
annihilateIntPoly : IntPolynumber -> IntPolynumber
annihilateIntPoly p = annihilateMultiset p

||| Multiply two IntPolynumbers in O(N*M).
public export
mulIntPoly : IntPolynumber -> IntPolynumber -> IntPolynumber
mulIntPoly xs ys =
  annihilateMultiset (mulOuter xs ys)
  where
    mulBasis : (Nat, Nat) -> (Nat, Nat) -> (Nat, Nat)
    mulBasis (a1, b1) (a2, b2) = (a1 + a2, b1 + b2)
    
    mulInner : (Nat, Nat) -> BoxInt -> IntPolynumber -> IntPolynumber
    mulInner _ _ ZeroM = ZeroM
    mulInner bx cx (AddM by cy rest) =
      let prod = mulBox cx cy
      in if boxIsZero prod then mulInner bx cx rest
         else AddM (mulBasis bx by) prod (mulInner bx cx rest)

    mulOuter : IntPolynumber -> IntPolynumber -> IntPolynumber
    mulOuter ZeroM _ = ZeroM
    mulOuter (AddM bx cx rest) ys2 = 
      addMultiset (mulInner bx cx ys2) (mulOuter rest ys2)

||| Scales an IntPolynumber by a BoxInt scalar, pruning zero weights.
public export
scaleIntPoly : BoxInt -> IntPolynumber -> IntPolynumber
scaleIntPoly = scaleMultisetBox

||| Hadamard (pointwise coefficient) product of two IntPolynumbers.
public export
hadamardIntPoly : IntPolynumber -> IntPolynumber -> IntPolynumber
hadamardIntPoly = hadamardMultisetBox

||| Tropical infimum (componentwise min) of two IntPolynumbers.
public export
minIntPoly : IntPolynumber -> IntPolynumber -> IntPolynumber
minIntPoly = minMultisetBox

||| Tropical supremum (componentwise max) of two IntPolynumbers.
public export
maxIntPoly : IntPolynumber -> IntPolynumber -> IntPolynumber
maxIntPoly = maxMultisetBox

||| Inner product / Frobenius pairing of two IntPolynumbers: sum c1_ij * c2_ij.
public export
dotIntPoly : IntPolynumber -> IntPolynumber -> BoxInt
dotIntPoly = dotMultisetBox

||| Evaluates a bivariate IntPolynumber P(alpha, beta) at BoxInt coordinates (a, b)
||| using O(log d) binary exponentiation.
public export
evalIntPoly : IntPolynumber -> BoxInt -> BoxInt -> BoxInt
evalIntPoly p a b =
  foldMultiset (\(degA, degB), c, acc =>
    let powFuel : Nat -> BoxInt -> Nat -> BoxInt
        powFuel Z _ _ = MkBoxInt 1
        powFuel _ _ Z = MkBoxInt 1
        powFuel (S fuel) base exp =
          let half = divNatNZ exp 2 ItIsSucc
              rem2 = modNatNZ exp 2 ItIsSucc
              hPow = powFuel fuel (mulBox base base) half
          in if rem2 == 0 then hPow else mulBox base hPow
        powA = powFuel (gohSteps (gohFuelForCapacity degA)) a degA
        powB = powFuel (gohSteps (gohFuelForCapacity degB)) b degB
    in addBox acc (mulBox c (mulBox powA powB)))
    (MkBoxInt 0)
    p

||| Raises an IntPolynumber to a natural power n via repeated Cauchy multiplication.
public export
powerIntPoly : IntPolynumber -> Nat -> IntPolynumber
powerIntPoly _ Z = AddM (0, 0) (MkBoxInt 1) ZeroM
powerIntPoly p (S k) = mulIntPoly p (powerIntPoly p k)

||| Substitutes alpha -> r and beta -> s into an IntPolynumber P(alpha, beta).
||| Evaluated structurally via multiset fold: sum c_ij * r^i * s^j.
public export
substituteIntPoly : (r : IntPolynumber) -> (s : IntPolynumber) -> IntPolynumber -> IntPolynumber
substituteIntPoly r s p =
  foldMultiset (\(degA, degB), c, acc =>
    let termR = powerIntPoly r degA
        termS = powerIntPoly s degB
        termProd = mulIntPoly termR termS
        scaledTerm = scaleIntPoly c termProd
    in addIntPoly acc scaledTerm)
    emptyIntPoly
    p
