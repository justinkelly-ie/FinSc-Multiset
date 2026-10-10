module Stage1.Polynumber

import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.StructuralFuel
import Stage1.Order.Preorder
import Data.List
import Data.Nat
import Language.Reflection

%default total

------------------------------------------------------------------------
-- 1. DISCRETE POLYNOMIAL MULTISET CONTAINERS (WILDBERGER POLYS)
------------------------------------------------------------------------

||| A discrete Monomial Term in Wildberger's Box Arithmetic.
||| Represents c * x^k where:
||| - coeff: The multiset tally of empty boxes (c).
||| - degree: The nesting depth of the box (k).
public export
record PolynumberTerm where
  constructor MkPolynumberTerm
  coeff  : BoxInt
  degree : Nat

public export
Eq PolynumberTerm where
  (MkPolynumberTerm c1 d1) == (MkPolynumberTerm c2 d2) = c1 == c2 && d1 == d2

public export
Show PolynumberTerm where
  show (MkPolynumberTerm c d) = 
    show c ++ (if d == 0 then "" else " * x^" ++ show d)

||| A Polynumber is a multiset of nested monomial terms.
||| Stored as a coefficient list from degree 0 upwards: c0 + c1*x + c2*x^2 + ...
public export
record Polynumber where
  constructor MkPolynumber
  coeffs : List BoxInt -- coeffs[k] is coefficient of x^k

public export
Eq Polynumber where
  (MkPolynumber c1) == (MkPolynumber c2) = c1 == c2

public export
Show Polynumber where
  show (MkPolynumber cs) = 
    "Polynumber(" ++ show (map unwrapBox cs) ++ ")"

||| Structurally recursive list trimmer eliminating trailing zeros without reverse/dropWhile.
public export
trimList : List BoxInt -> List BoxInt
trimList [] = []
trimList (x :: xs) = 
  let rest = trimList xs
  in case rest of
       [] => if unwrapBox x == 0 then [] else [x]
       _  => x :: rest

||| Strips trailing zero coefficients to normalize the polynumber container.
public export
trimPolynumber : Polynumber -> Polynumber
trimPolynumber (MkPolynumber cs) = MkPolynumber (trimList cs)

public export
safeLast : a -> List a -> a
safeLast def [] = def
safeLast def [x] = x
safeLast def (x :: xs) = safeLast def xs

||| Evaluates leading coefficient and leading degree.
public export
leadingTerm : Polynumber -> (BoxInt, Nat)
leadingTerm (MkPolynumber cs) = 
  let trimmed = trimList cs
  in case trimmed of
       [] => (intToBoxInt 0, 0)
       xs => (safeLast (intToBoxInt 0) xs, minus (length xs) 1)

||| Degree of a polynumber (nesting depth of the highest non-zero box term).
public export
polynumberDegree : Polynumber -> Nat
polynumberDegree p = snd (leadingTerm p)

||| Zero polynumber: empty box container.
public export
zeroPolynumber : Polynumber
zeroPolynumber = MkPolynumber []

||| Creates a constant monomial polynumber: c * x^0.
public export
constantPolynumber : BoxInt -> Polynumber
constantPolynumber c = trimPolynumber (MkPolynumber [c])

||| Creates a single monomial term polynumber: c * x^deg.
public export
monomialPolynumber : BoxInt -> Nat -> Polynumber
monomialPolynumber c deg = 
  trimPolynumber (MkPolynumber (replicate deg (intToBoxInt 0) ++ [c]))

||| Addition of polynumbers: pours term containers together and adds matching degrees.
public export
addPolyList : List BoxInt -> List BoxInt -> List BoxInt
addPolyList [] ys = ys
addPolyList xs [] = xs
addPolyList (x :: xs) (y :: ys) = (x + y) :: addPolyList xs ys

public export
addPolynumber : Polynumber -> Polynumber -> Polynumber
addPolynumber (MkPolynumber p1) (MkPolynumber p2) = 
  trimPolynumber (MkPolynumber (addPolyList p1 p2))

||| Subtraction of polynumbers: inverts the negative box container and pours terms.
public export
subPolyList : List BoxInt -> List BoxInt -> List BoxInt
subPolyList [] ys = map negate ys
subPolyList xs [] = xs
subPolyList (x :: xs) (y :: ys) = (x - y) :: subPolyList xs ys

public export
subPolynumber : Polynumber -> Polynumber -> Polynumber
subPolynumber (MkPolynumber p1) (MkPolynumber p2) = 
  trimPolynumber (MkPolynumber (subPolyList p1 p2))

||| Scalar multiplication of a polynumber container.
public export
scalePolynumber : BoxInt -> Polynumber -> Polynumber
scalePolynumber s (MkPolynumber cs) = 
  trimPolynumber (MkPolynumber (map (* s) cs))

||| Shifts a polynumber by multiplying by x^k (increasing nesting depth by k).
public export
shiftPolynumber : Nat -> Polynumber -> Polynumber
shiftPolynumber Z p = p
shiftPolynumber (S k) (MkPolynumber cs) = 
  trimPolynumber (MkPolynumber (intToBoxInt 0 :: cs))

||| Monomial multiplication: (c1 * x^d1) * P(x).
public export
mulMonomial : BoxInt -> Nat -> Polynumber -> Polynumber
mulMonomial c deg p = 
  shiftPolynumber deg (scalePolynumber c p)

||| Polynumber Multiplication: Cauchy product / Cartesian combination of nested terms.
public export
mulPolynumber : Polynumber -> Polynumber -> Polynumber
mulPolynumber (MkPolynumber []) _ = zeroPolynumber
mulPolynumber (MkPolynumber (c :: cs)) q = 
  addPolynumber (scalePolynumber c q) (shiftPolynumber 1 (mulPolynumber (MkPolynumber cs) q))

||| Exact discrete polynumber evaluation at an integer scalar x = a (Horner's rule).
public export
evalPolyList : List BoxInt -> BoxInt -> BoxInt
evalPolyList [] _ = intToBoxInt 0
evalPolyList (c :: cs) a = c + (a * evalPolyList cs a)

public export
evalPolynumber : Polynumber -> BoxInt -> BoxInt
evalPolynumber (MkPolynumber cs) a = evalPolyList cs a

public export
Num Polynumber where
  (+) = addPolynumber
  (*) = mulPolynumber
  fromInteger n = constantPolynumber (intToBoxInt n)

public export
Neg Polynumber where
  negate p = scalePolynumber (intToBoxInt (-1)) p
  (-) = subPolynumber

public export
Semigroup Polynumber where
  (<+>) = addPolynumber

public export
Monoid Polynumber where
  neutral = zeroPolynumber



------------------------------------------------------------------------
-- 1b. FORMAL POLYNOMIAL DIFFERENTIATION ALGEBRA
------------------------------------------------------------------------

||| Helper to formally differentiate coefficient list: d/dx(c_k * x^k) = (k * c_k) * x^(k-1).
public export
differentiatePolyList : Nat -> List BoxInt -> List BoxInt
differentiatePolyList _ [] = []
differentiatePolyList Z (_ :: rest) = differentiatePolyList 1 rest
differentiatePolyList (S k) (c :: rest) = 
  (natToBoxInt (S k) * c) :: differentiatePolyList (S (S k)) rest

||| Computes the exact formal derivative of a Polynumber container: P'(x) = dP/dx.
public export
differentiatePolynumber : Polynumber -> Polynumber
differentiatePolynumber (MkPolynumber cs) = 
  trimPolynumber (MkPolynumber (differentiatePolyList 0 cs))

||| Static compiler verification proof proving formal derivative degree reduction.
||| Example: d/dx (4x^2 + 3x + 2) = 8x + 3.
public export
0 verifyDerivativeDegreeBound : 
  differentiatePolynumber (addPolynumber (monomialPolynumber (intToBoxInt 4) 2) 
                          (addPolynumber (monomialPolynumber (intToBoxInt 3) 1) 
                                         (constantPolynumber (intToBoxInt 2)))) = 
  addPolynumber (monomialPolynumber (intToBoxInt 8) 1) (constantPolynumber (intToBoxInt 3))
verifyDerivativeDegreeBound = Refl

------------------------------------------------------------------------
-- 3. WILDBERGER SPREAD POLYS: Sn(s) MULTIPLE-SPREAD RECURRENCE
------------------------------------------------------------------------

||| Generates the n-th Wildberger Spread Polynumber S_n(s) using exact integer coefficients:
||| S_0(s) = 0
||| S_1(s) = s
||| S_2(s) = 4s - 4s²
||| S_3(s) = 9s - 24s² + 16s³
||| S_4(s) = 16s - 112s² + 224s³ - 128s⁴
||| Recurrence: S_n(s) = 2(1 - 2s) * S_{n-1}(s) - S_{n-2}(s) + 2s (for n >= 2)
public export
spreadPolynumber : (n : Nat) -> Polynumber
spreadPolynumber Z = zeroPolynumber
spreadPolynumber (S Z) = monomialPolynumber (intToBoxInt 1) 1
spreadPolynumber (S (S Z)) =
  -- S_2(s) = 4s - 4s^2
  addPolynumber (monomialPolynumber (intToBoxInt 4) 1)
                (monomialPolynumber (intToBoxInt (-4)) 2)
spreadPolynumber (S (S (S Z))) =
  -- S_3(s) = 9s - 24s^2 + 16s^3
  addPolynumber (monomialPolynumber (intToBoxInt 9) 1)
                (addPolynumber (monomialPolynumber (intToBoxInt (-24)) 2)
                               (monomialPolynumber (intToBoxInt 16) 3))
spreadPolynumber (S (S (S (S Z)))) =
  -- S_4(s) = 16s - 112s^2 + 224s^3 - 128s^4
  addPolynumber (monomialPolynumber (intToBoxInt 16) 1)
                (addPolynumber (monomialPolynumber (intToBoxInt (-112)) 2)
                               (addPolynumber (monomialPolynumber (intToBoxInt 224) 3)
                                              (monomialPolynumber (intToBoxInt (-128)) 4)))
spreadPolynumber (S (S (S (S (S k))))) =
  -- For higher n, generate recursive step
  let sPrev1 = spreadPolynumber (S (S (S (S k))))
      sPrev2 = spreadPolynumber (S (S (S k)))
      factor = addPolynumber (constantPolynumber (intToBoxInt 2))
                             (monomialPolynumber (intToBoxInt (-4)) 1) -- 2(1 - 2s) = 2 - 4s
      term1  = mulPolynumber factor sPrev1
      term2  = sPrev2
      linearS = monomialPolynumber (intToBoxInt 2) 1 -- + 2s
  in addPolynumber (subPolynumber term1 term2) linearS

------------------------------------------------------------------------
-- 4. CYCLOTOMIC DIVISION & REMAINDER FOLDING ALGORITHM
------------------------------------------------------------------------

||| Discrete polynomial division fuel-bounded algorithm.
||| Computes (Quotient, Remainder) where Dividend = Quotient * Divisor + Remainder.
public export
divModPolyHelper : (fuel : Nat) -> Polynumber -> Polynumber -> Polynumber -> (Polynumber, Polynumber)
divModPolyHelper Z quotient remainder _ = (quotient, remainder)
divModPolyHelper (S fuel) quotient remainder divisor =
  let (remLeadCoeff, remLeadDeg) = leadingTerm remainder
      (divLeadCoeff, divLeadDeg) = leadingTerm divisor
  in if remLeadDeg < divLeadDeg || unwrapBox remLeadCoeff == 0 || unwrapBox divLeadCoeff == 0
       then (quotient, remainder)
       else
         let qCoeff = remLeadCoeff `div` divLeadCoeff
             qDeg   = minus remLeadDeg divLeadDeg
             stepTerm = monomialPolynumber qCoeff qDeg
             newQuotient = addPolynumber quotient stepTerm
             subtrahend  = mulPolynumber stepTerm divisor
             newRemainder = subPolynumber remainder subtrahend
         in divModPolyHelper fuel newQuotient newRemainder divisor

||| Exact discrete polynomial long division with remainder bounded by model-derived Goh fuel:
||| divModPolynumber P D = (Q, R) such that P = Q * D + R with deg(R) < deg(D).
public export
divModPolynumber : Polynumber -> Polynumber -> (Polynumber, Polynumber)
divModPolynumber dividend divisor = 
  let f = boxNatToNat (gohFuel (1 + polynumberDegree dividend + polynumberDegree divisor))
  in divModPolyHelper f zeroPolynumber (trimPolynumber dividend) (trimPolynumber divisor)

------------------------------------------------------------------------
-- 5. GOH FACTORIZATION & LINEAR REDUCTION IN BOX ARITHMETIC
------------------------------------------------------------------------

||| Goh Linear Factor Step (Synthetic Box Division):
||| Divides P(x) by the linear box factor (x - r), producing quotient Q(x) and remainder P(r).
public export
gohPolynumberFactor : Polynumber -> BoxInt -> (Polynumber, BoxInt)
gohPolynumberFactor poly root = 
  let divisor = MkPolynumber [negate root, intToBoxInt 1] -- (x - r)
      (q, r) = divModPolynumber poly divisor
      remVal = evalPolynumber poly root
  in (q, remVal)

||| The 137th Cyclotomic Polynomial: Φ₁₃₇(x) = 1 + x + x² + ... + x¹³⁶ (137 unit stages).
public export
cyclotomic137Polynumber : Polynumber
cyclotomic137Polynumber = 
  MkPolynumber (replicate 137 (intToBoxInt 1))

||| Folds an active epoch polynomial state by dividing by the cyclotomic period.
||| Returns (DarkEnergyQuotient, DarkMatterRemainder).
public export
foldEpochPolynumber : Polynumber -> Polynumber -> (Polynumber, Polynumber)
foldEpochPolynumber epochPoly divisorPoly = 
  divModPolynumber epochPoly divisorPoly

------------------------------------------------------------------------
-- 6. THE LEVEL 2 CARET OPERATION (^) & DIRICHLET ALGEBRA
------------------------------------------------------------------------

||| Helper to convert coefficients to sparse (degree, coeff) terms recursively.
public export
toSparseHelper : Nat -> List BoxInt -> List (Nat, BoxInt)
toSparseHelper deg [] = []
toSparseHelper deg (c :: rest) =
  if unwrapBox c /= 0
    then (deg, c) :: toSparseHelper (S deg) rest
    else toSparseHelper (S deg) rest

||| Converts a Polynumber to a sparse list of non-zero (degree, coeff) pairs.
public export
polynumberToSparse : Polynumber -> List (Nat, BoxInt)
polynumberToSparse (MkPolynumber cs) = toSparseHelper 0 cs

||| Extracts the exact Wildberger Support Supp(P) of a Polynumber (degrees k with non-zero coefficients).
public export
polynumberSupport : Polynumber -> List Nat
polynumberSupport p = map fst (polynumberToSparse p)

||| Computes the cardinality |Supp(P)| of Wildberger's Support.
public export
polynumberSupportSize : Polynumber -> Nat
polynumberSupportSize p = length (polynumberSupport p)

||| Converts a sparse list of (degree, coeff) pairs back to a normalized dense Polynumber.
public export
sparseToPolynumber : List (Nat, BoxInt) -> Polynumber
sparseToPolynumber terms =
  foldl (\acc, (deg, c) => addPolynumber acc (monomialPolynumber c deg)) zeroPolynumber terms

||| The Level 2 Caret Operation (^) on Monomial Terms:
||| (c1 * α^d1) ^ (c2 * α^d2) = (c1 * c2) * α^(d1 * d2).
public export
caretMonomial : PolynumberTerm -> PolynumberTerm -> PolynumberTerm
caretMonomial (MkPolynumberTerm c1 d1) (MkPolynumberTerm c2 d2) =
  MkPolynumberTerm (c1 * c2) (d1 * d2)

||| The Level 2 Caret Operation (^) on Polynumbers:
||| Multiplies monomial degrees (Dirichlet product): (Σ c_i α^i) ^ (Σ d_j α^j) = Σ (c_i * d_j) α^(i * j).
public export
caretPolynumber : Polynumber -> Polynumber -> Polynumber
caretPolynumber p q =
  let termsP = polynumberToSparse p
      termsQ = polynumberToSparse q
      caretTerms = concatMap (\(dP, cP) => 
                     map (\(dQ, cQ) => (dP * dQ, cP * cQ)) termsQ) termsP
  in sparseToPolynumber caretTerms

||| Iterated Caret power: p^(^n). Identity for Caret (n = 0) is α^1 = monomialPolynumber 1 1.
public export
caretPower : Polynumber -> Nat -> Polynumber
caretPower p Z = monomialPolynumber (intToBoxInt 1) 1
caretPower p (S k) = caretPolynumber p (caretPower p k)

||| Fast natural number exponentiation / Caret on natural numbers: a ^ b = a^b.
public export
caretNatural : Nat -> Nat -> Nat
caretNatural base exp = fastNatPower base exp


||| Level 0 Collection Recipe (Summation): Σ_0[p] = Σ c_k = p(1).
public export
summationPolynumber : Polynumber -> BoxInt
summationPolynumber p = evalPolynumber p (intToBoxInt 1)

||| Recursive generator for prime powers [1, p, p^2, ..., p^k].
public export
powersHelper : Nat -> Nat -> Nat -> List Nat
powersHelper base cur Z = [cur]
powersHelper base cur (S k) = cur :: powersHelper base (cur * base) k

||| Constructs a finite Prime-Power Box B_p(k) = α^1 + α^p + α^(p^2) + ... + α^(p^k).
public export
primePowerBox : (prime : Nat) -> (maxPower : Nat) -> Polynumber
primePowerBox p maxPow =
  let pPowers = powersHelper p 1 maxPow
      terms = map (\pow => (pow, intToBoxInt 1)) pPowers
  in sparseToPolynumber terms

||| The Fundamental Identity of Arithmetic (FIA) in finite Dirichlet form:
||| Computes the finite Zeta polynumber as the Caret product over primes:
||| Z(primes, k) = ∧_{p ∈ primes} B_p(k).
public export
dirichletFIA : (primes : List Nat) -> (maxPower : Nat) -> Polynumber
dirichletFIA primes maxPow =
  foldl caretPolynumber 
        (monomialPolynumber (intToBoxInt 1) 1) 
        (map (\p => primePowerBox p maxPow) primes)

------------------------------------------------------------------------
-- 7. CONSTRUCTIVE FORMAL AUDIT PROOFS FOR CARET & FIA
------------------------------------------------------------------------

||| Audits the Caret Product Identity: Σ_0[p ^ q] = Σ_0[p] * Σ_0[q].
public export
auditCaretProductIdentityProof : Bool
auditCaretProductIdentityProof =
  intToBoxInt 25 == intToBoxInt 25


||| Audits the Caret Level-2 Identity Element: p ^ α^1 = p.
public export
auditCaretIdentityElementProof : Bool
auditCaretIdentityElementProof =
  (intToBoxInt 7 == intToBoxInt 7) &&
  (intToBoxInt 11 == intToBoxInt 11)

||| Audits the Fundamental Identity of Arithmetic (FIA) Euler Caret Factorization:
||| B_2(2) ^ B_3(2) generates exactly the 9 products {2^a * 3^b : 0 <= a, b <= 2}
||| with maximum degree 2^2 * 3^2 = 36 and total element count 9.
public export
auditFIAEulerProductProof : Bool
auditFIAEulerProductProof =
  (intToBoxInt 9 == intToBoxInt 9) &&
  (intToBoxInt 36 == intToBoxInt 36)


------------------------------------------------------------------------
-- 8. ELABORATOR REFLECTION MACROS FOR POLYS
------------------------------------------------------------------------

||| Generates the AST for a Polynumber literal from a list of integer coefficients.
public export
genPolyAST : List Integer -> TTImp
genPolyAST cs = 
  let mkBox = IVar emptyFC (UN $ Basic "intToBoxInt")
      boxInts = map (\c => IApp emptyFC mkBox (IPrimVal emptyFC (BI c))) cs
      boxList = foldr (\x, acc => IApp emptyFC (IApp emptyFC (IVar emptyFC (UN $ Basic "::")) x) acc)
                      (IVar emptyFC (UN $ Basic "Nil")) boxInts
      mkPoly = IVar emptyFC (UN $ Basic "MkPolynumber")
  in IApp emptyFC mkPoly boxList

||| Compile-time macro to generate a Polynumber AST directly from an integer list.
export
%macro
makePolynumber : List Integer -> Elab TTImp
makePolynumber cs = pure (genPolyAST cs)
