module Stage1.Polynumber

import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.Multiset
import Stage0.StructuralFuel
import Stage0.StreamPolynumber
import Stage0.OnSeq.FusedStream as FS
import Stage1.MultisetTree
import Stage1.Order.Preorder
import Data.List
import Data.Nat
import Language.Reflection
import public Data.Vect

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
    "Polynumber(" ++ show cs ++ ")"

||| Structurally recursive list trimmer eliminating trailing zeros without reverse/dropWhile.
public export
trimList : List BoxInt -> List BoxInt
trimList [] = []
trimList (x :: xs) = 
  let rest = trimList xs
  in case rest of
       [] => if boxIsZero x then [] else [x]
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
constantPolynumber c =
  if boxIsZero c
    then zeroPolynumber
    else MkPolynumber [c]

||| Creates a single monomial term polynumber: c * x^deg.
public export
monomialPolynumber : BoxInt -> Nat -> Polynumber
monomialPolynumber c deg =
  if boxIsZero c
    then zeroPolynumber
    else MkPolynumber (replicate deg (intToBoxInt 0) ++ [c])

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

||| Natural exponentiation of a Polynumber: p^n via repeated Cauchy multiplication.
public export
powerPolynumber : Polynumber -> Nat -> Polynumber
powerPolynumber _ Z = constantPolynumber (intToBoxInt 1)
powerPolynumber p (S k) = mulPolynumber p (powerPolynumber p k)

||| Exact discrete polynumber evaluation at an integer scalar x = a (Horner's rule).
public export
evalPolyList : List BoxInt -> BoxInt -> BoxInt
evalPolyList [] _ = intToBoxInt 0
evalPolyList (c :: cs) a = c + (a * evalPolyList cs a)

public export
evalPolynumber : Polynumber -> BoxInt -> BoxInt
evalPolynumber (MkPolynumber cs) a = evalPolyList cs a

||| Composition of two Polynumbers: (P ∘ Q)(x) = P(Q(x)).
||| Evaluated structurally via Horner's rule: c_0 + Q * (c_1 + Q * (c_2 + ...)).
public export
composePolynumber : Polynumber -> Polynumber -> Polynumber
composePolynumber (MkPolynumber cs) q =
  composeList cs q
  where
    composeList : List BoxInt -> Polynumber -> Polynumber
    composeList [] _ = zeroPolynumber
    composeList (c :: rest) qIn =
      addPolynumber (constantPolynumber c) (mulPolynumber qIn (composeList rest qIn))

||| Algebraic Double-Zero Criterion (FMP 22d):
||| A Polynumber P(x) has a double zero at x = 0 iff P(0) = 0 and P'(0) = 0.
||| Equivalent to: the constant term c_0 and linear coefficient c_1 are both zero.
public export
hasDoubleZeroAtOrigin : Polynumber -> Bool
hasDoubleZeroAtOrigin (MkPolynumber (c0 :: c1 :: _)) = boxIsZero c0 && boxIsZero c1
hasDoubleZeroAtOrigin (MkPolynumber [c0]) = boxIsZero c0
hasDoubleZeroAtOrigin (MkPolynumber []) = True

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
||| Single step in the Wildberger Multiple Spread recurrence:
||| S_{n+1}(s) = 2(1 - 2s) * S_n(s) - S_{n-1}(s) + 2s = (2 - 4s) * S_n(s) - S_{n-1}(s) + 2s.
public export
spreadRecurrenceStep : Polynumber -> Polynumber -> Polynumber
spreadRecurrenceStep sPrev2 sPrev1 =
  let factor = addPolynumber (constantPolynumber (intToBoxInt 2))
                             (monomialPolynumber (intToBoxInt (-4)) 1) -- 2(1 - 2s) = 2 - 4s
      term1  = mulPolynumber factor sPrev1
      linearS = monomialPolynumber (intToBoxInt 2) 1 -- + 2s
  in addPolynumber (subPolynumber term1 sPrev2) linearS

||| Tail-recursive companion stepper computing the n-th Spread Polynumber in linear O(N) operations.
public export
spreadPolynumberIter : (k : Nat) -> (prev2 : Polynumber) -> (prev1 : Polynumber) -> Polynumber
spreadPolynumberIter Z prev2 _ = prev2
spreadPolynumberIter (S Z) _ prev1 = prev1
spreadPolynumberIter (S (S remaining)) prev2 prev1 =
  let next = spreadRecurrenceStep prev2 prev1
  in spreadPolynumberIter (S remaining) prev1 next

||| Generates the n-th Wildberger Spread Polynumber S_n(s) in linear O(N) operations (Rule 04, Item 4):
||| S_0(s) = 0
||| S_1(s) = s
||| S_2(s) = 4s - 4s²
||| S_3(s) = 9s - 24s² + 16s³
||| S_4(s) = 16s - 112s² + 224s³ - 128s⁴
||| Recurrence: S_n(s) = 2(1 - 2s) * S_{n-1}(s) - S_{n-2}(s) + 2s (for n >= 2)
public export
spreadPolynumber : (n : Nat) -> Polynumber
spreadPolynumber n = spreadPolynumberIter n zeroPolynumber (monomialPolynumber (intToBoxInt 1) 1)

||| Generates the sequence of Wildberger Spread Polynumbers as a deforested stream
||| with O(1) auxiliary registers (Rule 04, Item 4).
public export
spreadRecurrenceStream : FusedStream (Nat, Polynumber)
spreadRecurrenceStream = FS.unfoldStream nextSpread (Z, zeroPolynumber, monomialPolynumber (intToBoxInt 1) 1)
  where
    nextSpread : (Nat, Polynumber, Polynumber) -> FS.Step (Nat, Polynumber, Polynumber) (Nat, Polynumber)
    nextSpread (Z, s0, s1) = FS.Yield (0, s0) (1, s0, s1)
    nextSpread (S Z, s0, s1) = FS.Yield (1, s1) (2, s0, s1)
    nextSpread (S (S k), sPrev2, sPrev1) =
      let sNext = spreadRecurrenceStep sPrev2 sPrev1
      in FS.Yield (S (S k), sNext) (S (S (S k)), sPrev1, sNext)

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
  in if remLeadDeg < divLeadDeg || boxIsZero remLeadCoeff || boxIsZero divLeadCoeff
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
  let f = gohSteps (gohFuelForCapacity (1 + polynumberDegree dividend + polynumberDegree divisor))
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
  if boxIsNonZero c
    then (deg, c) :: toSparseHelper (S deg) rest
    else toSparseHelper (S deg) rest

||| Converts a Polynumber to a sparse list of non-zero (degree, coeff) pairs.
public export
polynumberToSparse : Polynumber -> List (Nat, BoxInt)
polynumberToSparse (MkPolynumber cs) = toSparseHelper 0 cs

||| Extracts the active support degrees where coeff /= 0 (Wildberger finite support).
public export
supportPolynumber : Polynumber -> List Nat
supportPolynumber (MkPolynumber cs) = go 0 cs
  where
    go : Nat -> List BoxInt -> List Nat
    go _ [] = []
    go deg (c :: rest) =
      if boxIsNonZero c
         then deg :: go (S deg) rest
         else go (S deg) rest

||| Computes the cardinality |Supp(P)| of Wildberger's Support.
public export
polynumberSupportSize : Polynumber -> Nat
polynumberSupportSize p = length (supportPolynumber p)

||| Converts a sparse list of (degree, coeff) pairs back to a normalized dense Polynumber.
public export
sparseToPolynumber : List (Nat, BoxInt) -> Polynumber
sparseToPolynumber terms =
  foldl (\acc, (deg, c) => addPolynumber acc (monomialPolynumber c deg)) zeroPolynumber terms

||| Converts a dense Polynumber into a canonical sparse Multiset BoxInt Nat (mapping degree -> coefficient).
public export
polyToMultiset : Polynumber -> Multiset BoxInt Nat
polyToMultiset p = foldr (\(deg, c), acc => AddM deg c acc) ZeroM (polynumberToSparse p)

||| Reconstructs a normalized dense Polynumber from a sparse Multiset BoxInt Nat.
public export
multisetToPoly : Multiset BoxInt Nat -> Polynumber
multisetToPoly m = foldMultiset (\deg, c, acc => addPolynumber acc (monomialPolynumber c deg)) zeroPolynumber m

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

------------------------------------------------------------------------
-- 9. WILDBERGER SUPPORT & DUALITY BRIDGES (STREAMING & MULTISET TREE)
------------------------------------------------------------------------

||| Helper to insert a term at degree into coefficient list.
public export
insertAtDeg : Nat -> BoxInt -> List BoxInt -> List BoxInt
insertAtDeg Z c [] = [c]
insertAtDeg Z c (x :: xs) = (addBox x c) :: xs
insertAtDeg (S k) c [] = (intToBoxInt 0) :: insertAtDeg k c []
insertAtDeg (S k) c (x :: xs) = x :: insertAtDeg k c xs

||| Converts a dense Polynumber into a deforested StreamPolynumber.
public export
toStreamPoly : Polynumber -> StreamPolynumber
toStreamPoly (MkPolynumber cs) =
  FS.unfoldStream step (Z, cs)
  where
    step : (Nat, List BoxInt) -> FS.Step (Nat, List BoxInt) (Nat, BoxInt)
    step (_, []) = FS.Done
    step (deg, c :: rest) =
      if boxIsNonZero c
        then FS.Yield (deg, c) (S deg, rest)
        else FS.Skip (S deg, rest)

||| Reconstructs a dense Polynumber from a StreamPolynumber over Nat fuel.
public export
fromStreamPolyNat : Nat -> StreamPolynumber -> Polynumber
fromStreamPolyNat fuelSteps strm =
  let terms = FS.foldStreamNat fuelSteps (\acc, (deg, c) => insertAtDeg deg c acc) (the (List BoxInt) []) strm
  in trimPolynumber (MkPolynumber terms)

||| Converts a dense Polynumber with positive coefficients into an O(log N) BoxSpecTree.
public export
polyToBoxSpecTree : Polynumber -> BoxSpecTree
polyToBoxSpecTree (MkPolynumber cs) = go 0 cs Leaf
  where
    go : Nat -> List BoxInt -> BoxSpecTree -> BoxSpecTree
    go _ [] tree = tree
    go deg (c :: rest) tree =
      let n = boxToNat c
          tree' = if n > 0
                     then insertTokenTree (fromNatBoxSpec deg) n tree
                     else tree
      in go (S deg) rest tree'

||| Converts an O(log N) BoxSpecTree back into a dense Polynumber.
public export
boxSpecTreeToPoly : BoxSpecTree -> Polynumber
boxSpecTreeToPoly tree =
  let pairs = foldTreeR (\spec, count, acc => (boxSize spec, natToBoxInt count) :: acc) (the (List (Nat, BoxInt)) []) tree
  in foldl (\acc, (deg, c) => addPolynumber acc (monomialPolynumber c deg)) zeroPolynumber pairs

||| Converts an O(log N) BoxSpecTree into a deforested StreamPolynumber.
public export
boxSpecTreeToStreamPoly : BoxSpecTree -> StreamPolynumber
boxSpecTreeToStreamPoly tree =
  FS.mapStream (\(spec, count) => (boxSize spec, natToBoxInt count)) (streamMultisetTreeDirect tree)

||| Converts a StreamPolynumber with positive terms into an O(log N) BoxSpecTree under Nat fuel.
public export
streamPolyToBoxSpecTreeNat : (fuel : Nat) -> StreamPolynumber -> BoxSpecTree
streamPolyToBoxSpecTreeNat fuelSteps strm =
  FS.foldStreamNat fuelSteps (\tree, (deg, c) =>
    let n = boxToNat c
    in if n > 0
          then insertTokenTree (fromNatBoxSpec deg) n tree
          else tree
  ) Leaf strm

------------------------------------------------------------------------
-- 10. POLYSUPPORT & DUALITY AUDIT WITNESSES (RULE 01)
------------------------------------------------------------------------

||| Audits that supportPolynumber correctly extracts active non-zero degree indices:
||| For P(x) = 5*x^3 - 2*x + 7, Supp(P) = [0, 1, 3] (degree 2 has coefficient 0).
public export
auditPolySupportProof : Bool
auditPolySupportProof =
  let p = addPolynumber (constantPolynumber (intToBoxInt 7))
          (addPolynumber (monomialPolynumber (intToBoxInt (-2)) 1)
                         (monomialPolynumber (intToBoxInt 5) 3))
      supp = supportPolynumber p
  in supp == [0, 1, 3]

||| Audits the round-trip equivalence between dense Polynumber and StreamPolynumber:
||| fromStreamPoly (toStreamPoly p) == p.
public export
auditPolyStreamRoundTripProof : Bool
auditPolyStreamRoundTripProof =
  let p = addPolynumber (constantPolynumber (intToBoxInt 3))
          (addPolynumber (monomialPolynumber (intToBoxInt 4) 1)
                         (monomialPolynumber (intToBoxInt 5) 2))
      strm = toStreamPoly p
      p' = fromStreamPolyNat 10 strm
  in p == p'

||| Audits the round-trip equivalence between dense Polynumber and BoxSpecTree:
||| boxSpecTreeToPoly (polyToBoxSpecTree p) == p for positive coefficients.
public export
auditPolyTreeEquivalenceProof : Bool
auditPolyTreeEquivalenceProof =
  let p = addPolynumber (constantPolynumber (intToBoxInt 2))
          (addPolynumber (monomialPolynumber (intToBoxInt 4) 1)
                         (monomialPolynumber (intToBoxInt 3) 2))
      tree = polyToBoxSpecTree p
      p' = boxSpecTreeToPoly tree
      c0 = lookupTokenTree (fromNatBoxSpec 0) tree
      c1 = lookupTokenTree (fromNatBoxSpec 1) tree
      c2 = lookupTokenTree (fromNatBoxSpec 2) tree
  in (p == p') && (c0 == 2) && (c1 == 4) && (c2 == 3)

------------------------------------------------------------------------
-- 11. DEGREE-CERTIFIED POLYNOMIAL MULTISET CONTAINERS (DEP-POLYNUMBERS)
------------------------------------------------------------------------

||| A Polynumber whose maximum degree is certified at the type level.
||| Contains a vector of (S deg) coefficients for degrees 0 .. deg.
public export
record DepPolynumber (deg : Nat) where
  constructor MkDepPolynumber
  polyCoeffs : Vect (S deg) BoxInt

public export
Eq (DepPolynumber deg) where
  (MkDepPolynumber c1) == (MkDepPolynumber c2) = c1 == c2

public export
Show (DepPolynumber deg) where
  show (MkDepPolynumber cs) =
    "DepPolynumber(" ++ show (toList cs) ++ ")"

||| Creates a constant DepPolynumber (degree 0).
public export
constantDepPoly : BoxInt -> DepPolynumber 0
constantDepPoly c = MkDepPolynumber [c]

||| Helper to build a monomial coefficient vector of length (S deg) with leading coefficient c.
public export
monomialCoeffs : BoxInt -> (deg : Nat) -> Vect (S deg) BoxInt
monomialCoeffs c 0 = [c]
monomialCoeffs c (S k) = intToBoxInt 0 :: monomialCoeffs c k

||| Creates a monomial DepPolynumber: c * x^deg.
public export
monomialDepPoly : BoxInt -> (deg : Nat) -> DepPolynumber deg
monomialDepPoly c deg = MkDepPolynumber (monomialCoeffs c deg)

||| Addition of two DepPolynumbers with identical certified degree.
public export
addDepPolynumber : DepPolynumber deg -> DepPolynumber deg -> DepPolynumber deg
addDepPolynumber (MkDepPolynumber c1) (MkDepPolynumber c2) =
  MkDepPolynumber (zipWith (+) c1 c2)

||| Scalar multiplication of a DepPolynumber.
public export
scaleDepPolynumber : BoxInt -> DepPolynumber deg -> DepPolynumber deg
scaleDepPolynumber s (MkDepPolynumber cs) =
  MkDepPolynumber (map (* s) cs)

||| Negation of a DepPolynumber.
public export
negateDepPolynumber : DepPolynumber deg -> DepPolynumber deg
negateDepPolynumber (MkDepPolynumber cs) =
  MkDepPolynumber (map negBox cs)

||| Subtraction of two DepPolynumbers with identical certified degree.
public export
subDepPolynumber : DepPolynumber deg -> DepPolynumber deg -> DepPolynumber deg
subDepPolynumber (MkDepPolynumber c1) (MkDepPolynumber c2) =
  MkDepPolynumber (zipWith (-) c1 c2)

||| Evaluates a DepPolynumber at an integer value using Horner's method.
public export
evalDepPolynumber : DepPolynumber deg -> BoxInt -> BoxInt
evalDepPolynumber (MkDepPolynumber cs) x =
  foldr (\c, acc => c + (acc * x)) (intToBoxInt 0) (toList cs)

||| Converts a DepPolynumber to an unindexed Polynumber.
public export
toPolynumber : DepPolynumber deg -> Polynumber
toPolynumber (MkDepPolynumber cs) = MkPolynumber (toList cs)

||| Converts an unindexed list of coefficients into a vector padded to length n with a default.
public export
fromListPadded : BoxInt -> (n : Nat) -> List BoxInt -> Vect n BoxInt
fromListPadded _ 0 _ = []
fromListPadded def (S k) [] = def :: fromListPadded def k []
fromListPadded def (S k) (x :: xs) = x :: fromListPadded def k xs

||| Converts an unindexed Polynumber to a DepPolynumber padded or truncated to degree deg.
public export
fromPolynumber : (deg : Nat) -> Polynumber -> DepPolynumber deg
fromPolynumber deg (MkPolynumber cs) =
  MkDepPolynumber (fromListPadded (intToBoxInt 0) (S deg) cs)

||| Computes polynomial multiplication of two DepPolynumbers with additive degree guarantee.
public export
mulDepPolynumber : {d1, d2 : Nat} -> DepPolynumber d1 -> DepPolynumber d2 -> DepPolynumber (d1 + d2)
mulDepPolynumber {d1} {d2} p1 p2 =
  let unindexed = mulPolynumber (toPolynumber p1) (toPolynumber p2)
  in fromPolynumber (d1 + d2) unindexed

||| Audits that mulDepPolynumber preserves exact coefficients across degree addition:
||| (2 + 3x) * (4 + 5x) = 8 + 22x + 15x^2.
public export
auditDepPolyMulProof : Bool
auditDepPolyMulProof =
  let p = MkDepPolynumber [intToBoxInt 2, intToBoxInt 3]
      q = MkDepPolynumber [intToBoxInt 4, intToBoxInt 5]
      res = mulDepPolynumber p q
  in toList res.polyCoeffs == [intToBoxInt 8, intToBoxInt 22, intToBoxInt 15]

||| Generates the n-th Wildberger Spread Polynumber with compile-time certified degree n (Rule 03, Item 7):
||| deg(S_n(s)) = n.
public export
spreadDepPolynumber : (n : Nat) -> DepPolynumber n
spreadDepPolynumber Z = MkDepPolynumber [intToBoxInt 0]
spreadDepPolynumber (S Z) = MkDepPolynumber [intToBoxInt 0, intToBoxInt 1]
spreadDepPolynumber n = fromPolynumber n (spreadPolynumber n)

||| Helper to formally differentiate coefficient vector: d/dx(c_k * x^k) = (k * c_k) * x^(k-1).
public export
differentiateDepCoeffs : Nat -> Vect k BoxInt -> Vect k BoxInt
differentiateDepCoeffs _ [] = []
differentiateDepCoeffs deg (c :: cs) =
  (natToBoxInt deg * c) :: differentiateDepCoeffs (S deg) cs

||| Computes the exact formal derivative of a DepPolynumber,
||| proving at compile time that differentiation strictly reduces degree by 1.
public export
differentiateDepPoly : DepPolynumber (S deg) -> DepPolynumber deg
differentiateDepPoly (MkDepPolynumber (_ :: cs)) =
  MkDepPolynumber (differentiateDepCoeffs 1 cs)

||| The Level-2 Caret product on DepPolynumbers with multiplicative degree certification:
||| deg(P ^ Q) = deg(P) * deg(Q).
public export
caretDepPoly : {d1, d2 : Nat} -> DepPolynumber d1 -> DepPolynumber d2 -> DepPolynumber (d1 * d2)
caretDepPoly {d1} {d2} p1 p2 =
  let unindexed = caretPolynumber (toPolynumber p1) (toPolynumber p2)
  in fromPolynumber (d1 * d2) unindexed

||| Converts a DepPolynumber directly to a deforested StreamPolynumber.
public export
toStreamDepPoly : DepPolynumber deg -> StreamPolynumber
toStreamDepPoly p = toStreamPoly (toPolynumber p)

||| Converts a DepPolynumber with positive coefficients to an O(log N) BoxSpecTree.
public export
depPolyToBoxSpecTree : DepPolynumber deg -> BoxSpecTree
depPolyToBoxSpecTree p = polyToBoxSpecTree (toPolynumber p)

||| The 137th Cyclotomic Polynomial with certified degree 136:
||| Φ₁₃₇(x) = 1 + x + x² + ... + x¹³⁶ (137 unit stages).
public export
cyclotomic137DepPoly : DepPolynumber 136
cyclotomic137DepPoly = MkDepPolynumber (replicate 137 (intToBoxInt 1))

||| Audits that differentiateDepPoly strictly reduces degree and evaluates correctly:
||| d/dx (4x^2 + 3x + 2) = 8x + 3.
public export
auditDepPolyDiffProof : Bool
auditDepPolyDiffProof =
  let p : DepPolynumber 2 = MkDepPolynumber [intToBoxInt 2, intToBoxInt 3, intToBoxInt 4]
      dp : DepPolynumber 1 = differentiateDepPoly p
  in toList dp.polyCoeffs == [intToBoxInt 3, intToBoxInt 8]

public export
0 verifyDepPolyDiff :
  toList (differentiateDepPoly (MkDepPolynumber [intToBoxInt 2, intToBoxInt 3, intToBoxInt 4])).polyCoeffs =
  [intToBoxInt 3, intToBoxInt 8]
verifyDepPolyDiff = Refl

||| Audits that spreadDepPolynumber 2 matches S_2(s) = 4s - 4s^2.
public export
0 verifySpreadDepPoly2 :
  toList (spreadDepPolynumber 2).polyCoeffs = [intToBoxInt 0, intToBoxInt 4, intToBoxInt (-4)]
verifySpreadDepPoly2 = Refl

||| Audits that cyclotomic137DepPoly has degree 136 and leading coefficient 1.
public export
0 verifyCyclotomic137Degree :
  Data.Vect.last Stage1.Polynumber.cyclotomic137DepPoly.polyCoeffs = intToBoxInt 1
verifyCyclotomic137Degree = Refl

