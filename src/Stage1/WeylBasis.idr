module Stage1.WeylBasis

import Data.Nat
import public Stage0.Box
import public Stage0.BoxInt
import public Stage0.HereditaryMSet
import public Stage0.OnSeq.FusedStream
import public Stage1.Fuse
import public Stage1.Views
import public Stage1.Bridge.LaurentAntiMSetBridge

%default total

--------------------------------------------------------------------------------
-- 1. SYMMETRIC PAIR BASIS (`B_n`) & INTEGER WEYL PARITY (MF 234 / 236)
--------------------------------------------------------------------------------

||| Symmetric Binomial basis polynumber `B_n` (Wildberger MF 234):
||| - `B_0 = 2 * \alpha^0`
||| - `B_n = \alpha^{-n} + \alpha^{+n}` for `n >= 1`
public export
symPairPoly : Nat -> PureMultiset
symPairPoly Z = mkLaurentPure [(0, 2)]
symPairPoly (S k) =
  let n = natToInteger (S k)
  in mkLaurentPure [(negate n, 1), (n, 1)]

||| Integer Weyl parity split avoiding division by `2`:
||| `2M = (M + \sigma M) + (M - \sigma M)` (`evenPart`, `oddPart`).
public export
weylParityDouble : PureMultiset -> (PureMultiset, PureMultiset)
weylParityDouble m =
  let r = uvIrDual m
  in (addHMSet m r, subHMSet m r)

--------------------------------------------------------------------------------
-- 2. BABY WEYL CHARACTER DECONVOLUTION (`A_1 * q = m`) & `Dec` RECOGNIZER
--------------------------------------------------------------------------------

private
lastTerm : List (Integer, BoxInt) -> Maybe (Integer, BoxInt)
lastTerm []        = Nothing
lastTerm [x]       = Just x
lastTerm (_ :: xs) = lastTerm xs

||| Fueled multiset telescoping deconvolution peeling highest positive exponent
||| `+k` downward via `c * (\alpha^k - \alpha^{k-2})`, certifying zero remainder `[]`.
public export
weylDivideByA1Loop : Nat -> PureMultiset -> PureMultiset -> Maybe PureMultiset
weylDivideByA1Loop fuel acc rem =
  if rem == emptyPureMSet
    then Just acc
    else case fuel of
           Z => Nothing
           S remFuel =>
             case toLaurentTerms unwrapBox rem of
               [] => Nothing
               ((eMin, _) :: rest) =>
                 case lastTerm ((eMin, zeroWeight) :: rest) of
                   Nothing => Nothing
                   Just (eMax, wMax) =>
                     if eMax < eMin + 2
                       then Nothing
                       else
                         let w    = unwrapBox wMax
                             acc' = addHMSet acc (mkLaurentPure [(eMax - 1, w)])
                             subT = mkLaurentPure [(eMax, w), (eMax - 2, negate w)]
                             rem' = subHMSet rem subT
                         in weylDivideByA1Loop remFuel acc' rem'

||| Computes the exact integral polynumber quotient `m / A_1` inside `PureMultiset`
||| without rational fields when `m` is divisible by `A_1 = \alpha^{+1} - \alpha^{-1}`.
public export
weylDivideByA1 : PureMultiset -> Maybe PureMultiset
weylDivideByA1 m@(MkHMSet box) =
  let stats = collectSupportStats box
  in weylDivideByA1Loop (S (S (stats.maxDeg + stats.maxDeg))) emptyPureMSet m

||| Soundness predicate checking that `weylDivideByA1 m` succeeds and reconstructs
||| `mulHMSet (altBinomial 1) q == m`.
public export
isWeylDivisibleByA1Bool : PureMultiset -> Bool
isWeylDivisibleByA1Bool m =
  case weylDivideByA1 m of
    Nothing => False
    Just q  => mulHMSet (altBinomial 1) q == m

public export
IsWeylDivisibleByA1 : PureMultiset -> Type
IsWeylDivisibleByA1 m = (isWeylDivisibleByA1Bool m = True)

||| Constructive `Dec` recognizer certifying Baby Weyl divisibility by `A_1`
||| (`recognition-rule.md`).
public export
recognizeWeylDivisibleByA1 : (m : PureMultiset) -> Dec (IsWeylDivisibleByA1 m)
recognizeWeylDivisibleByA1 m = decideBoolTrue (isWeylDivisibleByA1Bool m)

--------------------------------------------------------------------------------
-- 3. CLEBSCH-GORDAN EXPANSION & HOLOGRAPHIC `GohFuel` COMPRESSION
--------------------------------------------------------------------------------

private
absDiffNat : Nat -> Nat -> Nat
absDiffNat a b = if a >= b then minus a b else minus b a

||| Explicit Clebsch-Gordan direct sum `C_m * C_n = sum_{k=0}^{min m n} C_{|m-n| + 2k}` (MF 236).
public export
clebschGordanSum : (m : Nat) -> (n : Nat) -> PureMultiset
clebschGordanSum m n = go (S (min m n)) (absDiffNat m n) emptyPureMSet
  where
    go : Nat -> Nat -> PureMultiset -> PureMultiset
    go Z     _   acc = acc
    go (S k) idx acc = go k (idx + 2) (addHMSet acc (centralPoly idx))

||| Holographic Baby Weyl evaluation of `C_m * C_n`:
||| multiplies the 2-term boundary dipole `A_{m+1}` by `C_n` in `2*(n+1)` yields
||| (instead of `(m+1)*(n+1)`), then telescopes back via `weylDivideByA1`.
public export
weylCompressMul : (cap : Nat) -> (m : Nat) -> (n : Nat) ->
                  (SolidifiedCarrier cap PureMultiset, Maybe PureMultiset)
weylCompressMul cap m n =
  let sol = runFueledHyperOp 1 cap (altBinomial (natToInteger (S m))) (centralPoly n)
  in (sol, weylDivideByA1 sol.carrier)

--------------------------------------------------------------------------------
-- 4. `B_n`-ORBIT MULTIPLICATION (`B_m * B_n = B_{|m-n|} + B_{m+n}`)
--------------------------------------------------------------------------------

||| Multiplies two symmetric-orbit distributions represented directly over `Nat`
||| orbit indices via Wildberger's binomial product law `B_m * B_n = B_{|m-n|} + B_{m+n}`.
public export
mulSymOrbits : Box BoxInt Nat -> Box BoxInt Nat -> Box BoxInt Nat
mulSymOrbits b1 b2 =
  foldBox (\m, w1, accOuter =>
            foldBox (\n, w2, accInner =>
                      let wProd = mulBox w1 w2
                      in if isZero wProd
                           then accInner
                           else addAtKeyBox (m + n) wProd (addAtKeyBox (absDiffNat m n) wProd accInner))
                    accOuter
                    b2)
          BoxLeaf
          b1

||| Expands a `B_n`-orbit `Box BoxInt Nat` back into explicit Laurent `PureMultiset`.
public export
fromSymOrbits : Box BoxInt Nat -> PureMultiset
fromSymOrbits =
  foldBox (\n, w, acc => addHMSet acc (scaleHMSet w (symPairPoly n))) emptyPureMSet

||| `symmetricMotionTick` (`\alpha^{-1} + 2 + \alpha^{+1} = B_1 + B_0`) in `B_n` orbit form.
public export
symMotionOrbits : Box BoxInt Nat
symMotionOrbits = setBox (the Nat 1) (intToBoxInt 1) (setBox (the Nat 0) (intToBoxInt 1) BoxLeaf)

--------------------------------------------------------------------------------
-- 5. 2D `A_2` (`SU(3)`) BARYON OCTET MULTISET CHECK (`3 * 3bar - 1`)
--------------------------------------------------------------------------------

||| Exact 2D Laurent convolution over `(Integer, Integer)` exponent boxes.
public export
convBox2D : Box BoxInt (Integer, Integer) ->
            Box BoxInt (Integer, Integer) ->
            Box BoxInt (Integer, Integer)
convBox2D b1 b2 =
  foldBox (\(x1, y1), w1, accOuter =>
            foldBox (\(x2, y2), w2, accInner =>
                      addAtKeyBox (x1 + x2, y1 + y2) (mulBox w1 w2) accInner)
                    accOuter
                    b2)
          BoxLeaf
          b1

||| Fundamental 2D `A_2` triplet `3` (`\alpha + \alpha^{-1}\beta + \beta^{-1}`).
public export
a2Fund3 : Box BoxInt (Integer, Integer)
a2Fund3 =
  setBox (1, 0) (intToBoxInt 1)
    (setBox (-1, 1) (intToBoxInt 1)
      (setBox (0, -1) (intToBoxInt 1) BoxLeaf))

||| Anti-fundamental 2D `A_2` anti-triplet `3bar` (`\alpha^{-1} + \alpha\beta^{-1} + \beta`).
public export
a2AntiFund3 : Box BoxInt (Integer, Integer)
a2AntiFund3 =
  setBox (-1, 0) (intToBoxInt 1)
    (setBox (1, -1) (intToBoxInt 1)
      (setBox (0, 1) (intToBoxInt 1) BoxLeaf))

||| 8-dimensional `A_2` Baryon Octet multiset `3 * 3bar - 1` (`6` outer hexagon
||| vertices of multiplicity `1` + origin `(0, 0)` of multiplicity `2`, mass `8`).
public export
a2BaryonOctet : Box BoxInt (Integer, Integer)
a2BaryonOctet = addAtKeyBox (0, 0) (intToBoxInt (-1)) (convBox2D a2Fund3 a2AntiFund3)

--------------------------------------------------------------------------------
-- 6. PURE QTT 0 `Refl` AUDITS (WILDERBERGER MF 234 & 236 IDENTITIES)
--------------------------------------------------------------------------------

public export
0 prfSymMotionIsB1PlusB0 :
  (Stage0.HereditaryMSet.addHMSet (Stage1.WeylBasis.symPairPoly 1) (Stage1.WeylBasis.symPairPoly 0)
    == Stage0.HereditaryMSet.symmetricMotionTick) = True
prfSymMotionIsB1PlusB0 = Refl

public export
0 prfA1SquareIsB2MinusB0 :
  (Stage0.HereditaryMSet.mulHMSet (Stage1.Fuse.altBinomial 1) (Stage1.Fuse.altBinomial 1)
    == Stage0.HereditaryMSet.subHMSet (Stage1.WeylBasis.symPairPoly 2) (Stage1.WeylBasis.symPairPoly 0)) = True
prfA1SquareIsB2MinusB0 = Refl

public export
0 prfBabyWeylC4 :
  (Stage1.WeylBasis.weylDivideByA1 (Stage1.Fuse.altBinomial 5)
    == Just (Stage1.Fuse.centralPoly 4)) = True
prfBabyWeylC4 = Refl

public export
0 prfClebschGordanC3C4 :
  (Stage0.HereditaryMSet.mulHMSet (Stage1.Fuse.centralPoly 3) (Stage1.Fuse.centralPoly 4)
    == Stage1.WeylBasis.clebschGordanSum 3 4) = True
prfClebschGordanC3C4 = Refl

public export
0 prfSymOrbitsSquareMatches :
  (Stage1.WeylBasis.fromSymOrbits (Stage1.WeylBasis.mulSymOrbits Stage1.WeylBasis.symMotionOrbits Stage1.WeylBasis.symMotionOrbits)
    == Stage0.HereditaryMSet.mulHMSet Stage0.HereditaryMSet.symmetricMotionTick Stage0.HereditaryMSet.symmetricMotionTick) = True
prfSymOrbitsSquareMatches = Refl
