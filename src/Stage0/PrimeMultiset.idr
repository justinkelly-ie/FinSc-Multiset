module Stage0.PrimeMultiset

import public Stage0.BoxInt
import public Stage0.Multiset
import Data.Vect
import Data.Nat
import Decidable.Equality

%default total

--------------------------------------------------------------------------------
-- 1. CONSTRUCTIVIST GOH PRIME SPECTRUM {2, 3, 5, 7, 11, 13}
--------------------------------------------------------------------------------

||| Constructivist Goh prime family indexed by its exact prime number p.
||| Strictly bounded by the 13-smooth horizon: {2, 3, 5, 7, 11, 13}.
public export
data GohPrime : (p : Nat) -> Type where
  Prime2  : GohPrime 2
  Prime3  : GohPrime 3
  Prime5  : GohPrime 5
  Prime7  : GohPrime 7
  Prime11 : GohPrime 11
  Prime13 : GohPrime 13

-- Dependently typed canonical constants:
public export gohPrime2  : GohPrime 2;  gohPrime2  = Prime2
public export gohPrime3  : GohPrime 3;  gohPrime3  = Prime3
public export gohPrime5  : GohPrime 5;  gohPrime5  = Prime5
public export gohPrime7  : GohPrime 7;  gohPrime7  = Prime7
public export gohPrime11 : GohPrime 11; gohPrime11 = Prime11
public export gohPrime13 : GohPrime 13; gohPrime13 = Prime13

||| Existential Sigma-pair used when prime indices vary dynamically
||| (e.g. factoring arbitrary integers into collections of certified primes).
public export
AnyGohPrime : Type
AnyGohPrime = (p : Nat ** GohPrime p)

||| Project the underlying Nat prime from an existential pair.
public export
gohPrimeNat : AnyGohPrime -> Nat
gohPrimeNat (p ** _) = p

public export anyPrime2  : AnyGohPrime; anyPrime2  = (the Nat 2 ** Prime2)
public export anyPrime3  : AnyGohPrime; anyPrime3  = (the Nat 3 ** Prime3)
public export anyPrime5  : AnyGohPrime; anyPrime5  = (the Nat 5 ** Prime5)
public export anyPrime7  : AnyGohPrime; anyPrime7  = (the Nat 7 ** Prime7)
public export anyPrime11 : AnyGohPrime; anyPrime11 = (the Nat 11 ** Prime11)
public export anyPrime13 : AnyGohPrime; anyPrime13 = (the Nat 13 ** Prime13)

public export
allGohPrimes : Vect 6 AnyGohPrime
allGohPrimes = [anyPrime2, anyPrime3, anyPrime5, anyPrime7, anyPrime11, anyPrime13]

public export
decideGohPrime : (p : Nat) -> Dec (GohPrime p)
decideGohPrime 2  = Yes Prime2
decideGohPrime 3  = Yes Prime3
decideGohPrime 5  = Yes Prime5
decideGohPrime 7  = Yes Prime7
decideGohPrime 11 = Yes Prime11
decideGohPrime 13 = Yes Prime13
decideGohPrime 0  = No (\case Prime2 impossible)
decideGohPrime 1  = No (\case Prime2 impossible)
decideGohPrime 4  = No (\case Prime2 impossible)
decideGohPrime 6  = No (\case Prime2 impossible)
decideGohPrime 8  = No (\case Prime2 impossible)
decideGohPrime 9  = No (\case Prime2 impossible)
decideGohPrime 10 = No (\case Prime2 impossible)
decideGohPrime 12 = No (\case Prime2 impossible)
decideGohPrime (S (S (S (S (S (S (S (S (S (S (S (S (S (S _)))))))))))))) =
  No (\case Prime2 impossible; Prime3 impossible; Prime5 impossible; Prime7 impossible; Prime11 impossible; Prime13 impossible)

public export
toGohPrime : (p : Nat) -> Maybe AnyGohPrime
toGohPrime p = case decideGohPrime p of
  Yes prf => Just (p ** prf)
  No _    => Nothing

public export
Eq AnyGohPrime where
  (p1 ** _) == (p2 ** _) = p1 == p2

public export
Show AnyGohPrime where
  show (p ** _) = "GohPrime(" ++ show p ++ ")"

--------------------------------------------------------------------------------
-- 2. CERTIFIED 13-SMOOTH GOH PRIME MULTISET
--------------------------------------------------------------------------------

||| First-class multiset of prime factor exponents over the constructive
||| Goh prime basis {2, 3, 5, 7, 11, 13}.
||| By construction, every represented prime is strictly bounded by 13,
||| rendering every instance definitionally 13-smooth without ad-hoc flags or shims.
public export
record GohPrimeMultiset where
  constructor MkGohPrimeMultiset
  exp2  : Nat
  exp3  : Nat
  exp5  : Nat
  exp7  : Nat
  exp11 : Nat
  exp13 : Nat

||| Zero prime multiset representing the multiplicative identity 1.
public export
emptyGohPrimeMultiset : GohPrimeMultiset
emptyGohPrimeMultiset = MkGohPrimeMultiset 0 0 0 0 0 0

||| Canonical type alias preserving backward API compatibility without shims.
public export
PrimeMultiset : Type
PrimeMultiset = GohPrimeMultiset

||| Canonical constructor pattern synonym for PrimeMultiset.
public export
MkPrimeMultiset : Nat -> Nat -> Nat -> Nat -> Nat -> Nat -> PrimeMultiset
MkPrimeMultiset = MkGohPrimeMultiset

public export
Eq GohPrimeMultiset where
  (MkGohPrimeMultiset a2 a3 a5 a7 a11 a13) == (MkGohPrimeMultiset b2 b3 b5 b7 b11 b13) =
    a2 == b2 && a3 == b3 && a5 == b5 && a7 == b7 && a11 == b11 && a13 == b13

public export
Show GohPrimeMultiset where
  show (MkGohPrimeMultiset e2 e3 e5 e7 e11 e13) =
    "2^" ++ show e2 ++ " * 3^" ++ show e3 ++ " * 5^" ++ show e5 ++ 
    " * 7^" ++ show e7 ++ " * 11^" ++ show e11 ++ " * 13^" ++ show e13

||| Smoothness is guaranteed by construction for all GohPrimeMultiset instances.
public export
is13Smooth : GohPrimeMultiset -> Bool
is13Smooth _ = True

||| Evaluates the total integer product encoded by a GohPrimeMultiset.
public export
gohPrimeMultisetProduct : GohPrimeMultiset -> Nat
gohPrimeMultisetProduct (MkGohPrimeMultiset e2 e3 e5 e7 e11 e13) =
  (power 2 e2) * (power 3 e3) * (power 5 e5) * (power 7 e7) * (power 11 e11) * (power 13 e13)

||| Multiplies two GohPrimeMultisets by adding prime exponents (monoid addition).
public export
mulGohPrimeMultiset : GohPrimeMultiset -> GohPrimeMultiset -> GohPrimeMultiset
mulGohPrimeMultiset (MkGohPrimeMultiset a2 a3 a5 a7 a11 a13) (MkGohPrimeMultiset b2 b3 b5 b7 b11 b13) =
  MkGohPrimeMultiset (a2 + b2) (a3 + b3) (a5 + b5) (a7 + b7) (a11 + b11) (a13 + b13)

public export
Semigroup GohPrimeMultiset where
  (<+>) = mulGohPrimeMultiset

public export
Monoid GohPrimeMultiset where
  neutral = emptyGohPrimeMultiset

||| Converts a GohPrimeMultiset into an RLE Multiset of AnyGohPrime pairs.
public export
toRLEMultiset : GohPrimeMultiset -> Multiset Nat AnyGohPrime
toRLEMultiset m =
  let m1 = if m.exp2 > 0 then AddM anyPrime2 m.exp2 ZeroM else ZeroM
      m2 = if m.exp3 > 0 then AddM anyPrime3 m.exp3 m1 else m1
      m3 = if m.exp5 > 0 then AddM anyPrime5 m.exp5 m2 else m2
      m4 = if m.exp7 > 0 then AddM anyPrime7 m.exp7 m3 else m3
      m5 = if m.exp11 > 0 then AddM anyPrime11 m.exp11 m4 else m4
      m6 = if m.exp13 > 0 then AddM anyPrime13 m.exp13 m5 else m5
  in m6

||| Converts a GohPrimeMultiset into a Box multiset container.
public export
toBoxMultiset : GohPrimeMultiset -> Box AnyGohPrime
toBoxMultiset m =
  let b1 = if m.exp2 > 0 then insertBox anyPrime2 (MkBoxInt (cast m.exp2)) emptyBox else emptyBox
      b2 = if m.exp3 > 0 then insertBox anyPrime3 (MkBoxInt (cast m.exp3)) b1 else b1
      b3 = if m.exp5 > 0 then insertBox anyPrime5 (MkBoxInt (cast m.exp5)) b2 else b2
      b4 = if m.exp7 > 0 then insertBox anyPrime7 (MkBoxInt (cast m.exp7)) b3 else b3
      b5 = if m.exp11 > 0 then insertBox anyPrime11 (MkBoxInt (cast m.exp11)) b4 else b4
      b6 = if m.exp13 > 0 then insertBox anyPrime13 (MkBoxInt (cast m.exp13)) b5 else b5
  in b6

--------------------------------------------------------------------------------
-- 3. CERTIFIED SMOOTH FACTORIZATION ALGORITHM
--------------------------------------------------------------------------------

||| Extracts the exponent of a given prime factor from an Integer using explicit fuel.
public export
extractPrime : (fuel : Nat) -> (p : Integer) -> (n : Integer) -> (Nat, Integer)
extractPrime Z _ n = (0, n)
extractPrime (S fuel) p n =
  if n <= 1 || p <= 1 then (0, n)
  else if n `mod` p == 0
    then let (k, rem) = extractPrime fuel p (n `div` p)
         in (S k, rem)
    else (0, n)

||| General trial division factorization across the Goh prime basis {2, 3, 5, 7, 11, 13}.
public export
factorizeGohGeneral : Nat -> Maybe GohPrimeMultiset
factorizeGohGeneral Z = Just emptyGohPrimeMultiset
factorizeGohGeneral (S Z) = Just emptyGohPrimeMultiset
factorizeGohGeneral (S k) =
  let n0 = natToInteger (S k)
      fuel = S k
      (e2,  n1) = extractPrime fuel 2 n0
      (e3,  n2) = extractPrime fuel 3 n1
      (e5,  n3) = extractPrime fuel 5 n2
      (e7,  n4) = extractPrime fuel 7 n3
      (e11, n5) = extractPrime fuel 11 n4
      (e13, n6) = extractPrime fuel 13 n5
  in if n6 == 1
       then Just (MkGohPrimeMultiset e2 e3 e5 e7 e11 e13)
       else Nothing

||| Attempts to factorize a positive integer into a certified 13-smooth GohPrimeMultiset.
||| Pattern-matches canonical Goh basis and cosmic dimensions for instantaneous compile-time
||| definitional reduction (Rule 01, Item 3), falling back to total integer trial division.
public export
factorizeGohSmooth : Nat -> Maybe GohPrimeMultiset
factorizeGohSmooth 0   = Just emptyGohPrimeMultiset
factorizeGohSmooth 1   = Just emptyGohPrimeMultiset
factorizeGohSmooth 2   = Just (MkGohPrimeMultiset 1 0 0 0 0 0)
factorizeGohSmooth 3   = Just (MkGohPrimeMultiset 0 1 0 0 0 0)
factorizeGohSmooth 4   = Just (MkGohPrimeMultiset 2 0 0 0 0 0)
factorizeGohSmooth 5   = Just (MkGohPrimeMultiset 0 0 1 0 0 0)
factorizeGohSmooth 6   = Just (MkGohPrimeMultiset 1 1 0 0 0 0)
factorizeGohSmooth 7   = Just (MkGohPrimeMultiset 0 0 0 1 0 0)
factorizeGohSmooth 8   = Just (MkGohPrimeMultiset 3 0 0 0 0 0)
factorizeGohSmooth 9   = Just (MkGohPrimeMultiset 0 2 0 0 0 0)
factorizeGohSmooth 10  = Just (MkGohPrimeMultiset 1 0 1 0 0 0)
factorizeGohSmooth 11  = Just (MkGohPrimeMultiset 0 0 0 0 1 0)
factorizeGohSmooth 12  = Just (MkGohPrimeMultiset 2 1 0 0 0 0)
factorizeGohSmooth 13  = Just (MkGohPrimeMultiset 0 0 0 0 0 1)
factorizeGohSmooth 26  = Just (MkGohPrimeMultiset 1 0 0 0 0 1)
factorizeGohSmooth 27  = Just (MkGohPrimeMultiset 0 3 0 0 0 0)
factorizeGohSmooth 39  = Just (MkGohPrimeMultiset 0 1 0 0 0 1)
factorizeGohSmooth 52  = Just (MkGohPrimeMultiset 2 0 0 0 0 1)
factorizeGohSmooth 55  = Just (MkGohPrimeMultiset 0 0 1 0 1 0)
factorizeGohSmooth 65  = Just (MkGohPrimeMultiset 0 0 1 0 0 1)
factorizeGohSmooth 78  = Just (MkGohPrimeMultiset 1 1 0 0 0 1)
factorizeGohSmooth 91  = Just (MkGohPrimeMultiset 0 0 0 1 0 1)
factorizeGohSmooth 104 = Just (MkGohPrimeMultiset 3 0 0 0 0 1)
factorizeGohSmooth 117 = Just (MkGohPrimeMultiset 0 2 0 0 0 1)
factorizeGohSmooth 128 = Just (MkGohPrimeMultiset 7 0 0 0 0 0)
factorizeGohSmooth 130 = Just (MkGohPrimeMultiset 1 0 1 0 0 1)
factorizeGohSmooth 143 = Just (MkGohPrimeMultiset 0 0 0 0 1 1)
factorizeGohSmooth 156 = Just (MkGohPrimeMultiset 2 1 0 0 0 1)
factorizeGohSmooth 169 = Just (MkGohPrimeMultiset 0 0 0 0 0 2)
factorizeGohSmooth 210 = Just (MkGohPrimeMultiset 1 1 1 1 0 0)
factorizeGohSmooth 216 = Just (MkGohPrimeMultiset 3 3 0 0 0 0)
factorizeGohSmooth n   = factorizeGohGeneral n

||| Constructivist Goh energy step representing rational energy scale transitions (num / den).
public export
record GohEnergyStep where
  constructor MkGohStep
  stepNumerator   : Nat
  stepDenominator : Nat

public export
Show GohEnergyStep where
  show (MkGohStep n d) = show n ++ "/" ++ show d

||| Factorizes a Goh energy step into optional certified 13-smooth GohPrimeMultisets.
public export
factorizeGohStep : GohEnergyStep -> (Maybe GohPrimeMultiset, Maybe GohPrimeMultiset)
factorizeGohStep (MkGohStep num den) = (factorizeGohSmooth num, factorizeGohSmooth den)

||| Audits that a Goh energy step is certified 13-smooth across both numerator and denominator.
public export
auditGoh13Smoothness : GohEnergyStep -> Bool
auditGoh13Smoothness step =
  let (mNum, mDen) = factorizeGohStep step
  in isJust mNum && isJust mDen

||| Static proof witness verifying that Prime 13 fuel step (13 / 1) is definitionally 13-smooth.
public export
0 verifyGoh13Smoothness : Stage0.PrimeMultiset.auditGoh13Smoothness (MkGohStep 13 1) = True
verifyGoh13Smoothness = Refl

||| Static proof witness verifying that Observer Generation 39 step (39 / 1) is definitionally 13-smooth.
public export
0 verifyObserver39Smoothness : Stage0.PrimeMultiset.auditGoh13Smoothness (MkGohStep 39 1) = True
verifyObserver39Smoothness = Refl

||| Static proof witness verifying that 17 / 1 is rejected by auditGoh13Smoothness (17 is not 13-smooth).
public export
0 verifyNonSmoothRejected : Stage0.PrimeMultiset.auditGoh13Smoothness (MkGohStep 17 1) = False
verifyNonSmoothRejected = Refl

||| Static compile-time factorization proof for the canonical Prime 13 step.
public export
0 verifyGoh13Factorization : factorizeGohSmooth 13 = Just (MkGohPrimeMultiset 0 0 0 0 0 1)
verifyGoh13Factorization = Refl

||| Static compile-time factorization proof for the Observer Epoch dimension 39 = 3 * 13.
public export
0 verifyObserver39Factorization : factorizeGohSmooth 39 = Just (MkGohPrimeMultiset 0 1 0 0 0 1)
verifyObserver39Factorization = Refl
