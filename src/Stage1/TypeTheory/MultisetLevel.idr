module Stage1.TypeTheory.MultisetLevel

import public Stage0.BoxInt
import public Stage0.Multiset
import public Stage0.OnSeq.FusedStream
import public Stage1.TypeTheory.Staging

%default total

------------------------------------------------------------------------
-- 1. STAGE-INDEXED MULTISET CONTAINERS
------------------------------------------------------------------------

||| A Multiset with an explicit type-level Stage Index n (2LTT / 12LTT universe stratification).
public export
record LevelMultiset (n : Nat) (c : Type) (a : Type) where
  constructor MkLevelMultiset
  unwrapLevelMultiset : Multiset c a

public export
(Eq a, Neg c, Num c, Eq c) => Eq (LevelMultiset n c a) where
  (MkLevelMultiset x) == (MkLevelMultiset y) = x == y

public export
(Show a, Show c) => Show (LevelMultiset n c a) where
  show (MkLevelMultiset x) = show x

||| A Box container with an explicit type-level Stage Index n.
public export
record LevelBox (n : Nat) (a : Type) where
  constructor MkLevelBox
  unwrapLevelBox : Box a

public export
Eq a => Eq (LevelBox n a) where
  (MkLevelBox x) == (MkLevelBox y) = x == y

public export
Show a => Show (LevelBox n a) where
  show (MkLevelBox x) = show x

------------------------------------------------------------------------
-- 2. STAGE-INDEXED MODAL COMBINATORS
------------------------------------------------------------------------

||| Stage-Indexed Multiset Quote: Quotes a LevelMultiset n to LevelMultiset (S n).
public export
quoteLevelMultiset : {n : Nat} -> LevelMultiset n c a -> LevelMultiset (S n) c a
quoteLevelMultiset (MkLevelMultiset m) = MkLevelMultiset m

||| Stage-Indexed Multiset Splice: Splices a LevelMultiset (S n) down to LevelMultiset n.
public export
spliceLevelMultiset : {n : Nat} -> LevelMultiset (S n) c a -> LevelMultiset n c a
spliceLevelMultiset (MkLevelMultiset m) = MkLevelMultiset m

||| Stage-Indexed Box Quote: Quotes a LevelBox n to LevelBox (S n).
public export
quoteLevelBox : {n : Nat} -> LevelBox n a -> LevelBox (S n) a
quoteLevelBox (MkLevelBox b) = MkLevelBox b

||| Stage-Indexed Box Splice: Splices a LevelBox (S n) down to LevelBox n.
public export
spliceLevelBox : {n : Nat} -> LevelBox (S n) a -> LevelBox n a
spliceLevelBox (MkLevelBox b) = MkLevelBox b

------------------------------------------------------------------------
-- 3. DEFINITIONAL INVERSE LAWS
------------------------------------------------------------------------

||| Property 1: Stage-Indexed Multiset Quote/Splice Inverse Law (~_n <m>_n ≡ m).
public export
0 prfInverseSpliceQuoteMultiset : {n : Nat} -> (m : LevelMultiset n c a) -> spliceLevelMultiset (quoteLevelMultiset m) = m
prfInverseSpliceQuoteMultiset (MkLevelMultiset _) = Refl

||| Property 2: Stage-Indexed Box Quote/Splice Inverse Law (~_n <b>_n ≡ b).
public export
0 prfInverseSpliceQuoteBox : {n : Nat} -> (b : LevelBox n a) -> spliceLevelBox (quoteLevelBox b) = b
prfInverseSpliceQuoteBox (MkLevelBox _) = Refl

------------------------------------------------------------------------
-- 4. INTENSIONAL MULTISET GENERATOR (U_1 SPATIAL CARRIER)
------------------------------------------------------------------------

||| 2LTT Level 1 Intensional Multiset:
||| Mathematical specification of a multiset as a finite support carrier paired
||| with an intensional multiplicity generator function (a -> BoxInt).
public export
record IntensionalBox (a : Type) where
  constructor MkIntensionalBox
  support        : List a
  multiplicityFn : a -> BoxInt

||| Quotes an intensional rule and support into a Level 1 IntensionalBox.
public export
quoteIntensional : List a -> (a -> BoxInt) -> IntensionalBox a
quoteIntensional supp gen = MkIntensionalBox supp gen

||| Splices an IntensionalBox down to an extensional Level 0 concrete Box container.
public export
spliceIntensionalToBox : Eq a => IntensionalBox a -> Box a
spliceIntensionalToBox (MkIntensionalBox supp gen) =
  let rawPairs = map (\x => (x, gen x)) supp
      filtered = filter (\(_, w) => unwrapBox w /= 0) rawPairs
  in consolidateBox (MkBox filtered)

||| Definitional inverse law for intensional multiset term evaluation.
public export
0 inverseIntensionalEvaluation : (supp : List a) -> (gen : a -> BoxInt) -> (x : a) ->
                                 multiplicityFn (quoteIntensional supp gen) x = gen x
inverseIntensionalEvaluation _ _ _ = Refl

------------------------------------------------------------------------
-- 5. DEFORESTED STREAM-BACKED INTENSIONAL MULTISET
------------------------------------------------------------------------

||| 2LTT Level 1 Deforested Stream-Backed Intensional Multiset:
||| Encodes support as a zero-allocation coinductive stream paired with a multiplicity generator.
public export
record IntensionalStreamBox (a : Type) where
  constructor MkIntensionalStreamBox
  streamSupport  : FusedStream a
  multiplicityFn : a -> BoxInt

||| Quotes an intensional stream support and multiplicity rule into an IntensionalStreamBox.
public export
quoteIntensionalStream : FusedStream a -> (a -> BoxInt) -> IntensionalStreamBox a
quoteIntensionalStream strm gen = MkIntensionalStreamBox strm gen

||| Splices an IntensionalStreamBox down to an extensional Level 0 concrete Box container
||| using total structural Nat fuel without intermediate list allocations.
public export
spliceIntensionalStreamToBoxNat : Eq a => (fuel : Nat) -> IntensionalStreamBox a -> Box a
spliceIntensionalStreamToBoxNat fuel (MkIntensionalStreamBox strm gen) =
  foldStreamNat fuel
    (\acc, x =>
      let w = gen x
      in if unwrapBox w == 0 then acc else insertBox x w acc)
    emptyBox
    strm

||| Splices an IntensionalStreamBox down to an extensional Level 0 concrete Box container
||| using model-derived Goh fuel based on support size.
public export
spliceIntensionalStreamToBox : Eq a => (sizeHint : Nat) -> IntensionalStreamBox a -> Box a
spliceIntensionalStreamToBox sizeHint ibox =
  spliceIntensionalStreamToBoxNat (boxNatToNat (gohFuel sizeHint)) ibox

||| Audit witness verifying stream-backed intensional multiset evaluation.
public export
auditIntensionalStreamBoxProof : Bool
auditIntensionalStreamBoxProof =
  let strm = stream [the Nat 1, the Nat 2, the Nat 3]
      ibox = quoteIntensionalStream strm (\x => if x == 2 then intToBoxInt 0 else intToBoxInt (cast x))
      resBox = spliceIntensionalStreamToBox 3 ibox
      w1 = lookupBox (the Nat 1) resBox
      w2 = lookupBox (the Nat 2) resBox
      w3 = lookupBox (the Nat 3) resBox
  in (unwrapBox w1 == 1) && (unwrapBox w2 == 0) && (unwrapBox w3 == 3)

