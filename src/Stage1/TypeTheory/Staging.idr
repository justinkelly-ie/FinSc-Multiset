||| Module Stage1.TypeTheory.Staging
|||
||| Canonical 2LTT Staging Operations for the FinSc Multiset Science Framework.
||| Implements modal type lifting (⇑A), quoting (⟨t⟩), splicing (~t), and definitional inverse laws
||| following Kovács (2022) Two-Level Type Theory.
module Stage1.TypeTheory.Staging

import public Stage1.TypeTheory.TwoLevel
import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.Multiset
import Stage0.OnSeq.FusedStream
import public Stage1.Basis.CoordCell
import Data.Vect

%default total

------------------------------------------------------------------------
-- 1. EXPLICIT 2LTT STAGING MODAL TYPES & OPERATIONS
------------------------------------------------------------------------

||| 2LTT Type Lifting (⇑A): Type of static metaprograms computing runtime expressions of type A.
public export
Lift : Type -> Type
Lift a = StrictLevel a

||| Synonym alias for 2LTT staged code block.
public export
Code : Type -> Type
Code a = Lift a



||| 2LTT Quoting (⟨t⟩): Quotes a runtime object term t : A into a static meta term ⟨t⟩ : Lift A.
public export
quote : a -> Lift a
quote x = MkStrict x

||| 2LTT Splicing (~t): Splices/evaluates a static meta term t : Lift A down to runtime object code.
public export
splice : Lift a -> a
splice (MkStrict x) = x

------------------------------------------------------------------------
-- 2. EXPLICIT DEFINITIONAL INVERSE LAWS
------------------------------------------------------------------------

||| 2LTT Inverse Law 1: Splicing a quoted term returns the original object term definitionally (~⟨t⟩ ≡ t).
public export
0 inverseSpliceQuote : (x : a) -> splice (quote x) = x
inverseSpliceQuote _ = Refl

||| 2LTT Inverse Law 2: Quoting a spliced term returns the original static meta term definitionally (⟨~t⟩ ≡ t).
public export
0 inverseQuoteSplice : (s : Lift a) -> quote (splice s) = s
inverseQuoteSplice (MkStrict _) = Refl

------------------------------------------------------------------------
-- 3. BINDING-TIME IMPROVEMENTS (CANONICAL 2LTT ISOMORPHISMS)
------------------------------------------------------------------------

||| Preservation of Function Types (⇑(A → B) ≃ (⇑A → ⇑B)):
||| Lifts a staged function into a meta-level function operating on staged values.
public export
presArrow : Lift (a -> b) -> (Lift a -> Lift b)
presArrow qf qa = quote ((splice qf) (splice qa))

||| Inverse preservation of function types:
||| Reifies a meta-level function into a staged runtime function.
public export
presArrowInv : (Lift a -> Lift b) -> Lift (a -> b)
presArrowInv f = quote (\x => splice (f (quote x)))

||| Round-trip identity for reified meta-functions.
public export
0 prfPresArrowRoundtrip : (f : Lift a -> Lift b) -> (x : a) -> splice (presArrowInv f) x = splice (f (quote x))
prfPresArrowRoundtrip _ _ = Refl

||| Preservation of Product Types (⇑(A × B) ≃ (⇑A × ⇑B)):
||| Deconstructs a staged pair into a pair of staged components.
public export
presProd : Lift (a, b) -> (Lift a, Lift b)
presProd qp =
  let (x, y) = splice qp
  in (quote x, quote y)

||| Inverse preservation of product types:
||| Combines a pair of staged components into a single staged pair.
public export
presProdInv : (Lift a, Lift b) -> Lift (a, b)
presProdInv (qa, qb) = quote (splice qa, splice qb)

||| Product preservation roundtrip 1: (presProd ∘ presProdInv = id)
public export
0 prfPresProdInv : (qa : Lift a) -> (qb : Lift b) -> presProd (presProdInv (qa, qb)) = (qa, qb)
prfPresProdInv (MkStrict _) (MkStrict _) = Refl

||| Product preservation roundtrip 2: (presProdInv ∘ presProd = id)
public export
0 prfPresProd : (qp : Lift (a, b)) -> presProdInv (presProd qp) = qp
prfPresProd (MkStrict (_, _)) = Refl

------------------------------------------------------------------------
-- 4. BINDING-TIME MULTISET COMBINATORS
------------------------------------------------------------------------

||| 2LTT Staged Multiset Union:
||| Combines two staged multiset boxes under 2LTT lifting.
public export
stagedMultisetUnion : Eq a => Lift (Box a) -> Lift (Box a) -> Lift (Box a)
stagedMultisetUnion qb1 qb2 = quote (unionBox (splice qb1) (splice qb2))

||| 2LTT Staged Multiset Empty Constructor.
public export
stagedEmptyBox : Lift (Box a)
stagedEmptyBox = quote emptyBox

||| 2LTT Staged Multiset Singleton Constructor.
public export
stagedUnixelBox : a -> BoxInt -> Lift (Box a)
stagedUnixelBox x w = quote (unixelBox x w)

||| 2LTT Staged Multiset Lookup:
||| Splices staged multiset and queries multiplicity at the object level.
public export
stagedLookupBox : Eq a => a -> Lift (Box a) -> BoxInt
stagedLookupBox x qb = lookupBox x (splice qb)

||| QTT 0 Erased Proof Witness: Staged Multiset Union Invariant
public export
0 prfStagedMultisetUnion : Eq a => (b1 : Box a) -> (b2 : Box a) ->
                          splice (stagedMultisetUnion (quote b1) (quote b2)) = unionBox b1 b2
prfStagedMultisetUnion _ _ = Refl

||| 2LTT Staged Multiset Consolidation:
||| Consolidates and sums duplicate tokens at compile time (U_1),
||| emitting an irreducible, canonical multiset at Level 0 (U_0).
public export
stagedConsolidateBox : Eq a => Lift (Box a) -> Lift (Box a)
stagedConsolidateBox qb = quote (consolidateBox (splice qb))

||| 2LTT Staged Charge Annihilation:
||| Annihilates opposite sign discrete tokens (Pos and Neg) during staging,
||| ensuring zero-weight tokens never allocate space in the object program.
public export
stagedAnnihilateBox : Eq a => Lift (Box a) -> Lift (Box a)
stagedAnnihilateBox qb = quote (consolidateBox (splice qb))

||| QTT 0 Erased Proof Witness: Staged Consolidation Invariant
public export
0 prfStagedConsolidateInvariant : Eq a => (b : Box a) ->
                                 splice (stagedConsolidateBox (quote b)) = consolidateBox b
prfStagedConsolidateInvariant _ = Refl

------------------------------------------------------------------------
-- 5. LINEAR 2LTT (LQTT) STAGED CODE MODALITY
------------------------------------------------------------------------

||| Linear 2LTT Staged Code Modality:
||| Encapsulates a linear runtime object term that must be consumed exactly once.
public export
data LinearLift : Type -> Type where
  MkLinearLift : (1 val : a) -> LinearLift a

||| Linear quote: lifts an object term into a LinearLift container.
public export
quoteLinear : (1 x : a) -> LinearLift a
quoteLinear x = MkLinearLift x

||| Linear splice: extracts the underlying linear object term with multiplicity 1.
public export
spliceLinear : (1 q : LinearLift a) -> a
spliceLinear (MkLinearLift x) = x

||| QTT 0 Erased Proof Witness: Linear Staging Round-Trip Invariance
public export
0 prfLinearStagingRoundtrip : (x : a) -> spliceLinear (quoteLinear x) = x
prfLinearStagingRoundtrip _ = Refl

-- Note: LinearStatePair is canonically defined in Stage0.OnSeq.FusedStream


||| 2LTT Staged Linear Transition:
||| Lifts static configuration into a compile-time specialized transition table
||| that acts on runtime linear state with exact linear multiplicity 1.
public export
StagedLinearTransition : Type -> Type -> Type -> Type
StagedLinearTransition cfg s obs = Lift cfg -> (1 state : s) -> LinearStatePair s obs

||| Folds a LinearStream with an accumulator and returns the linear final state paired with the accumulator.
public export
foldLinearStream : (fuel : Nat) -> (acc -> a -> acc) -> acc -> (1 str : LinearStream s a) -> LinearStatePair s acc
foldLinearStream Z _ acc (MkLinearStream _ seed) = MkLStatePair seed acc
foldLinearStream (S f) fn acc (MkLinearStream step seed) = case step seed of
  DoneL st => MkLStatePair st acc
  SkipL st => foldLinearStream f fn acc (MkLinearStream step st)
  YieldL x st => foldLinearStream f fn (fn acc x) (MkLinearStream step st)

------------------------------------------------------------------------
-- 5B. 2LTT STAGED STREAM FUSION (PHASE 4)
------------------------------------------------------------------------

||| A 2LTT Staged Stream: represents a stream pipeline where step functions and fusion
||| occur at the static meta level (Level 1), producing zero-overhead runtime iteration (Level 0).
public export
data StagedStream : Type -> Type where
  MkStagedStream : {0 s : Type} -> (init : Lift s) -> (step : s -> Step s a) -> StagedStream a

||| Lifts a FusedStream into a StagedStream.
public export
quoteFusedStream : FusedStream a -> StagedStream a
quoteFusedStream (MkStream next seed) =
  MkStagedStream (quote seed) next

||| Folds a StagedStream with static structural fuel.
public export
stagedFoldStream : (fuel : Nat) -> (acc -> a -> acc) -> acc -> StagedStream a -> acc
stagedFoldStream Z _ initAcc _ = initAcc
stagedFoldStream (S f) fn initAcc (MkStagedStream {s} init step) =
  go f initAcc (splice init)
  where
    go : Nat -> acc -> s -> acc
    go Z curr _ = curr
    go (S k) curr st = case step st of
      Done => curr
      Skip nextSt => go k curr nextSt
      Yield x nextSt => go k (fn curr x) nextSt

||| Deforested map over a StagedStream fusing statically at Level 1.
public export
mapStagedStream : (a -> b) -> StagedStream a -> StagedStream b
mapStagedStream f (MkStagedStream init step) =
  MkStagedStream init (\st => case step st of
    Done => Done
    Skip nextSt => Skip nextSt
    Yield x nextSt => Yield (f x) nextSt)

||| Deforested filter over a StagedStream fusing statically at Level 1.
public export
filterStagedStream : (a -> Bool) -> StagedStream a -> StagedStream a
filterStagedStream p (MkStagedStream init step) =
  MkStagedStream init (\st => case step st of
    Done => Done
    Skip nextSt => Skip nextSt
    Yield x nextSt => if p x then Yield x nextSt else Skip nextSt)


------------------------------------------------------------------------
-- 6. GENERALIZED DIMENSION-INDEXED N x N STAGED MATRIX ENGINE
------------------------------------------------------------------------

||| Dot product of two statically dimensioned vectors.
public export
dotProductVect : Num a => Vect n a -> Vect n a -> a
dotProductVect [] [] = 0
dotProductVect (x :: xs) (y :: ys) = (x * y) + dotProductVect xs ys

||| Staged matrix-vector contraction: contracts an N x N matrix with an N-vector.
public export
stagedUnrollMatVec : Num a => Vect n (Vect n a) -> Vect n a -> Vect n a
stagedUnrollMatVec mat v = map (\row => dotProductVect row v) mat

||| Staged matrix multiplication: multiplies two N x N matrices by unrolling dot products.
public export
stagedUnrollMatMul : Num a => {n : Nat} -> Vect n (Vect n a) -> Vect n (Vect n a) -> Vect n (Vect n a)
stagedUnrollMatMul matA matB =
  let colsB = transpose matB
  in map (\rowA => map (\colB => dotProductVect rowA colB) colsB) matA

||| Identity matrix of dimension n.
public export
stagedIdentityMat : Num a => (n : Nat) -> Vect n (Vect n a)
stagedIdentityMat Z = []
stagedIdentityMat (S k) =
  (1 :: replicate k 0) :: map (0 ::) (stagedIdentityMat k)

||| Fast repeated squaring for statically dimensioned N x N matrices with structural fuel.
public export
stagedFastMatPower : Num a => (fuel : Nat) -> {n : Nat} -> Vect n (Vect n a) -> Nat -> Vect n (Vect n a)
stagedFastMatPower Z mat _ = stagedIdentityMat n
stagedFastMatPower (S _) mat Z = stagedIdentityMat n
stagedFastMatPower (S _) mat (S Z) = mat
stagedFastMatPower (S f) mat exp =
  let (half, isOdd) = natHalfAndOdd exp
      halfMat = stagedFastMatPower f mat half
      squared = stagedUnrollMatMul halfMat halfMat
  in if isOdd
       then stagedUnrollMatMul mat squared
       else squared

------------------------------------------------------------------------
-- 7. 2LTT STAGED COORDINATE CELL & CARRIER OPERATIONS
------------------------------------------------------------------------

||| 2LTT Staged Unrolled Coordinate Addition for arbitrary static dimensions.
||| Emits branchless, flat Level 1 primitive additions without AVL tree traversal for D in {1, 2, 3, 4}.
public export
stagedUnrollAdd : (dim : Nat) -> Lift (CoordCell dim) -> Lift (CoordCell dim) -> Lift (CoordCell dim)
stagedUnrollAdd (S Z) qc1 qc2 =
  quote (let c1 = splice qc1; c2 = splice qc2
         in mkCell1 (coordAxis 0 c1 + coordAxis 0 c2))
stagedUnrollAdd (S (S Z)) qc1 qc2 =
  quote (let c1 = splice qc1; c2 = splice qc2
         in mkCell2 (coordAxis 0 c1 + coordAxis 0 c2)
                    (coordAxis 1 c1 + coordAxis 1 c2))
stagedUnrollAdd (S (S (S Z))) qc1 qc2 =
  quote (let c1 = splice qc1; c2 = splice qc2
         in mkCell3 (coordAxis 0 c1 + coordAxis 0 c2)
                    (coordAxis 1 c1 + coordAxis 1 c2)
                    (coordAxis 2 c1 + coordAxis 2 c2))
stagedUnrollAdd (S (S (S (S Z)))) qc1 qc2 =
  quote (let c1 = splice qc1; c2 = splice qc2
         in mkCell4 (coordAxis 0 c1 + coordAxis 0 c2)
                    (coordAxis 1 c1 + coordAxis 1 c2)
                    (coordAxis 2 c1 + coordAxis 2 c2)
                    (coordAxis 3 c1 + coordAxis 3 c2))
stagedUnrollAdd _ qc1 qc2 =
  quote (addCoordCell (splice qc1) (splice qc2))

||| 2LTT Staged Unrolled Coordinate Hadamard Multiplication.
public export
stagedUnrollMul : (dim : Nat) -> Lift (CoordCell dim) -> Lift (CoordCell dim) -> Lift (CoordCell dim)
stagedUnrollMul (S Z) qc1 qc2 =
  quote (let c1 = splice qc1; c2 = splice qc2
         in mkCell1 (coordAxis 0 c1 * coordAxis 0 c2))
stagedUnrollMul (S (S Z)) qc1 qc2 =
  quote (let c1 = splice qc1; c2 = splice qc2
         in mkCell2 (coordAxis 0 c1 * coordAxis 0 c2)
                    (coordAxis 1 c1 * coordAxis 1 c2))
stagedUnrollMul (S (S (S Z))) qc1 qc2 =
  quote (let c1 = splice qc1; c2 = splice qc2
         in mkCell3 (coordAxis 0 c1 * coordAxis 0 c2)
                    (coordAxis 1 c1 * coordAxis 1 c2)
                    (coordAxis 2 c1 * coordAxis 2 c2))
stagedUnrollMul (S (S (S (S Z)))) qc1 qc2 =
  quote (let c1 = splice qc1; c2 = splice qc2
         in mkCell4 (coordAxis 0 c1 * coordAxis 0 c2)
                    (coordAxis 1 c1 * coordAxis 1 c2)
                    (coordAxis 2 c1 * coordAxis 2 c2)
                    (coordAxis 3 c1 * coordAxis 3 c2))
stagedUnrollMul _ qc1 qc2 =
  quote (mulCoordCell (splice qc1) (splice qc2))

||| 2LTT Staged Unrolled Coordinate Scalar Multiplication.
public export
stagedUnrollScale : (dim : Nat) -> Nat -> Lift (CoordCell dim) -> Lift (CoordCell dim)
stagedUnrollScale (S Z) k qc =
  quote (let c = splice qc in mkCell1 (k * coordAxis 0 c))
stagedUnrollScale (S (S Z)) k qc =
  quote (let c = splice qc in mkCell2 (k * coordAxis 0 c) (k * coordAxis 1 c))
stagedUnrollScale (S (S (S Z))) k qc =
  quote (let c = splice qc in mkCell3 (k * coordAxis 0 c) (k * coordAxis 1 c) (k * coordAxis 2 c))
stagedUnrollScale (S (S (S (S Z)))) k qc =
  quote (let c = splice qc in mkCell4 (k * coordAxis 0 c) (k * coordAxis 1 c) (k * coordAxis 2 c) (k * coordAxis 3 c))
stagedUnrollScale _ k qc =
  quote (scaleCoordCell k (splice qc))

||| 2LTT Staged Unrolled Coordinate Subtraction.
public export
stagedUnrollMinus : (dim : Nat) -> Lift (CoordCell dim) -> Lift (CoordCell dim) -> Lift (CoordCell dim)
stagedUnrollMinus (S Z) qc1 qc2 =
  quote (let c1 = splice qc1; c2 = splice qc2
         in mkCell1 (minus (coordAxis 0 c1) (coordAxis 0 c2)))
stagedUnrollMinus (S (S Z)) qc1 qc2 =
  quote (let c1 = splice qc1; c2 = splice qc2
         in mkCell2 (minus (coordAxis 0 c1) (coordAxis 0 c2))
                    (minus (coordAxis 1 c1) (coordAxis 1 c2)))
stagedUnrollMinus (S (S (S Z))) qc1 qc2 =
  quote (let c1 = splice qc1; c2 = splice qc2
         in mkCell3 (minus (coordAxis 0 c1) (coordAxis 0 c2))
                    (minus (coordAxis 1 c1) (coordAxis 1 c2))
                    (minus (coordAxis 2 c1) (coordAxis 2 c2)))
stagedUnrollMinus (S (S (S (S Z)))) qc1 qc2 =
  quote (let c1 = splice qc1; c2 = splice qc2
         in mkCell4 (minus (coordAxis 0 c1) (coordAxis 0 c2))
                    (minus (coordAxis 1 c1) (coordAxis 1 c2))
                    (minus (coordAxis 2 c1) (coordAxis 2 c2))
                    (minus (coordAxis 3 c1) (coordAxis 3 c2)))
stagedUnrollMinus _ qc1 qc2 =
  quote (minusCoordCell (splice qc1) (splice qc2))

||| 2LTT Staged Unrolled Inner / Dot Product (c1 · c2).
public export
stagedUnrollDot : (dim : Nat) -> Lift (CoordCell dim) -> Lift (CoordCell dim) -> Lift Nat
stagedUnrollDot (S Z) qc1 qc2 =
  quote (let c1 = splice qc1; c2 = splice qc2
         in coordAxis 0 c1 * coordAxis 0 c2)
stagedUnrollDot (S (S Z)) qc1 qc2 =
  quote (let c1 = splice qc1; c2 = splice qc2
         in (coordAxis 0 c1 * coordAxis 0 c2) +
            (coordAxis 1 c1 * coordAxis 1 c2))
stagedUnrollDot (S (S (S Z))) qc1 qc2 =
  quote (let c1 = splice qc1; c2 = splice qc2
         in (coordAxis 0 c1 * coordAxis 0 c2) +
            (coordAxis 1 c1 * coordAxis 1 c2) +
            (coordAxis 2 c1 * coordAxis 2 c2))
stagedUnrollDot (S (S (S (S Z)))) qc1 qc2 =
  quote (let c1 = splice qc1; c2 = splice qc2
         in (coordAxis 0 c1 * coordAxis 0 c2) +
            (coordAxis 1 c1 * coordAxis 1 c2) +
            (coordAxis 2 c1 * coordAxis 2 c2) +
            (coordAxis 3 c1 * coordAxis 3 c2))
stagedUnrollDot _ qc1 qc2 =
  quote (dotCoordCell (splice qc1) (splice qc2))

||| 2LTT Staged Unrolled Wildberger Quadrance Q(c) = c · c.
public export
stagedUnrollQuadrance : (dim : Nat) -> Lift (CoordCell dim) -> Lift Nat
stagedUnrollQuadrance (S Z) qc =
  quote (let c = splice qc; x0 = coordAxis 0 c in x0 * x0)
stagedUnrollQuadrance (S (S Z)) qc =
  quote (let c = splice qc; x0 = coordAxis 0 c; x1 = coordAxis 1 c
         in (x0 * x0) + (x1 * x1))
stagedUnrollQuadrance (S (S (S Z))) qc =
  quote (let c = splice qc; x0 = coordAxis 0 c; x1 = coordAxis 1 c; x2 = coordAxis 2 c
         in (x0 * x0) + (x1 * x1) + (x2 * x2))
stagedUnrollQuadrance (S (S (S (S Z)))) qc =
  quote (let c = splice qc
             x0 = coordAxis 0 c; x1 = coordAxis 1 c
             x2 = coordAxis 2 c; x3 = coordAxis 3 c
         in (x0 * x0) + (x1 * x1) + (x2 * x2) + (x3 * x3))
stagedUnrollQuadrance _ qc =
  quote (quadranceCoordCell (splice qc))

------------------------------------------------------------------------
-- 8. 2LTT POLYMORPHIC STAGED COORDINATE CELL INTERFACE
------------------------------------------------------------------------

||| Overloaded 2LTT staging interface for dimension-unrolled coordinate cells.
public export
interface StagedCoordCell (dim : Nat) where
  stagedAddCell   : Lift (CoordCell dim) -> Lift (CoordCell dim) -> Lift (CoordCell dim)
  stagedMulCell   : Lift (CoordCell dim) -> Lift (CoordCell dim) -> Lift (CoordCell dim)
  stagedScaleCell : Nat -> Lift (CoordCell dim) -> Lift (CoordCell dim)
  stagedMinusCell : Lift (CoordCell dim) -> Lift (CoordCell dim) -> Lift (CoordCell dim)
  stagedDotCell   : Lift (CoordCell dim) -> Lift (CoordCell dim) -> Lift Nat
  stagedQuadCell  : Lift (CoordCell dim) -> Lift Nat

public export
{dim : Nat} -> StagedCoordCell dim where
  stagedAddCell   = stagedUnrollAdd dim
  stagedMulCell   = stagedUnrollMul dim
  stagedScaleCell = stagedUnrollScale dim
  stagedMinusCell = stagedUnrollMinus dim
  stagedDotCell   = stagedUnrollDot dim
  stagedQuadCell  = stagedUnrollQuadrance dim

-- Canonical Backwards-Compatible Staging Aliases
public export
stagedAddCoordCell : {dim : Nat} -> Lift (CoordCell dim) -> Lift (CoordCell dim) -> Lift (CoordCell dim)
stagedAddCoordCell {dim} = stagedUnrollAdd dim

public export
stagedMulCoordCell : {dim : Nat} -> Lift (CoordCell dim) -> Lift (CoordCell dim) -> Lift (CoordCell dim)
stagedMulCoordCell {dim} = stagedUnrollMul dim

public export
stagedScaleCoordCell : {dim : Nat} -> Nat -> Lift (CoordCell dim) -> Lift (CoordCell dim)
stagedScaleCoordCell {dim} = stagedUnrollScale dim

public export
stagedDotCoordCell : {dim : Nat} -> Lift (CoordCell dim) -> Lift (CoordCell dim) -> Lift Nat
stagedDotCoordCell {dim} = stagedUnrollDot dim

public export
stagedQuadranceCoordCell : {dim : Nat} -> Lift (CoordCell dim) -> Lift Nat
stagedQuadranceCoordCell {dim} = stagedUnrollQuadrance dim

------------------------------------------------------------------------
-- 9. 2LTT DEFINITIONAL EVALUATION INVERSE THEOREMS
------------------------------------------------------------------------

public export
0 prfStagedUnrollAdd1D : (c1, c2 : CoordCell 1) ->
  splice (stagedUnrollAdd 1 (quote c1) (quote c2)) = mkCell1 (coordAxis 0 c1 + coordAxis 0 c2)
prfStagedUnrollAdd1D _ _ = Refl

public export
0 prfStagedUnrollAdd2D : (c1, c2 : CoordCell 2) ->
  splice (stagedUnrollAdd 2 (quote c1) (quote c2)) = mkCell2 (coordAxis 0 c1 + coordAxis 0 c2) (coordAxis 1 c1 + coordAxis 1 c2)
prfStagedUnrollAdd2D _ _ = Refl

public export
0 prfStagedUnrollAdd3D : (c1, c2 : CoordCell 3) ->
  splice (stagedUnrollAdd 3 (quote c1) (quote c2)) = mkCell3 (coordAxis 0 c1 + coordAxis 0 c2) (coordAxis 1 c1 + coordAxis 1 c2) (coordAxis 2 c1 + coordAxis 2 c2)
prfStagedUnrollAdd3D _ _ = Refl

public export
0 prfStagedUnrollAdd4D : (c1, c2 : CoordCell 4) ->
  splice (stagedUnrollAdd 4 (quote c1) (quote c2)) = mkCell4 (coordAxis 0 c1 + coordAxis 0 c2) (coordAxis 1 c1 + coordAxis 1 c2) (coordAxis 2 c1 + coordAxis 2 c2) (coordAxis 3 c1 + coordAxis 3 c2)
prfStagedUnrollAdd4D _ _ = Refl

public export
0 prfStagedUnrollDot2D : (c1, c2 : CoordCell 2) ->
  splice (stagedUnrollDot 2 (quote c1) (quote c2)) = (coordAxis 0 c1 * coordAxis 0 c2) + (coordAxis 1 c1 * coordAxis 1 c2)
prfStagedUnrollDot2D _ _ = Refl

public export
0 prfStagedUnrollQuad2D : (c : CoordCell 2) ->
  splice (stagedUnrollQuadrance 2 (quote c)) = (coordAxis 0 c * coordAxis 0 c) + (coordAxis 1 c * coordAxis 1 c)
prfStagedUnrollQuad2D _ = Refl

------------------------------------------------------------------------
-- 10. 2LTT STAGED DIVISOR & COMPANION SPREAD MATRIX PIPELINES
------------------------------------------------------------------------

||| 2LTT Staged Divisor Factorization: evaluates divisor decomposition at compile-time (Level 1)
||| delivering a flat, unrolled list of harmonic divisors for runtime Level 0 execution without division.
public export
stagedDivisors : (n : Nat) -> Lift (List Nat)
stagedDivisors n = quote (runFueledStreamNat (S n) (divisorStream n))

||| 2LTT Staged 2x2 companion spread matrix power unrolled at compile time.
||| M(s) = [ [2 - 4s, -1], [1, 0] ].
public export
stagedCompanionSpreadPower : (fuel : Nat) -> (power : Nat) -> (s : BoxInt) -> Lift (Vect 2 (Vect 2 BoxInt))
stagedCompanionSpreadPower fuel power s =
  let c11 = subBox (intToBoxInt 2) (mulBox (intToBoxInt 4) s)
      mat : Vect 2 (Vect 2 BoxInt) =
        [ [c11, intToBoxInt (-1)]
        , [intToBoxInt 1, intToBoxInt 0]
        ]
  in quote (stagedFastMatPower fuel mat power)

||| 2LTT Definitional Inverse Law: Splicing staged divisors definitionally equals direct evaluation.
public export
0 prfStagedDivisorsDefinitional : (n : Nat) ->
  splice (stagedDivisors n) = runFueledStreamNat (S n) (divisorStream n)
prfStagedDivisorsDefinitional _ = Refl

||| 2LTT Definitional Inverse Law: Splicing staged companion power definitionally equals direct evaluation.
public export
0 prfStagedCompanionSpreadPowerDefinitional : (fuel, p : Nat) -> (s : BoxInt) ->
  splice (stagedCompanionSpreadPower fuel p s) =
    stagedFastMatPower fuel [ [subBox (intToBoxInt 2) (mulBox (intToBoxInt 4) s), intToBoxInt (-1)]
                            , [intToBoxInt 1, intToBoxInt 0] ] p
prfStagedCompanionSpreadPowerDefinitional _ _ _ = Refl
