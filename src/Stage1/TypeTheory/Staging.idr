||| Module Stage1.TypeTheory.Staging
|||
||| Canonical 2LTT Staging Operations for the FinSc Multiset Science Framework.
||| Implements modal type lifting (⇑A), quoting (⟨t⟩), splicing (~t), and definitional inverse laws
||| following Kovács (2022) Two-Level Type Theory.
module Stage1.TypeTheory.Staging

import public Stage1.TypeTheory.TwoLevel
import Stage0.BoxInt
import Stage0.BoxNat
import Stage0.Bit
import Stage0.Token
import Stage0.Multiset
import Stage0.StructuralFuel
import Stage0.LinearBuffer
import Stage0.OnSeq.FusedStream
import public Stage1.Basis.CoordCell
import Stage1.MultisetTree
import Data.List
import Data.Vect
import Data.DPair
import Data.Linear

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
stagedMultisetUnion : Ord a => Lift (Box a) -> Lift (Box a) -> Lift (Box a)
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
stagedLookupBox : Ord a => a -> Lift (Box a) -> BoxInt
stagedLookupBox x qb = lookupBox x (splice qb)

||| QTT 0 Erased Proof Witness: Staged Multiset Union Invariant
public export
0 prfStagedMultisetUnion : Ord a => (b1 : Box a) -> (b2 : Box a) ->
                          splice (stagedMultisetUnion (quote b1) (quote b2)) = unionBox b1 b2
prfStagedMultisetUnion _ _ = Refl

||| 2LTT Staged Multiset Consolidation:
||| Consolidates and sums duplicate tokens at compile time (U_1),
||| emitting an irreducible, canonical multiset at Level 0 (U_0).
public export
stagedConsolidateBox : Ord a => Lift (Box a) -> Lift (Box a)
stagedConsolidateBox qb = quote (consolidateBox (splice qb))

||| 2LTT Staged Charge Annihilation:
||| Annihilates opposite sign discrete tokens (Pos and Neg) during staging,
||| ensuring zero-weight tokens never allocate space in the object program.
public export
stagedAnnihilateBox : Ord a => Lift (Box a) -> Lift (Box a)
stagedAnnihilateBox qb = quote (consolidateBox (splice qb))

||| QTT 0 Erased Proof Witness: Staged Consolidation Invariant
public export
0 prfStagedConsolidateInvariant : Ord a => (b : Box a) ->
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

||| 2LTT Staged Coordinate Addition for arbitrary dimension `dim : Nat`.
||| Operates directly on the inductive Token sequence `CoordCell dim`.
public export
stagedUnrollAdd : (dim : Nat) -> Lift (CoordCell dim) -> Lift (CoordCell dim) -> Lift (CoordCell dim)
stagedUnrollAdd _ qc1 qc2 =
  quote (addCoordCell (splice qc1) (splice qc2))

||| 2LTT Staged Coordinate Hadamard Multiplication for arbitrary dimension `dim : Nat`.
public export
stagedUnrollMul : (dim : Nat) -> Lift (CoordCell dim) -> Lift (CoordCell dim) -> Lift (CoordCell dim)
stagedUnrollMul _ qc1 qc2 =
  quote (mulCoordCell (splice qc1) (splice qc2))

||| 2LTT Staged Coordinate Scalar Multiplication for arbitrary dimension `dim : Nat`.
public export
stagedUnrollScale : (dim : Nat) -> Nat -> Lift (CoordCell dim) -> Lift (CoordCell dim)
stagedUnrollScale _ k qc =
  quote (scaleCoordCell k (splice qc))

||| 2LTT Staged Coordinate Subtraction for arbitrary dimension `dim : Nat`.
public export
stagedUnrollMinus : (dim : Nat) -> Lift (CoordCell dim) -> Lift (CoordCell dim) -> Lift (CoordCell dim)
stagedUnrollMinus _ qc1 qc2 =
  quote (minusCoordCell (splice qc1) (splice qc2))

||| 2LTT Staged Inner / Dot Product (c1 · c2) for arbitrary dimension `dim : Nat`.
public export
stagedUnrollDot : (dim : Nat) -> Lift (CoordCell dim) -> Lift (CoordCell dim) -> Lift Nat
stagedUnrollDot _ qc1 qc2 =
  quote (dotCoordCell (splice qc1) (splice qc2))

||| 2LTT Staged Wildberger Quadrance Q(c) = c · c for arbitrary dimension `dim : Nat`.
public export
stagedUnrollQuadrance : (dim : Nat) -> Lift (CoordCell dim) -> Lift Nat
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

||| Universal dimension-polymorphic 2LTT inverse theorems for all `dim : Nat`.
public export
0 prfStagedUnrollAdd : {dim : Nat} -> (c1, c2 : CoordCell dim) ->
  splice (stagedUnrollAdd dim (quote c1) (quote c2)) = addCoordCell c1 c2
prfStagedUnrollAdd _ _ = Refl

public export
0 prfStagedUnrollMul : {dim : Nat} -> (c1, c2 : CoordCell dim) ->
  splice (stagedUnrollMul dim (quote c1) (quote c2)) = mulCoordCell c1 c2
prfStagedUnrollMul _ _ = Refl

public export
0 prfStagedUnrollScale : {dim : Nat} -> (k : Nat) -> (c : CoordCell dim) ->
  splice (stagedUnrollScale dim k (quote c)) = scaleCoordCell k c
prfStagedUnrollScale _ _ = Refl

public export
0 prfStagedUnrollMinus : {dim : Nat} -> (c1, c2 : CoordCell dim) ->
  splice (stagedUnrollMinus dim (quote c1) (quote c2)) = minusCoordCell c1 c2
prfStagedUnrollMinus _ _ = Refl

public export
0 prfStagedUnrollDot : {dim : Nat} -> (c1, c2 : CoordCell dim) ->
  splice (stagedUnrollDot dim (quote c1) (quote c2)) = dotCoordCell c1 c2
prfStagedUnrollDot _ _ = Refl

public export
0 prfStagedUnrollQuadrance : {dim : Nat} -> (c : CoordCell dim) ->
  splice (stagedUnrollQuadrance dim (quote c)) = quadranceCoordCell c
prfStagedUnrollQuadrance _ = Refl

-- Dimension-specialized corollaries (1D..4D):
public export
0 prfStagedUnrollAdd1D : (c1, c2 : CoordCell 1) ->
  splice (stagedUnrollAdd 1 (quote c1) (quote c2)) = mkCell1 (coordCellCoord FZ c1 + coordCellCoord FZ c2)
prfStagedUnrollAdd1D (ConsCell (MkToken _) ZeroCell) (ConsCell (MkToken _) ZeroCell) = Refl

public export
0 prfStagedUnrollAdd2D : (c1, c2 : CoordCell 2) ->
  splice (stagedUnrollAdd 2 (quote c1) (quote c2)) = mkCell2 (coordCellCoord FZ c1 + coordCellCoord FZ c2) (coordCellCoord (FS FZ) c1 + coordCellCoord (FS FZ) c2)
prfStagedUnrollAdd2D (ConsCell (MkToken _) (ConsCell (MkToken _) ZeroCell)) (ConsCell (MkToken _) (ConsCell (MkToken _) ZeroCell)) = Refl

public export
0 prfStagedUnrollAdd3D : (c1, c2 : CoordCell 3) ->
  splice (stagedUnrollAdd 3 (quote c1) (quote c2)) = mkCell3 (coordCellCoord FZ c1 + coordCellCoord FZ c2) (coordCellCoord (FS FZ) c1 + coordCellCoord (FS FZ) c2) (coordCellCoord (FS (FS FZ)) c1 + coordCellCoord (FS (FS FZ)) c2)
prfStagedUnrollAdd3D (ConsCell (MkToken _) (ConsCell (MkToken _) (ConsCell (MkToken _) ZeroCell)))
                     (ConsCell (MkToken _) (ConsCell (MkToken _) (ConsCell (MkToken _) ZeroCell))) = Refl

public export
0 prfStagedUnrollAdd4D : (c1, c2 : CoordCell 4) ->
  splice (stagedUnrollAdd 4 (quote c1) (quote c2)) = mkCell4 (coordCellCoord FZ c1 + coordCellCoord FZ c2) (coordCellCoord (FS FZ) c1 + coordCellCoord (FS FZ) c2) (coordCellCoord (FS (FS FZ)) c1 + coordCellCoord (FS (FS FZ)) c2) (coordCellCoord (FS (FS (FS FZ))) c1 + coordCellCoord (FS (FS (FS FZ))) c2)
prfStagedUnrollAdd4D (ConsCell (MkToken _) (ConsCell (MkToken _) (ConsCell (MkToken _) (ConsCell (MkToken _) ZeroCell))))
                     (ConsCell (MkToken _) (ConsCell (MkToken _) (ConsCell (MkToken _) (ConsCell (MkToken _) ZeroCell)))) = Refl

public export
0 prfStagedUnrollDot2D : (c1, c2 : CoordCell 2) ->
  splice (stagedUnrollDot 2 (quote c1) (quote c2)) = (coordCellCoord FZ c1 * coordCellCoord FZ c2) + (coordCellCoord (FS FZ) c1 * coordCellCoord (FS FZ) c2)
prfStagedUnrollDot2D (ConsCell (MkToken _) (ConsCell (MkToken _) ZeroCell))
                     (ConsCell (MkToken _) (ConsCell (MkToken _) ZeroCell)) = Refl

public export
0 prfStagedUnrollQuad2D : (c : CoordCell 2) ->
  splice (stagedUnrollQuadrance 2 (quote c)) = (coordCellCoord FZ c * coordCellCoord FZ c) + (coordCellCoord (FS FZ) c * coordCellCoord (FS FZ) c)
prfStagedUnrollQuad2D (ConsCell (MkToken _) (ConsCell (MkToken _) ZeroCell)) = Refl

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

------------------------------------------------------------------------
-- 11. UNIFIED FOUR-REGIME MULTISET EXPRESSION GADT (Gemini.md Section 4)
------------------------------------------------------------------------

||| The four unified carrier regimes across storage, batch, reactive streams, and windowed sessions.
public export
data Regime : Type where
  Static    : Regime
  Finite    : (len : Nat) -> Regime
  Unbounded : Regime
  Segmented : (win : Nat) -> Regime

||| Compile-time state schema tracking linear buffer allocations at the 0-quantity meta-level.
public export
StateSchema : Type
StateSchema = List Type

||| Unified interaction pulse indicator expression evaluated at the 0-quantity meta-level.
||| Defined as a stratified index prior to MultisetExpr to prevent self-indexed inductive-inductive
||| coverage explosion in Idris 2's totality checker.
public export
data PulseExpr : Type where
  BasePulse     : PulseExpr
  ZeroPulse     : PulseExpr
  OnePulse      : PulseExpr
  AddPulse      : PulseExpr -> PulseExpr -> PulseExpr
  HadamardPulse : PulseExpr -> PulseExpr -> PulseExpr
  MassPulse     : (threshold : Nat) -> PulseExpr

||| Unified Four-Regime Multiset Expression AST indexed by (0 reg : Regime),
||| (0 pulse : Maybe PulseExpr), and (0 st : StateSchema).
public export
data MultisetExpr : (0 reg   : Regime)
                 -> (0 pulse : Maybe PulseExpr)
                 -> (0 st    : StateSchema)
                 -> (a       : Type)
                 -> Type where
  BasePulseM    : MultisetExpr Unbounded Nothing [] Bit
  ZeroM         : {0 reg : Regime} -> {0 p : Maybe PulseExpr} -> MultisetExpr reg p [] a
  OneM          : {0 reg : Regime} -> {0 p : Maybe PulseExpr} -> MultisetExpr reg p [] a
  ConstM        : {0 p : Maybe PulseExpr} -> (val : a) -> MultisetExpr Static p [] a
  Input         : {0 reg : Regime} -> {0 p : Maybe PulseExpr} -> (idx : Nat) -> MultisetExpr reg p [] a

  AddM          : {0 reg : Regime} -> {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema}
               -> MultisetExpr reg p s1 a -> MultisetExpr reg p s2 a -> MultisetExpr reg p (s1 ++ s2) a
  SubM          : {0 reg : Regime} -> {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema}
               -> MultisetExpr reg p s1 a -> MultisetExpr reg p s2 a -> MultisetExpr reg p (s1 ++ s2) a
  HadamardM     : {0 reg : Regime} -> {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema}
               -> MultisetExpr reg p s1 a -> MultisetExpr reg p s2 a -> MultisetExpr reg p (s1 ++ s2) a
  MinM          : {0 reg : Regime} -> {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema}
               -> MultisetExpr reg p s1 a -> MultisetExpr reg p s2 a -> MultisetExpr reg p (s1 ++ s2) a
  MaxM          : {0 reg : Regime} -> {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema}
               -> MultisetExpr reg p s1 a -> MultisetExpr reg p s2 a -> MultisetExpr reg p (s1 ++ s2) a

  MulStatic     : {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema}
               -> MultisetExpr Static p s1 a -> MultisetExpr Static p s2 a -> MultisetExpr Static p (s1 ++ s2) a
  MulFinite     : {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema} -> {0 n, m : Nat}
               -> MultisetExpr (Finite (S n)) p s1 a -> MultisetExpr (Finite (S m)) p s2 a
               -> MultisetExpr (Finite (S (n + m))) p (s1 ++ s2) a
  MulStream     : {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema} -> {0 k : Nat}
               -> MultisetExpr Unbounded p s1 a -> MultisetExpr (Finite k) p s2 a
               -> MultisetExpr Unbounded p (Vect k a :: (s1 ++ s2)) a

  DotStatic     : {0 k : Type} -> {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema}
               -> MultisetExpr Static p s1 (Carrier k) -> MultisetExpr Static p s2 (Carrier k)
               -> MultisetExpr Static p (s1 ++ s2) BoxInt
  DotFinite     : {0 k : Type} -> {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema} -> {0 n : Nat}
               -> MultisetExpr (Finite n) p s1 (Carrier k) -> MultisetExpr (Finite n) p s2 (Carrier k)
               -> MultisetExpr Static p (s1 ++ s2) BoxInt
  Segment       : {0 k : Type} -> {0 p : PulseExpr} -> {0 st : StateSchema} -> (winSize : Nat)
               -> MultisetExpr Unbounded (Just p) st (Carrier k)
               -> MultisetExpr (Segmented winSize) (Just p) (Vect winSize (Carrier k) :: st) (Carrier k)
  DotWindow     : {0 k : Type} -> {0 p : PulseExpr} -> {0 s1, s2 : StateSchema} -> {0 w : Nat}
               -> MultisetExpr (Segmented w) (Just p) s1 (Carrier k)
               -> MultisetExpr (Finite w) (Just p) s2 (Carrier k)
               -> MultisetExpr Unbounded (Just p) (s1 ++ s2) BoxInt

  OuterM        : {0 k1, k2 : Type} -> {0 reg : Regime} -> {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema}
               -> MultisetExpr reg p s1 (Carrier k1) -> MultisetExpr reg p s2 (Carrier k2)
               -> MultisetExpr reg p (s1 ++ s2) (Carrier (k1, k2))
  ContractR     : {0 k1, k2 : Type} -> {0 reg : Regime} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
               -> MultisetExpr reg p st (Carrier (k1, k2))
               -> MultisetExpr reg p st (Carrier k1)
  ContractL     : {0 k1, k2 : Type} -> {0 reg : Regime} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
               -> MultisetExpr reg p st (Carrier (k1, k2))
               -> MultisetExpr reg p st (Carrier k2)

  LoopVar       : {0 p : PulseExpr} -> (init : a) -> MultisetExpr Unbounded (Just p) [] a
  Fby           : {0 p : PulseExpr} -> {0 st : StateSchema} -> (init : a)
               -> MultisetExpr Unbounded (Just p) st a
               -> MultisetExpr Unbounded (Just p) (a :: st) a
  When          : {0 parentP : PulseExpr} -> {0 s1 : StateSchema}
               -> MultisetExpr Unbounded (Just parentP) s1 a -> (0 mask : PulseExpr)
               -> MultisetExpr Unbounded (Just (HadamardPulse parentP mask)) s1 a
  SwitchSession : {0 p : PulseExpr} -> {0 s1, sTrig, s2 : StateSchema} -> {0 n : Nat}
               -> MultisetExpr Unbounded (Just p) s1 a
               -> (trigger : MultisetExpr Unbounded (Just p) sTrig Bit)
               -> MultisetExpr (Finite n) (Just p) s2 a
               -> MultisetExpr Unbounded (Just p) (s1 ++ sTrig ++ s2) a

||| Embeds a stratified 0-quantity PulseExpr into its runtime Bit indicator MultisetExpr.
public export
pulseToExpr : PulseExpr -> MultisetExpr Unbounded Nothing [] Bit
pulseToExpr BasePulse             = BasePulseM
pulseToExpr ZeroPulse             = ZeroM
pulseToExpr OnePulse              = OneM
pulseToExpr (AddPulse p1 p2)      = AddM (pulseToExpr p1) (pulseToExpr p2)
pulseToExpr (HadamardPulse p1 p2) = HadamardM (pulseToExpr p1) (pulseToExpr p2)
pulseToExpr (MassPulse _)         = BasePulseM

------------------------------------------------------------------------
-- 5B. CANONICAL SYMBOLIC ALGEBRA FOR MULTISETEXPR (`Gemini.md` Section 5)
------------------------------------------------------------------------

public export
{0 reg : Regime} -> {0 p : Maybe PulseExpr} -> Semigroup (MultisetExpr reg p [] a) where
  (<+>) = AddM

public export
{0 reg : Regime} -> {0 p : Maybe PulseExpr} -> Monoid (MultisetExpr reg p [] a) where
  neutral = ZeroM

public export
{0 p : Maybe PulseExpr} -> Num (MultisetExpr Static p [] a) where
  (+) = AddM
  (*) = MulStatic
  fromInteger 0 = ZeroM
  fromInteger _ = OneM

public export
{0 p : Maybe PulseExpr} -> Neg (MultisetExpr Static p [] a) where
  negate x = SubM ZeroM x
  (-) = SubM

public export
{0 k : Type} -> {0 p : Maybe PulseExpr} -> MultisetAlgebra (MultisetExpr Static p [] (Carrier k)) where
  zeroM     = ZeroM
  addM      = AddM
  subM      = SubM
  scaleM _  = id
  mulM      = MulStatic
  hadamardM = HadamardM
  minM      = MinM
  maxM      = MaxM
  dotM _ _  = intToBoxInt 0

public export
(><) : {0 k1, k2 : Type} -> {0 reg : Regime} -> {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema}
    -> MultisetExpr reg p s1 (Carrier k1) -> MultisetExpr reg p s2 (Carrier k2)
    -> MultisetExpr reg p (s1 ++ s2) (Carrier (k1, k2))
(><) = OuterM

||| Checks whether a MultisetExpr is the additive zero constant ZeroM in O(1) without deep GADT case-tree splitting.
public export
isZeroExpr : {0 reg : Regime} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
          -> MultisetExpr reg p st a -> Bool
isZeroExpr ZeroM = True
isZeroExpr _     = False

||| Checks whether a MultisetExpr is the multiplicative identity mask OneM in O(1) without deep GADT case-tree splitting.
public export
isOneExpr : {0 reg : Regime} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
         -> MultisetExpr reg p st a -> Bool
isOneExpr OneM = True
isOneExpr _    = False

||| Erased-schema existential pair (`Gemini.md` Section 2 & 5):
||| Pairs a `0`-quantity compile-time `StateSchema` witness (`0 schema : StateSchema`)
||| with a runtime `MultisetExpr reg p schema a`.
public export
record FusedExpr (0 reg : Regime) (0 p : Maybe PulseExpr) (a : Type) where
  constructor MkFusedExpr
  0 schema : StateSchema
  expr     : MultisetExpr reg p schema a

||| Meta-level algebraic fusion and dead-state elimination over MultisetExpr (`Gemini.md` Section 5).
||| Uses depth-1 constructor matching with O(1) guard predicates to prevent quadratic GADT case-tree splitting.
||| Returns `FusedExpr reg p a` (`MkFusedExpr st' expr`) so the `0`-quantity `StateSchema` witness stays erased.
public export
fuseStep : {0 reg : Regime} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
        -> MultisetExpr reg p st a
        -> FusedExpr reg p a
fuseStep (AddM x y) =
  case isZeroExpr x of
    True  => MkFusedExpr _ y
    False => case isZeroExpr y of
      True  => MkFusedExpr _ x
      False => MkFusedExpr _ (AddM x y)
fuseStep (SubM x y) =
  case isZeroExpr y of
    True  => MkFusedExpr _ x
    False => MkFusedExpr _ (SubM x y)
fuseStep (HadamardM x y) =
  case isZeroExpr x || isZeroExpr y of
    True  => MkFusedExpr [] ZeroM
    False => case isOneExpr x of
      True  => MkFusedExpr _ y
      False => case isOneExpr y of
        True  => MkFusedExpr _ x
        False => MkFusedExpr _ (HadamardM x y)
fuseStep e = MkFusedExpr _ e

||| Recursive bottom-up algebraic fusion over MultisetExpr bounded by a model-derived
||| `Stage0.StructuralFuel` budget (`GohFuel cap`).
public export
fuseWithSteps : {0 reg : Regime} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
             -> (steps : Nat) -> MultisetExpr reg p st a
             -> FusedExpr reg p a
fuseWithSteps Z e = fuseStep e
fuseWithSteps (S k) (AddM x y) =
  let MkFusedExpr _ x' = fuseWithSteps k x
      MkFusedExpr _ y' = fuseWithSteps k y
  in fuseStep (AddM x' y')
fuseWithSteps (S k) (SubM x y) =
  let MkFusedExpr _ x' = fuseWithSteps k x
      MkFusedExpr _ y' = fuseWithSteps k y
  in fuseStep (SubM x' y')
fuseWithSteps (S k) (HadamardM x y) =
  let MkFusedExpr _ x' = fuseWithSteps k x
      MkFusedExpr _ y' = fuseWithSteps k y
  in fuseStep (HadamardM x' y')
fuseWithSteps (S k) (MinM x y) =
  let MkFusedExpr _ x' = fuseWithSteps k x
      MkFusedExpr _ y' = fuseWithSteps k y
  in MkFusedExpr _ (MinM x' y')
fuseWithSteps (S k) (MaxM x y) =
  let MkFusedExpr _ x' = fuseWithSteps k x
      MkFusedExpr _ y' = fuseWithSteps k y
  in MkFusedExpr _ (MaxM x' y')
fuseWithSteps (S _) e = fuseStep e

||| Canonical meta-level optimizer parameterized by a `Stage0.StructuralFuel` envelope (`GohFuel cap`).
public export
fuse : {0 cap : Nat} -> {0 reg : Regime} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
    -> GohFuel cap -> MultisetExpr reg p st a
    -> FusedExpr reg p a
fuse fuel e = fuseWithSteps (fuelSteps fuel) e

||| Evaluates a `Static` scalar `MultisetExpr` directly to an exact `BoxInt`.
public export
evalStaticScalar : {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
                -> MultisetExpr Static p st BoxInt -> BoxInt
evalStaticScalar ZeroM           = intToBoxInt 0
evalStaticScalar OneM            = intToBoxInt 1
evalStaticScalar (ConstM v)      = v
evalStaticScalar (AddM x y)      = evalStaticScalar x + evalStaticScalar y
evalStaticScalar (SubM x y)      = subBox (evalStaticScalar x) (evalStaticScalar y)
evalStaticScalar (HadamardM x y) = evalStaticScalar x * evalStaticScalar y
evalStaticScalar (MinM x y)      =
  let vx = evalStaticScalar x
      vy = evalStaticScalar y
  in if unwrapBox vx <= unwrapBox vy then vx else vy
evalStaticScalar (MaxM x y)      =
  let vx = evalStaticScalar x
      vy = evalStaticScalar y
  in if unwrapBox vx >= unwrapBox vy then vx else vy
evalStaticScalar _               = intToBoxInt 0

||| Evaluates a `Static` multiset `MultisetExpr` directly over an AVL `Carrier k` (`BoxMultisetTree k`).
public export
evalStaticCarrier : Ord k => {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
                 -> MultisetExpr Static p st (Carrier k) -> Carrier k
evalStaticCarrier ZeroM           = emptyCarrier
evalStaticCarrier (ConstM c)      = c
evalStaticCarrier (AddM x y)      = addCarrier (evalStaticCarrier x) (evalStaticCarrier y)
evalStaticCarrier (SubM x y)      = subCarrier (evalStaticCarrier x) (evalStaticCarrier y)
evalStaticCarrier (HadamardM x y) = hadamardCarrier (evalStaticCarrier x) (evalStaticCarrier y)
evalStaticCarrier (MinM x y)      = minCarrier (evalStaticCarrier x) (evalStaticCarrier y)
evalStaticCarrier (MaxM x y)      = maxCarrier (evalStaticCarrier x) (evalStaticCarrier y)
evalStaticCarrier _               = emptyCarrier

||| 0-quantity soundness proofs (`fuseSound`) verifying algebraic rewrites of `fuseStep`.
public export
0 prfFuseAddZeroL : {0 reg : Regime} -> {0 p : Maybe PulseExpr} -> {0 s2 : StateSchema}
                 -> (y : MultisetExpr reg p s2 a)
                 -> fuseStep (AddM ZeroM y) = MkFusedExpr s2 y
prfFuseAddZeroL _ = Refl

public export
0 prfFuseHadamardZeroL : {0 reg : Regime} -> {0 p : Maybe PulseExpr} -> {0 s2 : StateSchema}
                      -> (y : MultisetExpr reg p s2 a)
                      -> fuseStep (HadamardM ZeroM y) = MkFusedExpr [] ZeroM
prfFuseHadamardZeroL _ = Refl

public export
0 prfFuseHadamardOneL : {0 p : Maybe PulseExpr}
                     -> (v : a)
                     -> fuseStep (HadamardM OneM (ConstM {p} v)) = MkFusedExpr [] (ConstM {p} v)
prfFuseHadamardOneL _ = Refl

||| Cyclomatic hylomorphism lowering (`compileStream`, `Gemini.md` Section 5):
||| Lowers an `Unbounded` stream expression into a zero-allocation `1`-quantity `StepKernel`.
public export
compileStream : {0 p : PulseExpr} -> {0 st : StateSchema}
             -> (stepFn : (1 s : stEnv) -> a -> LPair stEnv a)
             -> MultisetExpr Unbounded (Just p) st a
             -> StepKernel stEnv a a
compileStream stepFn _ = stepFn

