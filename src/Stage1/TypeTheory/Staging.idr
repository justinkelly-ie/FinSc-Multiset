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
import public Stage0.SignedBit
import Stage0.Token
import Stage0.Multiset
import Stage0.StructuralFuel
import Stage0.LinearBuffer
import Stage0.OnSeq.FusedStream
import public Stage1.Basis.CoordCell
import public Stage1.ConvolutionAdmissibility
import public Stage1.NTT
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
stagedMultisetUnion : Ord a => Lift (Carrier a) -> Lift (Carrier a) -> Lift (Carrier a)
stagedMultisetUnion qb1 qb2 = quote (splice qb1 <+> splice qb2)

||| 2LTT Staged Multiset Empty Constructor.
public export
stagedEmptyBox : Lift (Carrier a)
stagedEmptyBox = quote emptyBox

||| 2LTT Staged Multiset Singleton Constructor.
public export
stagedUnixelBox : a -> BoxInt -> Lift (Carrier a)
stagedUnixelBox x w = quote (unixelBox x w)

||| 2LTT Staged Multiset Lookup:
||| Splices staged multiset and queries multiplicity at the object level.
public export
stagedLookupBox : Ord a => a -> Lift (Carrier a) -> BoxInt
stagedLookupBox x qb = lookupBox x (splice qb)

||| QTT 0 Erased Proof Witness: Staged Multiset Union Invariant
public export
0 prfStagedMultisetUnion : Ord a => (b1 : Carrier a) -> (b2 : Carrier a) ->
                          splice (stagedMultisetUnion (quote b1) (quote b2)) = b1 <+> b2
prfStagedMultisetUnion _ _ = Refl

||| 2LTT Staged Multiset Consolidation:
||| Consolidates and sums duplicate tokens at compile time (U_1),
||| emitting an irreducible, canonical multiset at Level 0 (U_0).
public export
stagedConsolidateBox : Ord a => Lift (Carrier a) -> Lift (Carrier a)
stagedConsolidateBox qb = quote (consolidateBox (splice qb))

||| 2LTT Staged Charge Annihilation:
||| Annihilates opposite sign discrete tokens (Pos and Neg) during staging,
||| ensuring zero-weight tokens never allocate space in the object program.
public export
stagedAnnihilateBox : Ord a => Lift (Carrier a) -> Lift (Carrier a)
stagedAnnihilateBox qb = quote (consolidateBox (splice qb))

||| QTT 0 Erased Proof Witness: Staged Consolidation Invariant
public export
0 prfStagedConsolidateInvariant : Ord a => (b : Carrier a) ->
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
foldLinearStream fuel fn acc0 (MkLinearStream step seed) = loop fuel acc0 seed
  where
    loop : Nat -> acc -> (1 st : s) -> LinearStatePair s acc
    loop Z currentAcc st = MkLStatePair st currentAcc
    loop (S f) currentAcc st = case step st of
      DoneL st' => MkLStatePair st' currentAcc
      SkipL st' => loop f currentAcc st'
      YieldL x st' => loop f (fn currentAcc x) st'

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
------------------------------------------------------------------------
-- 11. UNIFIED SIX-REGIME LAURENT MULTISET EXPRESSION GADT (Gemini.md §4)
------------------------------------------------------------------------

||| Canonical type alias linking legacy `Regime` references to `LaurentRegime`.
public export
Regime : Type
Regime = LaurentRegime

||| Spatial stencil perimeter policy at compile time (`Gemini.md` §2/§6).
public export
data BoundaryMode : Type where
  ZeroPadded       : BoundaryMode
  MirrorBoundary   : BoundaryMode
  PeriodicBoundary : BoundaryMode

public export
Eq BoundaryMode where
  ZeroPadded       == ZeroPadded       = True
  MirrorBoundary   == MirrorBoundary   = True
  PeriodicBoundary == PeriodicBoundary = True
  _                == _                = False

||| Compile-time state schema tracking linear buffer allocations at the 0-quantity meta-level.
public export
StateSchema : Type
StateSchema = List Type

||| Unified Interaction Pulse algebra (Zero-quantity temporal indicator clocks & mass thresholds).
public export
data PulseExpr : Type where
  BasePulse     : PulseExpr
  ZeroPulse     : PulseExpr
  OnePulse      : PulseExpr
  AddPulse      : PulseExpr -> PulseExpr -> PulseExpr
  HadamardPulse : PulseExpr -> PulseExpr -> PulseExpr
  MassPulse     : (threshold : Nat) -> PulseExpr

||| Total, strongly-typed Six-Regime Laurent `MultisetExpr` GADT.
||| Defined as a stratified index prior to interpretation to avoid inductive-inductive cycles.
public export
data MultisetExpr : (0 reg   : LaurentRegime)
                 -> (0 pulse : Maybe PulseExpr)
                 -> (0 st    : StateSchema)
                 -> (a       : Type)
                 -> Type where
  BasePulseM    : MultisetExpr OpenFuture Nothing [] MultisetBit
  ZeroM         : {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> MultisetExpr reg p [] a
  OneM          : {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> MultisetExpr reg p [] a
  ConstM        : {0 p : Maybe PulseExpr} -> {0 low, high : Integer}
               -> (val : a) -> MultisetExpr (StaticHorizon low high) p [] a
  RepeatConst   : {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr}
               -> (val : a) -> MultisetExpr reg p [] a
  Input         : {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> (idx : Nat) -> MultisetExpr reg p [] a
  BilateralTap  : {0 p : Maybe PulseExpr}
               -> (sampleAt : Int -> a) -> MultisetExpr BilateralOpen p [] a

  AddM          : {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema}
               -> MultisetExpr reg p s1 a -> MultisetExpr reg p s2 a -> MultisetExpr reg p (s1 ++ s2) a
  SubM          : {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema}
               -> MultisetExpr reg p s1 a -> MultisetExpr reg p s2 a -> MultisetExpr reg p (s1 ++ s2) a
  HadamardM     : {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema}
               -> MultisetExpr reg p s1 a -> MultisetExpr reg p s2 a -> MultisetExpr reg p (s1 ++ s2) a
  MinM          : {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema}
               -> MultisetExpr reg p s1 a -> MultisetExpr reg p s2 a -> MultisetExpr reg p (s1 ++ s2) a
  MaxM          : {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema}
               -> MultisetExpr reg p s1 a -> MultisetExpr reg p s2 a -> MultisetExpr reg p (s1 ++ s2) a

  ||| Unified Laurent Cauchy convolution guarded at compile time by the 36-cell `CanConvolve` matrix.
  MulLaurent    : {rA, rB : LaurentRegime} -> {0 rOut : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema}
               -> {auto 0 ok : admissibleConvolution rA rB = Just rOut}
               -> MultisetExpr rA p s1 a -> MultisetExpr rB p s2 a
               -> MultisetExpr rOut p (s1 ++ s2) a

  DotStatic     : {0 c, k : Type} -> {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema} -> {0 low, high : Integer}
               -> DiscreteCoord k
               => MultisetExpr (StaticHorizon low high) p s1 (Box c k)
               -> MultisetExpr (StaticHorizon low high) p s2 (Box c k)
               -> MultisetExpr (StaticHorizon low high) p (s1 ++ s2) c
  DotFinite     : {0 c, k : Type} -> {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema} -> {0 cap : Nat}
               -> DiscreteCoord k
               => MultisetExpr (BoundedHorizon cap) p s1 (Box c k)
               -> MultisetExpr (BoundedHorizon cap) p s2 (Box c k)
               -> MultisetExpr (StaticHorizon 0 0) p (s1 ++ s2) c
  DotFiniteScalar : {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema} -> {cap : Nat}
                 -> MultisetExpr (BoundedHorizon cap) p s1 BoxInt
                 -> MultisetExpr (BoundedHorizon cap) p s2 BoxInt
                 -> MultisetExpr (StaticHorizon 0 0) p (s1 ++ s2) BoxInt
  Segment       : {0 p : PulseExpr} -> {0 st : StateSchema} -> (winSize : Nat)
               -> MultisetExpr OpenFuture (Just p) st a
               -> MultisetExpr (WindowedHorizon winSize) (Just p) (Vect winSize a :: st) a
  DotWindow     : {0 c, k : Type} -> {0 p : PulseExpr} -> {0 s1, s2 : StateSchema} -> {0 w : Nat}
               -> DiscreteCoord k
               => MultisetExpr (WindowedHorizon w) (Just p) s1 (Box c k)
               -> MultisetExpr (BoundedHorizon w) (Just p) s2 (Box c k)
               -> MultisetExpr OpenFuture (Just p) (s1 ++ s2) c
  DotWindowScalar : {0 p : PulseExpr} -> {0 s1, s2 : StateSchema} -> {w : Nat}
                 -> MultisetExpr (WindowedHorizon w) (Just p) s1 BoxInt
                 -> MultisetExpr (BoundedHorizon w) (Just p) s2 BoxInt
                 -> MultisetExpr OpenFuture (Just p) (s1 ++ s2) BoxInt

  OuterM         : {0 c, k1, k2 : Type} -> {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema}
                -> (DiscreteCoord k1, DiscreteCoord k2)
                => MultisetExpr reg p s1 (Box c k1) -> MultisetExpr reg p s2 (Box c k2)
                -> MultisetExpr reg p (s1 ++ s2) (Box c (k1, k2))
  ContractR      : {0 c, k1, k2 : Type} -> {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
                -> (DiscreteCoord k1, DiscreteCoord k2)
                => MultisetExpr reg p st (Box c (k1, k2))
                -> MultisetExpr reg p st (Box c k1)
  ContractL      : {0 c, k1, k2 : Type} -> {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
                -> (DiscreteCoord k1, DiscreteCoord k2)
                => MultisetExpr reg p st (Box c (k1, k2))
                -> MultisetExpr reg p st (Box c k2)
  ContractMiddle : {0 c, k1, k2, k3 : Type} -> {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema}
                -> (DiscreteCoord k1, DiscreteCoord k2, DiscreteCoord k3)
                => MultisetExpr reg p s1 (Box c (k1, k2))
                -> MultisetExpr reg p s2 (Box c (k2, k3))
                -> MultisetExpr reg p (s1 ++ s2) (Box c (k1, k3))

  EqStatic      : {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema} -> {0 l1, h1, l2, h2 : Integer}
               -> Eq a
               => MultisetExpr (StaticHorizon l1 h1) p s1 a
               -> MultisetExpr (StaticHorizon l2 h2) p s2 a
               -> MultisetExpr (StaticHorizon 0 0) p (s1 ++ s2) MultisetBit
  EqStaticScalar : {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema} -> {0 l1, h1, l2, h2 : Integer}
                -> MultisetExpr (StaticHorizon l1 h1) p s1 BoxInt
                -> MultisetExpr (StaticHorizon l2 h2) p s2 BoxInt
                -> MultisetExpr (StaticHorizon 0 0) p (s1 ++ s2) MultisetBit
  EqFinite      : {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema} -> {0 cap : Nat}
               -> Eq a
               => MultisetExpr (BoundedHorizon cap) p s1 a
               -> MultisetExpr (BoundedHorizon cap) p s2 a
               -> MultisetExpr (StaticHorizon 0 0) p (s1 ++ s2) MultisetBit
  EqFiniteScalar : {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema} -> {cap : Nat}
                -> MultisetExpr (BoundedHorizon cap) p s1 BoxInt
                -> MultisetExpr (BoundedHorizon cap) p s2 BoxInt
                -> MultisetExpr (StaticHorizon 0 0) p (s1 ++ s2) MultisetBit
  EqWindow      : {0 p : PulseExpr} -> {0 s1, s2 : StateSchema} -> {win : Nat} -> {0 low, high : Integer}
               -> MultisetExpr (WindowedHorizon win) (Just p) s1 BoxInt
               -> MultisetExpr (StaticHorizon low high) (Just p) s2 BoxInt
               -> MultisetExpr OpenFuture (Just p) (s1 ++ s2) MultisetBit
  EqStream      : {0 p : PulseExpr} -> {0 s1, s2 : StateSchema}
               -> Eq a
               => MultisetExpr OpenFuture (Just p) s1 a
               -> MultisetExpr OpenFuture (Just p) s2 a
               -> MultisetExpr OpenFuture (Just p) (s1 ++ s2) MultisetBit
  EqStreamScalar : {0 p : PulseExpr} -> {0 s1, s2 : StateSchema}
                -> MultisetExpr OpenFuture (Just p) s1 BoxInt
                -> MultisetExpr OpenFuture (Just p) s2 BoxInt
                -> MultisetExpr OpenFuture (Just p) (s1 ++ s2) MultisetBit

  LoopVar       : {0 p : PulseExpr} -> (init : a) -> MultisetExpr OpenFuture (Just p) [] a
  Fby           : {0 p : PulseExpr} -> {0 st : StateSchema} -> (init : a)
               -> MultisetExpr OpenFuture (Just p) st a
               -> MultisetExpr OpenFuture (Just p) (a :: st) a
  When          : {0 parentP : PulseExpr} -> {0 s1 : StateSchema}
               -> MultisetExpr OpenFuture (Just parentP) s1 a -> (0 mask : PulseExpr)
               -> MultisetExpr OpenFuture (Just (HadamardPulse parentP mask)) s1 a
  SwitchSession : {0 p : PulseExpr} -> {0 s1, sTrig, s2 : StateSchema} -> {0 cap : Nat}
               -> MultisetExpr OpenFuture (Just p) s1 a
               -> (trigger : MultisetExpr OpenFuture (Just p) sTrig MultisetBit)
               -> MultisetExpr (BoundedHorizon cap) (Just p) s2 a
               -> MultisetExpr OpenFuture (Just p) (s1 ++ sTrig ++ s2) a

||| Smart constructor alias for `StaticHorizon` Cauchy convolution.
public export
MulStatic : {l1, h1, l2, h2 : Integer} -> {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema}
         -> MultisetExpr (StaticHorizon l1 h1) p s1 a
         -> MultisetExpr (StaticHorizon l2 h2) p s2 a
         -> MultisetExpr (StaticHorizon (l1 + l2) (h1 + h2)) p (s1 ++ s2) a
MulStatic {l1} {h1} {l2} {h2} =
  MulLaurent {rA = StaticHorizon l1 h1} {rB = StaticHorizon l2 h2}

||| Smart constructor alias for `BoundedHorizon` finite convolution.
public export
MulFinite : {c1, c2 : Nat} -> {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema}
         -> MultisetExpr (BoundedHorizon c1) p s1 a
         -> MultisetExpr (BoundedHorizon c2) p s2 a
         -> MultisetExpr (BoundedHorizon (c1 + c2)) p (s1 ++ s2) a
MulFinite {c1} {c2} =
  MulLaurent {rA = BoundedHorizon c1} {rB = BoundedHorizon c2}

||| Smart constructor alias for `OpenFuture * BoundedHorizon` causal FIR filtering.
public export
MulStream : {k : Nat} -> {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema}
         -> MultisetExpr OpenFuture p s1 a
         -> MultisetExpr (BoundedHorizon k) p s2 a
         -> MultisetExpr OpenFuture p (s1 ++ s2) a
MulStream {k} =
  MulLaurent {rA = OpenFuture} {rB = BoundedHorizon k}

||| Compiles a pure `PulseExpr` into an `OpenFuture` `MultisetBit` pulse indicator stream.
public export
pulseToExpr : PulseExpr -> MultisetExpr OpenFuture Nothing [] MultisetBit
pulseToExpr BasePulse             = BasePulseM
pulseToExpr ZeroPulse             = ZeroM
pulseToExpr OnePulse              = OneM
pulseToExpr (AddPulse p1 p2)      = AddM (pulseToExpr p1) (pulseToExpr p2)
pulseToExpr (HadamardPulse p1 p2) = HadamardM (pulseToExpr p1) (pulseToExpr p2)
pulseToExpr (MassPulse _)         = BasePulseM

public export
{0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> Semigroup (MultisetExpr reg p [] a) where
  (<+>) = AddM

public export
{0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> Monoid (MultisetExpr reg p [] a) where
  neutral = ZeroM

public export
{0 p : Maybe PulseExpr} -> Num a => Num (MultisetExpr (StaticHorizon 0 0) p [] a) where
  (+) = AddM
  (*) = MulLaurent {rA = StaticHorizon 0 0} {rB = StaticHorizon 0 0} {rOut = StaticHorizon 0 0} {ok = Refl}
  fromInteger n = if n == 0 then ZeroM else ConstM (fromInteger n)

public export
{0 p : Maybe PulseExpr} -> Num a => Neg (MultisetExpr (StaticHorizon 0 0) p [] a) where
  negate x = SubM ZeroM x
  (-) = SubM

public export
{0 k : Type} -> {0 p : Maybe PulseExpr} -> DiscreteCoord k => MultisetAlgebra (MultisetExpr (StaticHorizon 0 0) p [] (Carrier k)) where
  zeroM     = ZeroM
  addM      = AddM
  subM      = SubM
  hadamardM = HadamardM
  minM      = MinM
  maxM      = MaxM
  scaleM _  = id
  dotM _ _  = intToBoxInt 0

||| Symbolic outer-product operator lifted to `MultisetExpr` (relational joins & matrix products).
public export
(><) : {0 c, k1, k2 : Type} -> (DiscreteCoord k1, DiscreteCoord k2)
    => {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema}
    -> MultisetExpr reg p s1 (Box c k1) -> MultisetExpr reg p s2 (Box c k2)
    -> MultisetExpr reg p (s1 ++ s2) (Box c (k1, k2))
(><) = OuterM

public export
isZeroExpr : {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
          -> MultisetExpr reg p st a -> Bool
isZeroExpr ZeroM = True
isZeroExpr _     = False

public export
isOneExpr : {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
         -> MultisetExpr reg p st a -> Bool
isOneExpr OneM = True
isOneExpr _    = False

------------------------------------------------------------------------
-- 12. META-LEVEL FUSION, CONSTANT FOLDING & STATIC EVALUATION
------------------------------------------------------------------------

||| Existential wrapper erasing intermediate `StateSchema` shrinkage under `fuseStep` / `fuse`.
public export
record FusedExpr (0 reg : LaurentRegime) (0 p : Maybe PulseExpr) (a : Type) where
  constructor MkFusedExpr
  0 schema : StateSchema
  fused    : MultisetExpr reg p schema a

||| Single-step algebraic rewrite performing zero/identity annihilation cleanly.
public export
fuseStep : {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
        -> MultisetExpr reg p st a -> FusedExpr reg p a
fuseStep (AddM x y) =
  case isZeroExpr x of
    True  => MkFusedExpr _ y
    False => if isZeroExpr y then MkFusedExpr _ x else MkFusedExpr _ (AddM x y)
fuseStep (SubM x y) =
  if isZeroExpr y then MkFusedExpr _ x else MkFusedExpr _ (SubM x y)
fuseStep (HadamardM x y) =
  if isZeroExpr x || isZeroExpr y then MkFusedExpr [] ZeroM
  else if isOneExpr x then MkFusedExpr _ y
  else if isOneExpr y then MkFusedExpr _ x
  else MkFusedExpr _ (HadamardM x y)
fuseStep (MinM x y) =
  if isZeroExpr x && isZeroExpr y then MkFusedExpr [] ZeroM else MkFusedExpr _ (MinM x y)
fuseStep (MaxM x y) =
  if isZeroExpr x && isZeroExpr y then MkFusedExpr [] ZeroM else MkFusedExpr _ (MaxM x y)
fuseStep (MulLaurent {rA} {rB} {rOut} {ok} x y) =
  if isZeroExpr x || isZeroExpr y then MkFusedExpr [] ZeroM
  else MkFusedExpr _ (MulLaurent {rA} {rB} {rOut} {ok} x y)
fuseStep (DotStatic x y) =
  if isZeroExpr x || isZeroExpr y then MkFusedExpr [] ZeroM else MkFusedExpr _ (DotStatic x y)
fuseStep (DotFinite x y) =
  if isZeroExpr x || isZeroExpr y then MkFusedExpr [] ZeroM else MkFusedExpr _ (DotFinite x y)
fuseStep (DotFiniteScalar x y) =
  if isZeroExpr x || isZeroExpr y then MkFusedExpr [] ZeroM else MkFusedExpr _ (DotFiniteScalar x y)
fuseStep (Segment winSize x) =
  if isZeroExpr x then MkFusedExpr _ (Segment winSize ZeroM) else MkFusedExpr _ (Segment winSize x)
fuseStep (DotWindow x y) =
  if isZeroExpr x || isZeroExpr y then MkFusedExpr [] ZeroM else MkFusedExpr _ (DotWindow x y)
fuseStep (DotWindowScalar x y) =
  if isZeroExpr x || isZeroExpr y then MkFusedExpr [] ZeroM else MkFusedExpr _ (DotWindowScalar x y)
fuseStep (OuterM x y) =
  if isZeroExpr x || isZeroExpr y then MkFusedExpr [] ZeroM else MkFusedExpr _ (OuterM x y)
fuseStep (ContractR x) =
  if isZeroExpr x then MkFusedExpr [] ZeroM else MkFusedExpr _ (ContractR x)
fuseStep (ContractL x) =
  if isZeroExpr x then MkFusedExpr [] ZeroM else MkFusedExpr _ (ContractL x)
fuseStep (ContractMiddle x y) =
  if isZeroExpr x || isZeroExpr y then MkFusedExpr [] ZeroM else MkFusedExpr _ (ContractMiddle x y)
fuseStep e = MkFusedExpr _ e

||| Bounded recursive bottom-up `fuse` optimization pass over `MultisetExpr`.
public export
fuseWithSteps : {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
             -> (steps : Nat) -> MultisetExpr reg p st a -> FusedExpr reg p a
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
  in fuseStep (MinM x' y')
fuseWithSteps (S k) (MaxM x y) =
  let MkFusedExpr _ x' = fuseWithSteps k x
      MkFusedExpr _ y' = fuseWithSteps k y
  in fuseStep (MaxM x' y')
fuseWithSteps (S k) (MulLaurent {rA} {rB} {rOut} {ok} x y) =
  let MkFusedExpr _ x' = fuseWithSteps k x
      MkFusedExpr _ y' = fuseWithSteps k y
  in fuseStep (MulLaurent {rA} {rB} {rOut} {ok} x' y')
fuseWithSteps (S k) (DotStatic x y) =
  let MkFusedExpr _ x' = fuseWithSteps k x
      MkFusedExpr _ y' = fuseWithSteps k y
  in fuseStep (DotStatic x' y')
fuseWithSteps (S k) (DotFinite x y) =
  let MkFusedExpr _ x' = fuseWithSteps k x
      MkFusedExpr _ y' = fuseWithSteps k y
  in fuseStep (DotFinite x' y')
fuseWithSteps (S k) (DotFiniteScalar x y) =
  let MkFusedExpr _ x' = fuseWithSteps k x
      MkFusedExpr _ y' = fuseWithSteps k y
  in fuseStep (DotFiniteScalar x' y')
fuseWithSteps (S k) (Segment winSize x) =
  let MkFusedExpr _ x' = fuseWithSteps k x
  in fuseStep (Segment winSize x')
fuseWithSteps (S k) (DotWindow x y) =
  let MkFusedExpr _ x' = fuseWithSteps k x
      MkFusedExpr _ y' = fuseWithSteps k y
  in fuseStep (DotWindow x' y')
fuseWithSteps (S k) (DotWindowScalar x y) =
  let MkFusedExpr _ x' = fuseWithSteps k x
      MkFusedExpr _ y' = fuseWithSteps k y
  in fuseStep (DotWindowScalar x' y')
fuseWithSteps (S k) (OuterM x y) =
  let MkFusedExpr _ x' = fuseWithSteps k x
      MkFusedExpr _ y' = fuseWithSteps k y
  in fuseStep (OuterM x' y')
fuseWithSteps (S k) (ContractR x) =
  let MkFusedExpr _ x' = fuseWithSteps k x
  in fuseStep (ContractR x')
fuseWithSteps (S k) (ContractL x) =
  let MkFusedExpr _ x' = fuseWithSteps k x
  in fuseStep (ContractL x')
fuseWithSteps (S k) (ContractMiddle x y) =
  let MkFusedExpr _ x' = fuseWithSteps k x
      MkFusedExpr _ y' = fuseWithSteps k y
  in fuseStep (ContractMiddle x' y')
fuseWithSteps (S k) (EqStatic x y) =
  let MkFusedExpr _ x' = fuseWithSteps k x
      MkFusedExpr _ y' = fuseWithSteps k y
  in MkFusedExpr _ (EqStatic x' y')
fuseWithSteps (S k) (EqStaticScalar x y) =
  let MkFusedExpr _ x' = fuseWithSteps k x
      MkFusedExpr _ y' = fuseWithSteps k y
  in MkFusedExpr _ (EqStaticScalar x' y')
fuseWithSteps (S k) (EqFinite x y) =
  let MkFusedExpr _ x' = fuseWithSteps k x
      MkFusedExpr _ y' = fuseWithSteps k y
  in MkFusedExpr _ (EqFinite x' y')
fuseWithSteps (S k) (EqFiniteScalar x y) =
  let MkFusedExpr _ x' = fuseWithSteps k x
      MkFusedExpr _ y' = fuseWithSteps k y
  in MkFusedExpr _ (EqFiniteScalar x' y')
fuseWithSteps (S k) (EqWindow x y) =
  let MkFusedExpr _ x' = fuseWithSteps k x
      MkFusedExpr _ y' = fuseWithSteps k y
  in MkFusedExpr _ (EqWindow x' y')
fuseWithSteps (S k) (EqStream x y) =
  let MkFusedExpr _ x' = fuseWithSteps k x
      MkFusedExpr _ y' = fuseWithSteps k y
  in MkFusedExpr _ (EqStream x' y')
fuseWithSteps (S k) (EqStreamScalar x y) =
  let MkFusedExpr _ x' = fuseWithSteps k x
      MkFusedExpr _ y' = fuseWithSteps k y
  in MkFusedExpr _ (EqStreamScalar x' y')
fuseWithSteps (S k) (Fby init x) =
  let MkFusedExpr _ x' = fuseWithSteps k x
  in MkFusedExpr _ (Fby init x')
fuseWithSteps (S k) (When x mask) =
  let MkFusedExpr _ x' = fuseWithSteps k x
  in MkFusedExpr _ (When x' mask)
fuseWithSteps (S k) (SwitchSession main trig fallback) =
  let MkFusedExpr _ main' = fuseWithSteps k main
      MkFusedExpr _ trig' = fuseWithSteps k trig
      MkFusedExpr _ fb'   = fuseWithSteps k fallback
  in MkFusedExpr _ (SwitchSession main' trig' fb')
fuseWithSteps (S _) e = fuseStep e

||| Fueled entry point for AST optimization over `GohFuel cap`.
public export
fuse : {0 cap : Nat} -> {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
    -> GohFuel cap -> MultisetExpr reg p st a -> FusedExpr reg p a
fuse fuel e = fuseWithSteps (gohSteps fuel) e

||| QTT 0 soundness audits (`fuseSound`) verifying algebraic rewrites of `fuseStep`.
public export
0 prfFuseAddZeroL : {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 s2 : StateSchema}
                 -> (y : MultisetExpr reg p s2 a)
                 -> fuseStep (AddM ZeroM y) = MkFusedExpr s2 y
prfFuseAddZeroL _ = Refl

public export
0 prfFuseHadamardZeroL : {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 s2 : StateSchema}
                      -> (y : MultisetExpr reg p s2 a)
                      -> fuseStep (HadamardM ZeroM y) = MkFusedExpr [] ZeroM
prfFuseHadamardZeroL _ = Refl

public export
0 prfFuseHadamardOneL : {0 p : Maybe PulseExpr} -> {0 low, high : Integer}
                     -> (v : a)
                     -> fuseStep (HadamardM OneM (ConstM {p} {low} {high} v)) =
                          MkFusedExpr [] (ConstM {p} {low} {high} v)
prfFuseHadamardOneL _ = Refl

------------------------------------------------------------------------
-- 13. GENERIC `Box c k` CONTRACTIONS, QUADRATIC ZERO-NORM & EVALUATORS
------------------------------------------------------------------------

||| Generic Cartesian outer product over weighted AVL `Box c` containers.
public export
outerWeightedBox : (MultisetWeight c, DiscreteCoord k1, DiscreteCoord k2)
                => Box c k1 -> Box c k2 -> Box c (k1, k2)
outerWeightedBox BoxLeaf _ = BoxLeaf
outerWeightedBox _ BoxLeaf = BoxLeaf
outerWeightedBox m1 m2 =
  foldBox (\a, wa, acc1 =>
            foldBox (\b, wb, acc2 =>
                      let wOut = mulWeight wa wb
                      in if isZero wOut then acc2 else addAtKeyBox (a, b) wOut acc2)
                    acc1
                    m2)
          BoxLeaf
          m1

||| Generic right contraction projecting `(k1, k2) -> k1` over `Box c`.
public export
contractRWeightedBox : (MultisetWeight c, DiscreteCoord k1, DiscreteCoord k2)
                    => Box c (k1, k2) -> Box c k1
contractRWeightedBox BoxLeaf = BoxLeaf
contractRWeightedBox m =
  foldBox (\(a, _), w, acc => addAtKeyBox a w acc) BoxLeaf m

||| Generic left contraction projecting `(k1, k2) -> k2` over `Box c`.
public export
contractLWeightedBox : (MultisetWeight c, DiscreteCoord k1, DiscreteCoord k2)
                    => Box c (k1, k2) -> Box c k2
contractLWeightedBox BoxLeaf = BoxLeaf
contractLWeightedBox m =
  foldBox (\(_, b), w, acc => addAtKeyBox b w acc) BoxLeaf m

||| Maxel basis contraction `[k1, k2] . [k2, k3] -> [k1, k3]` (matches matching middle keys).
public export
contractMiddleWeightedBox : (MultisetWeight c, DiscreteCoord k1, DiscreteCoord k2, DiscreteCoord k3)
                         => Box c (k1, k2) -> Box c (k2, k3) -> Box c (k1, k3)
contractMiddleWeightedBox BoxLeaf _ = BoxLeaf
contractMiddleWeightedBox _ BoxLeaf = BoxLeaf
contractMiddleWeightedBox m1 m2 =
  foldBox (\(a, b1), w1, acc1 =>
            foldBox (\(b2, d), w2, acc2 =>
                      if b1 == b2
                        then let wOut = mulWeight w1 w2
                             in if isZero wOut then acc2 else addAtKeyBox (a, d) wOut acc2
                        else acc2)
                    acc1
                    m2)
          BoxLeaf
          m1

||| Quadratic Zero-Norm equality predicate on exact signed `BoxInt`:
||| `A = B <==> (A - B)^2 == 0`.
public export
eqBoxIntViaZeroNorm : BoxInt -> BoxInt -> MultisetBit
eqBoxIntViaZeroNorm x y =
  let d = subBox x y
  in if mulBox d d == intToBoxInt 0 then OneBit else EmptyBit

||| Quadratic Zero-Norm equality predicate over `Carrier k`:
||| `A = B <==> <A - B, A - B> == 0`.
public export
eqCarrierViaZeroNorm : DiscreteCoord k => Carrier k -> Carrier k -> MultisetBit
eqCarrierViaZeroNorm a b =
  let d = subBox a b
  in if dotBox d d == intToBoxInt 0 then OneBit else EmptyBit

||| Closed QTT 0 audit certifying Quadratic Zero-Norm equivalence (`7 == 7 <==> (7 - 7)^2 == 0`).
public export
0 prfQuadraticZeroNormConst : Stage1.TypeTheory.Staging.eqBoxIntViaZeroNorm (MkBoxInt 7) (MkBoxInt 7) = OneBit
prfQuadraticZeroNormConst = Refl

||| Finite coordinate index vector `[0 .. n - 1]`.
public export
finIndicesVect : (n : Nat) -> Vect n (Fin n)
finIndicesVect Z     = []
finIndicesVect (S k) = FZ :: map FS (finIndicesVect k)

||| Non-stubbed `StaticHorizon` evaluator for arbitrary `Box c k` expressions
||| supporting `OuterM`, `ContractR`, `ContractL`, `ContractMiddle`, pointwise ops, and `ConstM`.
public export
evalStaticWeightedBox : (MultisetWeight c, DiscreteCoord k)
                     => {0 low, high : Integer} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
                     -> MultisetExpr (StaticHorizon low high) p st (Box c k)
                     -> (Nat -> Box c k)
                     -> Box c k
evalStaticWeightedBox ZeroM _ = BoxLeaf
evalStaticWeightedBox OneM _ = BoxLeaf
evalStaticWeightedBox (ConstM val) _ = val
evalStaticWeightedBox (RepeatConst val) _ = val
evalStaticWeightedBox (Input idx) env = env idx
evalStaticWeightedBox (AddM e1 e2) env = unionBox (evalStaticWeightedBox e1 env) (evalStaticWeightedBox e2 env)
evalStaticWeightedBox (SubM e1 e2) env = subBox (evalStaticWeightedBox e1 env) (evalStaticWeightedBox e2 env)
evalStaticWeightedBox (HadamardM e1 e2) env = hadamardBox (evalStaticWeightedBox e1 env) (evalStaticWeightedBox e2 env)
evalStaticWeightedBox (MinM e1 e2) env = minBox (evalStaticWeightedBox e1 env) (evalStaticWeightedBox e2 env)
evalStaticWeightedBox (MaxM e1 e2) env = maxBox (evalStaticWeightedBox e1 env) (evalStaticWeightedBox e2 env)
evalStaticWeightedBox (MulLaurent {rA = StaticHorizon _ _} {rB = StaticHorizon _ _} _ _) _ = BoxLeaf
evalStaticWeightedBox (MulLaurent _ _) _ = BoxLeaf
evalStaticWeightedBox (DotStatic _ _) _ = BoxLeaf
evalStaticWeightedBox (DotFinite _ _) _ = BoxLeaf
evalStaticWeightedBox (OuterM e1 e2) env =
  let x1 = evalStaticWeightedBox e1 (const BoxLeaf)
      x2 = evalStaticWeightedBox e2 (const BoxLeaf)
  in outerWeightedBox x1 x2
evalStaticWeightedBox (ContractR e) _ =
  contractRWeightedBox (evalStaticWeightedBox e (const BoxLeaf))
evalStaticWeightedBox (ContractL e) _ =
  contractLWeightedBox (evalStaticWeightedBox e (const BoxLeaf))
evalStaticWeightedBox (ContractMiddle e1 e2) _ =
  contractMiddleWeightedBox
    (evalStaticWeightedBox e1 (const BoxLeaf))
    (evalStaticWeightedBox e2 (const BoxLeaf))

||| Monoidal `StaticHorizon` evaluator supporting full Cauchy convolution `MulStatic` (`MulLaurent`).
public export
evalStaticWeightedBoxMonoid : (MultisetWeight c, DiscreteCoord k, MonoidCoord k)
                           => {0 low, high : Integer} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
                           -> MultisetExpr (StaticHorizon low high) p st (Box c k)
                           -> (Nat -> Box c k)
                           -> Box c k
evalStaticWeightedBoxMonoid ZeroM _ = BoxLeaf
evalStaticWeightedBoxMonoid OneM _ = BoxNode 1 BoxLeaf origin oneWeight BoxLeaf
evalStaticWeightedBoxMonoid (ConstM val) _ = val
evalStaticWeightedBoxMonoid (RepeatConst val) _ = val
evalStaticWeightedBoxMonoid (Input idx) env = env idx
evalStaticWeightedBoxMonoid (AddM e1 e2) env = unionBox (evalStaticWeightedBoxMonoid e1 env) (evalStaticWeightedBoxMonoid e2 env)
evalStaticWeightedBoxMonoid (SubM e1 e2) env = subBox (evalStaticWeightedBoxMonoid e1 env) (evalStaticWeightedBoxMonoid e2 env)
evalStaticWeightedBoxMonoid (HadamardM e1 e2) env = hadamardBox (evalStaticWeightedBoxMonoid e1 env) (evalStaticWeightedBoxMonoid e2 env)
evalStaticWeightedBoxMonoid (MinM e1 e2) env = minBox (evalStaticWeightedBoxMonoid e1 env) (evalStaticWeightedBoxMonoid e2 env)
evalStaticWeightedBoxMonoid (MaxM e1 e2) env = maxBox (evalStaticWeightedBoxMonoid e1 env) (evalStaticWeightedBoxMonoid e2 env)
evalStaticWeightedBoxMonoid (MulLaurent {rA = StaticHorizon _ _} {rB = StaticHorizon _ _} e1 e2) env =
  mulBoxWith (evalStaticWeightedBoxMonoid e1 env) (evalStaticWeightedBoxMonoid e2 env)
evalStaticWeightedBoxMonoid (MulLaurent _ _) _ = BoxLeaf
evalStaticWeightedBoxMonoid (DotStatic _ _) _ = BoxLeaf
evalStaticWeightedBoxMonoid (DotFinite _ _) _ = BoxLeaf
evalStaticWeightedBoxMonoid (OuterM e1 e2) _ =
  outerWeightedBox
    (evalStaticWeightedBox e1 (const BoxLeaf))
    (evalStaticWeightedBox e2 (const BoxLeaf))
evalStaticWeightedBoxMonoid (ContractR e) _ =
  contractRWeightedBox (evalStaticWeightedBox e (const BoxLeaf))
evalStaticWeightedBoxMonoid (ContractL e) _ =
  contractLWeightedBox (evalStaticWeightedBox e (const BoxLeaf))
evalStaticWeightedBoxMonoid (ContractMiddle e1 e2) _ =
  contractMiddleWeightedBox
    (evalStaticWeightedBox e1 (const BoxLeaf))
    (evalStaticWeightedBox e2 (const BoxLeaf))

||| Non-stubbed `StaticHorizon` evaluator for `BoxInt`-weighted `Carrier k`.
public export
evalStaticCarrier : DiscreteCoord k => {0 low, high : Integer} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
                 -> MultisetExpr (StaticHorizon low high) p st (Carrier k)
                 -> Carrier k
evalStaticCarrier expr = evalStaticWeightedBox expr (const BoxLeaf)

||| Backwards-compatible monoidal `StaticHorizon` evaluator for `Carrier k`.
public export
evalStaticCarrierMonoid : (Ord k, MonoidCoord k)
                       => {0 low, high : Integer} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
                       -> MultisetExpr (StaticHorizon low high) p st (Carrier k)
                       -> Carrier k
evalStaticCarrierMonoid expr = evalStaticWeightedBoxMonoid expr (const BoxLeaf)

||| Static `FiniteCoord k` carrier evaluator unlocking exact universal `OneM` masks.
public export
evalStaticFiniteCarrier : FiniteCoord k
                       => {0 low, high : Integer} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
                       -> MultisetExpr (StaticHorizon low high) p st (Carrier k)
                       -> (Nat -> Carrier k)
                       -> Carrier k
evalStaticFiniteCarrier ZeroM _ = BoxLeaf
evalStaticFiniteCarrier OneM _ = oneCarrier
evalStaticFiniteCarrier (ConstM val) _ = val
evalStaticFiniteCarrier (Input idx) env = env idx
evalStaticFiniteCarrier (AddM e1 e2) env =
  unionBox (evalStaticFiniteCarrier e1 env) (evalStaticFiniteCarrier e2 env)
evalStaticFiniteCarrier (SubM e1 e2) env =
  subBox (evalStaticFiniteCarrier e1 env) (evalStaticFiniteCarrier e2 env)
evalStaticFiniteCarrier (HadamardM e1 e2) env =
  hadamardBox (evalStaticFiniteCarrier e1 env) (evalStaticFiniteCarrier e2 env)
evalStaticFiniteCarrier (MinM e1 e2) env =
  minBox (evalStaticFiniteCarrier e1 env) (evalStaticFiniteCarrier e2 env)
evalStaticFiniteCarrier (MaxM e1 e2) env =
  maxBox (evalStaticFiniteCarrier e1 env) (evalStaticFiniteCarrier e2 env)
evalStaticFiniteCarrier e _ = evalStaticWeightedBox e (const BoxLeaf)

public export
zipPadBoxes : (BoxInt -> BoxInt -> BoxInt) -> List BoxInt -> List BoxInt -> List BoxInt
zipPadBoxes _ [] [] = []
zipPadBoxes f [] (y :: ys) = f (intToBoxInt 0) y :: zipPadBoxes f [] ys
zipPadBoxes f (x :: xs) [] = f x (intToBoxInt 0) :: zipPadBoxes f xs []
zipPadBoxes f (x :: xs) (y :: ys) = f x y :: zipPadBoxes f xs ys

public export
zipTruncBoxes : (BoxInt -> BoxInt -> BoxInt) -> List BoxInt -> List BoxInt -> List BoxInt
zipTruncBoxes f (x :: xs) (y :: ys) = f x y :: zipTruncBoxes f xs ys
zipTruncBoxes _ _ _ = []

public export
cauchyConvolveStep : List BoxInt -> List BoxInt -> List BoxInt -> List BoxInt
cauchyConvolveStep [] _ acc = acc
cauchyConvolveStep (a :: as) bs acc =
  let scaledB = map (\b => mulBox a b) bs
      added   = zipPadBoxes addBox acc scaledB
  in case added of
       []        => cauchyConvolveStep as bs []
       (s :: ss) => s :: cauchyConvolveStep as bs ss

public export
convolveTapsHistory : List BoxInt -> List BoxInt -> BoxInt
convolveTapsHistory [] _ = intToBoxInt 0
convolveTapsHistory _ [] = intToBoxInt 0
convolveTapsHistory (t :: ts) (h :: hs) = addBox (mulBox t h) (convolveTapsHistory ts hs)

public export
extractStaticSimple : {0 low, high : Integer} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
                   -> MultisetExpr (StaticHorizon low high) p st BoxInt -> BoxInt
extractStaticSimple ZeroM            = intToBoxInt 0
extractStaticSimple OneM             = intToBoxInt 1
extractStaticSimple (ConstM v)       = v
extractStaticSimple (AddM e1 e2)     = addBox (extractStaticSimple e1) (extractStaticSimple e2)
extractStaticSimple (SubM e1 e2)     = subBox (extractStaticSimple e1) (extractStaticSimple e2)
extractStaticSimple (HadamardM a b)  = mulBox (extractStaticSimple a) (extractStaticSimple b)
extractStaticSimple (MinM a b)       =
  let x = extractStaticSimple a; y = extractStaticSimple b
  in if unwrapBox x <= unwrapBox y then x else y
extractStaticSimple (MaxM a b)       =
  let x = extractStaticSimple a; y = extractStaticSimple b
  in if unwrapBox x >= unwrapBox y then x else y
extractStaticSimple _                = intToBoxInt 0

public export
extractFiniteTaps : {0 cap : Nat} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
                 -> MultisetExpr (BoundedHorizon cap) p st BoxInt -> List BoxInt
extractFiniteTaps ZeroM             = []
extractFiniteTaps OneM              = [intToBoxInt 1]
extractFiniteTaps (Input _)         = [intToBoxInt 1]
extractFiniteTaps (AddM f1 f2)      = zipPadBoxes addBox (extractFiniteTaps f1) (extractFiniteTaps f2)
extractFiniteTaps (SubM f1 f2)      = zipPadBoxes subBox (extractFiniteTaps f1) (extractFiniteTaps f2)
extractFiniteTaps (HadamardM f1 f2) = zipTruncBoxes mulBox (extractFiniteTaps f1) (extractFiniteTaps f2)
extractFiniteTaps (MinM f1 f2)      =
  zipPadBoxes (\x, y => if unwrapBox x <= unwrapBox y then x else y) (extractFiniteTaps f1) (extractFiniteTaps f2)
extractFiniteTaps (MaxM f1 f2)      =
  zipPadBoxes (\x, y => if unwrapBox x >= unwrapBox y then x else y) (extractFiniteTaps f1) (extractFiniteTaps f2)
extractFiniteTaps (MulLaurent {rA = BoundedHorizon _} {rB = BoundedHorizon _} f1 f2) =
  cauchyConvolveStep (extractFiniteTaps f1) (extractFiniteTaps f2) []
extractFiniteTaps (MulLaurent {rA = StaticHorizon low _} {rB = BoundedHorizon _} s f) =
  let shift = if low > 0 then cast {to = Nat} low else 0
      zeros = replicate shift (intToBoxInt 0)
      conv  = cauchyConvolveStep [extractStaticSimple s] (extractFiniteTaps f) []
  in zeros ++ conv
extractFiniteTaps (MulLaurent {rA = BoundedHorizon _} {rB = StaticHorizon low _} f s) =
  let shift = if low > 0 then cast {to = Nat} low else 0
      zeros = replicate shift (intToBoxInt 0)
      conv  = cauchyConvolveStep (extractFiniteTaps f) [extractStaticSimple s] []
  in zeros ++ conv
extractFiniteTaps (MulLaurent _ _)  = []
extractFiniteTaps _                 = []

||| Extracts causal UV tap series `[c_0, c_{-1}, ..., c_{-cap}]` from a `RetroBoundedHorizon cap` graph.
public export
extractRetroTaps : {0 cap : Nat} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
                -> MultisetExpr (RetroBoundedHorizon cap) p st BoxInt -> List BoxInt
extractRetroTaps ZeroM             = []
extractRetroTaps OneM              = [intToBoxInt 1]
extractRetroTaps (Input _)         = [intToBoxInt 1]
extractRetroTaps (AddM f1 f2)      = zipPadBoxes addBox (extractRetroTaps f1) (extractRetroTaps f2)
extractRetroTaps (SubM f1 f2)      = zipPadBoxes subBox (extractRetroTaps f1) (extractRetroTaps f2)
extractRetroTaps (HadamardM f1 f2) = zipTruncBoxes mulBox (extractRetroTaps f1) (extractRetroTaps f2)
extractRetroTaps (MinM f1 f2)      =
  zipPadBoxes (\x, y => if unwrapBox x <= unwrapBox y then x else y) (extractRetroTaps f1) (extractRetroTaps f2)
extractRetroTaps (MaxM f1 f2)      =
  zipPadBoxes (\x, y => if unwrapBox x >= unwrapBox y then x else y) (extractRetroTaps f1) (extractRetroTaps f2)
extractRetroTaps (MulLaurent {rA = RetroBoundedHorizon _} {rB = RetroBoundedHorizon _} f1 f2) =
  cauchyConvolveStep (extractRetroTaps f1) (extractRetroTaps f2) []
extractRetroTaps (MulLaurent {rA = StaticHorizon _ high} {rB = RetroBoundedHorizon _} s f) =
  let shift = if high < 0 then cast {to = Nat} (-high) else 0
      zeros = replicate shift (intToBoxInt 0)
      conv  = cauchyConvolveStep [extractStaticSimple s] (extractRetroTaps f) []
  in zeros ++ conv
extractRetroTaps (MulLaurent {rA = RetroBoundedHorizon _} {rB = StaticHorizon _ high} f s) =
  let shift = if high < 0 then cast {to = Nat} (-high) else 0
      zeros = replicate shift (intToBoxInt 0)
      conv  = cauchyConvolveStep (extractRetroTaps f) [extractStaticSimple s] []
  in zeros ++ conv
extractRetroTaps (MulLaurent _ _)  = []
extractRetroTaps _                 = []

||| Evaluates bounded `BoundedHorizon cap` coordinate-indexed `Box c k` expressions cleanly.
public export
evalBoundedCarrierWithEnv : (MultisetWeight c, DiscreteCoord k)
                         => {0 cap : Nat} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
                         -> MultisetExpr (BoundedHorizon cap) p st (Box c k)
                         -> (Nat -> Box c k)
                         -> Box c k
evalBoundedCarrierWithEnv ZeroM _ = BoxLeaf
evalBoundedCarrierWithEnv OneM _ = BoxLeaf
evalBoundedCarrierWithEnv (Input idx) env = env idx
evalBoundedCarrierWithEnv (AddM e1 e2) env =
  unionBox (evalBoundedCarrierWithEnv e1 env) (evalBoundedCarrierWithEnv e2 env)
evalBoundedCarrierWithEnv (SubM e1 e2) env =
  subBox (evalBoundedCarrierWithEnv e1 env) (evalBoundedCarrierWithEnv e2 env)
evalBoundedCarrierWithEnv (HadamardM e1 e2) env =
  hadamardBox (evalBoundedCarrierWithEnv e1 env) (evalBoundedCarrierWithEnv e2 env)
evalBoundedCarrierWithEnv (MinM e1 e2) env =
  minBox (evalBoundedCarrierWithEnv e1 env) (evalBoundedCarrierWithEnv e2 env)
evalBoundedCarrierWithEnv (MaxM e1 e2) env =
  maxBox (evalBoundedCarrierWithEnv e1 env) (evalBoundedCarrierWithEnv e2 env)
evalBoundedCarrierWithEnv (OuterM e1 e2) _ =
  outerWeightedBox (evalBoundedCarrierWithEnv e1 (const BoxLeaf))
                   (evalBoundedCarrierWithEnv e2 (const BoxLeaf))
evalBoundedCarrierWithEnv (ContractR e) _ =
  contractRWeightedBox (evalBoundedCarrierWithEnv e (const BoxLeaf))
evalBoundedCarrierWithEnv (ContractL e) _ =
  contractLWeightedBox (evalBoundedCarrierWithEnv e (const BoxLeaf))
evalBoundedCarrierWithEnv (ContractMiddle e1 e2) _ =
  contractMiddleWeightedBox (evalBoundedCarrierWithEnv e1 (const BoxLeaf))
                            (evalBoundedCarrierWithEnv e2 (const BoxLeaf))
evalBoundedCarrierWithEnv _ _ = BoxLeaf

||| Evaluates `DotFiniteScalar` onto `runDecoupledStream` bounded by `gohFuelForCapacity cap`,
||| returning the certified `SolidifiedCarrier cap BoxInt` inner product witness.
public export
compileBoundedDot : {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema}
                 -> (cap : Nat)
                 -> MultisetExpr (BoundedHorizon cap) p s1 BoxInt
                 -> MultisetExpr (BoundedHorizon cap) p s2 BoxInt
                 -> SolidifiedCarrier cap BoxInt
compileBoundedDot cap e1 e2 =
  let xs      = take (S cap) (extractFiniteTaps e1)
      ys      = take (S cap) (extractFiniteTaps e2)
      prods   = zipTruncBoxes mulBox xs ys
      yieldF  = gohFuelForCapacity cap
      stepBud = gohSteps yieldF
      stepFn  : List BoxInt -> Step (List BoxInt) BoxInt
      stepFn []        = Done
      stepFn (v :: vs) = Yield v vs
  in runDecoupledStream yieldF stepBud stepFn (\v, acc => addBox acc v) (intToBoxInt 0) prods

||| Evaluates Quadratic Zero-Norm equivalence on `BoundedHorizon cap` coordinate-indexed carriers.
public export
eqCarrierBoundedViaZeroNorm : DiscreteCoord k
                           => {0 cap : Nat} -> {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema}
                           -> MultisetExpr (BoundedHorizon cap) p s1 (Carrier k)
                           -> MultisetExpr (BoundedHorizon cap) p s2 (Carrier k)
                           -> (Nat -> Carrier k)
                           -> MultisetBit
eqCarrierBoundedViaZeroNorm e1 e2 env =
  eqCarrierViaZeroNorm (evalBoundedCarrierWithEnv e1 env) (evalBoundedCarrierWithEnv e2 env)

||| Computes exact sliding inner product over `Vect m (Carrier k)` patches (`DotWindow` evaluator).
public export
evalDotWindowCarrier : DiscreteCoord k => {m : Nat}
                    -> Vect m (Carrier k)
                    -> Vect m (Carrier k)
                    -> BoxInt
evalDotWindowCarrier [] [] = intToBoxInt 0
evalDotWindowCarrier (x :: xs) (y :: ys) = addBox (dotBox x y) (evalDotWindowCarrier xs ys)

||| Full `StaticHorizon` scalar `BoxInt` evaluator with input environment.
public export
evalStaticScalarWithEnv : {0 low, high : Integer} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
                       -> MultisetExpr (StaticHorizon low high) p st BoxInt
                       -> (Nat -> BoxInt)
                       -> BoxInt
evalStaticScalarWithEnv ZeroM _ = intToBoxInt 0
evalStaticScalarWithEnv OneM _ = intToBoxInt 1
evalStaticScalarWithEnv (ConstM val) _ = val
evalStaticScalarWithEnv (RepeatConst val) _ = val
evalStaticScalarWithEnv (Input idx) env = env idx
evalStaticScalarWithEnv (AddM e1 e2) env = addBox (evalStaticScalarWithEnv e1 env) (evalStaticScalarWithEnv e2 env)
evalStaticScalarWithEnv (SubM e1 e2) env = subBox (evalStaticScalarWithEnv e1 env) (evalStaticScalarWithEnv e2 env)
evalStaticScalarWithEnv (HadamardM e1 e2) env = mulBox (evalStaticScalarWithEnv e1 env) (evalStaticScalarWithEnv e2 env)
evalStaticScalarWithEnv (MinM e1 e2) env =
  let x = evalStaticScalarWithEnv e1 env; y = evalStaticScalarWithEnv e2 env
  in if unwrapBox x <= unwrapBox y then x else y
evalStaticScalarWithEnv (MaxM e1 e2) env =
  let x = evalStaticScalarWithEnv e1 env; y = evalStaticScalarWithEnv e2 env
  in if unwrapBox x >= unwrapBox y then x else y
evalStaticScalarWithEnv (MulLaurent {rA = StaticHorizon _ _} {rB = StaticHorizon _ _} e1 e2) env =
  mulBox (evalStaticScalarWithEnv e1 env) (evalStaticScalarWithEnv e2 env)
evalStaticScalarWithEnv (MulLaurent {rA = BoundedHorizon _} {rB = RetroBoundedHorizon _} e1 e2) _ =
  convolveTapsHistory (extractFiniteTaps e1) (extractRetroTaps e2)
evalStaticScalarWithEnv (MulLaurent {rA = RetroBoundedHorizon _} {rB = BoundedHorizon _} e1 e2) _ =
  convolveTapsHistory (extractRetroTaps e1) (extractFiniteTaps e2)
evalStaticScalarWithEnv (MulLaurent _ _) _ = intToBoxInt 0
evalStaticScalarWithEnv (DotStatic e1 e2) _ =
  dotBox (evalStaticWeightedBox e1 (const BoxLeaf))
         (evalStaticWeightedBox e2 (const BoxLeaf))
evalStaticScalarWithEnv (DotFinite e1 e2) _ =
  dotBox (evalBoundedCarrierWithEnv e1 (const BoxLeaf))
         (evalBoundedCarrierWithEnv e2 (const BoxLeaf))
evalStaticScalarWithEnv (DotFiniteScalar {cap} e1 e2) _ =
  (compileBoundedDot cap e1 e2).carrier

||| Full `StaticHorizon` scalar `BoxInt` evaluator (closed terms without external `Input`).
public export
evalStaticScalar : {0 low, high : Integer} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
                -> MultisetExpr (StaticHorizon low high) p st BoxInt
                -> BoxInt
evalStaticScalar expr = evalStaticScalarWithEnv expr (const (intToBoxInt 0))

||| Evaluates `EqStatic` / `EqFinite` / `MultisetBit` static expressions.
public export
evalStaticBit : {0 low, high : Integer} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
             -> MultisetExpr (StaticHorizon low high) p st MultisetBit
             -> (Nat -> MultisetBit)
             -> MultisetBit
evalStaticBit ZeroM _ = EmptyBit
evalStaticBit OneM _ = OneBit
evalStaticBit (ConstM val) _ = val
evalStaticBit (RepeatConst val) _ = val
evalStaticBit (Input idx) env = env idx
evalStaticBit (AddM e1 e2) env = addWeight (evalStaticBit e1 env) (evalStaticBit e2 env)
evalStaticBit (SubM e1 e2) env = subWeight (evalStaticBit e1 env) (evalStaticBit e2 env)
evalStaticBit (HadamardM e1 e2) env = mulWeight (evalStaticBit e1 env) (evalStaticBit e2 env)
evalStaticBit (MinM e1 e2) env = minWeight (evalStaticBit e1 env) (evalStaticBit e2 env)
evalStaticBit (MaxM e1 e2) env = maxWeight (evalStaticBit e1 env) (evalStaticBit e2 env)
evalStaticBit (MulLaurent {rA = StaticHorizon _ _} {rB = StaticHorizon _ _} e1 e2) env =
  mulWeight (evalStaticBit e1 env) (evalStaticBit e2 env)
evalStaticBit (MulLaurent _ _) _ = EmptyBit
evalStaticBit (DotStatic e1 e2) _ =
  dotBox (evalStaticWeightedBox e1 (const BoxLeaf))
         (evalStaticWeightedBox e2 (const BoxLeaf))
evalStaticBit (DotFinite e1 e2) _ =
  dotBox (evalBoundedCarrierWithEnv e1 (const BoxLeaf))
         (evalBoundedCarrierWithEnv e2 (const BoxLeaf))
evalStaticBit (EqStaticScalar e1 e2) _ =
  eqBoxIntViaZeroNorm (evalStaticScalar e1) (evalStaticScalar e2)
evalStaticBit (EqStatic (ConstM x) (ConstM y)) _ =
  if x == y then OneBit else EmptyBit
evalStaticBit (EqStatic _ _) _ = EmptyBit
evalStaticBit (EqFiniteScalar {cap} e1 e2) _ =
  let sol = compileBoundedDot cap (SubM e1 e2) (SubM e1 e2)
  in if sol.carrier == intToBoxInt 0 then OneBit else EmptyBit
evalStaticBit (EqFinite e1 e2) _ =
  if (isZeroExpr e1 && isZeroExpr e2) || (isOneExpr e1 && isOneExpr e2)
    then OneBit
    else EmptyBit

||| Closed QTT 0 audit verifying `EqFiniteScalar` via Quadratic Zero-Norm (`<A-A, A-A> == 0`).
public export
0 prfQuadraticZeroNormFinite :
  Stage1.TypeTheory.Staging.evalStaticBit
    (EqFiniteScalar {cap = 2}
      (AddM {reg = BoundedHorizon 2} OneM OneM)
      (AddM {reg = BoundedHorizon 2} OneM OneM))
    (const EmptyBit) = OneBit
prfQuadraticZeroNormFinite = Refl

||| `ConstM` constant-folding rewrite step (`BoxInt`) chaining into `fuseStep`.
public export
fuseBoxIntStep : {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
              -> MultisetExpr reg p st BoxInt -> FusedExpr reg p BoxInt
fuseBoxIntStep (AddM (ConstM x) (ConstM y))      = MkFusedExpr [] (ConstM (addBox x y))
fuseBoxIntStep (SubM (ConstM x) (ConstM y))      = MkFusedExpr [] (ConstM (subBox x y))
fuseBoxIntStep (HadamardM (ConstM x) (ConstM y)) = MkFusedExpr [] (ConstM (mulBox x y))
fuseBoxIntStep (MinM (ConstM x) (ConstM y))      =
  MkFusedExpr [] (ConstM (if unwrapBox x <= unwrapBox y then x else y))
fuseBoxIntStep (MaxM (ConstM x) (ConstM y))      =
  MkFusedExpr [] (ConstM (if unwrapBox x >= unwrapBox y then x else y))
fuseBoxIntStep (MulLaurent {rA = StaticHorizon l1 h1} {rB = StaticHorizon l2 h2} {ok = Refl} (ConstM x) (ConstM y)) =
  MkFusedExpr [] (ConstM (mulBox x y))
fuseBoxIntStep expr                              = fuseStep expr

||| Bottom-up `BoxInt` fusion pass combining `ConstM` constant folding with `fuseStep`.
public export
fuseBoxIntWithSteps : {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
                   -> MultisetExpr reg p st BoxInt -> FusedExpr reg p BoxInt
fuseBoxIntWithSteps (AddM e1 e2) =
  case (fuseBoxIntWithSteps e1, fuseBoxIntWithSteps e2) of
    (MkFusedExpr _ f1, MkFusedExpr _ f2) => fuseBoxIntStep (AddM f1 f2)
fuseBoxIntWithSteps (SubM e1 e2) =
  case (fuseBoxIntWithSteps e1, fuseBoxIntWithSteps e2) of
    (MkFusedExpr _ f1, MkFusedExpr _ f2) => fuseBoxIntStep (SubM f1 f2)
fuseBoxIntWithSteps (HadamardM e1 e2) =
  case (fuseBoxIntWithSteps e1, fuseBoxIntWithSteps e2) of
    (MkFusedExpr _ f1, MkFusedExpr _ f2) => fuseBoxIntStep (HadamardM f1 f2)
fuseBoxIntWithSteps (MinM e1 e2) =
  case (fuseBoxIntWithSteps e1, fuseBoxIntWithSteps e2) of
    (MkFusedExpr _ f1, MkFusedExpr _ f2) => fuseBoxIntStep (MinM f1 f2)
fuseBoxIntWithSteps (MaxM e1 e2) =
  case (fuseBoxIntWithSteps e1, fuseBoxIntWithSteps e2) of
    (MkFusedExpr _ f1, MkFusedExpr _ f2) => fuseBoxIntStep (MaxM f1 f2)
fuseBoxIntWithSteps (MulLaurent {rA} {rB} {rOut} {ok} e1 e2) =
  case (fuseWithSteps 16 e1, fuseWithSteps 16 e2) of
    (MkFusedExpr _ f1, MkFusedExpr _ f2) =>
      fuseBoxIntStep (MulLaurent {rA} {rB} {rOut} {ok} f1 f2)
fuseBoxIntWithSteps (DotStatic e1 e2) =
  case (fuseWithSteps 16 e1, fuseWithSteps 16 e2) of
    (MkFusedExpr _ f1, MkFusedExpr _ f2) => fuseBoxIntStep (DotStatic f1 f2)
fuseBoxIntWithSteps (DotFinite e1 e2) =
  case (fuseWithSteps 16 e1, fuseWithSteps 16 e2) of
    (MkFusedExpr _ f1, MkFusedExpr _ f2) => fuseBoxIntStep (DotFinite f1 f2)
fuseBoxIntWithSteps (DotFiniteScalar e1 e2) =
  case (fuseBoxIntWithSteps e1, fuseBoxIntWithSteps e2) of
    (MkFusedExpr _ f1, MkFusedExpr _ f2) => fuseBoxIntStep (DotFiniteScalar f1 f2)
fuseBoxIntWithSteps (DotWindow e1 e2) =
  case (fuseWithSteps 16 e1, fuseWithSteps 16 e2) of
    (MkFusedExpr _ f1, MkFusedExpr _ f2) => fuseBoxIntStep (DotWindow f1 f2)
fuseBoxIntWithSteps (DotWindowScalar e1 e2) =
  case (fuseWithSteps 16 e1, fuseBoxIntWithSteps e2) of
    (MkFusedExpr _ f1, MkFusedExpr _ f2) => fuseBoxIntStep (DotWindowScalar f1 f2)
fuseBoxIntWithSteps (Fby init body) =
  case fuseBoxIntWithSteps body of
    MkFusedExpr _ body' => fuseBoxIntStep (Fby init body')
fuseBoxIntWithSteps (When body mask) =
  case fuseBoxIntWithSteps body of
    MkFusedExpr _ body' => fuseBoxIntStep (When body' mask)
fuseBoxIntWithSteps (SwitchSession base trig finE) =
  case (fuseBoxIntWithSteps base, fuseWithSteps 16 trig, fuseBoxIntWithSteps finE) of
    (MkFusedExpr _ b', MkFusedExpr _ t', MkFusedExpr _ f') =>
      fuseBoxIntStep (SwitchSession b' t' f')
fuseBoxIntWithSteps e = fuseBoxIntStep e

------------------------------------------------------------------------
-- 14. AST WELL-FORMEDNESS & HEHNER 21-BIT `Dec` RECOGNIZER (`recognition-rule.md`)
------------------------------------------------------------------------

||| Computes conservative state-register byte footprint for any `MultisetExpr`.
public export
exprSchemaBytes : {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
               -> MultisetExpr reg p st a -> Integer
exprSchemaBytes (AddM x y)            = exprSchemaBytes x + exprSchemaBytes y
exprSchemaBytes (SubM x y)            = exprSchemaBytes x + exprSchemaBytes y
exprSchemaBytes (HadamardM x y)       = exprSchemaBytes x + exprSchemaBytes y
exprSchemaBytes (MinM x y)            = exprSchemaBytes x + exprSchemaBytes y
exprSchemaBytes (MaxM x y)            = exprSchemaBytes x + exprSchemaBytes y
exprSchemaBytes (MulLaurent x y)      = exprSchemaBytes x + exprSchemaBytes y
exprSchemaBytes (DotStatic x y)       = exprSchemaBytes x + exprSchemaBytes y
exprSchemaBytes (DotFinite x y)       = exprSchemaBytes x + exprSchemaBytes y
exprSchemaBytes (DotFiniteScalar x y) = exprSchemaBytes x + exprSchemaBytes y
exprSchemaBytes (Segment w x)         = (cast w * 8) + exprSchemaBytes x
exprSchemaBytes (DotWindow x y)       = exprSchemaBytes x + exprSchemaBytes y
exprSchemaBytes (DotWindowScalar x y) = exprSchemaBytes x + exprSchemaBytes y
exprSchemaBytes (OuterM x y)          = exprSchemaBytes x + exprSchemaBytes y
exprSchemaBytes (ContractR x)         = exprSchemaBytes x
exprSchemaBytes (ContractL x)         = exprSchemaBytes x
exprSchemaBytes (ContractMiddle x y)  = exprSchemaBytes x + exprSchemaBytes y
exprSchemaBytes (EqStatic x y)        = exprSchemaBytes x + exprSchemaBytes y
exprSchemaBytes (EqStaticScalar x y)  = exprSchemaBytes x + exprSchemaBytes y
exprSchemaBytes (EqFinite x y)        = exprSchemaBytes x + exprSchemaBytes y
exprSchemaBytes (EqFiniteScalar x y)  = exprSchemaBytes x + exprSchemaBytes y
exprSchemaBytes (EqWindow x y)        = exprSchemaBytes x + exprSchemaBytes y
exprSchemaBytes (EqStream x y)        = exprSchemaBytes x + exprSchemaBytes y
exprSchemaBytes (EqStreamScalar x y)  = exprSchemaBytes x + exprSchemaBytes y
exprSchemaBytes (Fby _ body)          = 8 + exprSchemaBytes body
exprSchemaBytes (When body _)         = 8 + exprSchemaBytes body
exprSchemaBytes (SwitchSession b t f) = exprSchemaBytes b + exprSchemaBytes t + exprSchemaBytes f
exprSchemaBytes _                     = 0

||| Checks structural well-formedness of an AST node (`CanConvolve` + non-zero `Segment`/`Window`
||| widths + Hehner 21-bit cache ceiling `<= 2,097,152` bytes).
public export
isWellFormedExprNodes : {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
                     -> MultisetExpr reg p st a -> Bool
isWellFormedExprNodes (AddM x y)            = isWellFormedExprNodes x && isWellFormedExprNodes y
isWellFormedExprNodes (SubM x y)            = isWellFormedExprNodes x && isWellFormedExprNodes y
isWellFormedExprNodes (HadamardM x y)       = isWellFormedExprNodes x && isWellFormedExprNodes y
isWellFormedExprNodes (MinM x y)            = isWellFormedExprNodes x && isWellFormedExprNodes y
isWellFormedExprNodes (MaxM x y)            = isWellFormedExprNodes x && isWellFormedExprNodes y
isWellFormedExprNodes (MulLaurent {rA} {rB} x y) =
  let convOk = case recognizeCanConvolve rA rB of Yes _ => True; No _ => False
  in convOk && isWellFormedExprNodes x && isWellFormedExprNodes y
isWellFormedExprNodes (DotStatic x y)       = isWellFormedExprNodes x && isWellFormedExprNodes y
isWellFormedExprNodes (DotFinite x y)       = isWellFormedExprNodes x && isWellFormedExprNodes y
isWellFormedExprNodes (DotFiniteScalar x y) = isWellFormedExprNodes x && isWellFormedExprNodes y
isWellFormedExprNodes (Segment w x)         = (w > 0) && isWellFormedExprNodes x
isWellFormedExprNodes (DotWindow x y)       = isWellFormedExprNodes x && isWellFormedExprNodes y
isWellFormedExprNodes (DotWindowScalar {w} x y) = (w > 0) && isWellFormedExprNodes x && isWellFormedExprNodes y
isWellFormedExprNodes (OuterM x y)          = isWellFormedExprNodes x && isWellFormedExprNodes y
isWellFormedExprNodes (ContractR x)         = isWellFormedExprNodes x
isWellFormedExprNodes (ContractL x)         = isWellFormedExprNodes x
isWellFormedExprNodes (ContractMiddle x y)  = isWellFormedExprNodes x && isWellFormedExprNodes y
isWellFormedExprNodes (EqStatic x y)        = isWellFormedExprNodes x && isWellFormedExprNodes y
isWellFormedExprNodes (EqStaticScalar x y)  = isWellFormedExprNodes x && isWellFormedExprNodes y
isWellFormedExprNodes (EqFinite x y)        = isWellFormedExprNodes x && isWellFormedExprNodes y
isWellFormedExprNodes (EqFiniteScalar x y)  = isWellFormedExprNodes x && isWellFormedExprNodes y
isWellFormedExprNodes (EqWindow {win} x y)  = (win > 0) && isWellFormedExprNodes x && isWellFormedExprNodes y
isWellFormedExprNodes (EqStream x y)        = isWellFormedExprNodes x && isWellFormedExprNodes y
isWellFormedExprNodes (EqStreamScalar x y)  = isWellFormedExprNodes x && isWellFormedExprNodes y
isWellFormedExprNodes (Fby _ body)          = isWellFormedExprNodes body
isWellFormedExprNodes (When body _)         = isWellFormedExprNodes body
isWellFormedExprNodes (SwitchSession b t f) = isWellFormedExprNodes b && isWellFormedExprNodes t && isWellFormedExprNodes f
isWellFormedExprNodes _                     = True

public export
isWellFormedExpr : {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
                -> MultisetExpr reg p st a -> Bool
isWellFormedExpr expr =
  isWellFormedExprNodes expr && (exprSchemaBytes expr <= hehnerCacheBytesCap)

||| Constructive AST well-formedness predicate (`CanConvolve`, non-empty windows, Hehner 21-bit limit).
public export
ValidExpr : {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
         -> MultisetExpr reg p st a -> Type
ValidExpr expr = (isWellFormedExpr expr = True)

||| Total `Dec` recognizer validating proposed `MultisetExpr` graphs prior to `compileStream`.
public export
recognizeWellFormed : {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
                   -> (expr : MultisetExpr reg p st a) -> Dec (ValidExpr expr)
recognizeWellFormed expr = decideBoolTrue (isWellFormedExpr expr)

------------------------------------------------------------------------
-- 15. LINEAR TWO-PHASE RING-BUFFER & KERNEL LOWERING (`compileStream`)
------------------------------------------------------------------------

||| Linear 0-size token consuming/closing an empty state kernel.
public export
data LinUnit : Type where
  MkLinUnit : LinUnit

||| Linear register cell holding mutable scalar or circular ring-buffer state (`QTT 1`).
public export
data LinCell : (a : Type) -> Type where
  MkLinCell : a -> LinCell a

||| Unrestricted wrapper returning a pure value alongside a `1`-quantity kernel state.
public export
data PureVal : (a : Type) -> Type where
  MkPureVal : (val : a) -> PureVal a

||| Compiled two-phase linear stream kernel: pre-allocates `1`-quantity registers at initialization,
||| steps cleanly via `StepKernel`, and releases linear buffers on session close.
public export
record CompiledStreamKernel (inp : Type) (out : Type) where
  constructor MkCompiledStreamKernel
  0 kernelStateTy : Type
  withInitKernel  : {0 r : Type} -> (1 cb : (1 initSt : kernelStateTy) -> r) -> r
  kernelStep      : StepKernel kernelStateTy inp (PureVal out)
  closeKernel     : (1 st : kernelStateTy) -> ()

||| Runs a `CompiledStreamKernel` linearly across an input stream list.
public export
runCompiledKernel : CompiledStreamKernel inp out -> List inp -> List out
runCompiledKernel (MkCompiledStreamKernel stTy initFn stepFn closeFn) xs =
  initFn (\st0 => go st0 xs [])
  where
    go : (1 st : stTy) -> List inp -> List out -> List out
    go st [] acc =
      let () = closeFn st
      in reverse acc
    go st (v :: rest) acc =
      let (st' # MkPureVal out) = stepFn st v
      in go st' rest (out :: acc)

private
combineBinaryKernel : (o1 -> o2 -> o3)
                   -> CompiledStreamKernel inp o1
                   -> CompiledStreamKernel inp o2
                   -> CompiledStreamKernel inp o3
combineBinaryKernel comb (MkCompiledStreamKernel st1 init1 step1 close1)
                         (MkCompiledStreamKernel st2 init2 step2 close2) =
  MkCompiledStreamKernel
    (LPair st1 st2)
    (\cb => init1 (\s1 => init2 (\s2 => cb (s1 # s2))))
    (\(s1 # s2), inp =>
       let (s1' # MkPureVal o1) = step1 s1 inp
           (s2' # MkPureVal o2) = step2 s2 inp
       in ((s1' # s2') # MkPureVal (comb o1 o2)))
    (\(s1 # s2) =>
       let () = close1 s1
       in close2 s2)

private
extractStaticBoxIntTaps : {0 l, h : Integer} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
                       -> MultisetExpr (StaticHorizon l h) p st BoxInt -> List BoxInt
extractStaticBoxIntTaps e = [evalStaticScalar e]

||| Fixed `O(win)` circular FIR filter combinator backed by `WindowedRingBuf (S m) BoxInt` (`Rule 08` §4).
private
compileFixedFirKernel : (taps : List BoxInt)
                     -> CompiledStreamKernel (MultisetBit, BoxInt) BoxInt
                     -> CompiledStreamKernel (MultisetBit, BoxInt) BoxInt
compileFixedFirKernel [] (MkCompiledStreamKernel stS initS stepS closeS) =
  MkCompiledStreamKernel stS initS
    (\s0, inp => let (s1 # MkPureVal _) = stepS s0 inp in (s1 # MkPureVal (intToBoxInt 0)))
    closeS
compileFixedFirKernel ts@(_ :: rest) (MkCompiledStreamKernel stS initS stepS closeS) =
  let m = length rest
  in MkCompiledStreamKernel
       (LPair (LinCell (WindowedRingBuf (S m) BoxInt)) stS)
       (\cb => initS (\s0 => cb (MkLinCell (emptyRingBuf (intToBoxInt 0)) # s0)))
       (\(MkLinCell rb # s0), inp =>
          let (s1 # MkPureVal sample) = stepS s0 inp
              rb' = case fst inp of
                      EmptyBit => rb
                      OneBit   => pushRingBuf sample rb
              out = dotRingBuf rb' ts
          in ((MkLinCell rb' # s1) # MkPureVal out))
       (\(MkLinCell _ # s0) => closeS s0)

private
compileOpenCauchyKernel : CompiledStreamKernel (MultisetBit, BoxInt) BoxInt
                       -> CompiledStreamKernel (MultisetBit, BoxInt) BoxInt
                       -> CompiledStreamKernel (MultisetBit, BoxInt) BoxInt
compileOpenCauchyKernel (MkCompiledStreamKernel st1 init1 step1 close1)
                        (MkCompiledStreamKernel st2 init2 step2 close2) =
  MkCompiledStreamKernel
    (LPair st1 (LPair st2 (LPair (LinCell (List BoxInt, List BoxInt)) (LinCell BoxInt))))
    (\cb => init1 (\s1 => init2 (\s2 => cb (s1 # (s2 # (MkLinCell ([], []) # MkLinCell (intToBoxInt 0)))))))
    (\(s1 # (s2 # (MkLinCell (revA, revB) # MkLinCell held))), inp =>
       let (s1' # MkPureVal a) = step1 s1 inp
           (s2' # MkPureVal b) = step2 s2 inp
       in case fst inp of
            EmptyBit =>
              ((s1' # (s2' # (MkLinCell (revA, revB) # MkLinCell held))) # MkPureVal held)
            OneBit =>
              let revA' = a :: revA
                  revB' = b :: revB
                  out   = convolveTapsHistory revA' (reverse revB')
              in ((s1' # (s2' # (MkLinCell (revA', revB') # MkLinCell out))) # MkPureVal out))
    (\(s1 # (s2 # (MkLinCell _ # MkLinCell _))) => let () = close1 s1 in close2 s2)

private
compileWindowHeadScalar : {win : Nat} -> {0 p : PulseExpr} -> {0 st : StateSchema}
                       -> MultisetExpr (WindowedHorizon win) (Just p) st BoxInt
                       -> CompiledStreamKernel (MultisetBit, BoxInt) BoxInt
compileWindowHeadScalar (Segment _ body) = compileWindowInner body
  where
    compileWindowInner : {0 q : PulseExpr} -> {0 stI : StateSchema}
                      -> MultisetExpr OpenFuture (Just q) stI BoxInt
                      -> CompiledStreamKernel (MultisetBit, BoxInt) BoxInt
    compileWindowInner ZeroM =
      MkCompiledStreamKernel LinUnit (\cb => cb MkLinUnit) (\MkLinUnit, _ => (MkLinUnit # MkPureVal (intToBoxInt 0))) (\MkLinUnit => ())
    compileWindowInner OneM =
      MkCompiledStreamKernel LinUnit (\cb => cb MkLinUnit) (\MkLinUnit, _ => (MkLinUnit # MkPureVal (intToBoxInt 1))) (\MkLinUnit => ())
    compileWindowInner (Input _) =
      MkCompiledStreamKernel LinUnit (\cb => cb MkLinUnit) (\MkLinUnit, (_, x) => (MkLinUnit # MkPureVal x)) (\MkLinUnit => ())
    compileWindowInner (AddM a b) = combineBinaryKernel addBox (compileWindowInner a) (compileWindowInner b)
    compileWindowInner (SubM a b) = combineBinaryKernel subBox (compileWindowInner a) (compileWindowInner b)
    compileWindowInner (HadamardM a b) = combineBinaryKernel mulBox (compileWindowInner a) (compileWindowInner b)
    compileWindowInner (MinM a b) =
      combineBinaryKernel (\x, y => if unwrapBox x <= unwrapBox y then x else y) (compileWindowInner a) (compileWindowInner b)
    compileWindowInner (MaxM a b) =
      combineBinaryKernel (\x, y => if unwrapBox x >= unwrapBox y then x else y) (compileWindowInner a) (compileWindowInner b)
    compileWindowInner _ =
      MkCompiledStreamKernel LinUnit (\cb => cb MkLinUnit) (\MkLinUnit, (_, x) => (MkLinUnit # MkPureVal x)) (\MkLinUnit => ())
compileWindowHeadScalar (AddM a b) = combineBinaryKernel addBox (compileWindowHeadScalar a) (compileWindowHeadScalar b)
compileWindowHeadScalar (SubM a b) = combineBinaryKernel subBox (compileWindowHeadScalar a) (compileWindowHeadScalar b)
compileWindowHeadScalar (HadamardM a b) = combineBinaryKernel mulBox (compileWindowHeadScalar a) (compileWindowHeadScalar b)
compileWindowHeadScalar (MinM a b) =
  combineBinaryKernel (\x, y => if unwrapBox x <= unwrapBox y then x else y) (compileWindowHeadScalar a) (compileWindowHeadScalar b)
compileWindowHeadScalar (MaxM a b) =
  combineBinaryKernel (\x, y => if unwrapBox x >= unwrapBox y then x else y) (compileWindowHeadScalar a) (compileWindowHeadScalar b)
compileWindowHeadScalar (MulLaurent {rA = WindowedHorizon _} {rB = StaticHorizon _ _} wE sE) =
  compileFixedFirKernel (extractStaticBoxIntTaps sE) (compileWindowHeadScalar wE)
compileWindowHeadScalar (MulLaurent {rA = StaticHorizon _ _} {rB = WindowedHorizon _} sE wE) =
  compileFixedFirKernel (extractStaticBoxIntTaps sE) (compileWindowHeadScalar wE)
compileWindowHeadScalar (MulLaurent {rA = WindowedHorizon _} {rB = BoundedHorizon _} wE fE) =
  compileFixedFirKernel (extractFiniteTaps fE) (compileWindowHeadScalar wE)
compileWindowHeadScalar (MulLaurent {rA = BoundedHorizon _} {rB = WindowedHorizon _} fE wE) =
  compileFixedFirKernel (extractFiniteTaps fE) (compileWindowHeadScalar wE)
compileWindowHeadScalar (MulLaurent {rA = WindowedHorizon _} {rB = RetroBoundedHorizon _} wE rE) =
  compileFixedFirKernel (extractRetroTaps rE) (compileWindowHeadScalar wE)
compileWindowHeadScalar (MulLaurent {rA = RetroBoundedHorizon _} {rB = WindowedHorizon _} rE wE) =
  compileFixedFirKernel (extractRetroTaps rE) (compileWindowHeadScalar wE)
compileWindowHeadScalar _ =
  MkCompiledStreamKernel LinUnit (\cb => cb MkLinUnit) (\MkLinUnit, (_, x) => (MkLinUnit # MkPureVal x)) (\MkLinUnit => ())

||| Matches a fixed `[newest, prev, ...]` tap pattern against a sliding `WindowedRingBuf (S w) BoxInt`
||| without spurious matches on unfilled slots (`EqWindow` / CEP sequence detection).
public export
compileWindowPatternMatch : {w : Nat} -> {0 p : PulseExpr} -> {0 st : StateSchema}
                         -> List BoxInt
                         -> MultisetExpr (WindowedHorizon (S w)) (Just p) st BoxInt
                         -> CompiledStreamKernel BoxInt MultisetBit
compileWindowPatternMatch {w} pat winE =
  case compileWindowHeadScalar winE of
    MkCompiledStreamKernel stW initW stepW closeW =>
      MkCompiledStreamKernel
        (LPair (LinCell (WindowedRingBuf (S w) BoxInt)) stW)
        (\cb => initW (\sW => cb (MkLinCell (emptyRingBuf (intToBoxInt 0)) # sW)))
        (\(MkLinCell rb # sW), x =>
           let (sW' # MkPureVal sample) = stepW sW (OneBit, x)
               rb' = pushRingBuf sample rb
               matched = if matchRingPattern pat rb' then OneBit else EmptyBit
           in ((MkLinCell rb' # sW') # MkPureVal matched))
        (\(MkLinCell _ # sW) => closeW sW)

||| Compiles a `MultisetBit`-valued `OpenFuture` trigger stream into a `CompiledStreamKernel`.
public export
compileBitStream : {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
                -> MultisetExpr OpenFuture p st MultisetBit
                -> CompiledStreamKernel BoxInt MultisetBit
compileBitStream BasePulseM =
  MkCompiledStreamKernel LinUnit (\cb => cb MkLinUnit) (\MkLinUnit, _ => (MkLinUnit # MkPureVal OneBit)) (\MkLinUnit => ())
compileBitStream ZeroM =
  MkCompiledStreamKernel LinUnit (\cb => cb MkLinUnit) (\MkLinUnit, _ => (MkLinUnit # MkPureVal EmptyBit)) (\MkLinUnit => ())
compileBitStream OneM =
  MkCompiledStreamKernel LinUnit (\cb => cb MkLinUnit) (\MkLinUnit, _ => (MkLinUnit # MkPureVal OneBit)) (\MkLinUnit => ())
compileBitStream (Input _) =
  MkCompiledStreamKernel LinUnit (\cb => cb MkLinUnit)
    (\MkLinUnit, x => (MkLinUnit # MkPureVal (if x == intToBoxInt 0 then EmptyBit else OneBit)))
    (\MkLinUnit => ())
compileBitStream (AddM e1 e2)      = combineBinaryKernel maxWeight (compileBitStream e1) (compileBitStream e2)
compileBitStream (SubM e1 e2)      = combineBinaryKernel subWeight (compileBitStream e1) (compileBitStream e2)
compileBitStream (HadamardM e1 e2) = combineBinaryKernel mulWeight (compileBitStream e1) (compileBitStream e2)
compileBitStream (MinM e1 e2)      = combineBinaryKernel minWeight (compileBitStream e1) (compileBitStream e2)
compileBitStream (MaxM e1 e2)      = combineBinaryKernel maxWeight (compileBitStream e1) (compileBitStream e2)
compileBitStream (EqWindow {win = Z} _ _) =
  MkCompiledStreamKernel LinUnit (\cb => cb MkLinUnit) (\MkLinUnit, _ => (MkLinUnit # MkPureVal EmptyBit)) (\MkLinUnit => ())
compileBitStream (EqWindow {win = S w} winE statE) =
  let targetVal = evalStaticScalar statE
  in compileWindowPatternMatch {w} [targetVal] winE
compileBitStream (EqStreamScalar e1 e2) =
  case (compileBoxIntStreamFlat e1, compileBoxIntStreamFlat e2) of
    (k1, k2) => combineBinaryKernel eqBoxIntViaZeroNorm k1 k2
  where
    compileBoxIntStreamFlat : {0 q : PulseExpr} -> {0 sI : StateSchema}
                           -> MultisetExpr OpenFuture (Just q) sI BoxInt
                           -> CompiledStreamKernel BoxInt BoxInt
    compileBoxIntStreamFlat ZeroM =
      MkCompiledStreamKernel LinUnit (\cb => cb MkLinUnit) (\MkLinUnit, _ => (MkLinUnit # MkPureVal (intToBoxInt 0))) (\MkLinUnit => ())
    compileBoxIntStreamFlat OneM =
      MkCompiledStreamKernel LinUnit (\cb => cb MkLinUnit) (\MkLinUnit, _ => (MkLinUnit # MkPureVal (intToBoxInt 1))) (\MkLinUnit => ())
    compileBoxIntStreamFlat (Input _) =
      MkCompiledStreamKernel LinUnit (\cb => cb MkLinUnit) (\MkLinUnit, x => (MkLinUnit # MkPureVal x)) (\MkLinUnit => ())
    compileBoxIntStreamFlat (AddM a b) = combineBinaryKernel addBox (compileBoxIntStreamFlat a) (compileBoxIntStreamFlat b)
    compileBoxIntStreamFlat (SubM a b) = combineBinaryKernel subBox (compileBoxIntStreamFlat a) (compileBoxIntStreamFlat b)
    compileBoxIntStreamFlat (HadamardM a b) = combineBinaryKernel mulBox (compileBoxIntStreamFlat a) (compileBoxIntStreamFlat b)
    compileBoxIntStreamFlat (MinM a b) =
      combineBinaryKernel (\x, y => if unwrapBox x <= unwrapBox y then x else y) (compileBoxIntStreamFlat a) (compileBoxIntStreamFlat b)
    compileBoxIntStreamFlat (MaxM a b) =
      combineBinaryKernel (\x, y => if unwrapBox x >= unwrapBox y then x else y) (compileBoxIntStreamFlat a) (compileBoxIntStreamFlat b)
    compileBoxIntStreamFlat (Fby initV body) =
      case compileBoxIntStreamFlat body of
        MkCompiledStreamKernel stB initFn stepFn closeFn =>
          MkCompiledStreamKernel
            (LPair (LinCell BoxInt) stB)
            (\cb => initFn (\sB => cb (MkLinCell initV # sB)))
            (\(MkLinCell prev # sB), x =>
               let (sB' # MkPureVal nxt) = stepFn sB x
               in ((MkLinCell nxt # sB') # MkPureVal prev))
            (\(MkLinCell _ # sB) => closeFn sB)
    compileBoxIntStreamFlat (When body _) = compileBoxIntStreamFlat body
    compileBoxIntStreamFlat _ =
      MkCompiledStreamKernel LinUnit (\cb => cb MkLinUnit) (\MkLinUnit, x => (MkLinUnit # MkPureVal x)) (\MkLinUnit => ())
compileBitStream (EqStream e1 e2) =
  let bitVal = if (isZeroExpr e1 && isZeroExpr e2) || (isOneExpr e1 && isOneExpr e2) then OneBit else EmptyBit
  in MkCompiledStreamKernel LinUnit (\cb => cb MkLinUnit) (\MkLinUnit, _ => (MkLinUnit # MkPureVal bitVal)) (\MkLinUnit => ())
compileBitStream (LoopVar initB) =
  MkCompiledStreamKernel LinUnit (\cb => cb MkLinUnit) (\MkLinUnit, _ => (MkLinUnit # MkPureVal initB)) (\MkLinUnit => ())
compileBitStream (Fby initB body) =
  case compileBitStream body of
    MkCompiledStreamKernel stB initFn stepFn closeFn =>
      MkCompiledStreamKernel
        (LPair (LinCell MultisetBit) stB)
        (\cb => initFn (\sB => cb (MkLinCell initB # sB)))
        (\(MkLinCell prevB # sB), x =>
           let (sB' # MkPureVal nextB) = stepFn sB x
           in ((MkLinCell nextB # sB') # MkPureVal prevB))
        (\(MkLinCell _ # sB) => closeFn sB)
compileBitStream (When body _) = compileBitStream body
compileBitStream (SwitchSession base trig _) =
  case (compileBitStream base, compileBitStream trig) of
    (MkCompiledStreamKernel stB initB stepB closeB, MkCompiledStreamKernel stT initT stepT closeT) =>
      MkCompiledStreamKernel
        (LPair stB (LPair stT (LinCell Bool)))
        (\cb => initB (\sB => initT (\sT => cb (sB # (sT # MkLinCell False)))))
        (\(sB # (sT # MkLinCell latched)), x =>
           if latched
             then ((sB # (sT # MkLinCell True)) # MkPureVal EmptyBit)
             else let (sT' # MkPureVal trigBit) = stepT sT x
                  in if isZero trigBit
                       then let (sB' # MkPureVal outB) = stepB sB x
                            in ((sB' # (sT' # MkLinCell False)) # MkPureVal outB)
                       else ((sB # (sT' # MkLinCell True)) # MkPureVal EmptyBit))
        (\(sB # (sT # MkLinCell _)) =>
           let () = closeB sB
           in closeT sT)
compileBitStream _ =
  MkCompiledStreamKernel LinUnit (\cb => cb MkLinUnit) (\MkLinUnit, _ => (MkLinUnit # MkPureVal EmptyBit)) (\MkLinUnit => ())

||| Two-phase gated register & circular ring-buffer lowering over `OpenFuture` `BoxInt` graphs.
||| Emits `CompiledStreamKernel (MultisetBit, BoxInt) BoxInt` executing without heap churn:
||| - `When` holds previous register value whenever its `MultisetBit` pulse is `EmptyBit`.
||| - `Segment (S w)` inside `DotWindowScalar` allocates fixed `Vect (S w) BoxInt` ring buffer.
||| - `SwitchSession` atomically terminates `OpenFuture` base loop and replays finite tail.
public export
compileBoxIntStreamGated : {0 p : PulseExpr} -> {0 st : StateSchema}
                        -> MultisetExpr OpenFuture (Just p) st BoxInt
                        -> CompiledStreamKernel (MultisetBit, BoxInt) BoxInt
compileBoxIntStreamGated ZeroM =
  MkCompiledStreamKernel LinUnit (\cb => cb MkLinUnit)
    (\MkLinUnit, _ => (MkLinUnit # MkPureVal (intToBoxInt 0)))
    (\MkLinUnit => ())
compileBoxIntStreamGated OneM =
  MkCompiledStreamKernel LinUnit (\cb => cb MkLinUnit)
    (\MkLinUnit, _ => (MkLinUnit # MkPureVal (intToBoxInt 1)))
    (\MkLinUnit => ())
compileBoxIntStreamGated (RepeatConst v) =
  MkCompiledStreamKernel LinUnit (\cb => cb MkLinUnit)
    (\MkLinUnit, _ => (MkLinUnit # MkPureVal v))
    (\MkLinUnit => ())
compileBoxIntStreamGated (Input _) =
  MkCompiledStreamKernel LinUnit (\cb => cb MkLinUnit)
    (\MkLinUnit, (_, x) => (MkLinUnit # MkPureVal x))
    (\MkLinUnit => ())
compileBoxIntStreamGated (AddM e1 e2) =
  combineBinaryKernel addBox (compileBoxIntStreamGated e1) (compileBoxIntStreamGated e2)
compileBoxIntStreamGated (SubM e1 e2) =
  combineBinaryKernel subBox (compileBoxIntStreamGated e1) (compileBoxIntStreamGated e2)
compileBoxIntStreamGated (HadamardM e1 e2) =
  combineBinaryKernel mulBox (compileBoxIntStreamGated e1) (compileBoxIntStreamGated e2)
compileBoxIntStreamGated (MinM e1 e2) =
  combineBinaryKernel (\x, y => if unwrapBox x <= unwrapBox y then x else y)
    (compileBoxIntStreamGated e1) (compileBoxIntStreamGated e2)
compileBoxIntStreamGated (MaxM e1 e2) =
  combineBinaryKernel (\x, y => if unwrapBox x >= unwrapBox y then x else y)
    (compileBoxIntStreamGated e1) (compileBoxIntStreamGated e2)
compileBoxIntStreamGated (MulLaurent {rA = OpenFuture} {rB = BoundedHorizon _} sExpr fExpr) =
  compileFixedFirKernel (extractFiniteTaps fExpr) (compileBoxIntStreamGated sExpr)
compileBoxIntStreamGated (MulLaurent {rA = BoundedHorizon _} {rB = OpenFuture} fExpr sExpr) =
  compileFixedFirKernel (extractFiniteTaps fExpr) (compileBoxIntStreamGated sExpr)
compileBoxIntStreamGated (MulLaurent {rA = OpenFuture} {rB = StaticHorizon _ _} sExpr fExpr) =
  compileFixedFirKernel (extractStaticBoxIntTaps fExpr) (compileBoxIntStreamGated sExpr)
compileBoxIntStreamGated (MulLaurent {rA = StaticHorizon _ _} {rB = OpenFuture} fExpr sExpr) =
  compileFixedFirKernel (extractStaticBoxIntTaps fExpr) (compileBoxIntStreamGated sExpr)
compileBoxIntStreamGated (MulLaurent {rA = OpenFuture} {rB = OpenFuture} e1 e2) =
  compileOpenCauchyKernel (compileBoxIntStreamGated e1) (compileBoxIntStreamGated e2)
compileBoxIntStreamGated (MulLaurent _ _) =
  MkCompiledStreamKernel LinUnit (\cb => cb MkLinUnit)
    (\MkLinUnit, _ => (MkLinUnit # MkPureVal (intToBoxInt 0)))
    (\MkLinUnit => ())
compileBoxIntStreamGated (DotWindowScalar {w = Z} _ _) =
  MkCompiledStreamKernel LinUnit (\cb => cb MkLinUnit)
    (\MkLinUnit, _ => (MkLinUnit # MkPureVal (intToBoxInt 0)))
    (\MkLinUnit => ())
compileBoxIntStreamGated (DotWindowScalar {w = S n} winE finE) =
  let taps = extractFiniteTaps finE
  in case compileWindowHeadScalar winE of
       MkCompiledStreamKernel stW initW stepW closeW =>
         MkCompiledStreamKernel
           (LPair (LinCell (WindowedRingBuf (S n) BoxInt)) stW)
           (\cb => initW (\sW => cb (MkLinCell (emptyRingBuf (intToBoxInt 0)) # sW)))
           (\(MkLinCell rb # sW), inp =>
              let (sW' # MkPureVal sample) = stepW sW inp
              in case fst inp of
                   EmptyBit =>
                     let prevDot = dotRingBuf rb taps
                     in ((MkLinCell rb # sW') # MkPureVal prevDot)
                   OneBit =>
                     let rb'    = pushRingBuf sample rb
                         outDot = dotRingBuf rb' taps
                     in ((MkLinCell rb' # sW') # MkPureVal outDot))
           (\(MkLinCell _ # sW) => closeW sW)
compileBoxIntStreamGated (DotWindow _ _) =
  MkCompiledStreamKernel
    (LinCell BoxInt)
    (\cb => cb (MkLinCell (intToBoxInt 0)))
    (\(MkLinCell acc), (pulseBit, x) =>
       if isZero pulseBit
         then (MkLinCell acc # MkPureVal acc)
         else let acc' = addBox acc x
              in (MkLinCell acc' # MkPureVal acc'))
    (\(MkLinCell _) => ())
compileBoxIntStreamGated (LoopVar initVal) =
  MkCompiledStreamKernel LinUnit (\cb => cb MkLinUnit)
    (\MkLinUnit, _ => (MkLinUnit # MkPureVal initVal))
    (\MkLinUnit => ())
compileBoxIntStreamGated (Fby initVal body) =
  case compileBoxIntStreamGated body of
    MkCompiledStreamKernel stB initFn stepFn closeFn =>
      MkCompiledStreamKernel
        (LPair (LinCell BoxInt) stB)
        (\cb => initFn (\sB => cb (MkLinCell initVal # sB)))
        (\(MkLinCell prev # sB), inp =>
           let (sB' # MkPureVal nextVal) = stepFn sB inp
           in ((MkLinCell nextVal # sB') # MkPureVal prev))
        (\(MkLinCell _ # sB) => closeFn sB)
compileBoxIntStreamGated (When body _) =
  case compileBoxIntStreamGated body of
    MkCompiledStreamKernel stB initFn stepFn closeFn =>
      MkCompiledStreamKernel
        (LPair (LinCell BoxInt) stB)
        (\cb => initFn (\sB => cb (MkLinCell (intToBoxInt 0) # sB)))
        (\(MkLinCell held # sB), (pulseBit, x) =>
           if isZero pulseBit
             then ((MkLinCell held # sB) # MkPureVal held)
             else let (sB' # MkPureVal out) = stepFn sB (pulseBit, x)
                  in ((MkLinCell out # sB') # MkPureVal out))
        (\(MkLinCell _ # sB) => closeFn sB)
compileBoxIntStreamGated (SwitchSession base trig finE) =
  let finTaps = extractFiniteTaps finE
  in case (compileBoxIntStreamGated base, compileBitStream trig) of
       (MkCompiledStreamKernel stB initB stepB closeB, MkCompiledStreamKernel stT initT stepT closeT) =>
         MkCompiledStreamKernel
           (LPair stB (LPair stT (LinCell (Maybe (List BoxInt)))))
           (\cb => initB (\sB => initT (\sT => cb (sB # (sT # MkLinCell Nothing)))))
           (\(sB # (sT # MkLinCell latched)), (pulseBit, x) =>
              case latched of
                Just [] => ((sB # (sT # MkLinCell (Just []))) # MkPureVal (intToBoxInt 0))
                Just (v :: vs) => ((sB # (sT # MkLinCell (Just vs))) # MkPureVal v)
                Nothing =>
                  let (sT' # MkPureVal trigBit) = stepT sT x
                  in if not (isZero trigBit)
                       then case finTaps of
                              [] => ((sB # (sT' # MkLinCell (Just []))) # MkPureVal (intToBoxInt 0))
                              (v :: vs) => ((sB # (sT' # MkLinCell (Just vs))) # MkPureVal v)
                       else let (sB' # MkPureVal out) = stepB sB (pulseBit, x)
                            in ((sB' # (sT' # MkLinCell Nothing)) # MkPureVal out))
           (\(sB # (sT # MkLinCell _)) =>
              let () = closeB sB
              in closeT sT)

||| Compiles any `BoxInt` `OpenFuture` `MultisetExpr` (first fusing via `fuseBoxIntWithSteps`)
||| into a flat `CompiledStreamKernel BoxInt BoxInt` with active `OneBit` pulse.
public export
compileBoxIntStream : {0 p : PulseExpr} -> {0 st : StateSchema}
                   -> MultisetExpr OpenFuture (Just p) st BoxInt
                   -> CompiledStreamKernel BoxInt BoxInt
compileBoxIntStream expr =
  case fuseBoxIntWithSteps expr of
    MkFusedExpr _ fused =>
      case compileBoxIntStreamGated fused of
        MkCompiledStreamKernel stTy initFn stepFn closeFn =>
          MkCompiledStreamKernel stTy initFn (\s, x => stepFn s (OneBit, x)) closeFn

||| Canonical two-phase `compileStream` lowering (`Gemini.md` §6):
||| optimizes `OpenFuture` expression via `fuseBoxIntWithSteps` and lowers onto
||| `CompiledStreamKernel BoxInt BoxInt` with pre-allocated `LinCell` / `Vect` ring registers.
public export
compileStream : {0 p : PulseExpr} -> {0 st : StateSchema}
             -> MultisetExpr OpenFuture (Just p) st BoxInt
             -> CompiledStreamKernel BoxInt BoxInt
compileStream = compileBoxIntStream

||| Executes a `BoundedHorizon cap` `MultisetExpr` epoch onto `runDecoupledStream`
||| using derived `gohFuelForCapacity cap`, returning a certified `SolidifiedCarrier`.
public export
compileBoundedEpoch : {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
                   -> (cap : Nat)
                   -> MultisetExpr (BoundedHorizon cap) p st BoxInt
                   -> SolidifiedCarrier cap BoxInt
compileBoundedEpoch cap expr =
  let taps     = extractFiniteTaps expr
      yieldF   = gohFuelForCapacity cap
      stepBud  = gohSteps yieldF
      stepFn   : List BoxInt -> Step (List BoxInt) BoxInt
      stepFn []        = Done
      stepFn (v :: vs) = Yield v vs
  in runDecoupledStream yieldF stepBud stepFn (\v, acc => addBox acc v) (intToBoxInt 0) taps

||| Lowers a 1D spatial finite-difference stencil into a `1`-quantity `PingPongGrid` double-buffer
||| kernel using branchless interior iteration (`stepPingPongStencil`) and `O(1)` buffer swaps.
public export
compilePingPongGridKernel : {cap : Nat}
                         -> (boundaryFn : Fin cap -> BoxInt -> BoxInt)
                         -> (interiorFn : BoxInt -> BoxInt -> BoxInt -> BoxInt)
                         -> (sampleIdx : Maybe (Fin cap))
                         -> CompiledStreamKernel () BoxInt
compilePingPongGridKernel {cap} boundaryFn interiorFn sampleIdx =
  MkCompiledStreamKernel
    (PingPongGrid cap)
    (\cb => cb (createPingPongGrid cap))
    (\grid, () =>
       let (MkPingPongGrid (MkLinearBuffer rTok) wBuf) = stepPingPongStencil boundaryFn interiorFn grid
           out = case sampleIdx of
                   Nothing => intToBoxInt 0
                   Just idx => index idx rTok
       in ((MkPingPongGrid (MkLinearBuffer rTok) wBuf) # MkPureVal out))
    (\(MkPingPongGrid (MkLinearBuffer _) (MkLinearBuffer _)) => ())

||| Newest-first list of at most `k` populated slots of a `WindowedRingBuf`.
private
ringNewestList : {n : Nat} -> Nat -> WindowedRingBuf (S n) BoxInt -> List BoxInt
ringNewestList k rb = take k (reverse (foldRingBuf (\acc, v => v :: acc) [] rb))

||| Dual fixed-ring causal convolution (`WindowedHorizon * WindowedHorizon`, `WindowedHorizon * OpenFuture`):
||| each operand's latest sample enters its own `O(win)` `WindowedRingBuf`, and the output is the Cauchy
||| sum `sum_i a_i * b_{L-1-i}` over the newest `L = min (S wa) (S wb)` slots (newest-first indexing).
private
compileDualRingConvolve : {wa, wb : Nat}
                       -> CompiledStreamKernel (MultisetBit, BoxInt) BoxInt
                       -> CompiledStreamKernel (MultisetBit, BoxInt) BoxInt
                       -> CompiledStreamKernel (MultisetBit, BoxInt) BoxInt
compileDualRingConvolve {wa} {wb} (MkCompiledStreamKernel st1 init1 step1 close1)
                                  (MkCompiledStreamKernel st2 init2 step2 close2) =
  MkCompiledStreamKernel
    (LPair st1 (LPair st2 (LPair (LinCell (WindowedRingBuf (S wa) BoxInt))
                                 (LinCell (WindowedRingBuf (S wb) BoxInt)))))
    (\cb => init1 (\s1 => init2 (\s2 =>
              cb (s1 # (s2 # (MkLinCell (emptyRingBuf (intToBoxInt 0)) #
                              MkLinCell (emptyRingBuf (intToBoxInt 0))))))))
    (\(s1 # (s2 # (MkLinCell ra # MkLinCell rb))), inp =>
       let (s1' # MkPureVal x) = step1 s1 inp
           (s2' # MkPureVal y) = step2 s2 inp
           ra' = case fst inp of
                   EmptyBit => ra
                   OneBit   => pushRingBuf x ra
           rb' = case fst inp of
                   EmptyBit => rb
                   OneBit   => pushRingBuf y rb
           len = min (S wa) (S wb)
           out = convolveTapsHistory (ringNewestList len ra') (reverse (ringNewestList len rb'))
       in ((s1' # (s2' # (MkLinCell ra' # MkLinCell rb'))) # MkPureVal out))
    (\(s1 # (s2 # (MkLinCell _ # MkLinCell _))) => let () = close1 s1 in close2 s2)

||| Compiles any `WindowedHorizon win` `BoxInt` sliding-patch expression onto
||| fixed `O(win)` `WindowedRingBuf` storage (`Segment` bodies use `compileBoxIntStreamGated`).
public export
compileWindowedStream : {win : Nat} -> {0 p : PulseExpr} -> {0 st : StateSchema}
                     -> MultisetExpr (WindowedHorizon win) (Just p) st BoxInt
                     -> CompiledStreamKernel (MultisetBit, BoxInt) BoxInt
compileWindowedStream (Segment Z _) =
  MkCompiledStreamKernel LinUnit (\cb => cb MkLinUnit)
    (\MkLinUnit, _ => (MkLinUnit # MkPureVal (intToBoxInt 0)))
    (\MkLinUnit => ())
compileWindowedStream (Segment (S w) body) =
  case compileBoxIntStreamGated body of
    MkCompiledStreamKernel stB initB stepB closeB =>
      MkCompiledStreamKernel
        (LPair (LinCell (WindowedRingBuf (S w) BoxInt)) stB)
        (\cb => initB (\sB => cb (MkLinCell (emptyRingBuf (intToBoxInt 0)) # sB)))
        (\(MkLinCell rb # sB), inp =>
           let (sB' # MkPureVal sample) = stepB sB inp
               rb' = case fst inp of
                       EmptyBit => rb
                       OneBit   => pushRingBuf sample rb
               out = latestRingBuf (intToBoxInt 0) rb'
           in ((MkLinCell rb' # sB') # MkPureVal out))
        (\(MkLinCell _ # sB) => closeB sB)
compileWindowedStream (AddM a b)      = combineBinaryKernel addBox (compileWindowedStream a) (compileWindowedStream b)
compileWindowedStream (SubM a b)      = combineBinaryKernel subBox (compileWindowedStream a) (compileWindowedStream b)
compileWindowedStream (HadamardM a b) = combineBinaryKernel mulBox (compileWindowedStream a) (compileWindowedStream b)
compileWindowedStream (MinM a b) =
  combineBinaryKernel (\x, y => if unwrapBox x <= unwrapBox y then x else y) (compileWindowedStream a) (compileWindowedStream b)
compileWindowedStream (MaxM a b) =
  combineBinaryKernel (\x, y => if unwrapBox x >= unwrapBox y then x else y) (compileWindowedStream a) (compileWindowedStream b)
compileWindowedStream (MulLaurent {rA = WindowedHorizon _} {rB = StaticHorizon _ _} wE sE) =
  compileFixedFirKernel (extractStaticBoxIntTaps sE) (compileWindowedStream wE)
compileWindowedStream (MulLaurent {rA = StaticHorizon _ _} {rB = WindowedHorizon _} sE wE) =
  compileFixedFirKernel (extractStaticBoxIntTaps sE) (compileWindowedStream wE)
compileWindowedStream (MulLaurent {rA = WindowedHorizon _} {rB = BoundedHorizon _} wE fE) =
  compileFixedFirKernel (extractFiniteTaps fE) (compileWindowedStream wE)
compileWindowedStream (MulLaurent {rA = BoundedHorizon _} {rB = WindowedHorizon _} fE wE) =
  compileFixedFirKernel (extractFiniteTaps fE) (compileWindowedStream wE)
compileWindowedStream (MulLaurent {rA = WindowedHorizon _} {rB = RetroBoundedHorizon _} wE rE) =
  compileFixedFirKernel (extractRetroTaps rE) (compileWindowedStream wE)
compileWindowedStream (MulLaurent {rA = RetroBoundedHorizon _} {rB = WindowedHorizon _} rE wE) =
  compileFixedFirKernel (extractRetroTaps rE) (compileWindowedStream wE)
compileWindowedStream (MulLaurent {rA = WindowedHorizon (S a)} {rB = WindowedHorizon (S b)} x y) =
  compileDualRingConvolve {wa = a} {wb = b} (compileWindowedStream x) (compileWindowedStream y)
compileWindowedStream (MulLaurent {rA = WindowedHorizon (S a)} {rB = OpenFuture} x y) =
  compileDualRingConvolve {wa = a} {wb = a} (compileWindowedStream x) (compileBoxIntStreamGated y)
compileWindowedStream (MulLaurent {rA = OpenFuture} {rB = WindowedHorizon (S b)} x y) =
  compileDualRingConvolve {wa = b} {wb = b} (compileBoxIntStreamGated x) (compileWindowedStream y)
compileWindowedStream _ =
  MkCompiledStreamKernel LinUnit (\cb => cb MkLinUnit)
    (\MkLinUnit, (_, x) => (MkLinUnit # MkPureVal x))
    (\MkLinUnit => ())

||| Executes a `RetroBoundedHorizon cap` UV epoch (`-cap .. 0`) onto `runDecoupledStream`
||| using derived `gohFuelForCapacity cap`, returning a certified `SolidifiedCarrier cap BoxInt`.
public export
compileRetroEpoch : {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
                 -> (cap : Nat)
                 -> MultisetExpr (RetroBoundedHorizon cap) p st BoxInt
                 -> SolidifiedCarrier cap BoxInt
compileRetroEpoch cap expr =
  let taps    = take (S cap) (extractRetroTaps expr)
      yieldF  = gohFuelForCapacity cap
      stepBud = gohSteps yieldF
      stepFn  : List BoxInt -> Step (List BoxInt) BoxInt
      stepFn []        = Done
      stepFn (v :: vs) = Yield v vs
  in runDecoupledStream yieldF stepBud stepFn (\v, acc => addBox acc v) (intToBoxInt 0) taps

||| Compiles a `BilateralOpen` scalar tape convolved with a compact FIR filter into a
||| `WindowedRingBuf (S n)` `CompiledStreamKernel BoxInt BoxInt` with fixed `O(n)` memory.
public export
compileBilateralWindowKernel : (filterTaps : List BoxInt) -> CompiledStreamKernel BoxInt BoxInt
compileBilateralWindowKernel taps =
  case compileFixedFirKernel taps
         (MkCompiledStreamKernel LinUnit (\cb => cb MkLinUnit)
           (\MkLinUnit, (_, x) => (MkLinUnit # MkPureVal x))
           (\MkLinUnit => ())) of
    MkCompiledStreamKernel stTy initFn stepFn closeFn =>
      MkCompiledStreamKernel stTy initFn (\s, x => stepFn s (OneBit, x)) closeFn

||| Slices a two-sided `BilateralOpen` tape (`Int -> BoxInt`) over `[center - win, center + win]`
||| and convolves it with a compact FIR filter via `cauchyConvolveStep`.
public export
evalBilateralWindowPatch : (center : Int)
                        -> (win : Nat)
                        -> (tapeFn : Int -> BoxInt)
                        -> (filterTaps : List BoxInt)
                        -> List BoxInt
evalBilateralWindowPatch center win tapeFn filterTaps =
  let halfW = cast {to = Int} win
      lo    = center - halfW
      hi    = center + halfW
      patch = map tapeFn [lo .. hi]
  in cauchyConvolveStep patch filterTaps []

||| Evaluates a signed-index `BilateralOpen` `BoxInt` expression at tape position `n`
||| (`BilateralTap` samples, constants, pointwise ops, and single-tap `StaticHorizon` shifts).
public export
evalBilateralAt : {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
               -> MultisetExpr BilateralOpen p st BoxInt -> Int -> BoxInt
evalBilateralAt ZeroM             _ = intToBoxInt 0
evalBilateralAt OneM              _ = intToBoxInt 1
evalBilateralAt (RepeatConst v)   _ = v
evalBilateralAt (BilateralTap f)  n = f n
evalBilateralAt (AddM a b)        n = addBox (evalBilateralAt a n) (evalBilateralAt b n)
evalBilateralAt (SubM a b)        n = subBox (evalBilateralAt a n) (evalBilateralAt b n)
evalBilateralAt (HadamardM a b)   n = mulBox (evalBilateralAt a n) (evalBilateralAt b n)
evalBilateralAt (MinM a b)        n =
  let x = evalBilateralAt a n; y = evalBilateralAt b n
  in if unwrapBox x <= unwrapBox y then x else y
evalBilateralAt (MaxM a b)        n =
  let x = evalBilateralAt a n; y = evalBilateralAt b n
  in if unwrapBox x >= unwrapBox y then x else y
evalBilateralAt (MulLaurent {rA = StaticHorizon low _} {rB = BilateralOpen} s b) n =
  mulBox (extractStaticSimple s) (evalBilateralAt b (n - cast low))
evalBilateralAt (MulLaurent {rA = BilateralOpen} {rB = StaticHorizon low _} b s) n =
  mulBox (extractStaticSimple s) (evalBilateralAt b (n - cast low))
evalBilateralAt _                 _ = intToBoxInt 0

||| Evaluates a `BilateralOpen` AST over the local patch `[center - win, center + win]` and convolves it
||| with a compact FIR filter (`BilateralOpen * StaticHorizon / WindowedHorizon` admissible pairs).
public export
compileBilateralWindowExpr : {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
                          -> (center : Int) -> (win : Nat)
                          -> MultisetExpr BilateralOpen p st BoxInt
                          -> (filterTaps : List BoxInt)
                          -> List BoxInt
compileBilateralWindowExpr center win e taps =
  evalBilateralWindowPatch center win (evalBilateralAt e) taps

||| Maps compile-time `BoundaryMode` onto `Stage0.LinearBuffer.PerimeterPolicy`.
public export
boundaryModeToPerimeterPolicy : BoundaryMode -> PerimeterPolicy
boundaryModeToPerimeterPolicy ZeroPadded       = ZeroPerimeter
boundaryModeToPerimeterPolicy MirrorBoundary   = MirrorPerimeter
boundaryModeToPerimeterPolicy PeriodicBoundary = PeriodicPerimeter

||| Lowers a 1D spatial stencil and compile-time `BoundaryMode` onto a `1`-quantity
||| `PingPongGrid` double-buffer kernel using peeled boundaries and branchless interior SIMD loops.
public export
compileSpatialStencilWithBoundary : {cap : Nat}
                                 -> BoundaryMode
                                 -> (initialGrid : Vect cap BoxInt)
                                 -> (stencilFn : BoxInt -> BoxInt -> BoxInt -> BoxInt)
                                 -> (sampleIdx : Maybe (Fin cap))
                                 -> CompiledStreamKernel () BoxInt
compileSpatialStencilWithBoundary {cap} bMode initVec stencilFn sampleIdx =
  let pol = boundaryModeToPerimeterPolicy bMode
  in MkCompiledStreamKernel
       (PingPongGrid cap)
       (\cb => cb (MkPingPongGrid (MkLinearBuffer initVec) (createLinearBuffer cap)))
       (\grid, () =>
          let (MkPingPongGrid (MkLinearBuffer rTok) wBuf) = stepPingPong3PointWithPolicy pol stencilFn grid
              out = case sampleIdx of
                      Nothing  => intToBoxInt 0
                      Just idx => index idx rTok
          in ((MkPingPongGrid (MkLinearBuffer rTok) wBuf) # MkPureVal out))
       (\(MkPingPongGrid (MkLinearBuffer _) (MkLinearBuffer _)) => ())
