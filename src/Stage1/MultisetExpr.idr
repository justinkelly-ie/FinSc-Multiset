module Stage1.MultisetExpr

import Data.Vect
import public Stage0.BoxInt
import public Stage0.Box
import public Stage0.SignedBit
import public Stage0.HereditaryMSet
import public Stage1.ConvolutionAdmissibility

%default total

------------------------------------------------------------------------
-- 1. PULSE CLOCKS, STATE SCHEMAS & HORIZON TYPE-LEVEL HELPERS
------------------------------------------------------------------------

||| Temporal and causal activation clock index (`0`-quantity meta-level):
||| Models periodic heartbeats, event arrivals, and endogenous mass thresholds.
public export
data PulseExpr : Type where
  BasePulse     : PulseExpr
  ZeroPulse     : PulseExpr
  OnePulse      : PulseExpr
  AddPulse      : PulseExpr -> PulseExpr -> PulseExpr
  HadamardPulse : PulseExpr -> PulseExpr -> PulseExpr
  MassPulse     : (threshold : Nat) -> PulseExpr

||| Compile-time linear state schema tracking QTT `1`-quantity buffers (`LinBuf`, `PingPongGrid`).
public export
StateSchema : Type
StateSchema = List Type

||| Coordinate-indexed multiset carrier (`Box c k`).
public export
Carrier : (c : Type) -> (k : Type) -> Type
Carrier c k = Box c k

||| Compile-time check identifying regimes with bounded support where global
||| inner products (`DotM`) and total mass sums are well-defined.
public export
IsBoundedRegime : LaurentRegime -> Bool
IsBoundedRegime (StaticHorizon _ _) = True
IsBoundedRegime (BoundedHorizon _)  = True
IsBoundedRegime (WindowedHorizon _) = True
IsBoundedRegime _                   = False

||| Determines the output regime of algebraic equality (`EqM`) across horizons:
||| - Bounded horizons collapse into a single static `MultisetBit` (`StaticHorizon 0 0`).
||| - Open horizons emit a live `OpenFuture` stream of tick-by-tick match pulses.
public export
EqReturnRegime : LaurentRegime -> LaurentRegime
EqReturnRegime (StaticHorizon _ _)     = StaticHorizon 0 0
EqReturnRegime (BoundedHorizon _)      = StaticHorizon 0 0
EqReturnRegime (RetroBoundedHorizon _) = StaticHorizon 0 0
EqReturnRegime (WindowedHorizon _)     = OpenFuture
EqReturnRegime OpenFuture              = OpenFuture
EqReturnRegime BilateralOpen           = OpenFuture

||| Computes the resulting `LaurentRegime` for `HyperOpM level`:
||| - `level = 0` (`+`): Pointwise union requires matching regimes (`rA == rB`).
||| - `level = 1` (`*`): Cauchy convolution guarded by `admissibleConvolution rA rB`.
||| - `level >= 2` (`^`, ...): Caretation guarded by `caretRegime rA rB`.
public export
hyperOpRegime : (level : Nat) -> LaurentRegime -> LaurentRegime -> Maybe LaurentRegime
hyperOpRegime Z rA rB =
  case decEq rA rB of
    Yes _ => Just rA
    No _  => Nothing
hyperOpRegime (S Z) rA rB =
  admissibleConvolution rA rB
hyperOpRegime (S (S _)) rA rB =
  caretRegime rA rB

------------------------------------------------------------------------
-- 2. UNIFIED STAGE-1 EXPRESSION GADT (`MultisetExpr`)
------------------------------------------------------------------------

||| Unified Stage-1 Expression AST over pure `HereditaryMSet c` and `Carrier c k`:
||| - `reg`   : `0`-quantity `LaurentRegime` (horizon topology on Z)
||| - `pulse` : `0`-quantity `Maybe PulseExpr` (activation clock / proper time)
||| - `st`    : `0`-quantity `StateSchema` (pre-allocated QTT `1` buffer layout)
||| - `a`     : Payload type (`HereditaryMSet c` or `Carrier c k`)
public export
data MultisetExpr : (0 reg   : LaurentRegime)
                 -> (0 pulse : Maybe PulseExpr)
                 -> (0 st    : StateSchema)
                 -> (a       : Type)
                 -> Type where

  -- A. PRIMITIVE SOURCES & CONSTANTS
  BasePulseM : MultisetExpr OpenFuture Nothing [] MultisetBit

  ZeroM      : {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr}
            -> MultisetExpr reg p [] a

  OneM       : {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr}
            -> MultisetExpr reg p [] a

  ConstM     : {0 p : Maybe PulseExpr} -> {0 low, high : Integer}
            -> (val : a)
            -> MultisetExpr (StaticHorizon low high) p [] a

  Input      : {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr}
            -> (idx : Nat)
            -> MultisetExpr reg p [] a

  -- B. UNIFIED RECURSIVE HYPER-OPERATION TOWER (`0 = +`, `1 = *`, `2 = ^`, ...)
  HyperOpM   : {rA, rB : LaurentRegime} -> {0 rOut : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema}
            -> (level : Nat)
            -> {auto 0 ok : hyperOpRegime level rA rB = Just rOut}
            -> MultisetExpr rA p s1 a
            -> MultisetExpr rB p s2 a
            -> MultisetExpr rOut p (s1 ++ s2) a

  -- C. POINTWISE DIFFERENCE, HADAMARD & TROPICAL LATTICE ENVELOPES
  SubM       : {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema}
            -> MultisetExpr reg p s1 a
            -> MultisetExpr reg p s2 a
            -> MultisetExpr reg p (s1 ++ s2) a

  HadamardM  : {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema}
            -> MultisetExpr reg p s1 a
            -> MultisetExpr reg p s2 a
            -> MultisetExpr reg p (s1 ++ s2) a

  MinM       : {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema}
            -> MultisetExpr reg p s1 a
            -> MultisetExpr reg p s2 a
            -> MultisetExpr reg p (s1 ++ s2) a

  MaxM       : {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema}
            -> MultisetExpr reg p s1 a
            -> MultisetExpr reg p s2 a
            -> MultisetExpr reg p (s1 ++ s2) a

  -- D. UNIFIED INNER PRODUCT / TRACE (GUARDED BY `IsBoundedRegime`)
  DotM       : {0 c : Type} -> {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema}
            -> {auto 0 bounded : IsBoundedRegime reg = True}
            -> MultisetExpr reg p s1 (HereditaryMSet c)
            -> MultisetExpr reg p s2 (HereditaryMSet c)
            -> MultisetExpr (StaticHorizon 0 0) p (s1 ++ s2) c

  -- E. UNIFIED ALGEBRAIC EQUALITY (`EqM`: QUADRATIC ZERO-NORM ON BOUNDED REGIMES)
  EqM        : {0 c : Type} -> MultisetWeight c
            => {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema}
            -> MultisetExpr reg p s1 (HereditaryMSet c)
            -> MultisetExpr reg p s2 (HereditaryMSet c)
            -> MultisetExpr (EqReturnRegime reg) p (s1 ++ s2) MultisetBit

  -- F. HORIZON SLICING, CAUSAL DELAY (`Fby`) & CLOCK GATING (`When`)
  Segment    : {0 k : Type} -> {0 p : PulseExpr} -> {0 st : StateSchema} -> (winSize : Nat)
            -> MultisetExpr OpenFuture (Just p) st k
            -> MultisetExpr (WindowedHorizon winSize) (Just p) (Vect winSize k :: st) k

  SliceEpoch : {0 p : Maybe PulseExpr} -> {0 st : StateSchema} -> (cap : Nat)
            -> MultisetExpr OpenFuture p st a
            -> MultisetExpr (BoundedHorizon cap) p st a

  Fby        : {0 p : PulseExpr} -> {0 s1, s2 : StateSchema}
            -> MultisetExpr (StaticHorizon 0 0) Nothing s1 a
            -> MultisetExpr OpenFuture (Just p) s2 a
            -> MultisetExpr OpenFuture (Just p) (a :: (s1 ++ s2)) a

  When       : {0 reg : LaurentRegime} -> {0 p : PulseExpr} -> {0 s1, s2 : StateSchema}
            -> MultisetExpr reg (Just p) s1 a
            -> MultisetExpr reg (Just p) s2 MultisetBit
            -> MultisetExpr reg (Just p) (s1 ++ s2) a

  -- G. MULTIPLICITY CARRIER PROJECTIONS (`BoxInt` -> `SignedBit` -> `MultisetBit`)
  ProjectSupportM : {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
                 -> MultisetExpr reg p st (HereditaryMSet BoxInt)
                 -> MultisetExpr reg p st (HereditaryMSet MultisetBit)

  ProjectSignedM  : {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema}
                 -> MultisetExpr reg p st (HereditaryMSet BoxInt)
                 -> MultisetExpr reg p st (HereditaryMSet SignedBit)

------------------------------------------------------------------------
-- 3. ERGONOMIC SMART CONSTRUCTORS (`+`, `*`, `^`, `CosmicExpr`)
------------------------------------------------------------------------

||| Ergonomic type alias for pure hereditary multiset expressions over carrier `c`.
public export
CosmicExpr : (0 reg : LaurentRegime) -> (c : Type) -> Type
CosmicExpr reg c = MultisetExpr reg Nothing [] (HereditaryMSet c)

||| Level 0 Superposition (`+`)
public export
addExpr : {reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema}
       -> {auto 0 ok : hyperOpRegime 0 reg reg = Just reg}
       -> MultisetExpr reg p s1 a -> MultisetExpr reg p s2 a -> MultisetExpr reg p (s1 ++ s2) a
addExpr = HyperOpM 0

||| Level 1 Cauchy / Laurent Convolution (`*`)
public export
mulExpr : {rA, rB : LaurentRegime} -> {0 rOut : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema}
       -> {auto 0 ok : hyperOpRegime 1 rA rB = Just rOut}
       -> MultisetExpr rA p s1 a -> MultisetExpr rB p s2 a -> MultisetExpr rOut p (s1 ++ s2) a
mulExpr = HyperOpM 1

||| Level 2 Dirichlet Caretation (`^`)
public export
caretExpr : {rA, rB : LaurentRegime} -> {0 rOut : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema}
         -> {auto 0 ok : hyperOpRegime 2 rA rB = Just rOut}
         -> MultisetExpr rA p s1 a -> MultisetExpr rB p s2 a -> MultisetExpr rOut p (s1 ++ s2) a
caretExpr = HyperOpM 2
