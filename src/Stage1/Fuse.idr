module Stage1.Fuse

import Data.Vect
import public Stage0.BoxInt
import public Stage0.Box
import public Stage0.SignedBit
import public Stage0.HereditaryMSet
import public Stage0.StructuralFuel
import public Stage1.ConvolutionAdmissibility
import public Stage1.MultisetExpr

%default total

------------------------------------------------------------------------
-- 1. MF 234-236 BASIS HELPERS (`convolveWith` / `hyperOp` IN `Stage0.HereditaryMSet`)
------------------------------------------------------------------------

||| Alternating Binomial `A_n = alpha^n - alpha^(-n)` (MF 234).
public export
altBinomial : Integer -> PureMultiset
altBinomial n =
  subHMSet (MkHMSet (setBox (stage0SignedKey n) (intToBoxInt 1) BoxLeaf))
           (MkHMSet (setBox (stage0SignedKey (negate n)) (intToBoxInt 1) BoxLeaf))

||| Central Polynumber `C_n = alpha^(-n) + alpha^(-n+2) + ... + alpha^n` (MF 234/235).
public export
centralPoly : Nat -> PureMultiset
centralPoly n = buildShells (S n) (negate (natToInteger n))
  where
    buildShells : Nat -> Integer -> PureMultiset
    buildShells Z _ = emptyHMSet
    buildShells (S rem) expK =
      addHMSet (MkHMSet (setBox (stage0SignedKey expK) (intToBoxInt 1) BoxLeaf))
               (buildShells rem (expK + 2))

------------------------------------------------------------------------
-- 2. AXIOM-FREE `0`-QUANTITY REGIME UNIFICATION LEMMAS 
------------------------------------------------------------------------

||| `0`-quantity lemma: for `level = 0`, `hyperOpRegime 0 rA rB = Just reg`
||| proves `rA = reg` and `rB = reg` directly via `decEq` and `Refl`.
public export
0 matchingRegimeZ : (rA, rB, reg : LaurentRegime) ->
                    hyperOpRegime Z rA rB = Just reg ->
                    (rA = reg, rB = reg)
matchingRegimeZ rA rB reg prf with (decEq rA rB)
  matchingRegimeZ rA rA rA Refl | Yes Refl = (Refl, Refl)
  matchingRegimeZ rA rB reg prf | No _     = case prf of Refl impossible

||| `0`-quantity lemma: for `level >= 2`, `caretRegime` on `ConstM ^ ConstM` yields
||| the tight static bounds `[caretStaticLow, caretStaticHigh]` with zero `believe_me`.
public export
0 caretStaticRegime : (l1, h1, l2, h2 : Integer) -> (reg : LaurentRegime) ->
                      caretRegime (StaticHorizon l1 h1) (StaticHorizon l2 h2) = Just reg ->
                      StaticHorizon (caretStaticLow l1 h1 l2 h2) (caretStaticHigh l1 h1 l2 h2) = reg
caretStaticRegime _ _ _ _ _ Refl = Refl

||| `0`-quantity lemma for `OneM * e` at Level 1 (`StaticHorizon 0 0` unit) on non-static regimes.
public export
0 leftUnitOpen : (reg : LaurentRegime) ->
                 admissibleConvolution (StaticHorizon 0 0) OpenFuture = Just reg ->
                 OpenFuture = reg
leftUnitOpen _ Refl = Refl

public export
0 leftUnitBilateral : (reg : LaurentRegime) ->
                      admissibleConvolution (StaticHorizon 0 0) BilateralOpen = Just reg ->
                      BilateralOpen = reg
leftUnitBilateral _ Refl = Refl

public export
0 leftUnitBounded : (c : Nat) -> (reg : LaurentRegime) ->
                    admissibleConvolution (StaticHorizon 0 0) (BoundedHorizon c) = Just reg ->
                    BoundedHorizon c = reg
leftUnitBounded _ _ Refl = Refl

public export
0 leftUnitRetro : (c : Nat) -> (reg : LaurentRegime) ->
                  admissibleConvolution (StaticHorizon 0 0) (RetroBoundedHorizon c) = Just reg ->
                  RetroBoundedHorizon c = reg
leftUnitRetro _ _ Refl = Refl

public export
0 leftUnitWindowed : (w : Nat) -> (reg : LaurentRegime) ->
                     admissibleConvolution (StaticHorizon 0 0) (WindowedHorizon w) = Just reg ->
                     WindowedHorizon w = reg
leftUnitWindowed _ _ Refl = Refl

||| `0`-quantity lemmas for `e * OneM` at Level 1 (`StaticHorizon 0 0` unit) on non-static regimes.
public export
0 rightUnitOpen : (reg : LaurentRegime) ->
                  admissibleConvolution OpenFuture (StaticHorizon 0 0) = Just reg ->
                  OpenFuture = reg
rightUnitOpen _ Refl = Refl

public export
0 rightUnitBilateral : (reg : LaurentRegime) ->
                       admissibleConvolution BilateralOpen (StaticHorizon 0 0) = Just reg ->
                       BilateralOpen = reg
rightUnitBilateral _ Refl = Refl

public export
0 rightUnitBounded : (c : Nat) -> (reg : LaurentRegime) ->
                     admissibleConvolution (BoundedHorizon c) (StaticHorizon 0 0) = Just reg ->
                     BoundedHorizon c = reg
rightUnitBounded _ _ Refl = Refl

public export
0 rightUnitRetro : (c : Nat) -> (reg : LaurentRegime) ->
                   admissibleConvolution (RetroBoundedHorizon c) (StaticHorizon 0 0) = Just reg ->
                   RetroBoundedHorizon c = reg
rightUnitRetro _ _ Refl = Refl

public export
0 rightUnitWindowed : (w : Nat) -> (reg : LaurentRegime) ->
                      admissibleConvolution (WindowedHorizon w) (StaticHorizon 0 0) = Just reg ->
                      WindowedHorizon w = reg
rightUnitWindowed _ _ Refl = Refl

||| `0`-quantity lemma for `ConstM * ConstM` at Level 1.
public export
0 staticMulRegime : (l1, h1, l2, h2 : Integer) -> (reg : LaurentRegime) ->
                    admissibleConvolution (StaticHorizon l1 h1) (StaticHorizon l2 h2) = Just reg ->
                    StaticHorizon (l1 + l2) (h1 + h2) = reg
staticMulRegime _ _ _ _ _ Refl = Refl

||| `0`-quantity associative kernel pre-contraction lemma on `OpenFuture`.
public export
0 assocOpenStaticKernel :
  (l1, h1, l2, h2 : Integer) ->
  (rMid, reg : LaurentRegime) ->
  admissibleConvolution OpenFuture (StaticHorizon l1 h1) = Just rMid ->
  admissibleConvolution rMid (StaticHorizon l2 h2) = Just reg ->
  admissibleConvolution OpenFuture (StaticHorizon (l1 + l2) (h1 + h2)) = Just reg
assocOpenStaticKernel _ _ _ _ _ _ Refl Refl = Refl

||| `0`-quantity associative kernel pre-contraction lemma on `BilateralOpen`.
public export
0 assocBilateralStaticKernel :
  (l1, h1, l2, h2 : Integer) ->
  (rMid, reg : LaurentRegime) ->
  admissibleConvolution BilateralOpen (StaticHorizon l1 h1) = Just rMid ->
  admissibleConvolution rMid (StaticHorizon l2 h2) = Just reg ->
  admissibleConvolution BilateralOpen (StaticHorizon (l1 + l2) (h1 + h2)) = Just reg
assocBilateralStaticKernel _ _ _ _ _ _ Refl Refl = Refl

------------------------------------------------------------------------
-- 3. STRUCTURAL AST EQUALITY & EXISTENTIAL `FusedExpr` WRAPPER
------------------------------------------------------------------------

||| Structural equality check on `MultisetExpr` nodes for compile-time
||| cancellation rewrites (`SubM x x -> ZeroM`, `EqM x x -> OneM`).
public export
exprStructEq : Eq a =>
               MultisetExpr r1 p1 s1 a ->
               MultisetExpr r2 p2 s2 a ->
               Bool
exprStructEq BasePulseM BasePulseM = True
exprStructEq ZeroM ZeroM = True
exprStructEq OneM OneM = True
exprStructEq (Input i) (Input j) = i == j
exprStructEq (ConstM v1) (ConstM v2) = v1 == v2
exprStructEq (HyperOpM l1 a1 b1) (HyperOpM l2 a2 b2) =
  (l1 == l2) && exprStructEq a1 a2 && exprStructEq b1 b2
exprStructEq (SubM a1 b1) (SubM a2 b2) =
  exprStructEq a1 a2 && exprStructEq b1 b2
exprStructEq (HadamardM a1 b1) (HadamardM a2 b2) =
  exprStructEq a1 a2 && exprStructEq b1 b2
exprStructEq (MinM a1 b1) (MinM a2 b2) =
  exprStructEq a1 a2 && exprStructEq b1 b2
exprStructEq (MaxM a1 b1) (MaxM a2 b2) =
  exprStructEq a1 a2 && exprStructEq b1 b2
exprStructEq (Segment w1 e1) (Segment w2 e2) =
  (w1 == w2) && exprStructEq e1 e2
exprStructEq (SliceEpoch c1 e1) (SliceEpoch c2 e2) =
  (c1 == c2) && exprStructEq e1 e2
exprStructEq (Fby i1 s1) (Fby i2 s2) =
  exprStructEq i1 i2 && exprStructEq s1 s2
exprStructEq (When e1 m1) (When e2 m2) =
  exprStructEq e1 e2 && exprStructEq m1 m2
exprStructEq _ _ = False

||| Existential wrapper hiding the shrunk `StateSchema` after `fuse`.
public export
record FusedExpr (0 reg : LaurentRegime) (0 p : Maybe PulseExpr) (a : Type) where
  constructor MkFusedExpr
  0 schema : StateSchema
  expr     : MultisetExpr reg p schema a

private
tryLeftUnit : {rA, rB : LaurentRegime} -> {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema}
           -> {0 ok : admissibleConvolution rA rB = Just reg}
           -> MultisetExpr rA p s1 a -> MultisetExpr rB p s2 a
           -> FusedExpr reg p a
tryLeftUnit {rA = StaticHorizon 0 0} {rB = OpenFuture}            {ok} _ b' = rewrite sym (leftUnitOpen reg ok) in MkFusedExpr _ b'
tryLeftUnit {rA = StaticHorizon 0 0} {rB = BilateralOpen}         {ok} _ b' = rewrite sym (leftUnitBilateral reg ok) in MkFusedExpr _ b'
tryLeftUnit {rA = StaticHorizon 0 0} {rB = BoundedHorizon c}      {ok} _ b' = rewrite sym (leftUnitBounded c reg ok) in MkFusedExpr _ b'
tryLeftUnit {rA = StaticHorizon 0 0} {rB = RetroBoundedHorizon c} {ok} _ b' = rewrite sym (leftUnitRetro c reg ok) in MkFusedExpr _ b'
tryLeftUnit {rA = StaticHorizon 0 0} {rB = WindowedHorizon w}     {ok} _ b' = rewrite sym (leftUnitWindowed w reg ok) in MkFusedExpr _ b'
tryLeftUnit {ok} a' b' = MkFusedExpr _ (HyperOpM (S Z) {ok} a' b')

private
tryRightUnit : {rA, rB : LaurentRegime} -> {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 s1, s2 : StateSchema}
            -> {0 ok : admissibleConvolution rA rB = Just reg}
            -> MultisetExpr rA p s1 a -> MultisetExpr rB p s2 a
            -> FusedExpr reg p a
tryRightUnit {rA = OpenFuture}            {rB = StaticHorizon 0 0} {ok} a' _ = rewrite sym (rightUnitOpen reg ok) in MkFusedExpr _ a'
tryRightUnit {rA = BilateralOpen}         {rB = StaticHorizon 0 0} {ok} a' _ = rewrite sym (rightUnitBilateral reg ok) in MkFusedExpr _ a'
tryRightUnit {rA = BoundedHorizon c}      {rB = StaticHorizon 0 0} {ok} a' _ = rewrite sym (rightUnitBounded c reg ok) in MkFusedExpr _ a'
tryRightUnit {rA = RetroBoundedHorizon c} {rB = StaticHorizon 0 0} {ok} a' _ = rewrite sym (rightUnitRetro c reg ok) in MkFusedExpr _ a'
tryRightUnit {rA = WindowedHorizon w}     {rB = StaticHorizon 0 0} {ok} a' _ = rewrite sym (rightUnitWindowed w reg ok) in MkFusedExpr _ a'
tryRightUnit {ok} a' b' = MkFusedExpr _ (HyperOpM (S Z) {ok} a' b')

------------------------------------------------------------------------
-- 4. MUTUALLY RECURSIVE ALGEBRAIC FUSION PASS (`fuseHMSet` & `fuseScalar`)
------------------------------------------------------------------------

mutual
  ||| Bottom-up algebraic fusion pass over `MultisetExpr reg p st (HereditaryMSet c)`:
  ||| - Eliminates `ZeroM` / `OneM` identities and `SubM x x -> ZeroM`.
  ||| - Folds constant `HyperOpM` nodes (including Wildberger's `A_1 * C_n -> A_{n+1}`).
  ||| - Contracts associative `OpenFuture` / `BilateralOpen` static kernels into a single
  |||   pass (`halfStepBackward` + `halfStepForward` -> `symmetricMotionTick`) with zero `believe_me`.
  public export
  fuseHMSet : MultisetWeight c =>
              {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema} ->
              MultisetExpr reg p st (HereditaryMSet c) ->
              FusedExpr reg p (HereditaryMSet c)
  fuseHMSet ZeroM = MkFusedExpr [] ZeroM
  fuseHMSet OneM  = MkFusedExpr [] OneM
  fuseHMSet (ConstM val) = MkFusedExpr [] (ConstM val)
  fuseHMSet (Input idx)  = MkFusedExpr [] (Input idx)

  fuseHMSet (SubM a b) =
    let (MkFusedExpr s1 a') = fuseHMSet a
        (MkFusedExpr s2 b') = fuseHMSet b
    in if exprStructEq a' b'
         then MkFusedExpr [] ZeroM
         else case b' of
                ZeroM => MkFusedExpr s1 a'
                _     => case (a', b') of
                           (ConstM m1, ConstM m2) =>
                             let diff = subHMSet m1 m2
                             in if diff == emptyHMSet
                                  then MkFusedExpr [] ZeroM
                                  else MkFusedExpr [] (ConstM diff)
                           _ => MkFusedExpr (s1 ++ s2) (SubM a' b')

  fuseHMSet (HadamardM a b) =
    let (MkFusedExpr s1 a') = fuseHMSet a
        (MkFusedExpr s2 b') = fuseHMSet b
    in case (a', b') of
         (ZeroM, _) => MkFusedExpr [] ZeroM
         (_, ZeroM) => MkFusedExpr [] ZeroM
         (ConstM m1, ConstM m2) =>
           let prod = hadamardHMSet m1 m2
           in if prod == emptyHMSet
                then MkFusedExpr [] ZeroM
                else MkFusedExpr [] (ConstM prod)
         _ => MkFusedExpr (s1 ++ s2) (HadamardM a' b')

  fuseHMSet (MinM a b) =
    let (MkFusedExpr s1 a') = fuseHMSet a
        (MkFusedExpr s2 b') = fuseHMSet b
    in case (a', b') of
         (ConstM m1, ConstM m2) => MkFusedExpr [] (ConstM (minHMSet m1 m2))
         _ => MkFusedExpr (s1 ++ s2) (MinM a' b')

  fuseHMSet (MaxM a b) =
    let (MkFusedExpr s1 a') = fuseHMSet a
        (MkFusedExpr s2 b') = fuseHMSet b
    in case (a', b') of
         (ConstM m1, ConstM m2) => MkFusedExpr [] (ConstM (maxHMSet m1 m2))
         _ => MkFusedExpr (s1 ++ s2) (MaxM a' b')

  -- UNIFIED RECURSIVE HYPER-OPERATION TOWER (100% AXIOM-FREE)
  fuseHMSet (HyperOpM {rA} {rB} level {ok} a b) =
    let (MkFusedExpr s1 a') = fuseHMSet a
        (MkFusedExpr s2 b') = fuseHMSet b
    in case level of
         -- Level 0: Additive Superposition (`+`)
         Z =>
           let 0 eqPair = matchingRegimeZ rA rB reg ok
               0 eqL    = fst eqPair
               0 eqR    = snd eqPair
           in case (a', b') of
                (ZeroM, _) => rewrite sym eqR in MkFusedExpr s2 b'
                (_, ZeroM) => rewrite sym eqL in MkFusedExpr s1 a'
                (ConstM m1, ConstM m2) =>
                  let merged = addHMSet m1 m2
                  in if merged == emptyHMSet
                       then MkFusedExpr [] ZeroM
                       else rewrite sym eqL in MkFusedExpr [] (ConstM merged)
                _ => MkFusedExpr (s1 ++ s2) (HyperOpM Z {ok} a' b')

         -- Level 1: Cauchy / Laurent Convolution (`*`)
         S Z =>
           case (a', b') of
             (ZeroM, _) => MkFusedExpr [] ZeroM
             (_, ZeroM) => MkFusedExpr [] ZeroM
             (OneM, _) => tryLeftUnit {ok} a' b'
             (_, OneM) => tryRightUnit {ok} a' b'
             -- Constant Folding & Wildberger Weyl Boundary Collapse (`A_1 * C_n -> A_{n+1}`)
             (ConstM {low = l1} {high = h1} m1, ConstM {low = l2} {high = h2} m2) =>
               let conv   = mulHMSet m1 m2
                   0 eqSt = staticMulRegime l1 h1 l2 h2 reg ok
               in if conv == emptyHMSet
                    then MkFusedExpr [] ZeroM
                    else rewrite sym eqSt in MkFusedExpr [] (ConstM {low = l1 + l2} {high = h1 + h2} conv)
             -- Associative Kernel Pre-Contraction on `OpenFuture`:
             --   (state * ConstM k1) * ConstM k2  ==>  state * ConstM (mulHMSet k1 k2)
             (HyperOpM (S Z) {rA = OpenFuture} {rB = StaticHorizon l1 h1} {rOut = rMid} {ok = okInner} state (ConstM k1),
              ConstM {low = l2} {high = h2} k2) =>
               let fusedKernel = mulHMSet k1 k2
                   0 okAssoc   = assocOpenStaticKernel l1 h1 l2 h2 rMid reg okInner ok
               in if fusedKernel == emptyHMSet
                    then MkFusedExpr [] ZeroM
                    else MkFusedExpr _ (HyperOpM (S Z) {ok = okAssoc} state (ConstM {low = l1 + l2} {high = h1 + h2} fusedKernel))
             -- Associative Kernel Pre-Contraction on `BilateralOpen`:
             (HyperOpM (S Z) {rA = BilateralOpen} {rB = StaticHorizon l1 h1} {rOut = rMid} {ok = okInner} state (ConstM k1),
              ConstM {low = l2} {high = h2} k2) =>
               let fusedKernel = mulHMSet k1 k2
                   0 okAssoc   = assocBilateralStaticKernel l1 h1 l2 h2 rMid reg okInner ok
               in if fusedKernel == emptyHMSet
                    then MkFusedExpr [] ZeroM
                    else MkFusedExpr _ (HyperOpM (S Z) {ok = okAssoc} state (ConstM {low = l1 + l2} {high = h1 + h2} fusedKernel))
             _ => MkFusedExpr (s1 ++ s2) (HyperOpM (S Z) {ok} a' b')

         -- Level 2+: Dirichlet Caretation (`^`) & Higher Hyper-Convolutions
         S (S k) =>
           case (a', b') of
             (ZeroM, _) => MkFusedExpr [] ZeroM
             (_, ZeroM) => MkFusedExpr [] ZeroM
             (ConstM {low = l1} {high = h1} m1, ConstM {low = l2} {high = h2} m2) =>
               let res    = hyperOp (S (S k)) m1 m2
                   0 eqSt = caretStaticRegime l1 h1 l2 h2 reg ok
               in if res == emptyHMSet
                    then MkFusedExpr [] ZeroM
                    else rewrite sym eqSt in
                           MkFusedExpr [] (ConstM {low = caretStaticLow l1 h1 l2 h2}
                                                  {high = caretStaticHigh l1 h1 l2 h2} res)
             _ => MkFusedExpr (s1 ++ s2) (HyperOpM (S (S k)) {ok} a' b')

  fuseHMSet (DotM {bounded} a b) =
    MkFusedExpr _ (DotM {bounded} a b)

  fuseHMSet (Segment win e) =
    let (MkFusedExpr s e') = fuseHMSet e
    in MkFusedExpr (Vect win (HereditaryMSet c) :: s) (Segment win e')

  fuseHMSet (SliceEpoch cap e) =
    let (MkFusedExpr s e') = fuseHMSet e
    in MkFusedExpr s (SliceEpoch cap e')

  fuseHMSet (Fby initE stepE) =
    let (MkFusedExpr s1 initE') = fuseHMSet initE
        (MkFusedExpr s2 stepE') = fuseHMSet stepE
    in MkFusedExpr (HereditaryMSet c :: (s1 ++ s2)) (Fby initE' stepE')

  fuseHMSet (When valE maskE) =
    let (MkFusedExpr s1 valE')  = fuseHMSet valE
        (MkFusedExpr s2 maskE') = fuseScalar maskE
    in case maskE' of
         ZeroM => MkFusedExpr [] ZeroM
         _     => MkFusedExpr (s1 ++ s2) (When valE' maskE')

  fuseHMSet (ProjectSupportM e) =
    let (MkFusedExpr s e') = fuseHMSet e
    in MkFusedExpr s (ProjectSupportM e')

  fuseHMSet (ProjectSignedM e) =
    let (MkFusedExpr s e') = fuseHMSet e
    in MkFusedExpr s (ProjectSignedM e')

  ||| Companion fusion pass over scalar and bit-stream `MultisetExpr` nodes
  ||| (`BasePulseM`, `DotM`, `EqM`, `When` masks).
  public export
  fuseScalar : MultisetWeight w =>
               {0 reg : LaurentRegime} -> {0 p : Maybe PulseExpr} -> {0 st : StateSchema} ->
               MultisetExpr reg p st w ->
               FusedExpr reg p w
  fuseScalar BasePulseM   = MkFusedExpr [] BasePulseM
  fuseScalar ZeroM        = MkFusedExpr [] ZeroM
  fuseScalar OneM         = MkFusedExpr [] OneM
  fuseScalar (ConstM val) = MkFusedExpr [] (ConstM val)
  fuseScalar (Input idx)  = MkFusedExpr [] (Input idx)

  fuseScalar (HyperOpM level {ok} a b) =
    let (MkFusedExpr s1 a') = fuseScalar a
        (MkFusedExpr s2 b') = fuseScalar b
    in MkFusedExpr (s1 ++ s2) (HyperOpM level {ok} a' b')

  fuseScalar (SubM a b) =
    let (MkFusedExpr s1 a') = fuseScalar a
        (MkFusedExpr s2 b') = fuseScalar b
    in if exprStructEq a' b'
         then MkFusedExpr [] ZeroM
         else MkFusedExpr (s1 ++ s2) (SubM a' b')

  fuseScalar (HadamardM a b) =
    let (MkFusedExpr s1 a') = fuseScalar a
        (MkFusedExpr s2 b') = fuseScalar b
    in case (a', b') of
         (ZeroM, _) => MkFusedExpr [] ZeroM
         (_, ZeroM) => MkFusedExpr [] ZeroM
         _          => MkFusedExpr (s1 ++ s2) (HadamardM a' b')

  fuseScalar (MinM a b) =
    let (MkFusedExpr s1 a') = fuseScalar a
        (MkFusedExpr s2 b') = fuseScalar b
    in MkFusedExpr (s1 ++ s2) (MinM a' b')

  fuseScalar (MaxM a b) =
    let (MkFusedExpr s1 a') = fuseScalar a
        (MkFusedExpr s2 b') = fuseScalar b
    in MkFusedExpr (s1 ++ s2) (MaxM a' b')

  fuseScalar (DotM {bounded} a b) =
    let (MkFusedExpr s1 a') = fuseHMSet a
        (MkFusedExpr s2 b') = fuseHMSet b
    in case (a', b') of
         (ZeroM, _) => MkFusedExpr [] ZeroM
         (_, ZeroM) => MkFusedExpr [] ZeroM
         (ConstM m1, ConstM m2) =>
           let scalar = dotHMSet m1 m2
           in if isZero scalar
                then MkFusedExpr [] ZeroM
                else MkFusedExpr [] (ConstM {low = 0} {high = 0} scalar)
         _ => MkFusedExpr (s1 ++ s2) (DotM {bounded} a' b')

  fuseScalar (EqM a b) =
    let (MkFusedExpr s1 a') = fuseHMSet a
        (MkFusedExpr s2 b') = fuseHMSet b
    in if exprStructEq a' b'
         then MkFusedExpr [] OneM
         else MkFusedExpr (s1 ++ s2) (EqM a' b')

  fuseScalar (Segment win e) =
    let (MkFusedExpr s e') = fuseScalar e
    in MkFusedExpr (Vect win w :: s) (Segment win e')

  fuseScalar (SliceEpoch cap e) =
    let (MkFusedExpr s e') = fuseScalar e
    in MkFusedExpr s (SliceEpoch cap e')

  fuseScalar (Fby initE stepE) =
    let (MkFusedExpr s1 initE') = fuseScalar initE
        (MkFusedExpr s2 stepE') = fuseScalar stepE
    in MkFusedExpr (w :: (s1 ++ s2)) (Fby initE' stepE')

  fuseScalar (When valE maskE) =
    let (MkFusedExpr s1 valE')  = fuseScalar valE
        (MkFusedExpr s2 maskE') = fuseScalar maskE
    in case maskE' of
         ZeroM => MkFusedExpr [] ZeroM
         _     => MkFusedExpr (s1 ++ s2) (When valE' maskE')

  fuseScalar (ProjectSupportM e) =
    let (MkFusedExpr s e') = fuseHMSet e
    in MkFusedExpr s (ProjectSupportM e')

  fuseScalar (ProjectSignedM e) =
    let (MkFusedExpr s e') = fuseHMSet e
    in MkFusedExpr s (ProjectSignedM e')

------------------------------------------------------------------------
-- 5. COMPILE-TIME `Refl` AUDITS (100% AXIOM-FREE)
------------------------------------------------------------------------

||| Audit 1: Fusing `ConstM A_1 * ConstM C_4` collapses the 5-node central shell
||| down to the 2-node boundary dipole `ConstM A_5` at compile time via `Refl`
||| (verified modulo balanced AVL tree rotation via `exprStructEq`):
public export
0 prfFuseWeylBoundaryCollapse :
  let exprIn : MultisetExpr (StaticHorizon (-5) 5) Nothing [] PureMultiset
      exprIn = HyperOpM 1 (ConstM {low = -1} {high = 1} (altBinomial 1))
                          (ConstM {low = -4} {high = 4} (centralPoly 4))
  in exprStructEq (Stage1.Fuse.fuseHMSet exprIn).expr
                  (ConstM {low = -5} {high = 5} (altBinomial 5)) = True
prfFuseWeylBoundaryCollapse = Refl

||| Audit 2: Fusing chained `(Input 0 * ConstM halfStepBackward) * ConstM halfStepForward`
||| on `OpenFuture` contracts both half-steps into `symmetricMotionTick`:
public export
0 prfFuseHalfStepsIntoSymmetricTick :
  let exprIn : MultisetExpr OpenFuture Nothing [] PureMultiset
      exprIn = HyperOpM 1
                 (HyperOpM 1 (Input {reg = OpenFuture} 0)
                             (ConstM {low = -1} {high = 0} halfStepBackward))
                 (ConstM {low = 0} {high = 1} halfStepForward)
  in Stage1.Fuse.fuseHMSet exprIn
     = MkFusedExpr []
         (HyperOpM 1 (Input {reg = OpenFuture} 0)
                     (ConstM {low = -1} {high = 1} symmetricMotionTick))
prfFuseHalfStepsIntoSymmetricTick = Refl
