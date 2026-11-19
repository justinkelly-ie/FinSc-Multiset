module Stage1.Views

import public Stage0.HereditaryMSet

%default total

------------------------------------------------------------------------
-- 1. ANTI-BOX VIEW (BLACK +1 / RED -1 QUANTUM STEPPING)
------------------------------------------------------------------------

||| View exposing Wildberger's Black (`+1`) and Red (`-1`) box quanta
||| one single unit at a time directly over `HereditaryMSet c`.
public export
data AntiBoxView : (c : Type) -> Type where
  EmptyVacuum : AntiBoxView c
  PopBlackBox : (term : HereditaryMSet c) -> (rest : HereditaryMSet c) -> AntiBoxView c
  PopRedBox   : (term : HereditaryMSet c) -> (rest : HereditaryMSet c) -> AntiBoxView c

public export
popMinNode : Box c k -> Maybe (k, c, Box c k)
popMinNode = extractMinBox

public export
antiBoxLoop : QuantumCarrier c => Nat -> HereditaryMSet c -> AntiBoxView c
antiBoxLoop Z _ = EmptyVacuum
antiBoxLoop (S rem) (MkHMSet BoxLeaf) = EmptyVacuum
antiBoxLoop (S rem) (MkHMSet tree@(BoxNode _ _ _ _ _)) =
  case popMinNode tree of
    Nothing => EmptyVacuum
    Just (term, weight, tailTree) =>
      case peelQuantum weight of
        Nothing => antiBoxLoop rem (MkHMSet tailTree)
        Just (Left remW) =>
          let restBox = if isZero remW then tailTree else setBox term remW tailTree
          in PopBlackBox term (MkHMSet restBox)
        Just (Right remW) =>
          let restBox = if isZero remW then tailTree else setBox term remW tailTree
          in PopRedBox term (MkHMSet restBox)

||| Total covering function peeling one `+1` Black or `-1` Red quantum from the minimum key.
public export
viewAsAntiBox : QuantumCarrier c => HereditaryMSet c -> AntiBoxView c
viewAsAntiBox m@(MkHMSet tree) = antiBoxLoop (S (boxNodeCount tree)) m

------------------------------------------------------------------------
-- 2. DUAL-CHANNEL VIEW (DISJOINT MATTER M_+ & ANTIMATTER M_- CHANNELS)
------------------------------------------------------------------------

||| Splits a signed `HereditaryMSet c` into two disjoint positive-magnitude channels.
public export
record DualChannelView (c : Type) where
  constructor MkDualChannels
  posChannel : HereditaryMSet c
  negChannel : HereditaryMSet c

||| Projects a signed multiset into `(M_+, M_-)` using `compare weight zeroWeight`.
public export
splitChannels : MultisetWeight c => HereditaryMSet c -> DualChannelView c
splitChannels (MkHMSet box) =
  let (pBox, nBox) =
        foldBox (\k, w, (pAcc, nAcc) =>
                  case compare w zeroWeight of
                    GT => (setBox k w pAcc, nAcc)
                    LT => (pAcc, setBox k (negWeight w) nAcc)
                    EQ => (pAcc, nAcc))
                (BoxLeaf, BoxLeaf)
                box
  in MkDualChannels (MkHMSet pBox) (MkHMSet nBox)

||| Recombines `(M_+, M_-)` via `subHMSet`, annihilating any overlapping keys.
public export
interactChannels : MultisetWeight c => DualChannelView c -> HereditaryMSet c
interactChannels (MkDualChannels posM negM) = subHMSet posM negM

------------------------------------------------------------------------
-- 3. LAURENT POLYNUMBER VIEW (`LaurentView`: coeff * alpha^(+/- k))
------------------------------------------------------------------------

||| Classifies a key in `HereditaryMSet c` as either:
||| - `ExponentKey k`   : A canonical scalar exponent `k : Integer` (for `alpha^k`)
||| - `NestedTermKey m` : A deeper nested multiset structure
public export
data LaurentKeyKind : (c : Type) -> Type where
  ExponentKey   : (expK : Integer) -> LaurentKeyKind c
  NestedTermKey : (subM : HereditaryMSet c) -> LaurentKeyKind c

||| Helper extracting a signed `Integer` exponent from a scalar key `HereditaryMSet c`
||| via a carrier-to-`Integer` projection (`toInt : c -> Integer`).
public export
classifyLaurentKey : MultisetWeight c => (toInt : c -> Integer) -> HereditaryMSet c -> LaurentKeyKind c
classifyLaurentKey _ (MkHMSet BoxLeaf) = ExponentKey 0
classifyLaurentKey toInt m@(MkHMSet (BoxNode _ BoxLeaf (MkHMSet BoxLeaf) w BoxLeaf)) =
  ExponentKey (toInt w)
classifyLaurentKey _ m = NestedTermKey m

||| View exposing a `HereditaryMSet c` as a sorted sequence of Laurent polynumber
||| terms (`coeff * alpha^expK`) from lowest negative exponent to highest positive exponent.
public export
data LaurentView : (c : Type) -> Type where
  ||| Zero Laurent polynumber (`0`)
  LaurentZero   : LaurentView c
  ||| Head Laurent monomial `coeff * alpha^expK` followed by the remaining polynumber `rest`
  LaurentTerm   : (expK : Integer) -> (coeff : c) -> (rest : HereditaryMSet c) -> LaurentView c
  ||| Non-scalar nested sub-multiset term `coeff * subM` followed by `rest`
  LaurentNested : (subM : HereditaryMSet c) -> (coeff : c) -> (rest : HereditaryMSet c) -> LaurentView c

public export
laurentViewLoop : MultisetWeight c => Nat -> (toInt : c -> Integer) -> HereditaryMSet c -> LaurentView c
laurentViewLoop Z _ _ = LaurentZero
laurentViewLoop (S rem) _ (MkHMSet BoxLeaf) = LaurentZero
laurentViewLoop (S rem) toInt (MkHMSet tree@(BoxNode _ _ _ _ _)) =
  case popMinNode tree of
    Nothing => LaurentZero
    Just (key, coeff, tailTree) =>
      if isZero coeff
        then laurentViewLoop rem toInt (MkHMSet tailTree)
        else case classifyLaurentKey toInt key of
               ExponentKey k   => LaurentTerm k coeff (MkHMSet tailTree)
               NestedTermKey m => LaurentNested m coeff (MkHMSet tailTree)

||| Total covering function projecting any `HereditaryMSet c` into `LaurentView c`
||| in O(log N) per step by peeling the minimum AVL key.
public export
viewAsLaurent : MultisetWeight c => (toInt : c -> Integer) -> HereditaryMSet c -> LaurentView c
viewAsLaurent toInt m@(MkHMSet tree) = laurentViewLoop (S (boxNodeCount tree)) toInt m

public export
toLaurentTermsLoop : MultisetWeight c => Nat -> (toInt : c -> Integer) -> HereditaryMSet c -> List (Integer, c)
toLaurentTermsLoop Z _ _ = []
toLaurentTermsLoop (S rem) toInt m =
  case viewAsLaurent toInt m of
    LaurentZero            => []
    LaurentTerm k coeff r  => (k, coeff) :: toLaurentTermsLoop rem toInt r
    LaurentNested _ _ r    => toLaurentTermsLoop rem toInt r

||| Helper converting any `HereditaryMSet c` into a flat sorted list of `(exponent, coeff)`
||| pairs for display, evaluation, or NTT lowering using structural `boxNodeCount` fuel.
public export
toLaurentTerms : MultisetWeight c => (toInt : c -> Integer) -> HereditaryMSet c -> List (Integer, c)
toLaurentTerms toInt m@(MkHMSet tree) = toLaurentTermsLoop (S (boxNodeCount tree)) toInt m


------------------------------------------------------------------------
-- 4. CONSTRUCTIVIST DUAL-CHANNEL DISJOINTNESS RECOGNIZER (`recognition-rule.md`)
------------------------------------------------------------------------

public export
isHMBoxLeaf : HereditaryMSet c -> Bool
isHMBoxLeaf (MkHMSet BoxLeaf) = True
isHMBoxLeaf _                 = False

||| Boolean check that `posChannel` (`M_+`) and `negChannel` (`M_-`) share zero active keys.
public export
disjointDualSupports : MultisetWeight c => DualChannelView c -> Bool
disjointDualSupports (MkDualChannels p n) = isHMBoxLeaf (hadamardHMSet p n)

||| Proof predicate witnessing disjoint supports between `posChannel` and `negChannel`.
public export
DisjointSupports : MultisetWeight c => DualChannelView c -> Type
DisjointSupports v = (disjointDualSupports v = True)

||| Total `Dec` recognizer verifying that a `DualChannelView c` has strictly disjoint supports.
public export
recognizeDisjointChannels : MultisetWeight c => (v : DualChannelView c) -> Dec (DisjointSupports v)
recognizeDisjointChannels v = decideBoolTrue (disjointDualSupports v)

||| Erased-proof `Subset` storing a verified disjoint `DualChannelView c`.
public export
DisjointDualChannels : (c : Type) -> MultisetWeight c => Type
DisjointDualChannels c = Subset (DualChannelView c) DisjointSupports

||| Smart constructor returning `Just (Subset v prf)` when both channels have disjoint supports.
public export
toDisjointDualChannels : MultisetWeight c => (v : DualChannelView c) -> Maybe (DisjointDualChannels c)
toDisjointDualChannels v =
  case recognizeDisjointChannels v of
    Yes prf => Just (Element v prf)
    No _    => Nothing
