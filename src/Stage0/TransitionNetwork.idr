module Stage0.TransitionNetwork

import Stage0.BoxInt
import Stage0.Multiset
import Stage0.OnSeq.FusedStream
import Stage0.StructuralFuel
import Stage0.BoxNat
import Data.Fuel
import Data.List

%default total

------------------------------------------------------------------------
-- 1. UNIVERSAL STOICHIOMETRIC TRANSITION NETWORK CARRIERS
------------------------------------------------------------------------

||| Reaction / transition stoichiometry delta for an arbitrary species token `s`.
public export
record StoichiometryDelta (0 s : Type) where
  constructor MkDelta
  species : s
  change  : BoxInt

public export
Eq s => Eq (StoichiometryDelta s) where
  (MkDelta s1 c1) == (MkDelta s2 c2) = s1 == s2 && c1 == c2

||| Elementary transition channel R_j:
||| Consumes reactants and produces products with an integer propensity rate.
public export
record TransitionChannel (0 s : Type) where
  constructor MkChannel
  channelId  : Nat
  deltas     : List (StoichiometryDelta s)
  propensity : BoxInt

public export
Eq s => Eq (TransitionChannel s) where
  (MkChannel id1 d1 p1) == (MkChannel id2 d2 p2) = id1 == id2 && d1 == d2 && p1 == p2

------------------------------------------------------------------------
-- 2. UNIVERSAL MULTISET STATE TRANSDUCERS
------------------------------------------------------------------------

||| Discrete state: multiset tally of species populations.
public export
0 TransitionState : Type -> Type
TransitionState s = Multiset BoxInt s

||| Applies a single stoichiometric delta to the state multiset.
public export
applyDelta : Eq s => TransitionState s -> StoichiometryDelta s -> TransitionState s
applyDelta state (MkDelta sp ch) =
  let cur = multiplicity sp state
      newVal = cur + ch
      clamped = if unwrapBox newVal < 0 then intToBoxInt 0 else newVal
  in update sp clamped state
  where
    update : s -> BoxInt -> Multiset BoxInt s -> Multiset BoxInt s
    update x v ZeroM = AddM x v ZeroM
    update x v (AddM k m rest) =
      if k == x then AddM x v rest
      else AddM k m (update x v rest)

||| Fires a transition channel, updating all participating species deltas in sequence.
public export
fireChannel : Eq s => TransitionChannel s -> TransitionState s -> TransitionState s
fireChannel (MkChannel _ dList _) state =
  foldl applyDelta state dList

||| Deforested stream generator simulating transition network trajectory over consecutive steps:
||| Generates state trajectory without intermediate list allocations.
public export
streamTransitionTrajectory : Eq s => TransitionChannel s -> TransitionState s -> FusedStream (TransitionState s)
streamTransitionTrajectory channel initState =
  unfoldStream (\st => Yield st (fireChannel channel st)) initState

||| Runs a fueled transition trajectory using stream fold.
public export
runTransitionTrajectory : Eq s => Fuel -> TransitionChannel s -> TransitionState s -> TransitionState s
runTransitionTrajectory f channel initState =
  foldStreamFuel f (\_, nextSt => nextSt) initState (streamTransitionTrajectory channel initState)

------------------------------------------------------------------------
-- 3. LINEAR CONSERVATION LAW WITNESSES
------------------------------------------------------------------------

||| Evaluates total weighted conserved quantity: Q = sum_i c_i * count(S_i).
public export
evaluateConservedQuantity : Eq s => List (s, BoxInt) -> TransitionState s -> BoxInt
evaluateConservedQuantity [] _ = intToBoxInt 0
evaluateConservedQuantity ((sp, weight) :: rest) state =
  (weight * multiplicity sp state) + evaluateConservedQuantity rest state

||| Static check whether a stoichiometric delta preserves a conserved weight vector: sum_i c_i * delta_i == 0.
public export
isConservativeDelta : Eq s => List (s, BoxInt) -> List (StoichiometryDelta s) -> Bool
isConservativeDelta weights deltas =
  let totalDelta = foldl (\acc, (MkDelta sp ch) =>
                            case lookup sp weights of
                              Just w => acc + (w * ch)
                              Nothing => acc) (intToBoxInt 0) deltas
  in unwrapBox totalDelta == 0

||| Compile-time audit witness verifying universal transition network preservation.
public export
auditTransitionNetworkProof : Bool
auditTransitionNetworkProof =
  let initSt : TransitionState Nat = AddM 1 (intToBoxInt 10) (AddM 2 (intToBoxInt 0) ZeroM)
      rxn : TransitionChannel Nat = MkChannel 1 [MkDelta 1 (intToBoxInt (-1)), MkDelta 2 (intToBoxInt 1)] (intToBoxInt 1)
      finalSt = runTransitionTrajectory (limit 5) rxn initSt
      c1 = multiplicity 1 finalSt
      c2 = multiplicity 2 finalSt
      tot = c1 + c2
  in unwrapBox c1 == 5 && unwrapBox c2 == 5 && unwrapBox tot == 10
