module Stage1.Bridge.LaurentAntiMSetBridge

import public Stage0.BoxInt
import public Stage0.HereditaryMSet
import public Stage1.Views

%default total

------------------------------------------------------------------------
-- CANONICAL LAURENT EXPONENT ENCODING OVER `PureMultiset`
------------------------------------------------------------------------

||| Canonical exponent key `alpha^k` inside `PureMultiset`:
||| Alias for `Stage0.HereditaryMSet.scalarKeyHMSet`.
||| Matches `Stage1.Views.classifyLaurentKey` bijectively.
public export
signedKeyM : Integer -> PureMultiset
signedKeyM = scalarKeyHMSet

||| Builds a signed Laurent polynumber `PureMultiset` from `(exponent, coeff)` pairs
||| with automatic merging of duplicate exponents and zero-pruning annihilation.
public export
mkLaurentPure : List (Integer, Integer) -> PureMultiset
mkLaurentPure terms =
  MkHMSet $ foldl (\acc, (expK, coeff) =>
                    addAtKeyBox (signedKeyM expK) (intToBoxInt coeff) acc)
                  BoxLeaf
                  terms

public export
shiftExponents : Integer -> PureMultiset -> PureMultiset
shiftExponents delta (MkHMSet box) =
  MkHMSet $ foldBox (\key, weight, acc =>
                      case classifyLaurentKey unwrapBox key of
                        ExponentKey e   => addAtKeyBox (signedKeyM (e + delta)) weight acc
                        NestedTermKey m => addAtKeyBox m weight acc)
                    BoxLeaf
                    box

||| Coarse-graining IR scale shift (`* alpha^(+k)`): adds `+k` to all scalar Laurent exponents.
public export
laurentZoomOut : Nat -> PureMultiset -> PureMultiset
laurentZoomOut k = shiftExponents (cast k)

||| Fine-graining UV scale shift (`* alpha^(-k)`): subtracts `k` from all scalar Laurent exponents.
public export
laurentZoomIn : Nat -> PureMultiset -> PureMultiset
laurentZoomIn k = shiftExponents (- cast k)

||| UV-IR duality reflection (`alpha^e <-> alpha^(-e)`): negates all scalar Laurent exponents.
public export
uvIrDual : PureMultiset -> PureMultiset
uvIrDual (MkHMSet box) =
  MkHMSet $ foldBox (\key, weight, acc =>
                      case classifyLaurentKey unwrapBox key of
                        ExponentKey e   => addAtKeyBox (signedKeyM (-e)) weight acc
                        NestedTermKey m => addAtKeyBox m weight acc)
                    BoxLeaf
                    box

------------------------------------------------------------------------
-- VACUUM DIPOLE SPLIT (`[] -> +alpha^(+1) - alpha^(-1)`)
------------------------------------------------------------------------

||| Canonical Tick-1 Laurent vacuum dipole (`+alpha^(+1) - alpha^(-1)`):
||| represents the first distinguishable Black/Red split of `[] = [+1, -1]`
||| across opposite Laurent scale degrees (`+1` vs. `-1`) with zero net charge.
public export
vacuumDipoleSplit : PureMultiset
vacuumDipoleSplit = mkLaurentPure [(1, 1), (-1, -1)]

||| Affine transition kernel breaking empty vacuum degeneracy:
||| - On empty `[]` (`MkHMSet BoxLeaf`), nucleates `+alpha^(+1) - alpha^(-1)`.
||| - On non-empty states, splits `(M_+, M_-)` and shifts `M_+` outward (`* alpha^(+1)`)
|||   and `M_-` inward (`* alpha^(-1)`), preserving net signed charge.
public export
vacuumSplitKernel : PureMultiset -> PureMultiset
vacuumSplitKernel (MkHMSet BoxLeaf) = vacuumDipoleSplit
vacuumSplitKernel state =
  let ch = splitChannels state
  in subHMSet (laurentZoomOut 1 ch.posChannel) (laurentZoomIn 1 ch.negChannel)

||| QTT 0 witness: `Tick 0: [] -> Tick 1: +alpha^(+1) - alpha^(-1)` leaves empty vacuum.
public export
0 prfTick0SplitsToDipole :
  Stage1.Bridge.LaurentAntiMSetBridge.vacuumSplitKernel (MkHMSet BoxLeaf) =
    Stage1.Bridge.LaurentAntiMSetBridge.vacuumDipoleSplit
prfTick0SplitsToDipole = Refl

||| QTT 0 witness: Same-key Black/Red cancellation collapses `[M, M^a]` back to `[]`.
public export
0 prfSameKeyDipoleAnnihilates :
  subHMSet (Stage1.Bridge.LaurentAntiMSetBridge.signedKeyM 1)
           (Stage1.Bridge.LaurentAntiMSetBridge.signedKeyM 1) = MkHMSet BoxLeaf
prfSameKeyDipoleAnnihilates = Refl

||| QTT 0 witness: The nucleated dipole `+alpha^(+1) - alpha^(-1)` has strictly zero net charge.
public export
0 prfVacuumDipoleNetZero :
  sumHMSet Stage1.Bridge.LaurentAntiMSetBridge.vacuumDipoleSplit = MkBoxInt 0
prfVacuumDipoleNetZero = Refl

