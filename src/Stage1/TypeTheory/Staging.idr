||| Module Stage1.TypeTheory.Staging
|||
||| Canonical 2LTT Staging Operations for the FinSc Multiset Science Framework.
||| Implements modal type lifting (⇑A), quoting (⟨t⟩), splicing (~t), and definitional inverse laws
||| following Kovács (2022) Two-Level Type Theory.
module Stage1.TypeTheory.Staging

import public Stage1.TypeTheory.TwoLevel
import Stage0.BoxInt
import Stage0.Multiset

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
record LinearLift (a : Type) where
  constructor MkLinearLift
  unwrapLinear : a

||| Linear quote: lifts an object term into a LinearLift container.
public export
quoteLinear : a -> LinearLift a
quoteLinear x = MkLinearLift x

||| Linear splice: extracts the underlying linear object term with multiplicity 1.
public export
spliceLinear : (1 q : LinearLift a) -> a
spliceLinear (MkLinearLift x) = x

||| QTT 0 Erased Proof Witness: Linear Staging Round-Trip Invariance
public export
0 prfLinearStagingRoundtrip : (x : a) -> spliceLinear (quoteLinear x) = x
prfLinearStagingRoundtrip _ = Refl




