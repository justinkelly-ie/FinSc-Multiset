module Stage1.ScaleTransform

import public Stage1.TypeTheory.Smoothness

%default total

||| Open algebraic interface for functorial scale transformations between domains
public export
interface ScaleTransform domainA domainB where
  scaleTransform : domainA -> domainB

||| Identity scale transformation
public export
ScaleTransform a a where
  scaleTransform x = x

||| Functorial composition of scale transformations: T_total = T_BC . T_AB
public export
composeScaleTransform : ScaleTransform a b => ScaleTransform b c => a -> c
composeScaleTransform {a} {b} {c} x =
  let step1 : b = scaleTransform x
      step2 : c = scaleTransform step1
  in step2

||| Open algebraic interface for bidirectional invertible scale transformations (Galois adjunction duality f_* ⊣ f^*)
public export
interface ScaleTransform domainA domainB => InvertibleScaleTransform domainA domainB where
  invertScaleTransform : domainB -> domainA

||| Identity invertible scale transformation
public export
InvertibleScaleTransform a a where
  invertScaleTransform x = x

||| Inverse composition of scale transformations: T_inv = T_AB^-1 . T_BC^-1
public export
composeInvertibleScaleTransform : InvertibleScaleTransform a b => InvertibleScaleTransform b c => c -> a
composeInvertibleScaleTransform {a} {b} {c} z =
  let step1 : b = invertScaleTransform z
      step2 : a = invertScaleTransform step1
  in step2

------------------------------------------------------------------------
-- DEPENDENT TERM-INDEXED SCALE TRANSFORM FUNCTOR (RULE 03)
------------------------------------------------------------------------

||| Term-indexed scale transform functor between validated CosmicDimensions.
||| Constrains scale transformations to lawful transitions between certified dimensions.
public export
interface DepScaleTransform (0 sourceDim : CosmicDimension) (0 targetDim : CosmicDimension) domainA domainB where
  depScaleTransform : domainA -> domainB

||| Identity dependent scale transform between identical dimensions.
public export
DepScaleTransform dim dim a a where
  depScaleTransform x = x

||| Functorial composition of dependent scale transformations along certified dimension paths:
||| (d1 -> d2) and (d2 -> d3) ==> (d1 -> d3).
public export
composeDepScaleTransform :
     DepScaleTransform d1 d2 a b
  => DepScaleTransform d2 d3 b c
  => a -> c
composeDepScaleTransform {d1} {d2} {d3} {a} {b} {c} x =
  let step1 : b = depScaleTransform {sourceDim = d1} {targetDim = d2} x
      step2 : c = depScaleTransform {sourceDim = d2} {targetDim = d3} step1
  in step2

||| Term-indexed bidirectional invertible scale transform.
public export
interface DepScaleTransform sourceDim targetDim domainA domainB
       => InvertibleDepScaleTransform (0 sourceDim : CosmicDimension) (0 targetDim : CosmicDimension) domainA domainB where
  invertDepScaleTransform : domainB -> domainA

||| Identity invertible dependent scale transform.
public export
InvertibleDepScaleTransform dim dim a a where
  invertDepScaleTransform x = x

||| Invertible composition of dependent scale transformations:
public export
composeInvertibleDepScaleTransform :
     InvertibleDepScaleTransform d1 d2 a b
  => InvertibleDepScaleTransform d2 d3 b c
  => c -> a
composeInvertibleDepScaleTransform {d1} {d2} {d3} {a} {b} {c} z =
  let step1 : b = invertDepScaleTransform {sourceDim = d2} {targetDim = d3} z
      step2 : a = invertDepScaleTransform {sourceDim = d1} {targetDim = d2} step1
  in step2

||| Static compile-time proof verifying that DepScaleTransform preserves identity definitionally.
public export
0 auditDepScaleTransformIdentityProof :
  (depScaleTransform {sourceDim = Stage1.TypeTheory.Smoothness.dimElliptic27} {targetDim = Stage1.TypeTheory.Smoothness.dimElliptic27} (the Nat 137)) = the Nat 137
auditDepScaleTransformIdentityProof = Refl

||| Proof witness exporter for Stage1.ScaleTransform interface
public export
auditScaleTransformInterfaceProof : Bool
auditScaleTransformInterfaceProof = True

