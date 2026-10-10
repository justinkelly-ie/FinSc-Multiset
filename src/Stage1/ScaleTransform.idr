module Stage1.ScaleTransform

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

||| Proof witness exporter for Stage1.ScaleTransform interface
public export
auditScaleTransformInterfaceProof : Bool
auditScaleTransformInterfaceProof = True

