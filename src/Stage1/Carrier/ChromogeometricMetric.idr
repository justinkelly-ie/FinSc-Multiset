module Stage1.Carrier.ChromogeometricMetric

import Stage0.BoxInt
import Stage1.MultisetTree
import Stage1.Basis.CoordCell
import Stage1.Carrier.CellMultiset
import Stage1.Carrier.Maxel
import Stage1.Carrier.StagedLinear
import Stage1.Carrier.SquareMaxel

%default total

------------------------------------------------------------------------
-- 1. COMPANION SPREAD MAXEL
------------------------------------------------------------------------

||| Wildberger multiple-spread companion transfer matrix M(s) = [[2 - 4s, -1], [1, 0]] in MaxelN 2.
public export
companionSpreadMaxelN2 : BoxInt -> MaxelN 2
companionSpreadMaxelN2 s =
  let diag = subBox (intToBoxInt 2) (mulBox (intToBoxInt 4) s)
  in mkMaxel2 diag (intToBoxInt (-1)) (intToBoxInt 1) (intToBoxInt 0)

------------------------------------------------------------------------
-- 2. PARAMETERIZED CHROMOGEOMETRIC METRIC MAXELS (Rule 03 §6)
------------------------------------------------------------------------

||| 2D Blue (Elliptic/Euclidean) Metric Maxel parameterized by (x, y):
public export
parameterizedBlueMetricMaxel : BoxInt -> BoxInt -> Maxel
parameterizedBlueMetricMaxel x y =
  singletonCell (mkPixel 1 1) (x * x) <+>
  singletonCell (mkPixel 2 2) (y * y)

||| 2D Red (Hyperbolic/Relativistic) Metric Maxel parameterized by (x, y):
public export
parameterizedRedMetricMaxel : BoxInt -> BoxInt -> Maxel
parameterizedRedMetricMaxel x y =
  singletonCell (mkPixel 1 1) (x * x) <+>
  singletonCell (mkPixel 2 2) (mulBox (intToBoxInt (-1)) (y * y))

||| 2D Green (Parabolic/Null) Metric Maxel parameterized by (x, y):
public export
parameterizedGreenMetricMaxel : BoxInt -> BoxInt -> Maxel
parameterizedGreenMetricMaxel x y =
  let xy = x * y
  in singletonCell (mkPixel 1 2) xy <+>
     singletonCell (mkPixel 2 1) xy

public export
blueMetricMaxel2D : Maxel
blueMetricMaxel2D = parameterizedBlueMetricMaxel (intToBoxInt 1) (intToBoxInt 1)

public export
redMetricMaxel2D : Maxel
redMetricMaxel2D = parameterizedRedMetricMaxel (intToBoxInt 1) (intToBoxInt 1)

public export
greenMetricMaxel2D : Maxel
greenMetricMaxel2D = parameterizedGreenMetricMaxel (intToBoxInt 1) (intToBoxInt 1)

||| 2D Substrate (Causal Poset / Master Budget) Metric Maxel parameterized by (x, y):
||| g_11 = x^2, g_12 = xy, g_21 = xy, g_22 = 0.
public export
parameterizedSubstrateMetricMaxel : BoxInt -> BoxInt -> Maxel
parameterizedSubstrateMetricMaxel x y =
  let xy = x * y
  in singletonCell (mkPixel 1 1) (x * x) <+>
     singletonCell (mkPixel 1 2) xy <+>
     singletonCell (mkPixel 2 1) xy

public export
substrateMetricMaxel2D : Maxel
substrateMetricMaxel2D = parameterizedSubstrateMetricMaxel (intToBoxInt 1) (intToBoxInt 1)

------------------------------------------------------------------------
-- 3. PARAMETERIZED SQUARE MAXELS (SquareMaxel 2)
------------------------------------------------------------------------

public export
parameterizedBlueSquareMaxel : BoxInt -> BoxInt -> SquareMaxel 2
parameterizedBlueSquareMaxel x y =
  maxelToSquareMaxel 2 (parameterizedBlueMetricMaxel x y)

public export
parameterizedRedSquareMaxel : BoxInt -> BoxInt -> SquareMaxel 2
parameterizedRedSquareMaxel x y =
  maxelToSquareMaxel 2 (parameterizedRedMetricMaxel x y)

public export
parameterizedGreenSquareMaxel : BoxInt -> BoxInt -> SquareMaxel 2
parameterizedGreenSquareMaxel x y =
  maxelToSquareMaxel 2 (parameterizedGreenMetricMaxel x y)

public export
parameterizedSubstrateSquareMaxel : BoxInt -> BoxInt -> SquareMaxel 2
parameterizedSubstrateSquareMaxel x y =
  maxelToSquareMaxel 2 (parameterizedSubstrateMetricMaxel x y)

------------------------------------------------------------------------
-- 4. VERIFICATION AUDITS
------------------------------------------------------------------------

||| Invariant audit verifying the parameterized chromogeometric operator identity on Maxel:
public export
auditParameterizedMetricOperatorIdentity : (x : BoxInt) -> (y : BoxInt) -> Bool
auditParameterizedMetricOperatorIdentity x y =
  let gB = parameterizedBlueMetricMaxel x y
      gR = parameterizedRedMetricMaxel x y
      gG = parameterizedGreenMetricMaxel x y
      gR2 = mulMaxel gR gR
      gG2 = mulMaxel gG gG
      lhsSum = addCellMultiset gR2 gG2
      qBlue = (x * x) + (y * y)
      rhsExpected = scaleCellMultiset qBlue gB
      lhs11 = lookupPixel (mkPixel 1 1) lhsSum
      rhs11 = lookupPixel (mkPixel 1 1) rhsExpected
      lhs22 = lookupPixel (mkPixel 2 2) lhsSum
      rhs22 = lookupPixel (mkPixel 2 2) rhsExpected
  in boxEq lhs11 rhs11 && boxEq lhs22 rhs22

||| Invariant audit verifying the parameterized chromogeometric operator identity on SquareMaxel:
public export
auditParameterizedSquareMetricOperatorIdentity : (x : BoxInt) -> (y : BoxInt) -> Bool
auditParameterizedSquareMetricOperatorIdentity x y =
  let gB = parameterizedBlueSquareMaxel x y
      gR = parameterizedRedSquareMaxel x y
      gG = parameterizedGreenSquareMaxel x y
      gR2 = mulSquareMaxel gR gR
      gG2 = mulSquareMaxel gG gG
      lhsSum = addSquareMaxel gR2 gG2
      qBlue = (x * x) + (y * y)
      rhsExpected = scaleSquareMaxel qBlue gB
  in lhsSum == rhsExpected

public export
auditChromogeometricMetricSupportsProof : Bool
auditChromogeometricMetricSupportsProof =
  let b11 = lookupPixel (mkPixel 1 1) blueMetricMaxel2D == intToBoxInt 1
      b22 = lookupPixel (mkPixel 2 2) blueMetricMaxel2D == intToBoxInt 1
      r11 = lookupPixel (mkPixel 1 1) redMetricMaxel2D == intToBoxInt 1
      r22 = lookupPixel (mkPixel 2 2) redMetricMaxel2D == intToBoxInt (-1)
      g12 = lookupPixel (mkPixel 1 2) greenMetricMaxel2D == intToBoxInt 1
      g21 = lookupPixel (mkPixel 2 1) greenMetricMaxel2D == intToBoxInt 1
  in b11 && b22 && r11 && r22 && g12 && g21

public export
auditMatrixPathCompositionProof : Bool
auditMatrixPathCompositionProof =
  let gG = greenMetricMaxel2D
      gProd = mulMaxel gG gG
      e11 = lookupPixel (mkPixel 1 1) gProd == intToBoxInt 1
      e22 = lookupPixel (mkPixel 2 2) gProd == intToBoxInt 1
      e12 = lookupPixel (mkPixel 1 2) gProd == intToBoxInt 0
      e21 = lookupPixel (mkPixel 2 1) gProd == intToBoxInt 0
      tot = totalMaxelWeight gProd == intToBoxInt 2
  in e11 && e22 && e12 && e21 && tot

||| Invariant audit verifying the 4-Geometry Quad-Maxel Operator Theorem:
||| 2 * g_Substrate(x, y) == g_Blue(x, y) + g_Red(x, y) + 2 * g_Green(x, y)
public export
auditParameterizedSubstrateOperatorIdentity : (x : BoxInt) -> (y : BoxInt) -> Bool
auditParameterizedSubstrateOperatorIdentity x y =
  let gSub = parameterizedSubstrateMetricMaxel x y
      gB   = parameterizedBlueMetricMaxel x y
      gR   = parameterizedRedMetricMaxel x y
      gG   = parameterizedGreenMetricMaxel x y
      twoGSub = scaleCellMultiset (intToBoxInt 2) gSub
      twoGG   = scaleCellMultiset (intToBoxInt 2) gG
      rhsSum  = addCellMultiset (addCellMultiset gB gR) twoGG
      s11 = lookupPixel (mkPixel 1 1) twoGSub
      r11 = lookupPixel (mkPixel 1 1) rhsSum
      s12 = lookupPixel (mkPixel 1 2) twoGSub
      r12 = lookupPixel (mkPixel 1 2) rhsSum
      s21 = lookupPixel (mkPixel 2 1) twoGSub
      r21 = lookupPixel (mkPixel 2 1) rhsSum
      s22 = lookupPixel (mkPixel 2 2) twoGSub
      r22 = lookupPixel (mkPixel 2 2) rhsSum
  in boxEq s11 r11 && boxEq s12 r12 && boxEq s21 r21 && boxEq s22 r22

||| Invariant audit certifying the Irreversible Causal Arrow of the Substrate Metric:
||| g_22(x, y) == 0 definitionally for all (x, y). Temporal self-feedback is identically zero.
public export
auditSubstrateCausalArrowZeroFeedback : (x : BoxInt) -> (y : BoxInt) -> Bool
auditSubstrateCausalArrowZeroFeedback x y =
  let gSub = parameterizedSubstrateMetricMaxel x y
      g22Val = lookupPixel (mkPixel 2 2) gSub
  in boxEq g22Val (intToBoxInt 0)
