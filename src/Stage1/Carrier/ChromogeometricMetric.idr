module Stage1.Carrier.ChromogeometricMetric

import Stage0.BoxInt
import Stage1.MultisetTree
import Stage1.Basis.CoordCell
import Stage1.Carrier.CellMultiset
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
  let sBlue  = supportMaxel blueMetricMaxel2D
      sRed   = supportMaxel redMetricMaxel2D
      sGreen = supportMaxel greenMetricMaxel2D
      tBlue  = sBlue  == [mkPixel 1 1, mkPixel 2 2]
      tRed   = sRed   == [mkPixel 1 1, mkPixel 2 2]
      tGreen = sGreen == [mkPixel 1 2, mkPixel 2 1]
  in tBlue && tRed && tGreen

public export
auditMatrixPathCompositionProof : Bool
auditMatrixPathCompositionProof =
  let gG = greenMetricMaxel2D
      gProd = mulMaxel gG gG
      sProd = supportMaxel gProd
      e11 = lookupPixel (mkPixel 1 1) gProd
      e22 = lookupPixel (mkPixel 2 2) gProd
  in sProd == [mkPixel 1 1, mkPixel 2 2] && e11 == intToBoxInt 1 && e22 == intToBoxInt 1
