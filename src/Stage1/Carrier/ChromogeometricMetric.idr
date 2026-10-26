module Stage1.Carrier.ChromogeometricMetric

import Stage0.BoxInt
import Stage1.MultisetTree
import Stage1.Basis.CoordCell
import Stage1.Carrier.CellMultiset
import Stage1.Carrier.StagedLinear

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
