module Stage0.Basis.GeometricPixel

%default total

------------------------------------------------------------------------
-- 1. THE 4 FUNDAMENTAL GEOMETRIES
------------------------------------------------------------------------

||| The 4 Fundamental Geometries governing discrete space, time, gauge, and causality (Rule 03).
public export
data Geometry = Elliptic | Hyperbolic | Parabolic | Substrate

public export
Eq Geometry where
  Elliptic   == Elliptic   = True
  Hyperbolic == Hyperbolic = True
  Parabolic  == Parabolic  = True
  Substrate  == Substrate  = True
  _          == _          = False

public export
Show Geometry where
  show Elliptic   = "Elliptic"
  show Hyperbolic = "Hyperbolic"
  show Parabolic  = "Parabolic"
  show Substrate  = "Substrate"

------------------------------------------------------------------------
-- 2. GEOMETRIC BASIS COORDINATE CELLS
------------------------------------------------------------------------

||| 2D Basis Coordinate Cell carrying a canonical Geometry tag.
public export
record GeometricPixel where
  constructor MkGeometricPixel
  source   : Int
  target   : Int
  geometry : Geometry

public export
Eq GeometricPixel where
  (MkGeometricPixel s1 t1 g1) == (MkGeometricPixel s2 t2 g2) =
    s1 == s2 && t1 == t2 && g1 == g2

public export
Ord GeometricPixel where
  compare (MkGeometricPixel s1 t1 _) (MkGeometricPixel s2 t2 _) =
    case compare s1 s2 of
      EQ => compare t1 t2
      other => other

public export
Show GeometricPixel where
  show (MkGeometricPixel s t g) =
    "[" ++ show s ++ ", " ++ show t ++ "]_" ++ show g

||| 1D Basis Coordinate Cell carrying a canonical Geometry tag.
public export
record GeometricUnixel where
  constructor MkGeometricUnixel
  index    : Int
  geometry : Geometry

public export
Eq GeometricUnixel where
  (MkGeometricUnixel i1 g1) == (MkGeometricUnixel i2 g2) =
    i1 == i2 && g1 == g2

public export
Ord GeometricUnixel where
  compare (MkGeometricUnixel i1 _) (MkGeometricUnixel i2 _) =
    compare i1 i2

public export
Show GeometricUnixel where
  show (MkGeometricUnixel i g) =
    "[" ++ show i ++ "]_" ++ show g

------------------------------------------------------------------------
-- 3. BACKWARD COMPATIBILITY ALIASES
------------------------------------------------------------------------

||| Deprecated: Use `Geometry` instead.
public export %deprecate
0 GeometrySector : Type
GeometrySector = Geometry

||| Deprecated: Use `GeometricPixel` instead.
public export %deprecate
0 MaxelUnit : Type
MaxelUnit = GeometricPixel

||| Deprecated: Use `MkGeometricPixel` instead.
public export %deprecate
MkMaxelUnit : Int -> Int -> Geometry -> GeometricPixel
MkMaxelUnit = MkGeometricPixel

||| Deprecated: Use `GeometricUnixel` instead.
public export %deprecate
0 VexelUnit : Type
VexelUnit = GeometricUnixel

||| Deprecated: Use `MkGeometricUnixel` instead.
public export %deprecate
MkVexelUnit : Int -> Geometry -> GeometricUnixel
MkVexelUnit = MkGeometricUnixel

||| Deprecated: Use `.geometry` instead.
public export %deprecate
sector : GeometricPixel -> Geometry
sector p = p.geometry

