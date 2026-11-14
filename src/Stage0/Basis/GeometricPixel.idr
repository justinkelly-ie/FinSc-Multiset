module Stage0.Basis.GeometricPixel

%default total

------------------------------------------------------------------------
-- 1. THE 4 FUNDAMENTAL GEOMETRIES
------------------------------------------------------------------------

||| The 4 Fundamental Geometries governing discrete space, time, gauge, and causality (Rule 03).
public export
data Geometry = Elliptic | Hyperbolic | Parabolic | Substrate

public export
geomEq : Geometry -> Geometry -> Bool
geomEq Elliptic   Elliptic   = True
geomEq Hyperbolic Hyperbolic = True
geomEq Parabolic  Parabolic  = True
geomEq Substrate  Substrate  = True
geomEq _          _          = False

public export
Eq Geometry where
  (==) = geomEq

public export
geomRank : Geometry -> Nat
geomRank Elliptic   = 0
geomRank Hyperbolic = 1
geomRank Parabolic  = 2
geomRank Substrate  = 3

public export
Ord Geometry where
  compare g1 g2 = compare (geomRank g1) (geomRank g2)

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
geomPixelEq : GeometricPixel -> GeometricPixel -> Bool
geomPixelEq (MkGeometricPixel s1 t1 g1) (MkGeometricPixel s2 t2 g2) =
  s1 == s2 && t1 == t2 && geomEq g1 g2

public export
Eq GeometricPixel where
  (==) = geomPixelEq

public export
Ord GeometricPixel where
  compare (MkGeometricPixel s1 t1 g1) (MkGeometricPixel s2 t2 g2) =
    case compare s1 s2 of
      EQ => case compare t1 t2 of
              EQ => compare g1 g2
              o  => o
      o  => o

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
geomUnixelEq : GeometricUnixel -> GeometricUnixel -> Bool
geomUnixelEq (MkGeometricUnixel i1 g1) (MkGeometricUnixel i2 g2) =
  i1 == i2 && geomEq g1 g2

public export
Eq GeometricUnixel where
  (==) = geomUnixelEq

public export
Ord GeometricUnixel where
  compare (MkGeometricUnixel i1 g1) (MkGeometricUnixel i2 g2) =
    case compare i1 i2 of
      EQ => compare g1 g2
      o  => o

public export
Show GeometricUnixel where
  show (MkGeometricUnixel i g) =
    "[" ++ show i ++ "]_" ++ show g

