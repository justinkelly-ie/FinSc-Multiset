||| Exact Constructive Number Theoretic Transform (`NTT`) for `StaticHorizon` Convolution (`> 64`).
||| Uses Proth prime `P = 998244353 = 119 * 2^23 + 1` with primitive root `g = 3` and
||| centered signed recovery `(-P/2, P/2]` under exact `%default total` integer arithmetic.
module Stage1.NTT

import Data.List
import Data.Nat
import Stage0.BoxInt

%default total

||| Exact 30-bit NTT-friendly prime `998244353 = 119 * 2^23 + 1`.
public export
nttPrime : Integer
nttPrime = 998244353

||| Primitive root modulo `998244353`.
public export
nttPrimRoot : Integer
nttPrimRoot = 3

||| Threshold (`totalTaps > 64`) above which fast `O(n log n)` NTT replaces direct Cauchy sums.
public export
nttThreshold : Nat
nttThreshold = 64

public export
modNormNTT : Integer -> Integer
modNormNTT x =
  let r = x `mod` nttPrime
  in if r < 0 then r + nttPrime else r

public export
modAddNTT : Integer -> Integer -> Integer
modAddNTT a b =
  let s = modNormNTT a + modNormNTT b
  in if s >= nttPrime then s - nttPrime else s

public export
modSubNTT : Integer -> Integer -> Integer
modSubNTT a b =
  let d = modNormNTT a - modNormNTT b
  in if d < 0 then d + nttPrime else d

public export
modMulNTT : Integer -> Integer -> Integer
modMulNTT a b = modNormNTT (modNormNTT a * modNormNTT b)

||| Total binary modular exponentiation bounded by `fuel` steps (`fuel >= 32` covers 30-bit primes).
public export
modPowFuel : Nat -> Integer -> Integer -> Integer
modPowFuel Z     _ _ = 1
modPowFuel (S k) base exp =
  if exp <= 0
    then 1
    else
      let half = modPowFuel k (modMulNTT base base) (exp `div` 2)
      in if exp `mod` 2 == 1 then modMulNTT base half else half

public export
modPowNTT : Integer -> Integer -> Integer
modPowNTT = modPowFuel 64

public export
modInvNTT : Integer -> Integer
modInvNTT a = modPowNTT a (nttPrime - 2)

private
splitParity : List Integer -> (List Integer, List Integer)
splitParity []             = ([], [])
splitParity [x]            = ([x], [])
splitParity (x :: y :: xs) =
  let (ev, od) = splitParity xs
  in (x :: ev, y :: od)

private
combineButterflies : Integer -> Integer -> List Integer -> List Integer -> List Integer
combineButterflies omega wInit evens odds =
  let (tops, bots) = loop wInit evens odds [] []
  in tops ++ bots
  where
    loop : Integer -> List Integer -> List Integer -> List Integer -> List Integer -> (List Integer, List Integer)
    loop _ [] _ topAcc botAcc = (reverse topAcc, reverse botAcc)
    loop _ _ [] topAcc botAcc = (reverse topAcc, reverse botAcc)
    loop w (e :: es) (o :: os) topAcc botAcc =
      let wo  = modMulNTT w o
          top = modAddNTT e wo
          bot = modSubNTT e wo
      in loop (modMulNTT w omega) es os (top :: topAcc) (bot :: botAcc)

private
padZeros : Nat -> List Integer -> List Integer
padZeros Z     _         = []
padZeros (S k) []        = 0 :: padZeros k []
padZeros (S k) (x :: xs) = modNormNTT x :: padZeros k xs

||| Recursive radix-2 Cooley–Tukey NTT structurally decreasing on `logLen : Nat`.
public export
nttCore : (logLen : Nat) -> (omega : Integer) -> List Integer -> List Integer
nttCore Z     _     xs = take 1 (padZeros 1 xs)
nttCore (S k) omega xs =
  let (ev, od) = splitParity xs
      w2       = modMulNTT omega omega
      yE       = nttCore k w2 ev
      yO       = nttCore k w2 od
  in combineButterflies omega 1 yE yO

private
nextPow2Log : Nat -> Nat -> Nat -> Nat -> (Nat, Nat)
nextPow2Log Z     logN pow2 _      = (logN, pow2)
nextPow2Log (S k) logN pow2 target =
  if pow2 >= target
    then (logN, pow2)
    else nextPow2Log k (S logN) (pow2 * 2) target

private
signedFromNTT : Integer -> BoxInt
signedFromNTT r =
  let n     = modNormNTT r
      halfP = nttPrime `div` 2
  in intToBoxInt (if n > halfP then n - nttPrime else n)

||| Exact signed `BoxInt` polynomial convolution via Cooley–Tukey NTT modulo `998244353`.
||| Assumes exact output coefficients stay within `(-499122176, 499122176]`.
public export
nttConvolve : List BoxInt -> List BoxInt -> List BoxInt
nttConvolve [] _ = []
nttConvolve _ [] = []
nttConvolve xs ys =
  let m      = length xs
      n      = length ys
      outLen = minus (m + n) 1
      (logLen, pow2Len) = nextPow2Log 24 0 1 outLen
      omega  = modPowNTT nttPrimRoot ((nttPrime - 1) `div` cast pow2Len)
      invOm  = modInvNTT omega
      invN   = modInvNTT (cast pow2Len)
      padX   = padZeros pow2Len (map unwrapBox xs)
      padY   = padZeros pow2Len (map unwrapBox ys)
      fX     = nttCore logLen omega padX
      fY     = nttCore logLen omega padY
      fProd  = zipWith modMulNTT fX fY
      rawOut = nttCore logLen invOm fProd
      scaled = map (\v => signedFromNTT (modMulNTT v invN)) rawOut
  in take outLen scaled

||| Direct `O(m * n)` Cauchy convolution over `BoxInt` coefficient lists.
public export
cauchyConvolveLists : List BoxInt -> List BoxInt -> List BoxInt
cauchyConvolveLists [] _ = []
cauchyConvolveLists _ [] = []
cauchyConvolveLists as bs = go as []
  where
    zipPad : List BoxInt -> List BoxInt -> List BoxInt
    zipPad []        ys        = ys
    zipPad xs        []        = xs
    zipPad (x :: xs) (y :: ys) = addBox x y :: zipPad xs ys

    go : List BoxInt -> List BoxInt -> List BoxInt
    go []        acc = acc
    go (x :: xs) acc =
      let scaled = map (\b => mulBox x b) bs
          added  = zipPad acc scaled
      in case added of
           []        => go xs []
           (s :: ss) => s :: go xs ss

||| Threshold-gated convolution dispatcher (`<= 64`: direct Cauchy; `> 64`: exact `O(n log n)` NTT).
public export
convolveListsFast : List BoxInt -> List BoxInt -> List BoxInt
convolveListsFast [] _ = []
convolveListsFast _ [] = []
convolveListsFast xs ys =
  if length xs + length ys <= nttThreshold
    then cauchyConvolveLists xs ys
    else nttConvolve xs ys
