module Stage0.LinearBuffer

import Stage0.BoxInt
import Stage0.Interfaces
import Stage0.Multiset
import Data.DPair
import Data.Vect
import Data.Fin
import Data.Fin.Properties
import Data.Nat

%default total

||| A QTT linear memory buffer holding exactly `capacity` discrete BoxInt quadrance tokens.
||| Guarantees zero runtime heap allocation during linear state updating cycles.
public export
record LinearBuffer (capacity : Nat) where
  constructor MkLinearBuffer
  tokens : Vect capacity BoxInt

||| Creates a zeroed linear buffer token pool.
public export
createLinearBuffer : (cap : Nat) -> LinearBuffer cap
createLinearBuffer cap = MkLinearBuffer (replicate cap (intToBoxInt 0))

||| Linear write update to a specific buffer index with QTT multiplicity 1.
public export
writeLinearBuffer : {capacity : Nat} -> (1 buf : LinearBuffer capacity) -> (idx : Fin capacity) -> (val : BoxInt) -> LinearBuffer capacity
writeLinearBuffer (MkLinearBuffer tok) idx val = MkLinearBuffer (replaceAt idx val tok)

||| Linear read from a specific buffer index preserving QTT multiplicity 1.
public export
readLinearBuffer : {capacity : Nat} -> (1 buf : LinearBuffer capacity) -> (idx : Fin capacity) -> LPair (LinearBuffer capacity) BoxInt
readLinearBuffer (MkLinearBuffer tok) idx = (MkLinearBuffer tok # index idx tok)

||| Interior-peeled spatial stencil write pass over PingPongGrid (`Gemini.md` Section 6):
||| Extracts total BoxInt value across buffer.
public export
bufferTotalValueBox : {capacity : Nat} -> LinearBuffer capacity -> BoxInt
bufferTotalValueBox (MkLinearBuffer tok) = foldl (+) (intToBoxInt 0) tok

||| Extracts total integer value across buffer.
public export
bufferTotalValue : {capacity : Nat} -> LinearBuffer capacity -> Integer
bufferTotalValue buf = unwrapBox (bufferTotalValueBox buf)

||| Canonical alias for 1-quantity linear buffer (`Gemini.md` Section 2).
public export
LinBuf : Nat -> Type
LinBuf = LinearBuffer

||| Double-buffered spatial grid (`PingPongGrid`) for lowered `Fby` stencil kernels (`Gemini.md` Section 6).
public export
record PingPongGrid (capacity : Nat) where
  constructor MkPingPongGrid
  1 readBuf  : LinearBuffer capacity
  1 writeBuf : LinearBuffer capacity

||| Allocates a zeroed double-buffered PingPongGrid.
public export
createPingPongGrid : (cap : Nat) -> PingPongGrid cap
createPingPongGrid cap = MkPingPongGrid (createLinearBuffer cap) (createLinearBuffer cap)

||| O(1) linear double-buffer swap (`unfold` read <-> `fold` write) with zero heap allocation.
public export
swapBuffers : {capacity : Nat} -> (1 grid : PingPongGrid capacity) -> PingPongGrid capacity
swapBuffers (MkPingPongGrid r w) = MkPingPongGrid w r

||| Flat, zero-allocation two-phase unfold/fold transition kernel (`compileStream` target).
||| Consumes linear state with multiplicity 1 and returns an LPair `(st' # out)`.
public export
StepKernel : (s : Type) -> (inp : Type) -> (out : Type) -> Type
StepKernel s inp out = (1 state : s) -> inp -> LPair s out

||| Reads from `readBuf` and writes into `writeBuf` without perimeter branching on interior cells,
||| returning the O(1) swapped `PingPongGrid` with strict `1`-quantity linearity.
public export
stepPingPongStencil : {capacity : Nat}
                   -> (boundaryFn : Fin capacity -> BoxInt -> BoxInt)
                   -> (interiorFn : BoxInt -> BoxInt -> BoxInt -> BoxInt)
                   -> (1 grid : PingPongGrid capacity)
                   -> PingPongGrid capacity
stepPingPongStencil {capacity = Z} _ _ (MkPingPongGrid r w) = MkPingPongGrid w r
stepPingPongStencil {capacity = S Z} bFn _ (MkPingPongGrid (MkLinearBuffer rTok) (MkLinearBuffer wTok)) =
  let v0 = bFn FZ (index FZ rTok)
  in MkPingPongGrid (MkLinearBuffer (replaceAt FZ v0 wTok)) (MkLinearBuffer rTok)
stepPingPongStencil {capacity = S (S k)} bFn iFn (MkPingPongGrid (MkLinearBuffer rTok) (MkLinearBuffer wTok)) =
  let updated = fillRow 0 rTok wTok
  in MkPingPongGrid (MkLinearBuffer updated) (MkLinearBuffer rTok)
  where
    peelLast : Fin (S (S k))
    peelLast = last

    fillRow : Nat -> Vect (S (S k)) BoxInt -> Vect (S (S k)) BoxInt -> Vect (S (S k)) BoxInt
    fillRow _ rV wV =
      -- Peel left perimeter (FZ) and right perimeter (last), leaving interior cells branchless
      let w0 = replaceAt FZ (bFn FZ (index FZ rV)) wV
          w1 = replaceAt peelLast (bFn peelLast (index peelLast rV)) w0
      in fillInterior k FZ rV w1
      where
        fillInterior : Nat -> Fin (S k) -> Vect (S (S k)) BoxInt -> Vect (S (S k)) BoxInt -> Vect (S (S k)) BoxInt
        fillInterior Z _ _ wAcc = wAcc
        fillInterior (S rem) leftIdx rV wAcc =
          let midIdx : Fin (S (S k)) = FS leftIdx
              rightIdx : Fin (S (S k)) = case strengthen midIdx of
                                           Nothing => peelLast
                                           Just mSmall => FS mSmall
              newV = iFn (index (weaken leftIdx) rV) (index midIdx rV) (index rightIdx rV)
              wAcc' = replaceAt midIdx newV wAcc
          in case strengthen (FS leftIdx) of
               Nothing => wAcc'
               Just nextLeft => fillInterior rem nextLeft rV wAcc'

-- =========================================================================
-- FiniteCoord k <-> LinBuf Bridge & Constructive Dec Bounds Recognition
-- =========================================================================

||| Linearly reads the scalar weight at a `FiniteCoord k` from a `1`-quantity `LinBuf`.
public export
readFiniteCoord : {0 k : Type} -> FiniteCoord k
               => (1 buf : LinBuf (cardinality {k}))
               -> (coord : k)
               -> LPair (LinBuf (cardinality {k})) BoxInt
readFiniteCoord buf coord = readLinearBuffer buf (toIndex coord)

||| Linearly writes a scalar weight at a `FiniteCoord k` into a `1`-quantity `LinBuf`.
public export
writeFiniteCoord : {0 k : Type} -> FiniteCoord k
                => (1 buf : LinBuf (cardinality {k}))
                -> (coord : k)
                -> (val : BoxInt)
                -> LinBuf (cardinality {k})
writeFiniteCoord buf coord val = writeLinearBuffer buf (toIndex coord) val

public export
tabulateFinBox : (m : Nat) -> (Fin m -> BoxInt) -> Vect m BoxInt
tabulateFinBox Z     _ = []
tabulateFinBox (S m) f = f FZ :: tabulateFinBox m (f . FS)

||| Flattens a sparse AVL `Carrier k` onto a dense contiguous `LinBuf (cardinality {k})`.
public export
carrierToLinBuf : {0 k : Type} -> FiniteCoord k => Carrier k -> LinBuf (cardinality {k})
carrierToLinBuf carrier =
  MkLinearBuffer (tabulateFinBox (cardinality {k}) (\i => lookupCarrier (fromIndex i) carrier))

public export
vectToCarrierFrom : {0 k : Type} -> FiniteCoord k
                 => {m : Nat} -> (offset : Nat) -> (vec : Vect m BoxInt) -> Carrier k -> Carrier k
vectToCarrierFrom _     []        acc = acc
vectToCarrierFrom offset (v :: vs) acc =
  let nextAcc = case isLT offset (cardinality {k}) of
                  Yes lt => if boxIsZero v then acc
                            else setBoxTree (fromIndex (natToFinLT offset @{lt})) v acc
                  No _   => acc
  in vectToCarrierFrom (S offset) vs nextAcc

||| Reads back non-zero slots from a `1`-quantity `LinBuf (cardinality {k})` into a canonical `Carrier k`.
public export
linBufToCarrier : {0 k : Type} -> FiniteCoord k
               => (1 buf : LinBuf (cardinality {k}))
               -> Carrier k
linBufToCarrier (MkLinearBuffer vec) = vectToCarrierFrom 0 vec BoxLeaf

||| Constructive `Dec` bounds recognizer checking whether a raw runtime index `idx`
||| lies strictly within `[0, cap)`.
public export
recognizeBounds : (cap : Nat) -> (idx : Nat) -> Dec (LT idx cap)
recognizeBounds cap idx = isLT idx cap

||| Constructive `Dec` bounds recognizer specialized to `FiniteCoord k`'s cardinality.
public export
recognizeCoordBounds : {0 k : Type} -> FiniteCoord k
                    => (idx : Nat) -> Dec (LT idx (cardinality {k}))
recognizeCoordBounds {k} idx = isLT idx (cardinality {k})

||| Total index-to-coordinate conversion gated by an erased `LT` proof from `recognizeBounds`.
public export
boundedIndexToCoord : {0 k : Type} -> FiniteCoord k
                   => (idx : Nat) -> (0 prf : LT idx (cardinality {k})) -> k
boundedIndexToCoord idx prf = fromIndex (natToFinLT idx @{prf})

||| Packs a validated coordinate together with its erased `0` round-trip proof
||| `finToNat (toIndex coord) = idx` into a zero-overhead `Subset` container.
public export
boundedIndexToSubset : {0 k : Type} -> FiniteCoord k
                    => (idx : Nat)
                    -> (0 prf : LT idx (cardinality {k}))
                    -> Subset k (\coord => finToNat (toIndex coord) = idx)
boundedIndexToSubset idx prf =
  let fi : Fin (cardinality {k})
      fi = natToFinLT idx @{prf}
      coord : k
      coord = fromIndex fi
      0 eqPrf : (finToNat (toIndex coord) = idx)
      eqPrf = trans (cong finToNat (rightInv fi)) (finToNatNatToFinLT idx prf)
  in Element coord eqPrf



------------------------------------------------------------------------
-- 5. BOUNDARY & I/O BOX PAYLOAD RECOGNIZERS (`recognition-rule.md`)
------------------------------------------------------------------------

||| Boundary validity predicate for raw deserialized `Box c k` payloads.
public export
ValidBox : MultisetWeight c => Ord k => Box c k -> Type
ValidBox = IsCanonicalBox

||| Total `Dec` recognizer validating raw external `Box c k` payloads at the I/O boundary
||| before entering `StepKernel` or `PingPongGrid` pipelines.
public export
recognizeBox : (MultisetWeight c, Ord k) => (raw : Box c k) -> Dec (ValidBox raw)
recognizeBox = recognizeCanonicalBox

||| Erased-proof `Subset` alias bundling a validated boundary `Box c k`.
public export
ValidatedBox : (c : Type) -> (k : Type) -> (MultisetWeight c, Ord k) => Type
ValidatedBox c k = CanonicalBox c k

||| Checks a raw boundary entry list `List (Nat, c)` against `FiniteCoord k` bounds
||| and non-zero weight invariants.
public export
isValidFiniteEntries : {0 k : Type} -> (FiniteCoord k, MultisetWeight c) => List (Nat, c) -> Bool
isValidFiniteEntries [] = True
isValidFiniteEntries ((idx, w) :: xs) =
  let inBounds = case recognizeCoordBounds {k} idx of
                   Yes _ => True
                   No  _ => False
  in inBounds && not (isZero w) && isValidFiniteEntries {k} xs

||| Proof predicate for raw finite-coordinate boundary entry batches.
public export
ValidFiniteEntries : (k : Type) -> (FiniteCoord k, MultisetWeight c) => List (Nat, c) -> Type
ValidFiniteEntries k entries = (isValidFiniteEntries {k} entries = True)

||| Total `Dec` recognizer validating raw `(Nat, c)` boundary packets for `FiniteCoord k`.
public export
recognizeFiniteEntries : {0 c : Type} -> (k : Type) -> (FiniteCoord k, MultisetWeight c) =>
                         (raw : List (Nat, c)) -> Dec (ValidFiniteEntries k raw)
recognizeFiniteEntries k raw = decideBoolTrue (isValidFiniteEntries {k} raw)


------------------------------------------------------------------------
-- 6. HEHNER 21-BIT L1/L2 CACHE TIERING & DUAL-MODE `HybridBuf` (`QTT 1`)
------------------------------------------------------------------------

||| Hard Hehner 21-bit L1/L2 cache ceiling in bytes (2^21 = 2,097,152 bytes).
public export
hehnerCacheBytesCap : Integer
hehnerCacheBytesCap = 2097152

||| Maximum contiguous 64-bit `BoxInt` slots fitting inside the 21-bit cache ceiling (`2^21 / 8`).
public export
hehnerMaxBoxIntSlots : Integer
hehnerMaxBoxIntSlots = 262144

||| Fast flat 1D SIMD threshold (`cardinality <= 1024`).
public export
denseFastThreshold : Integer
denseFastThreshold = 1024

||| Upper cardinality ceiling for hybrid sparse/dense dual execution (`<= 10^7`).
public export
hybridCardinalityCap : Integer
hybridCardinalityCap = 10000000

||| Three-tier storage classification derived from `FiniteCoord k` cardinality (`Rule 07` §2).
public export
data HybridTier : Type where
  DenseSimdTier  : HybridTier
  HybridDualTier : HybridTier
  SparseAvlTier  : HybridTier

public export
Eq HybridTier where
  DenseSimdTier  == DenseSimdTier  = True
  HybridDualTier == HybridDualTier = True
  SparseAvlTier  == SparseAvlTier  = True
  _              == _              = False

||| Selects storage tier directly from coordinate cardinality using exact `Integer` bounds.
public export
selectLoweringTier : (card : Nat) -> HybridTier
selectLoweringTier card =
  let c = cast {to = Integer} card
  in if c <= 1024 then DenseSimdTier
     else if c <= 10000000 then HybridDualTier
     else SparseAvlTier

||| Type-level witness that a slot budget fits within the Hehner 21-bit L1/L2 cache ceiling.
public export
FitsHehnerL1L2 : Nat -> Type
FitsHehnerL1L2 slots = ((cast {to = Integer} slots <= 262144) = True)

||| Constructive `Dec` recognizer verifying a slot budget fits the Hehner 21-bit cache ceiling.
public export
recognizeHehnerSlotBound : (slots : Nat) -> Dec (FitsHehnerL1L2 slots)
recognizeHehnerSlotBound slots = decideBoolTrue (cast {to = Integer} slots <= 262144)

||| Active backing representation inside a `1`-quantity `HybridBuf`.
public export
data HybridMode : Type where
  DenseMode  : HybridMode
  SparseMode : HybridMode

public export
Eq HybridMode where
  DenseMode  == DenseMode  = True
  SparseMode == SparseMode = True
  _          == _          = False

||| Dual-mode `1`-quantity linear buffer (`HybridBuf`) covering `1024 < card <= 10^7`:
||| pre-allocates its dense `LinBuf denseCap` inside the 21-bit Hehner cache ceiling
||| (`FitsHehnerL1L2 denseCap`) alongside sparse AVL `Carrier k` storage so hot-path mode
||| switches perform zero heap allocations. Intentionally omits `Eq` and `Ord`.
public export
data HybridBuf : (denseCap : Nat) -> (k : Type) -> Type where
  MkHybridBuf : (mode : HybridMode)
             -> (1 denseBuf : LinBuf denseCap)
             -> (sparseBox : Carrier k)
             -> (0 fitsL1L2 : FitsHehnerL1L2 denseCap)
             -> HybridBuf denseCap k

||| Pre-allocates a `HybridBuf` at initialization time with an erased Hehner 21-bit proof.
public export
createHybridBuf : (denseCap : Nat) -> {auto 0 fit : FitsHehnerL1L2 denseCap} -> HybridMode -> HybridBuf denseCap k
createHybridBuf denseCap {fit} mode =
  MkHybridBuf mode (createLinearBuffer denseCap) emptyBox fit

||| Boundary-checked constructor returning `Just (HybridBuf denseCap k)` when
||| `denseCap <= 262144` passes `recognizeHehnerSlotBound`.
public export
createHybridBufChecked : (denseCap : Nat) -> HybridMode -> Maybe (HybridBuf denseCap k)
createHybridBufChecked denseCap mode =
  case recognizeHehnerSlotBound denseCap of
    Yes prf => Just (MkHybridBuf mode (createLinearBuffer denseCap) emptyBox prf)
    No  _   => Nothing

||| Zero-allocation hot-path mode switch preserving linear ownership of `denseBuf`.
public export
switchHybridMode : {denseCap : Nat} -> (1 hb : HybridBuf denseCap k) -> HybridMode -> HybridBuf denseCap k
switchHybridMode (MkHybridBuf _ dBuf sBox prf) newMode = MkHybridBuf newMode dBuf sBox prf

||| Writes a `BoxInt` multiplicity according to the active `HybridBuf` mode without extra allocations.
public export
writeHybridBuf : DiscreteCoord k => {denseCap : Nat}
              -> (1 hb : HybridBuf denseCap k) -> Fin denseCap -> k -> BoxInt -> HybridBuf denseCap k
writeHybridBuf (MkHybridBuf DenseMode dBuf sBox prf) idx _ val =
  MkHybridBuf DenseMode (writeLinearBuffer dBuf idx val) sBox prf
writeHybridBuf (MkHybridBuf SparseMode dBuf sBox prf) _ key val =
  MkHybridBuf SparseMode dBuf (setBox key val sBox) prf

||| Reads a `BoxInt` multiplicity linearly according to the active `HybridBuf` mode.
public export
readHybridBuf : DiscreteCoord k => {denseCap : Nat}
             -> (1 hb : HybridBuf denseCap k) -> Fin denseCap -> k -> LPair (HybridBuf denseCap k) BoxInt
readHybridBuf (MkHybridBuf DenseMode dBuf sBox prf) idx _ =
  case readLinearBuffer dBuf idx of
    (dBuf' # val) => (MkHybridBuf DenseMode dBuf' sBox prf # val)
readHybridBuf (MkHybridBuf SparseMode dBuf sBox prf) _ key =
  (MkHybridBuf SparseMode dBuf sBox prf # lookupBox key sBox)

||| Consumes a `1`-quantity `HybridBuf` at session teardown, projecting its contents
||| back into an unrestricted `Carrier k` snapshot via `linBufToCarrier`.
public export
consumeHybridBuf : {0 k : Type} -> FiniteCoord k
                => {denseCap : Nat} -> {auto 0 eqCap : denseCap = cardinality {k}}
                -> (1 hb : HybridBuf denseCap k) -> Carrier k
consumeHybridBuf {eqCap} (MkHybridBuf DenseMode dBuf _ _) =
  linBufToCarrier (rewrite sym eqCap in dBuf)
consumeHybridBuf (MkHybridBuf SparseMode (MkLinearBuffer _) sBox _) = sBox

------------------------------------------------------------------------
-- 7. CIRCULAR `O(win)` WINDOWED RING BUFFER (`WindowedHorizon win`)
------------------------------------------------------------------------

||| Fixed-capacity circular ring buffer backed by contiguous `Vect win a` (`O(win)` memory).
||| Implements `Rule 08` §4 circular storage for `Segment win` and `HubblePatch` horizons
||| without heap list accumulation.
public export
record WindowedRingBuf (win : Nat) (a : Type) where
  constructor MkWindowedRingBuf
  headIdx     : Fin win
  filledCount : Nat
  slots       : Vect win a

||| Constructs an initialized ring buffer filled with `defaultVal`.
public export
emptyRingBuf : {win : Nat} -> a -> WindowedRingBuf (S win) a
emptyRingBuf defaultVal = MkWindowedRingBuf FZ 0 (replicate (S win) defaultVal)

||| Advances a circular `Fin (S n)` index forward by 1 modulo `S n`.
public export
ringNextIdx : {n : Nat} -> Fin (S n) -> Fin (S n)
ringNextIdx cur =
  case strengthen (FS cur) of
    Nothing  => FZ
    Just nxt => nxt

||| Steps a circular `Fin (S n)` index backward by 1 modulo `S n`.
public export
ringPrevIdx : {n : Nat} -> Fin (S n) -> Fin (S n)
ringPrevIdx FZ     = last
ringPrevIdx (FS j) = weaken j

||| Pushes a new sample into `WindowedRingBuf (S n) a` in `O(1)` index wrap.
public export
pushRingBuf : {n : Nat} -> a -> WindowedRingBuf (S n) a -> WindowedRingBuf (S n) a
pushRingBuf val (MkWindowedRingBuf cur filled vec) =
  MkWindowedRingBuf
    (ringNextIdx cur)
    (min (S n) (S filled))
    (replaceAt cur val vec)

||| Reads the slot `offset` ticks behind the latest entry (`0` = most recently pushed).
public export
readRingOffset : {n : Nat} -> Nat -> WindowedRingBuf (S n) a -> a
readRingOffset off (MkWindowedRingBuf cur _ vec) =
  go off (ringPrevIdx cur)
  where
    go : Nat -> Fin (S n) -> a
    go Z     idx = index idx vec
    go (S k) idx = go k (ringPrevIdx idx)

||| Returns the most recently pushed value, or `fallback` if `filledCount == 0`.
public export
latestRingBuf : {n : Nat} -> a -> WindowedRingBuf (S n) a -> a
latestRingBuf fallback rb =
  if rb.filledCount == 0 then fallback else readRingOffset 0 rb

||| Folds over populated ring slots from newest to oldest without allocating lists (`Rule 04` §10).
public export
foldRingBuf : {n : Nat} -> (acc -> a -> acc) -> acc -> WindowedRingBuf (S n) a -> acc
foldRingBuf fn initAcc (MkWindowedRingBuf cur filled vec) =
  go (min (S n) filled) (ringPrevIdx cur) initAcc
  where
    go : Nat -> Fin (S n) -> acc -> acc
    go Z _ acc = acc
    go (S rem) idx acc = go rem (ringPrevIdx idx) (fn acc (index idx vec))

||| Computes causal FIR / sliding dot product between newest `S n` slots and `taps`.
public export
dotRingBuf : {n : Nat} -> WindowedRingBuf (S n) BoxInt -> List BoxInt -> BoxInt
dotRingBuf (MkWindowedRingBuf cur _ vec) taps =
  go (S n) (ringPrevIdx cur) taps (intToBoxInt 0)
  where
    go : Nat -> Fin (S n) -> List BoxInt -> BoxInt -> BoxInt
    go Z _ _ acc = acc
    go _ _ [] acc = acc
    go (S rem) idx (t :: ts) acc =
      go rem (ringPrevIdx idx) ts (addBox acc (mulBox t (index idx vec)))

||| Matches a target pattern `[newest, prev, ...]` against the active history in `WindowedRingBuf`.
||| Requires `filledCount >= length pat` so uninitialized slots never produce spurious matches.
public export
matchRingPattern : {n : Nat} -> Eq a => List a -> WindowedRingBuf (S n) a -> Bool
matchRingPattern pat (MkWindowedRingBuf cur filled vec) =
  if filled < length pat
    then False
    else go (S n) (ringPrevIdx cur) pat
  where
    go : Nat -> Fin (S n) -> List a -> Bool
    go _ _ [] = True
    go Z _ (_ :: _) = False
    go (S rem) idx (p :: ps) =
      (index idx vec == p) && go rem (ringPrevIdx idx) ps

------------------------------------------------------------------------
-- 8. PERIMETER-PEELED 3-POINT STENCIL STEPPER FOR `PingPongGrid`
------------------------------------------------------------------------

||| Spatial perimeter handling policy for 1D `PingPongGrid` stencils (`Rule 08` §4).
public export
data PerimeterPolicy : Type where
  ZeroPerimeter     : PerimeterPolicy
  MirrorPerimeter   : PerimeterPolicy
  PeriodicPerimeter : PerimeterPolicy

public export
Eq PerimeterPolicy where
  ZeroPerimeter     == ZeroPerimeter     = True
  MirrorPerimeter   == MirrorPerimeter   = True
  PeriodicPerimeter == PeriodicPerimeter = True
  _                 == _                 = False

||| Reads `readBuf` with peeled left/right boundary handling (`Zero`, `Mirror`, `Periodic`),
||| runs branchless `interiorFn (left, mid, right)` across interior cells, and swaps buffers in O(1).
public export
stepPingPong3PointWithPolicy : {capacity : Nat}
                            -> PerimeterPolicy
                            -> (BoxInt -> BoxInt -> BoxInt -> BoxInt)
                            -> (1 grid : PingPongGrid capacity)
                            -> PingPongGrid capacity
stepPingPong3PointWithPolicy _ _ (MkPingPongGrid r w) {capacity = Z} = MkPingPongGrid w r
stepPingPong3PointWithPolicy pol fn (MkPingPongGrid (MkLinearBuffer rTok) (MkLinearBuffer wTok)) {capacity = S Z} =
  let c0 = index FZ rTok
      nbr = case pol of
              ZeroPerimeter     => intToBoxInt 0
              MirrorPerimeter   => c0
              PeriodicPerimeter => c0
      v0 = fn nbr c0 nbr
  in MkPingPongGrid (MkLinearBuffer (replaceAt FZ v0 wTok)) (MkLinearBuffer rTok)
stepPingPong3PointWithPolicy pol fn (MkPingPongGrid (MkLinearBuffer rTok) (MkLinearBuffer wTok)) {capacity = S (S k)} =
  let r0   = index FZ rTok
      r1   = index (FS FZ) rTok
      rLast = index lastIdx rTok
      rPrev = index (weaken lastButOne) rTok
      leftOut  = case pol of
                   ZeroPerimeter     => intToBoxInt 0
                   MirrorPerimeter   => fn r0 r0 r1
                   PeriodicPerimeter => fn rLast r0 r1
      rightOut = case pol of
                   ZeroPerimeter     => intToBoxInt 0
                   MirrorPerimeter   => fn rPrev rLast rLast
                   PeriodicPerimeter => fn rPrev rLast r0
      w0   = replaceAt FZ leftOut wTok
      w1   = replaceAt lastIdx rightOut w0
      wFin = fillInt k FZ rTok w1
  in MkPingPongGrid (MkLinearBuffer wFin) (MkLinearBuffer rTok)
  where
    lastIdx : Fin (S (S k))
    lastIdx = last

    lastButOne : Fin (S k)
    lastButOne = last

    fillInt : Nat -> Fin (S k) -> Vect (S (S k)) BoxInt -> Vect (S (S k)) BoxInt -> Vect (S (S k)) BoxInt
    fillInt Z _ _ wAcc = wAcc
    fillInt (S rem) leftIdx rV wAcc =
      let midIdx : Fin (S (S k)) = FS leftIdx
          rightIdx : Fin (S (S k)) = case strengthen midIdx of
                                       Nothing => lastIdx
                                       Just mSmall => FS mSmall
          newV = fn (index (weaken leftIdx) rV) (index midIdx rV) (index rightIdx rV)
          wAcc' = replaceAt midIdx newV wAcc
      in case strengthen (FS leftIdx) of
           Nothing => wAcc'
           Just nextLeft => fillInt rem nextLeft rV wAcc'
