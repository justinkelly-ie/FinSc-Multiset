module Stage0.LinearBuffer

import Stage0.BoxInt
import Data.Vect
import Data.Fin

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

||| Double-buffered spatial grid (`PingPongGrid`) for lowered `Fby` stencil kernels (`Gemini.md` Section 5).
public export
record PingPongGrid (capacity : Nat) where
  constructor MkPingPongGrid
  1 readBuf  : LinearBuffer capacity
  1 writeBuf : LinearBuffer capacity

||| Allocates a zeroed double-buffered PingPongGrid.
public export
createPingPongGrid : (cap : Nat) -> PingPongGrid cap
createPingPongGrid cap = MkPingPongGrid (createLinearBuffer cap) (createLinearBuffer cap)

||| O(1) linear double-buffer swap (`ana` read <-> `cata` write) with zero heap allocation.
public export
swapBuffers : {capacity : Nat} -> (1 grid : PingPongGrid capacity) -> PingPongGrid capacity
swapBuffers (MkPingPongGrid r w) = MkPingPongGrid w r

||| Flat, zero-allocation cyclomatic hylomorphism transition kernel (`compileStream` target).
||| Consumes linear state with multiplicity 1 and returns an LPair `(st' # out)`.
public export
StepKernel : (s : Type) -> (inp : Type) -> (out : Type) -> Type
StepKernel s inp out = (1 state : s) -> inp -> LPair s out

