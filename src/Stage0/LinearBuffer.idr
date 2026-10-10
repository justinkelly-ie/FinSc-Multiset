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

||| Extracts total integer value across buffer.
public export
bufferTotalValue : {capacity : Nat} -> LinearBuffer capacity -> Integer
bufferTotalValue (MkLinearBuffer tok) = foldl (\acc, b => acc + unwrapBox b) 0 tok
