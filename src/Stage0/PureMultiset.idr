module Stage0.PureMultiset

import public Stage0.BoxInt
import public Stage0.HereditaryMSet

%default total

------------------------------------------------------------------------
-- SPECIALIZED `BoxInt` HELPERS OVER `Stage0.HereditaryMSet`
------------------------------------------------------------------------

||| Looks up a key in `Box BoxInt k`, returning `0` when absent.
public export
lookupBoxInt : Ord k => k -> Box BoxInt k -> BoxInt
lookupBoxInt = lookupBox

||| Canonical zero-pruning insertion for `Box BoxInt k`:
||| Inserts or overwrites `val`, automatically deleting the node if `val == 0`
||| so `BoxLeaf` remains the unique canonical zero representation.
public export
insertBoxInt : Ord k => k -> BoxInt -> Box BoxInt k -> Box BoxInt k
insertBoxInt = setBox
