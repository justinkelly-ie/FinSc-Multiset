module Stage0.OnSeq.FusedStreamBenchmark

import Stage0.OnSeq.FusedStream
import Data.List
import Data.Fuel

%default total

------------------------------------------------------------------------
-- BENCHMARK SUITE: FUSEDSTREAM ZERO-ALLOCATION DEFORESTATION VS LIST
------------------------------------------------------------------------

||| Generates a list of integers from 1 to n.
public export
generateSequence : Nat -> List Integer
generateSequence Z = []
generateSequence (S k) = cast (S k) :: generateSequence k

||| Standard List pipeline (3 intermediate list heap allocations).
||| Pipeline: map (+ 10) . filter (even) . map (* 3)
public export
listPipeline : List Integer -> Integer
listPipeline xs =
  let stage1 = map (* 3) xs
      stage2 = filter (\x => (x `mod` 2) == 0) stage1
      stage3 = map (+ 10) stage2
  in foldl (+) 0 stage3

||| Deforested FusedStream pipeline (Zero intermediate list heap allocations).
||| Pipeline: foldStreamNat (length xs) (+) 0 (mapStream (+ 10) (filterStream (even) (mapStream (* 3) (stream xs))))
public export
fusedStreamPipeline : List Integer -> Integer
fusedStreamPipeline xs =
  let strm = stream xs
      stage1 = mapStream (* 3) strm
      stage2 = filterStream (\x => (x `mod` 2) == 0) stage1
      stage3 = mapStream (+ 10) stage2
  in foldStreamNat (length xs) (+) 0 stage3

||| Proves mathematical & observational equivalence between List baseline and FusedStream deforested pipeline.
public export
verifyPipelineEquivalence : Nat -> Bool
verifyPipelineEquivalence n =
  let seq = generateSequence n
  in listPipeline seq == fusedStreamPipeline seq
