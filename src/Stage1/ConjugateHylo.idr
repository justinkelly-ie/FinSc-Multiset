module Stage1.ConjugateHylo

import public Stage0.BoxInt
import public Stage0.Multiset
import Data.Fuel

%default total

||| A Conjugate Hylomorphism (Ralf Hinze, Thomas Wu, Jeremy Gibbons)
||| unfolds a seed value `a` using coalgebra `coalg : a -> f a`,
||| applies a natural layer transformation `eta : forall x . f x -> g x`,
||| and folds the transformed structure using algebra `alg : g b -> b`.
|||
||| This unifies heterogeneous recursive scheme transformations into a single deforested pass.
public export
conjugateHylo : Functor f => Functor g
             => (alg : g b -> b)
             -> (coalg : a -> f a)
             -> (eta : forall x . f x -> g x)
             -> a -> b
conjugateHylo alg coalg eta x =
  alg (map (assert_total (conjugateHylo alg coalg eta)) (eta (coalg x)))

||| Bounded fuel version of Conjugate Hylomorphism guaranteeing termination.
public export
conjugateHyloFuel : Functor f => Functor g
                 => Fuel
                 -> (alg : g b -> b)
                 -> (coalg : a -> f a)
                 -> (eta : forall x . f x -> g x)
                 -> b -> a -> b
conjugateHyloFuel Dry _ _ _ fallback _ = fallback
conjugateHyloFuel (More fuel) alg coalg eta fallback x =
  alg (map (conjugateHyloFuel fuel alg coalg eta fallback) (eta (coalg x)))
