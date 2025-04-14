import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Distributions.Uniform


theorem examle_multi_samples  (F : Type) [Field F] [Fintype F] [Nonempty F] (m : ℕ ): (PMF.uniformOfFintype (Fin m → F)).toOuterMeasure {x | (Finset.univ.sum x) = 1} = 1/(Fintype.card F) := by sorry

open Finset

theorem example_multi_samples_subset
  (F : Type) [Field F] [Fintype F] [Nonempty F]
  (L : Set F) [DecidablePred (· ∈ L)]
  (hL : Set.Nonempty (Set.univ \ L))
  [Nonempty {x // x ∉ L}]
  (m : ℕ) :
  (PMF.uniformOfFintype (Fin m → { x // x ∉ L })).toOuterMeasure
    { x | (Finset.univ.sum (fun i ↦ (x i : F))) = 1 }
  = 1 / ((Fintype.card { x // x ∉ L }) ^ m) := by sorry
