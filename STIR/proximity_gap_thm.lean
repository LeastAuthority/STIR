import STIR.ReedSolomonCodes

import Mathlib.Data.Real.Sqrt
import Mathlib.Probability.Distributions.Uniform
import Mathlib.InformationTheory.Hamming


/-
Let Δ(.,.) be the fractional hamming distance between a function and a set,
let C[F,L,d] be a Reed Solomon Code with rate ρ = d/|L|, let δ be a real number and
let f_1, ..., f_m : L → F be functions, such that:
 - δ is in the range (0, √ρ)
 -

then



 -/
theorem proximity_gap
  -- Let
  (F : Type*) [Field F]
  (C : ReedSolomonCode F)
  (δ : ℝ)
  (m : ℕ) (f : Fin m → (C.L → F))
  -- such that
  (hδ : 0 < δ ∧ δ < 1 - Real.sqrt C.rate)   -- δ ∈ (0, √ρ)
  -- TODO: the probability thing
  -- then
  : ∃ (S : Finset F),
    S ⊆ C.L ∧
    S.card ≥ (1 - δ) * C.L.card ∧
    ∀ i : Fin m, ∃ u ∈ C.code, ∀ x ∈ S, ∀ hx : x ∈ C.L, f i ⟨x, hx⟩ = u ⟨x, hx⟩:= by
  sorry
