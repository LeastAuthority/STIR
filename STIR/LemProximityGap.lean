import STIR.DefReedSolomonCodes
import STIR.DefFracHammingDist

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

/- TODO: Make Everything ENNReal in the first place. Working with probabilities
   ENNReal seems to be the proper type. We might want to discuss this with the
   larger team at some point -/
noncomputable def err'
  (F : Type*) [Field F] [Fintype F] [DecidableEq F]
  (d : ℕ)
  (ρ : ℝ )
  (δ : {x : ℝ // 0 < x ∧ x < 1 - Real.sqrt ρ})
  (m : ℕ) : ENNReal :=
  ENNReal.ofReal (
    if δ.val ≤ (1 - ρ) / 2 then
      ((m - 1 : ℝ) * d) / (ρ * (Fintype.card F))
    else
      let min_val := min (1 - Real.sqrt ρ - δ.val) (Real.sqrt ρ / 20)
      ((m - 1 : ℝ) * (d : ℝ)^2) / ((Fintype.card F) * (2 * min_val)^7)
  )

lemma proximityGap
  (F : Type*) [Field F] [Fintype F] [DecidableEq F]
  (C : ReedSolomonCode F)
  (δ : {x : ℝ // 0 < x ∧ x < 1 - Real.sqrt C.rate})
  (m : ℕ)
  (f : Fin m → (C.L → F))
  (h : (PMF.uniformOfFintype F).toOuterMeasure { r |
          fractionalHammingDistSet
            (λ x ↦ ∑ j : Fin m, (r^(j : ℕ)) • (f j x))
            (C.code)
            (C.nonempty)
          ≤ δ.val } > err' F C.d C.rate δ m) :
  ∃ (S : Finset F),
    S ⊆ C.L ∧
    S.card ≥ (1 - δ.val) * C.L.card ∧
    ∀ i : Fin m, ∃ u ∈ C.code, ∀ x ∈ S, ∀ hx : x ∈ C.L, f i ⟨x, hx⟩ = u ⟨x, hx⟩ := by
  sorry
