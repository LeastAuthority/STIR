import STIR.DefProximityBound
import STIR.DefReedSolomonCodes
import STIR.DefFracHammingDist

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt


lemma proximityGap
  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {L : Finset F}
  {d : ℕ}
  (C : ReedSolomonCode F L d)
  (Rnge  : ℝ)
  (hRnge : Rnge = 1 - Bstar C)
  (δ : {x : ℝ // 0 < x ∧ x < Rnge})
  (m : ℕ)
  (f : Fin m → (L → F))
  (h : (PMF.uniformOfFintype F).toOuterMeasure { r |
          fractionalHammingDistSet
            (λ x ↦ ∑ j : Fin m, (r^(j : ℕ)) • (f j x))
            (C.code)
            (C.nonempty)
          ≤ δ.val } > err' C Rnge δ m) :
  ∃ (S : Finset F), -- better S Finset L ? then S subset L is automatic
    S ⊆ L ∧
    S.card ≥ (1 - δ.val) * L.card ∧
    ∀ i : Fin m, ∃ u ∈ C.code, ∀ x ∈ S, ∀ hx : x ∈ L, f i ⟨x, hx⟩ = u ⟨x, hx⟩ := by
  sorry
