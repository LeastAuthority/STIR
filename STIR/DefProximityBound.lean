import STIR.DefReedSolomonCodes

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

  noncomputable def Bstar
  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {L : Finset F}
  {d : ℕ}
  (C : ReedSolomonCode F L d) : ℝ :=
  Real.sqrt C.rate

/- TODO: Make Everything ENNReal in the first place. Working with probabilities ENNReal seems to be the proper type. We might want to discuss this with the larger team at some point -/
noncomputable def err'
  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {L : Finset F}
  {d : ℕ}
  (C : ReedSolomonCode F L d)
  (δ : {x : ℝ // 0 < x ∧ x < 1 - Bstar C})
  (m : ℕ) : ENNReal :=
  ENNReal.ofReal (
    if δ.val ≤ (1 - C.rate) / 2 then
      ((m - 1 : ℝ) * d) / (C.rate * (Fintype.card F))
    else
      let min_val := min (1 - Bstar C - δ.val) (C.rate / 20)
      ((m - 1 : ℝ) * (d : ℝ)^2) / ((Fintype.card F) * (2 * min_val)^7)
  )
