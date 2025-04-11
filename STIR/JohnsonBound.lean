import STIR.ReedSolomonCodes


import Mathlib.Data.Real.Sqrt

-- Formalization (without proof) of Johnson bound theorem for Reed-Solomon codes.
theorem JohnsonBound {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  (C : ReedSolomonCode F)
  (η : ℝ)
  (hη : 0 < η ∧ η < 1 - Real.sqrt C.rate) :

  C.listDecodable (1 - Real.sqrt C.rate - η) (1 / (2 *  η * Real.sqrt C.rate)) := by
sorry
