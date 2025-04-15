import STIR.DefReedSolomonCodes

import Mathlib.Data.Real.Sqrt

lemma JohnsonBound
  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {L : Finset F}
  {d : ℕ}
  (C : ReedSolomonCode F L d)
  (η : ℝ)
  (hη : 0 < η ∧ η < 1 - Real.sqrt C.rate) :
    C.listDecodable (1 - Real.sqrt C.rate - η) (1 / (2 *  η * Real.sqrt C.rate)) := by sorry
