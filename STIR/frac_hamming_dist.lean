import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Real.Basic
import Mathlib.InformationTheory.Hamming

variable {L F : Type*} [Fintype L] [DecidableEq F]

/-- The fractional Hamming distance between two functions `f, g : L → F`, normalized between 0 and 1. -/
def fractionalHammingDist (f g : L → F) : ℚ :=
  (hammingDist f g : ℚ) / Fintype.card L

 /-- The fractional Hamming distance between a function `f : L → F` and a nonempty finite set of functions `S ⊆ (L → F)`. -/
def fractionalHammingDistSet (f : L → F) (S : Finset (L → F)) (h_nonempty : S.Nonempty) : ℚ :=
  (S.inf' h_nonempty (hammingDist f ·) : ℚ) / Fintype.card L
