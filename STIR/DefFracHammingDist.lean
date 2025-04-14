import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Real.Basic
import Mathlib.InformationTheory.Hamming

/- The fractional Hamming distance between two functions `f, g : L → F` is the number of
    points at which they differ, normalized between 0 and 1.
-/

/-- The fractional Hamming distance between two functions `f, g : L → F`, normalized between 0 and 1. -/
def fractionalHammingDist {L F : Type*} [Fintype L] [DecidableEq F] (f g : L → F) : ℚ :=
  (hammingDist f g : ℚ) / Fintype.card L

 /-- The fractional Hamming distance between a function `f : L → F` and a nonempty finite set of functions `S ⊆ (L → F)`
     is defined as ∆(f, S) := minh∈S ∆(f, h)
 -/
def fractionalHammingDistSet {L F : Type*} [Fintype L] [DecidableEq F] (f : L → F) (S : Finset (L → F)) (h_nonempty : S.Nonempty) : ℚ :=
  (S.inf' h_nonempty (hammingDist f ·) : ℚ) / Fintype.card L
