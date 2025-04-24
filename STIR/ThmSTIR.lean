import STIR.DefReedSolomonCodes
import STIR.DefSmoothDom

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-- Dummy type representing a public-coin IOPP. -/
structure IOPP
  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {L : Finset F}
  {d : ℕ}
  (C : ReedSolomonCode F L d)
  (hsmooth : smoothDom L)
  (hd : ∃ m, d = 2^m): Type where
  dummy : True


/-- STIR Main Theorem -/
theorem STIR_main_theorem
  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {L : Finset F} (hsmooth : smoothDom L)
  {d : ℕ} (hd : ∃ m, d = 2^m)
  (C : ReedSolomonCode F L d)
  (lambda : ℕ)
  (δ : ℝ) (hδ0 : 0 < δ) (hδub : δ < 1 - 1.05 * Real.sqrt (d / L.card))
  (k : ℕ) (hk : ∃ m, k = 2^m) (hk4 : 4 ≤ k)
  (hF : Fintype.card F ≥ lambda * 2 ^ lambda * d^2 * L.card^(7/2) / Real.log (1 / C.rate)):
    ∃ π : IOPP C hsmooth hd, True := by sorry -- Dummy for now
