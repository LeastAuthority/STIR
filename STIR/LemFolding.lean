import STIR.DefReedSolomonCodes

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Distributions.Uniform

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt


/-The STIR paper assumes that the polynomials f(.) and Q(q(.),.) are fully determined by their
  evaluations on F, which is not necessarily true for arbitrary polynomials of degrees larger then
  |F|. So we include an assumption in what follows that q has degree < |F| fom which the uniqueness
  of f and Q can be derived -/

/-- Helper For Readability: Evaluate a bivariate polynomial Q at (a, b) ∈ F×F -/
def evalBivar
  {F  : Type*} [Field F] [Fintype F] [DecidableEq F]
  (Q : MvPolynomial (Fin 2) F) (a b : F) : F := MvPolynomial.eval (Fin.cases a (fun _ ↦ b)) Q

lemma exists_unique_fold
  {F  : Type*} [Field F] [Fintype F] [DecidableEq F]
  (q : Polynomial F) (hdeg_q_min : q.natDegree > 0) (hdeq_q_max : q.natDegree < Fintype.card F)
  (f : Polynomial F) :
    -- Q ∈ 𝔽[X,Y]
    ∃! Q : MvPolynomial (Fin 2) F,
      -- deg_x(Q) = Floor ( deg() / deg(q) )
      -- This is natrual number division towards zero, which is floor
      (MvPolynomial.degreeOf 0 Q = (Polynomial.natDegree f) / (Polynomial.natDegree q)) ∧
      -- deg_y(Q) < deg (q)
      (MvPolynomial.degreeOf 1 Q < Polynomial.natDegree q) ∧
      -- point‑wise equality on F: f(z) = Q(q(z), z)
      (∀ z : F, Polynomial.eval z f = evalBivar Q (Polynomial.eval z q) z):=
  sorry

lemma degX_lt_of_deg_lt
  {F  : Type*} [Field F] [Fintype F] [DecidableEq F]
  (t : ℕ)
  (q : Polynomial F) (hdeg_q : q.natDegree ≠ 0)
  (f : Polynomial F) (hdeg_f : f.natDegree < t * q.natDegree)
  (Q : MvPolynomial (Fin 2) F)
  (hX : MvPolynomial.degreeOf 0 Q = f.natDegree / q.natDegree)
  (hY : MvPolynomial.degreeOf 1 Q < q.natDegree)
  (heq : ∀ z : F, f.eval z = evalBivar Q (q.eval z) z) : MvPolynomial.degreeOf 0 Q < t :=
  sorry

/- L^k := {x^k | x ∈ L} -/
/- TODO PUT IT SOMEWHERE ELSE LATER-/
noncomputable def powDomain
  {F  : Type*} [Field F] [Fintype F] [DecidableEq F]
  (k : ℕ)
  (L : Finset F) : Finset F := L.image fun x : F => x ^ k

noncomputable def fold
  {F  : Type*} [Field F] [Fintype F] [DecidableEq F]
  {L : Finset F}
  (f : L → F)
  (k : ℕ)
  (α : F) : powDomain k L → F := by sorry -- We should implement this at some point. Not a proof

lemma folding
  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {L : Finset F}
  {d : ℕ}
  (f : L → F)
  (k : ℕ) -- We might need an assumption that k is a factor of d
  (C : ReedSolomonCode F (powDomain k L) (d/k))
  (δ : {x : ℝ // 0 < x ∧ x < 1 - Real.sqrt C.rate}) : -- WRONG, NEEDS AN UPDATE
    (PMF.uniformOfFintype F).toOuterMeasure { r |
            fractionalHammingDistSet
              (fold f k r)
              (C.code)
              (C.nonempty)
            ≤ δ.val } > 0 -- TODO PROPER ERR FUNCTION

   := by sorry
