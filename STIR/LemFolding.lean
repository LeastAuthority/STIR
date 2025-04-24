/-
Copyright (c) 2025 ZKLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import STIR.DefReedSolomonCodes
import STIR.DefProximityBound
import STIR.DefSmoothDom

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
  /- The construction proof is not in STIR but its proposition 6.3 in
      https://people.csail.mit.edu/madhu/papers/2005/rspcpp-full.pdf ...
      Unfortunately 𝔽[X,Y] is not an Euclidean Domain, so this proof might need some work
      to show existence of polynomials Q and Q' such that P = Q'*(y- q) + Q ...
      (It can be done fixing an order though)

      In particular we don't have an equivalent to

      EuclideanDomain.quotient_mul_add_remainder_eq (a b : R) :
        b * EuclideanDomain.quotient a b + EuclideanDomain.remainder a b = a

      so we can not construct existence trivially
      -/
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


noncomputable def fold
  {F  : Type*} [Field F] [Fintype F] [DecidableEq F]
  {L : Finset F}
  (f : L → F)
  (k : ℕ)
  (α : F) : powDom L k → F := by sorry -- We should implement this at some point. Not a proof

noncomputable def foldingRange
  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {L : Finset F}
  {d : ℕ}
  (C : ReedSolomonCode F L d)
  (f : L → F) : ℝ :=
   min (fractionalHammingDistSet f (C.code) (C.nonempty)) (1 - Bstar C.rate)

lemma folding
  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {L : Finset F}
  {d : ℕ} -- Can lean really deduce it?
  (f : L → F)
  (k : ℕ) -- We might need an assumption that k is a factor of d
  (C1 : ReedSolomonCode F L d)
  (C2 : ReedSolomonCode F (powDom k L) (d/k))
  (δ : {x : ℝ // 0 < x ∧ x < foldingRange C1 f}) :
    (PMF.uniformOfFintype F).toOuterMeasure { r |
            fractionalHammingDistSet
              (fold f k r)
              (C2.code)
              (C2.nonempty)
            ≤ δ.val } > err' F (d/k) C1.rate δ k -- Double check if this really is C1.rate not C2.rate

   := by sorry
