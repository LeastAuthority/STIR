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
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Nat.Basic

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

/-- Helper For Readability: Evaluate a bivariate polynomial Q at (a, b) ∈ F×F -/
def evalBivar
  {F  : Type*} [Field F] [Fintype F] [DecidableEq F]
  (Q : MvPolynomial (Fin 2) F) (a b : F) : F := MvPolynomial.eval (Fin.cases a (fun _ ↦ b)) Q

/-The STIR paper assumes that the polynomials f(.) and Q(q(.),.) are fully determined by their
  evaluations on F, which is not necessarily true for arbitrary polynomials of degrees larger then
  |F|. So we include an assumption in what follows that q has degree < |F| fom which the uniqueness
  of f and Q can be derived from their evaluation on F -/
lemma existsUniqueFold
  {F  : Type*} [Field F] [Fintype F] [DecidableEq F]
  (q : Polynomial F) (hdeg_q_min : q.natDegree > 0) (hdeg_q_max : q.natDegree < Fintype.card F)
  (f : Polynomial F) :
    -- Q ∈ 𝔽[X,Y]
    ∃! Q : MvPolynomial (Fin 2) F,
      -- deg_x(Q) = Floor ( deg() / deg(q) )
      -- This is natrual number division towards zero, which is floor
      (MvPolynomial.degreeOf 0 Q = (Polynomial.natDegree f) / (Polynomial.natDegree q)) ∧
      -- deg_y(Q) < deg (q)
      (MvPolynomial.degreeOf 1 Q < Polynomial.natDegree q) ∧
      -- point‑wise equality on F: f(z) = Q(q(z), z)
      (∀ z : F, Polynomial.eval z f = evalBivar Q (Polynomial.eval z q) z) ∧
  (∀ t : ℕ, f.natDegree < t * q.natDegree → MvPolynomial.degreeOf 0 Q < t):=

  /- The construction proof of Q is not in STIR but its proposition 6.3 in
      https://people.csail.mit.edu/madhu/papers/2005/rspcpp-full.pdf ...
      Unfortunately 𝔽[X,Y] is not an Euclidean Domain, so this proof might need some work
      to show existence of polynomials Q and Q' such that P = Q'*(y- q) + Q ...

      Using MonomialOrder.div from Mathlib.RingTheory.MvPolynomial.Groebner should work

      In order to define polynomial division on the non-Euclidean Ring 𝔽[z,y] we need
      to fix an order on monomials. Using the usual lexicographic order x₀ > x₁ is equal to
      proposition 6.3 in https://people.csail.mit.edu/madhu/papers/2005/rspcpp-full.pdf
      under the substitution z = x₀ and y = x₁

      noncomputable def m : MonomialOrder (Fin 2) := MonomialOrder.lex is how you define
      the order.
  -/
  sorry

lemma foldDegreeBound
  {F  : Type*} [Field F] [Fintype F] [DecidableEq F]
  (q : Polynomial F) (hdeg_q_min : q.natDegree > 0) (hdeg_q_max : q.natDegree < Fintype.card F)
  {t : ℕ}
  (Q : MvPolynomial (Fin 2) F)
  (hdegX : MvPolynomial.degreeOf 0 Q < t)
  (hdegY : MvPolynomial.degreeOf 1 Q < q.natDegree) :
  (MvPolynomial.eval₂Hom (Polynomial.C : F →+* Polynomial F)
      (fun i : Fin 2 => if i = 0 then q else Polynomial.X) Q).natDegree < t * q.natDegree :=
by sorry

noncomputable def polyFold
  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  (f : Polynomial F)
  (k : ℕ) (hk0 : 0 < k) (hkfin : k < Fintype.card F)
  (r : F): Polynomial F :=
    let q : Polynomial F := Polynomial.X ^ k
    let hdeg_q_min : q.natDegree > 0 := sorry
    let hdeg_q_max : q.natDegree < Fintype.card F := sorry
  -- choose the unique bivariate lift Q
    let Q : MvPolynomial (Fin 2) F :=
    (Classical.choose (existsUniqueFold q hdeg_q_min hdeg_q_max f ) : MvPolynomial (Fin 2) F)
  -- now freeze Y ↦ r, X ↦ X, using the constant‐polynomial ring‐hom `Polynomial.C`
    MvPolynomial.eval₂Hom
      (Polynomial.C : F →+* Polynomial F)
      (fun i : Fin 2 => if i = 0 then Polynomial.X else Polynomial.C r)
      Q

noncomputable def xPoly
  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  (L : Finset F)
  (f : L → F)
  (k : ℕ)
  (x : powDom L k) : Polynomial F :=
    let S := powFiber L k x
    Lagrange.interpolate
      S.attach
      Subtype.val
      fun i =>
        let hL : i.1 ∈ L := (Finset.mem_filter.1 i.2).1
        f ⟨i.1, hL⟩

noncomputable def fold
  {F  : Type*} [Field F] [Fintype F] [DecidableEq F]
  {L : Finset F}
  (f : L → F)
  (k : ℕ)
  (α : F) : powDom L k → F :=
    fun x => (xPoly L f k x).eval α

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
  (C2 : ReedSolomonCode F (powDom L k) (d/k))
  (δ : {x : ℝ // 0 < x ∧ x < foldingRange C1 f}) :
    (PMF.uniformOfFintype F).toOuterMeasure { r |
            fractionalHammingDistSet
              (fold f k r)
              (C2.code)
              (C2.nonempty)
            ≤ δ.val } > err' F (d/k) C1.rate δ k -- Double check if this really is C1.rate not C2.rate

   := by sorry
