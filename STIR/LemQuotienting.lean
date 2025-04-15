import STIR.DefFracHammingDist
import STIR.DefReedSolomonCodes

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.Basic


namespace quotient

/- PolyAns S Ans is the unique interpolating polynomial of degree < |S|
   with PolyAns(s) = Ans(s) for each s ∈ S.

  Note: For S=∅ we get PolyAns(x) = 0 (the zero polynomial)
-/
noncomputable def AnsPoly
  (F : Type*) [Field F] [Fintype F] [DecidableEq F]
  (S : Finset F)
  (Ans : S → F) : Polynomial F :=
  Lagrange.interpolate S.attach (fun i => (i : F)) Ans

/- VanishingPoly is the vanishing polynomial on S, i.e. the unique polynomial of degree |S|+1
   that is 0 at each s ∈ S and is not the zero polynomial if S ≠ F.
   It is defined as ∏(s ∈ S) (X - s).
-/
noncomputable def VanishingPoly
  (F : Type*) [Field F] [Fintype F] [DecidableEq F]
  (S : Finset F) : Polynomial F :=
  ∏ s in S, (Polynomial.X - Polynomial.C s)

noncomputable def Quotient
  (F : Type*) [Field F] [Fintype F] [DecidableEq F]
  (L : Finset F)
  (f : L → F)
  (S : Finset F)
  (Ans : S → F)
  (Fill : S → F)
  : L → F :=
    let pAns := AnsPoly F S Ans
    let pV   := VanishingPoly F S
    fun x =>
      if hx : x.val ∈ S then
        Fill ⟨x.val, hx⟩
      else
        (f x - pAns.eval x.val) / pV.eval x.val


/-
  We define the set T(f,L,S,Ans) as the set of all points x ∈ L that lie in S such that
  the AnsPoly disagrees with f. Formally: T := { x ∈ L | x.val ∈ S ∧ AnsPoly x ≠ f x }.
-/
noncomputable def T
  (F : Type*) [Field F] [Fintype F] [DecidableEq F]
  (L : Finset F)
  (f : L → F)
  (S : Finset F)
  (Ans : S → F) : Finset F :=
  (L.attach.filter (λ x ↦ (AnsPoly F S Ans).eval x.val ≠ f x)).image Subtype.val

/- NOT THE ACTUAL LEMMA; WORK IN PROGRESS-/
/-
lemma quotienting_lemma
  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {L : Finset F}
  {d : ℕ}
  (C : ReedSolomonCode F L d)
  (f : L → F)
  (degree : ℕ)
  (distance : ℝ) (h_distance : 0 < distance ∧ distance < 1)
  (S : Finset F) (hS : S.card < degree)
  (Ans Fill : S → F)
  (hC : d = degree)
  (h_close : ∀ u ∈ C.List f distance, ∃ x ∈ S, polynomialEvalOn F L (AnsPoly F S Ans) x ≠ u x)
  : fractionalHammingDistSet (Quotient F L f S Ans Fill) (C.code) (C.nonempty) +
    ((T F L f S Ans).card : ℚ) / (L.card : ℚ) > distance :=
sorry

/-NOT THE ACTUAL LEMMA. WORK IN PROGRESS-/
lemma quotienting_lemma1
  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {L : Finset F}
  {d : ℕ}
  (C : ReedSolomonCode F L d)
  (f : L → F)
  (d : ℕ)
  (δ : ℝ) (hδ : 0 < δ ∧ δ < 1)
  (S : Finset F) (hS : S.card < d)
  (Ans Fill : S → F)
  (h_close : ∀ u ∈ C.List f δ, ∃ x ∈ S, polynomialEvalOn F L (AnsPoly F S Ans) x ≠ u x)
  : fractionalHammingDistSet (Quotient F L f S Ans Fill) (C.code) (C.nonempty) +
    ((T F L f S Ans).card : ℚ) / (L.card : ℚ) > δ :=
sorry
-/
end quotient
