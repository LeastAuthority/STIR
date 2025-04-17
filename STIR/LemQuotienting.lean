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

namespace quotient

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {L : Finset F}
variable {d : ℕ} {δ : ℝ}
variable {S : Finset F} (hS_lt : S.card < d)
variable {Ans Fill : S → F}
variable (f : L → F)
variable (C : ReedSolomonCode F L (d - S.card))

/--
Let `f : L → F` be a function, `d` a degree parameter, `δ` a distance parameter,
`S ⊆ F` a set with `|S| < d`, and `Ans, Fill : S → F`. Suppose that
for every `u ∈ C.List f δ` there exists `x ∈ S` with `u x ≠ Ans x`. Then
```lean
  (fractionalHammingDistSet (Quotient f S Ans Fill) C.code C.nonempty_L : ℝ)
  + ((T F L f S Ans).card : ℝ) / (L.card : ℝ) > δ.
```
-/
lemma quotienting1 :
  (∀ u, u ∈ C.List f δ → ∃ (x : ↑L ) (hx : x.val ∈ S), u x ≠ Ans ⟨x, hx⟩ ) →
  (fractionalHammingDistSet (Quotient F L f S Ans Fill) C.code C.nonempty : ℝ)
    + ((T F L f S Ans).card : ℝ) / (L.card : ℝ) > δ := by
  sorry

end quotient


lemma quotienting {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {L : Finset F}
  {d : ℕ}
  (S : Finset F) (hS_lt : S.card < d)
  (C1 : ReedSolomonCode F L d)
  (C2 : ReedSolomonCode F L (d - S.card))
  (f : L → F)
  (Ans Fill : S → F)
  (δ : ℝ) (hδ : 0 < δ ∧ δ < 1)
  (h : ∀ u, u ∈ C1.List f δ → ∃ (x : ↑L) (hx : x.val ∈ S), u x ≠ Ans ⟨x.val, hx⟩) :
  (fractionalHammingDistSet (Quotient F L f S Ans Fill) C2.code C2.nonempty : ℝ)
    + ((T F L f S Ans).card : ℝ) / (L.card : ℝ) > δ := by
  sorry
