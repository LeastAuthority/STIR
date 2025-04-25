/-
Copyright (c) 2025 ZKLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

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
   that is 0 at each s ∈ S and is not the zero polynomial. I.e V(X) = ∏(s ∈ S) (X - s).
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

noncomputable def polyQuotient
  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {d : ℕ}
  (f : Polynomial F) (hf : f.degree < d)
  (S : Finset F) (hS : S.card < d) : Polynomial F :=
    let pAns := AnsPoly F S (fun s => f.eval s)
    let pV   := VanishingPoly F S
    (f - pAns) / pV

/-
  We define the set T(f,L,S,Ans) as the set of all points x ∈ L that lie in S such that
  the AnsPoly disagrees with f. Formally: T := { x ∈ L | x ∈ S ∧ AnsPoly x ≠ f x }.
-/
noncomputable def T
  (F : Type*) [Field F] [Fintype F] [DecidableEq F]
  (L : Finset F)
  (f : L → F)
  (S : Finset F)
  (Ans : S → F) : Finset F :=
  (L.attach.filter (λ x ↦ (AnsPoly F S Ans).eval x.val ≠ f x)).image Subtype.val

/- Quotienting Lemma-/
lemma quotienting
  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
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
