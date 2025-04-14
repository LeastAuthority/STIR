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
   that is 0 at each s ∈ S and is not the zero polynomial if S ≠ F, defined as ∏(s ∈ S) (X - s).
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
    -- `x : { x // x ∈ L }`, so `x.val : F` is the actual field element.
    if hx : x.val ∈ S then
      -- Here we coerce x.val ∈ S into a subtype of S so that `Fill` can be applied
      Fill ⟨x.val, hx⟩
    else
      (f x - pAns.eval x.val) / pV.eval x.val

end quotient
