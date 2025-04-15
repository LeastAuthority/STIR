import STIR.DefFracHammingDist

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Prime.Basic

/-TODO: Make C.d a positive natural number, because expressions like (1-C.d) occure
  e.g. in the OutOfDomainSmpl lemma and for d=0 this makes no sense-/

/- THIS IS A PLACEHOLDER STRUCTURE AND NOT A GOOD DEFINITION YET. WE NEED THE SET OF
   CODEWORDS TO BE FINITE AND IN ORDER FOR FINSET TO BE CONSTRUCTED WE NEED TO EXPLICITLY
   COMPUTE AN ASSOCIATED POLYNOMIAL TO ANY GIVEN CODEWORD [E.G. BY LAGRANGE INTERPOLATION]
   TBD -/

/-- Polynomials of degree < d over a finite field F -/
noncomputable def polynomialsUpTo (F : Type*) [Field F] [Fintype F] [DecidableEq F] (d : ℕ)
    : Finset (Polynomial F) :=
  (Finset.univ : Finset (Fin d → F)).image (λ c => ∑ i : Fin d, Polynomial.monomial (i : ℕ) (c i))

/-- Evaluate a polynomial p at each x ∈ L, returning a function `↑L → F`. -/
def polynomialEvalOn (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (L : Finset F) (p : Polynomial F) : ↑L → F :=
  λ (x : ↑L) => p.eval x.val

/-- All polynomial evaluations of degree < d on L, i.e. a Reed-Solomon code as a finset. -/
noncomputable def reedSolomonCodeFinset (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (L : Finset F) (hL : L.Nonempty) (d : ℕ) : Finset (↑L → F) :=
  (polynomialsUpTo F d).image (polynomialEvalOn F L)

/- The ReedSolomonCode structure, storing the code as `Finset (↑L → F)`. -/
structure ReedSolomonCode
  (F : Type*) [Field F] [Fintype F] [DecidableEq F]
  (L : Finset F)
  (d : ℕ) where
    nonempty_L : L.Nonempty
    code       : Finset (L → F)
    code_def   : code = (polynomialsUpTo F d).image (polynomialEvalOn F L)

namespace ReedSolomonCode

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {L : Finset F} {d : ℕ}

-- Rate of Reed-Solomon code
noncomputable def rate (_C : ReedSolomonCode F L d) : ℝ :=
  (d : ℝ) / (L.card : ℝ)

-- Ensures the Reed-Solomon code is nonempty
theorem nonempty (C : ReedSolomonCode F L d) : C.code.Nonempty := sorry

-- List of codewords close to a given function `f` within fractional Hamming distance `δ`
noncomputable def List (C : ReedSolomonCode F L d) (f : L → F) (δ : ℝ) : Finset (L → F) :=
  C.code.filter (λ c ↦ fractionalHammingDist f c ≤ δ)

-- The Reed-Solomon code `C` is `(δ, l)`-list decodable if every function `f` has fewer than `l` close codewords
-- within fractional Hamming distance `δ`
def listDecodable (C : ReedSolomonCode F L d) (δ : ℝ) (l : ℝ) : Prop :=
  ∀ f : L → F, ((C.List f δ).card : ℝ) < l

-- Complement of the evaluation set `L` in `F` as a Finset
noncomputable def domainComplement (_C : ReedSolomonCode F L d) : Finset F :=
  Finset.univ \ L

lemma domainComplementNonempty (C : ReedSolomonCode F L d) : Nonempty C.domainComplement := by sorry

end ReedSolomonCode
