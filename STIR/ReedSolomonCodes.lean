import STIR.FracHammingDist

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Prime.Basic


/- THIS IS A PLACEHOLDER STRUCTURE AND NOT A GOOD DEFINITION YET. WE NEED THE SET OF
   CODEWORDS TO BE FINITE AND IN ORDER FOR FINSET TO BE CONSTRUCTED WE NEED TO EXPLICITLY
   COMPUTE AN ASSOCIATED POLYNOMIAL TO ANY GIVEN CODEWORD [E.G. BY LAGRANGE INTERPOLATION]
   TBD -/

open Polynomial  -- for monomial, X, etc.
open Finset      -- for using Finset.univ without qualification

noncomputable def polynomialsUpTo (F : Type*) [Field F] [Fintype F] [DecidableEq F]  (d : ℕ) : Finset (Polynomial F) :=
  (Finset.univ : Finset (Fin d → F)).image (λ c => ∑ i : Fin d, Polynomial.monomial (i : ℕ) (c i))

def polynomialEvalOn (F : Type*) [Field F] [Fintype F] [DecidableEq F] (L : Finset F) (p : Polynomial F) : (L → F) :=
  fun (x : L) => p.eval x.val

noncomputable def reedSolomonCodeFinset (F : Type*) [Field F] [Fintype F] [DecidableEq F]
  (L : Finset F) (hL : L.Nonempty) (d : ℕ) : Finset (L → F) :=
  (polynomialsUpTo F d).image (polynomialEvalOn F L)

structure ReedSolomonCode (F : Type*) [Field F] [Fintype F] [DecidableEq F] where
  L          : Finset F
  nonempty_L : L.Nonempty
  d          : ℕ
  code       : Finset (L → F)
  code_def   : code = (polynomialsUpTo F d).image (polynomialEvalOn F L)

namespace ReedSolomonCode

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

-- Rate of Reed-Solomon code
def rate (C : ReedSolomonCode F) : ℚ :=
  (C.d : ℚ) / (C.L.card : ℚ)

-- Ensures the Reed-Solomon code is nonempty
theorem nonempty (C : ReedSolomonCode F) : C.code.Nonempty := sorry

-- List of codewords close to a given function `f` within fractional Hamming distance `δ`
def List (C : ReedSolomonCode F) (f : C.L → F) (δ : ℚ) : Finset (C.L → F) :=
  C.code.filter (λ c ↦ fractionalHammingDist f c ≤ δ)

-- The Reed-Solomon code `C` is `(δ, l)`-list decodable if every function `f` has fewer than `l` close codewords
-- within fractional Hamming distance `δ`
def listDecodable (C : ReedSolomonCode F) (δ : ℚ) (l : ℕ) : Prop :=
  ∀ f : C.L → F, (C.List f δ).card < l

end ReedSolomonCode
