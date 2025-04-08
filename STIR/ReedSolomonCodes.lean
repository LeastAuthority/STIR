import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Prime.Basic


open Polynomial

/-
We choose to use a structure for Reed–Solomon codes rather than a type definition (subset) for the following reasons:

1. **Parameter Bundling:**
   A structure bundles the parameters (the field `F`, the evaluation domain `L`, and the degree bound `d`)
   into a single object. This simplifies statements like "Let C be a ReedSolomonCode F L d" in theorems.

2. **Explicit Parameters:**
   The structure explicitly stores `L`, `d`, and the associated properties, which makes it easier to access
   these parameters in proofs and definitions.

3. **Derived Properties:**
   Additional properties (such as the rate, minimum distance, encoding, decoding functions, etc.) can be
   conveniently defined as functions within the namespace of the structure.

4. **Modularity and Extensibility:**
   Using a structure improves readability and maintainability. If we need to modify or extend the definition
   later, all parameters and properties are neatly encapsulated.

For comparison, a lightweight type definition for Reed–Solomon codes could look like this:

def reedSolomonCode {F : Type*} [Field F] {L : Finset F} {d : ℕ} {_hL : L.Nonempty} : Set (L → F) :=
{ f | ∃ (p : Polynomial F), p.natDegree < d ∧ ∀ (x : F) (hx : x ∈ L), f ⟨x, hx⟩ = p.eval x }

This type definition is simpler but does not bundle the parameters together, making it less convenient
for large developments where many theorems refer to a Reed–Solomon code with specific parameters.
-/

-- Define the ReedSolomonCode structure
structure ReedSolomonCode (F : Type*) [Field F] where
  L            : Finset F                            -- evaluation domain (finite set of points in F)
  hL           : L.Nonempty                          -- evaluation domain is nonempty
  d            : ℕ                                   -- degree bound (e.g. one plus the message polynomial degree)
  code         : Set (L → F)                         -- subset of functions L → F
  constraint   : code = { f | ∃ p : Polynomial F,    -- exactly polynomial evaluations
    p.natDegree < d ∧ ∀ (x : F) (hx : x ∈ L), f ⟨x, hx⟩ = p.eval x }



-- Define a method to compute the code's rate
def ReedSolomonCode.rate {F : Type*} [Field F] (C : ReedSolomonCode F) : ℚ :=
  (C.d : ℚ) / (C.L.card : ℚ)
