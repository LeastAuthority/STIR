import STIR.ReedSolomonCodes
import STIR.FracHammingDist

/-- Structure encapsulating a list of Reed-Solomon codewords close to a given function `f`. -/
structure ListCode (F : Type*) [Field F] [Fintype F] [DecidableEq F] (C : ReedSolomonCode F) where
  f : C.L → F
  δ : ℚ
  codewords : Finset (C.L → F)
  codewords_def : codewords = { c ∈ C.code | fractionalHammingDist f c ≤ δ }



namespace ListCode

/-- The Reed-Solomon code `C` is `(δ, d)`-list decodable if for every function `f`, the list of codewords within fractional distance `δ` from `f` is strictly smaller than the size of the evaluation domain. -/
def isListDecodable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {C : ReedSolomonCode F} (δ : ℚ) : Prop :=
  ∀ f : C.L → F, (ListCode.mk f δ { c ∈ C.code | fractionalHammingDist f c ≤ δ } rfl).codewords.card < C.L.card

end ListCode
