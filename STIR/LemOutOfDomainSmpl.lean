import STIR.DefReedSolomonCodes

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Fintype.Basic


-- Formalizing the lemma statement about random samples for list decoding of Reed-Solomon codes.
noncomputable def listDecodingCollisionProbability
  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  (C : ReedSolomonCode F)
  (δ : ℝ)
  (s : ℕ)
  (h_nonempty : Nonempty C.domainComplement) : ENNReal :=
  (PMF.uniformOfFintype (Fin s → (C.domainComplement))).toOuterMeasure {r |
    ∃ u ∈ C.code, ∃ u' ∈ C.code,
      u ≠ u' ∧ u ∈ C.List u δ ∧ u' ∈ C.List u δ ∧
      ∀ i : Fin s, (r i).val  = (r i).val} -- TODO: We need the RSC polynomial

      -- TODO: ∀ i : Fin s, Polynomial.eval (r i).val u = Polynomial.eval (r i).val u'
      ---         requires to get the assiciated polynomial of a ReedSolomon code

lemma outOfDomainSmpl_1
  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  (C : ReedSolomonCode F)
  (δ : ℝ)
  (l s : ℕ)
  (h_decodable : C.listDecodable δ l) :
  listDecodingCollisionProbability C δ s C.domainComplementNonempty ≤
    (l.choose 2) * ((C.d - 1) / (Fintype.card F - C.L.card))^s := by sorry

lemma outOfDomainSmpl_2
  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  (C : ReedSolomonCode F)
  (δ : ℝ)
  (l s : ℕ)
  (h_decodable : C.listDecodable δ l) :
  listDecodingCollisionProbability C δ s C.domainComplementNonempty ≤
    (l^2 / 2) * (C.d / (Fintype.card F - C.L.card))^s := by sorry
