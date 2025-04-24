/-
Copyright (c) 2025 ZKLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import STIR.DefReedSolomonCodes

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Fintype.Basic

/- Prob-/
noncomputable def listDecodingCollisionProbability
  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {L : Finset F}
  {d : ℕ}
  (C : ReedSolomonCode F L d)
  (δ : ℝ)
  (s : ℕ)
  (h_nonempty : Nonempty C.domainComplement) : ENNReal :=
  (PMF.uniformOfFintype (Fin s → C.domainComplement)).toOuterMeasure { r |
    ∃ (u u' : ↥C.code),
      u.val ≠ u'.val ∧
      -- both u and u' lie within δ of some target f
      u.val ∈ C.List u.val δ ∧
      u'.val ∈ C.List u.val δ ∧
      -- their interpolating polynomials agree on each sampled r_i
      ∀ i : Fin s,
        (C.poly u).eval (r i).val = (C.poly u').eval (r i).val
  }

lemma outOfDomainSmpl_1
  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {L : Finset F}
  {d : ℕ}
  (C : ReedSolomonCode F L d)
  (δ : ℝ)
  (l s : ℕ)
  (h_decodable : C.listDecodable δ l) :
  listDecodingCollisionProbability C δ s C.domainComplementNonempty ≤
    (l.choose 2) * ((d - 1) / (Fintype.card F - L.card))^s := by sorry

lemma outOfDomainSmpl_2
  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {L : Finset F}
  {d : ℕ}
  (C : ReedSolomonCode F L d)
  (δ : ℝ)
  (l s : ℕ)
  (h_decodable : C.listDecodable δ l) :
  listDecodingCollisionProbability C δ s C.domainComplementNonempty ≤
    (l^2 / 2) * (d / (Fintype.card F - L.card))^s := by sorry
