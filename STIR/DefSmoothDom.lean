/-
Copyright (c) 2025 ZKLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Fintype.Units
import Mathlib.Data.Fintype.Card

/- Given a smooth domain, we know that there exist a subgroup H and an invertible
   field element a such that L = a • H and moreover that there exists a natural number
   k with L = 2^k -/
def smoothDom
  {F  : Type*} [Field F] [Fintype F] [DecidableEq F]
  (L : Finset F) : Prop :=
    ∃ H : Subgroup (Units F), ∃ a : Units F,
      (L : Set F) = (fun h : Units F ↦ (a : F) * h) '' -- L = a • H for some a and H
                  (H : Set (Units F)) ∧
      ∃ k : ℕ, L.card = 2 ^ k

/- L^k := {x^k | x ∈ L} -/
noncomputable def powDom
  {F  : Type*} [Field F] [Fintype F] [DecidableEq F]
  (L : Finset F)
  (k : ℕ) : Finset F := L.image fun x : F => x ^ k

noncomputable def powFiber
  {F  : Type*} [Field F] [Fintype F] [DecidableEq F]
  (L : Finset F)
  (k : ℕ)
  (x : powDom L k) : Finset F :=
    L.filter (fun y => y ^ k = x)
