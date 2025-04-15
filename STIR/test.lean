import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Finset.Basic
import Mathlib.LinearAlgebra.Lagrange

/- MEASURE SPACE MINIMAL EXAMPLE-/

theorem examle_multi_samples  (F : Type) [Field F] [Fintype F] [Nonempty F] (m : ℕ ): (PMF.uniformOfFintype (Fin m → F)).toOuterMeasure {x | (Finset.univ.sum x) = 1} = 1/(Fintype.card F) := by sorry

open Finset

theorem example_multi_samples_subset
  (F : Type) [Field F] [Fintype F] [Nonempty F]
  (L : Set F) [DecidablePred (· ∈ L)]
  (hL : Set.Nonempty (Set.univ \ L))
  [Nonempty {x // x ∉ L}]
  (m : ℕ) :
  (PMF.uniformOfFintype (Fin m → { x // x ∉ L })).toOuterMeasure
    { x | (Finset.univ.sum (fun i ↦ (x i : F))) = 1 }
  = 1 / ((Fintype.card { x // x ∉ L }) ^ m) := by sorry


/- LAGRANGE INTERPOLATION MINIMAL EXAMPLE-/
noncomputable def interpolate {F : Type _} [Field F] [Fintype F] [DecidableEq F]
  (L : Finset F) (f : ↥L → F) : Polynomial F :=
  let nodes : Finset ↥L := L.attach  -- attach gives Finset of subtype {x // x ∈ L}
  -- Define the node mapping (subtype to actual field element) and the value function:
  let v : ↥L → F := fun i => (i : F)        -- project subtype i to the element in F
  let r : ↥L → F := fun i => f i            -- value at node i (i is already in ↥L)
  Lagrange.interpolate nodes v r
