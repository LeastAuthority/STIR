import Mathlib.Data.Finset.Basic
import Mathlib.FieldTheory.Finite.Basic

namespace combine
/--
Given

 F //a finite field with decidable equality,
 L : Finset F //a finite subset of F,
 dstar : ℕ //a target degree,
 r : F //a shift parameter,
 fs : Fin m → L → F //a family of functions, and
 degs : Fin m → ℕ //a corresponding family of degrees with each degs i ≤ dstar,

we define combine L dstar r fs degs: L → F
as follows
--/
noncomputable def ri
  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {m : ℕ}     [Fintype (Fin m)]
  (dstar : ℕ) (r : F) (degs : Fin m → ℕ)
  (i : Fin m) : F :=
    if i.val - 1 = 0 then (1:F)
    else r^(i.val - 1 + (Finset.univ.filter (· < i)).sum fun j => dstar - degs j)

noncomputable def CombineInterm
{F : Type*} [Field F] [Fintype F] [DecidableEq F]
(m : ℕ) [Fintype (Fin m)]
(L : Finset F)
(dstar : ℕ)
(r : F)
(fs : Fin m → L → F)
(degs : Fin m → ℕ) :
L → F :=
fun x =>
  (Finset.univ : Finset (Fin m)).sum
  fun i =>
  let di := degs i
  let geom := (Finset.range (dstar - di + 1)).sum fun l => (r * x.val)^l
  ri dstar r degs i * fs i x * geom

noncomputable def CombineFinal
{F : Type*} [Field F] [Fintype F] [DecidableEq F]
(m : ℕ) [Fintype (Fin m)]
(L : Finset F)
(dstar : ℕ)
(r : F)
(fs : Fin m → L → F)
(degs : Fin m → ℕ) :
L → F :=
fun x =>
  let q := r * x.val
  (Finset.univ : Finset (Fin m)).sum fun i =>
  let di := degs i
  let geom := if q = 1 then (dstar - di + 1 : F)
              else (1 - q^(dstar - di + 1)) / (1 - q)
  ri dstar r degs i * fs i x * geom

noncomputable def DegreeCorrInterm
(F : Type*) [Field F] [Fintype F] [DecidableEq F]
(L : Finset F)
(dstar : ℕ) (r : F)
(f : L → F)
(d : ℕ) (hd : d ≤ dstar) :
L → F :=
fun x =>
  let geom := (Finset.range (dstar - d + 1)).sum fun l =>
    (r * x.val) ^ l
  f x * geom

noncomputable def DegreeCorrFinal
(F : Type*) [Field F] [Fintype F] [DecidableEq F]
(L : Finset F)
(dstar : ℕ) (r : F)
(f : L → F)
(d : ℕ) (hd : d ≤ dstar) : L → F :=
fun x =>
  let q := r * x.val
  let exp := dstar - d + 1
  let geom := if q = 1 then (dstar - d + 1 : F)
              else (1 - q ^ exp) / (1 - q)
f x * geom

end combine
