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

noncomputable def Combine1
(F : Type*) [Field F] [Fintype F] [DecidableEq F]
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
  let ri := if i.val = 1 then (1 : F)
            else r ^ (i.val - 1 + (Finset.univ.filter (· < i)).sum fun j => dstar - degs j)
  let geom := (Finset.range (dstar - di + 1)).sum fun l => (r * x.val) ^ l
  ri * fs i x * geom

noncomputable def Combine2
(F : Type*) [Field F] [Fintype F] [DecidableEq F]
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
    let ri := if i.val = 1 then (1 : F)
              else r^((i.val - 1) + (Finset.univ.filter fun j => j.val < i.val).sum fun j => dstar - degs j)
    let geom := if q = 1 then (dstar - di + 1 : F)
                else (1 - q^(dstar - di + 1)) / (1 - q)
    ri * fs i x * geom

noncomputable def DegreeCorr1
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

noncomputable def DegreeCorr2
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
