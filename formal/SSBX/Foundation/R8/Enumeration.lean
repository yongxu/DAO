/-
# Foundation.R8.Enumeration — 256-element handles

Per `r8.md` v0.2 §3, `R 8` has 256 elements; we don't list them
exhaustively, but provide handles for the key elements and helpers:

* The origin `zero8` (= `0 : R 8`).
* The all-ones element `ones8` (= `R.constx 8`).
* The 8 basis vectors `e_0, …, e_7`.
* A Hamming-weight function and its weight-class structure.
* The 16-element {oo, xx}^4 diagonal sub-tower.

Per `r8.md` §3.2, the weight distribution is `1+8+28+56+70+56+28+8+1 = 256`.

## Doctrinal anchor

* `r8.md` v0.2 §3.1 (key elements), §3.2 (weight distribution), §3.3
  ({oo, xx}^4 sub-tower in R 8).
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.SubTower
import Mathlib.Data.Fintype.Card

namespace SSBX.Foundation.R8

open SSBX.Foundation.R

/-! ## § 1 Distinguished elements -/

/-- The origin (zero vector) of `R 8`. -/
def zero8 : R 8 := (0 : R 8)

/-- The all-ones element of `R 8`. -/
def ones8 : R 8 := R.constx 8

@[simp] theorem zero8_apply (i : Fin 8) : zero8 i = false := rfl

@[simp] theorem ones8_apply (i : Fin 8) : ones8 i = true := rfl

/-- `zero8 + ones8 = ones8`. -/
theorem zero8_add_ones8 : zero8 + ones8 = ones8 := by
  funext i; show Bool.xor false true = true; rfl

/-- `ones8 + ones8 = zero8` (self-cancellation in char 2). -/
theorem ones8_add_ones8 : ones8 + ones8 = zero8 := by
  apply R.add_self

/-! ## § 2 The 8 basis vectors -/

/-- The `i`-th basis vector of `R 8`. -/
def basis8 (i : Fin 8) : R 8 := R.basis i

@[simp] theorem basis8_self (i : Fin 8) : basis8 i i = true := R.basis_self i

theorem basis8_other {i j : Fin 8} (h : i ≠ j) : basis8 i j = false :=
  R.basis_other h

/-! ## § 3 Hamming weight -/

/-- The Hamming weight of `w : R 8`: the number of coordinates that are
    `true`. -/
def hammingWeight (w : R 8) : ℕ :=
  Finset.univ.filter (fun i : Fin 8 => w i = true) |>.card

@[simp] theorem hammingWeight_zero : hammingWeight zero8 = 0 := by
  unfold hammingWeight
  apply Finset.card_eq_zero.mpr
  ext i; simp [zero8]

@[simp] theorem hammingWeight_ones : hammingWeight ones8 = 8 := by
  unfold hammingWeight
  have : (Finset.univ : Finset (Fin 8)).filter (fun i => ones8 i = true)
        = Finset.univ := by
    ext i; simp [ones8, R.constx_apply]
  rw [this]; rfl

theorem hammingWeight_le_8 (w : R 8) : hammingWeight w ≤ 8 := by
  unfold hammingWeight
  calc (Finset.univ.filter (fun i : Fin 8 => w i = true)).card
      ≤ (Finset.univ : Finset (Fin 8)).card := Finset.card_filter_le _ _
    _ = 8 := by rfl

/-! ## § 4 Basis vector weight = 1 -/

theorem hammingWeight_basis (i : Fin 8) : hammingWeight (basis8 i) = 1 := by
  unfold hammingWeight basis8
  have : (Finset.univ : Finset (Fin 8)).filter (fun j => R.basis i j = true) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hj
      by_contra hne
      rw [R.basis_other (fun h => hne h.symm)] at hj
      exact Bool.false_ne_true hj
    · rintro rfl; exact R.basis_self j
  rw [this]; rfl

/-! ## § 5 The 16-element diagonal sub-tower {oo, xx}^4 -/

/-- The predicate "every 2-block has both coordinates equal" specialised
    to `R 8 = R (2 * 4)`.  This is the 16-element {oo, xx}⁴ sub-tower
    of `r8.md` §3.3. -/
def inDiagonalSubTower (w : R 8) : Prop :=
  ∀ k : Fin 4, w ⟨2 * k.val, by have := k.isLt; omega⟩
             = w ⟨2 * k.val + 1, by have := k.isLt; omega⟩

instance instDecidableInDiagonalSubTower (w : R 8) :
    Decidable (inDiagonalSubTower w) := by
  unfold inDiagonalSubTower
  exact Fintype.decidableForallFintype

/-- `zero8` is in the diagonal sub-tower. -/
theorem zero8_inDiagonalSubTower : inDiagonalSubTower zero8 := by
  intro k; rfl

/-- `ones8` is in the diagonal sub-tower. -/
theorem ones8_inDiagonalSubTower : inDiagonalSubTower ones8 := by
  intro k; rfl

/-! ## § 6 Cardinality of R 8 -/

theorem R8_card : Fintype.card (R 8) = 256 := R.R8_card

end SSBX.Foundation.R8
