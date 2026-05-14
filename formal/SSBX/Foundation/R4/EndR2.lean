/-
# Foundation.R4.EndR2 — `R 4 = End(R 2)`: matrix view, apply, compose

Per `r4.md` v0.2 §8 ("R 4 = End(R 2)"):

`R 4` carries a natural matrix view as `Mat_{2×2}(F_2)`.  Concretely,
the 4 bits `w₀w₁w₂w₃` of `w : R 4` are read row-major as the matrix

    M_w = [[w₀, w₁],
           [w₂, w₃]]

acting on `R 2` by matrix-vector product.  This identifies `R 4`
with `End_{F_2}(R 2) = Mat_{2×2}(F_2)`, the **first** self-closure
of the R-tower into its own endomorphism algebra.

This file delivers:

* `asMatrix`  — `R 4 → (Fin 2 → Fin 2 → Bool)` (row-major 2×2).
* `applyR2`   — `R 4 → R 2 → R 2` (matrix-vector product).
* `composeR2` — `R 4 → R 4 → R 4` (matrix product = composition).
* `idR4`      — `R 4`-element representing identity (= `xoox`).
* Closure of the 6 rank-2 elements under `composeR2` (the GL(2, F_2)
  subgroup structure from `GL2Embedding.lean`).

## Doctrinal anchor

* `r4.md` v0.2 §1.3 (matrix view), §8.1 (R 4 = End(R 2)),
  §8.2 (apply), §8.3 (compose), §8.4 (id and inverses).
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R4.Enumeration
import SSBX.Foundation.R4.RankStratification
import SSBX.Foundation.R4.GL2Embedding

namespace SSBX.Foundation.R4

open SSBX.Foundation.R

/-! ## § 1 The 2×2 matrix view of R 4 -/

/-- Read `w : R 4` as a 2×2 `F_2`-matrix, row-major:

      `asMatrix w i j = w_{2i + j}`. -/
def asMatrix (w : R 4) (i j : Fin 2) : Bool :=
  w ⟨2 * i.val + j.val, by
    have hi := i.isLt
    have hj := j.isLt
    omega⟩

@[simp] theorem asMatrix_00 (w : R 4) :
    asMatrix w ⟨0, by decide⟩ ⟨0, by decide⟩ = w ⟨0, by decide⟩ := rfl

@[simp] theorem asMatrix_01 (w : R 4) :
    asMatrix w ⟨0, by decide⟩ ⟨1, by decide⟩ = w ⟨1, by decide⟩ := rfl

@[simp] theorem asMatrix_10 (w : R 4) :
    asMatrix w ⟨1, by decide⟩ ⟨0, by decide⟩ = w ⟨2, by decide⟩ := rfl

@[simp] theorem asMatrix_11 (w : R 4) :
    asMatrix w ⟨1, by decide⟩ ⟨1, by decide⟩ = w ⟨3, by decide⟩ := rfl

/-! ## § 2 The inverse: `Fin 2 → Fin 2 → Bool` → `R 4` -/

/-- Inverse of `asMatrix`: pack a 2×2 Bool matrix into `R 4`. -/
def ofMatrix (m : Fin 2 → Fin 2 → Bool) : R 4 := fun k =>
  match k.val with
  | 0 => m ⟨0, by decide⟩ ⟨0, by decide⟩
  | 1 => m ⟨0, by decide⟩ ⟨1, by decide⟩
  | 2 => m ⟨1, by decide⟩ ⟨0, by decide⟩
  | _ => m ⟨1, by decide⟩ ⟨1, by decide⟩

/-- `ofMatrix` is a left inverse of `asMatrix`. -/
theorem asMatrix_ofMatrix (m : Fin 2 → Fin 2 → Bool) :
    asMatrix (ofMatrix m) = m := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- `asMatrix` is a left inverse of `ofMatrix`. -/
theorem ofMatrix_asMatrix (w : R 4) :
    ofMatrix (asMatrix w) = w := by
  funext k
  have hk := k.isLt
  match h : k.val with
  | 0 =>
    have hk0 : k = ⟨0, by decide⟩ := Fin.ext h
    rw [hk0]; rfl
  | 1 =>
    have hk1 : k = ⟨1, by decide⟩ := Fin.ext h
    rw [hk1]; rfl
  | 2 =>
    have hk2 : k = ⟨2, by decide⟩ := Fin.ext h
    rw [hk2]; rfl
  | 3 =>
    have hk3 : k = ⟨3, by decide⟩ := Fin.ext h
    rw [hk3]; rfl
  | n + 4 => omega

/-! ## § 3 Apply: matrix-vector product `R 4 × R 2 → R 2`

Per `r4.md §8.2`: `(M_w u)_i = (w_{2i} ∧ u_0) ⊕ (w_{2i+1} ∧ u_1)`. -/

/-- Apply `w : R 4` (as a 2×2 matrix) to a vector `u : R 2`. -/
def applyR2 (w : R 4) (u : R 2) : R 2 := fun i =>
  Bool.xor
    (Bool.and (asMatrix w i ⟨0, by decide⟩) (u ⟨0, by decide⟩))
    (Bool.and (asMatrix w i ⟨1, by decide⟩) (u ⟨1, by decide⟩))

/-! ## § 4 Compose: matrix product `R 4 × R 4 → R 4` -/

/-- Compose two `R 4` elements viewed as 2×2 matrices:
    `(M_g · M_f)_{ij} = (g_{i0} ∧ f_{0j}) ⊕ (g_{i1} ∧ f_{1j})`. -/
def composeR2 (g f : R 4) : R 4 :=
  ofMatrix (fun i j =>
    Bool.xor
      (Bool.and (asMatrix g i ⟨0, by decide⟩) (asMatrix f ⟨0, by decide⟩ j))
      (Bool.and (asMatrix g i ⟨1, by decide⟩) (asMatrix f ⟨1, by decide⟩ j)))

/-! ## § 5 The identity element

Per `r4.md §8.4`: `id = xoox` (the matrix `[[1,0],[0,1]]`). -/

/-- The identity element of `End(R 2) = R 4`. -/
def idR4 : R 4 := xoox

theorem idR4_eq_xoox : idR4 = xoox := rfl

/-! ## § 6 Apply identity = identity -/

theorem applyR2_id (u : R 2) : applyR2 idR4 u = u := by
  funext i
  fin_cases i <;> simp [applyR2, asMatrix, idR4, xoox, mk4]
    <;> (first | rfl | (cases u ⟨0, by decide⟩ <;> cases u ⟨1, by decide⟩ <;> rfl))

/-! ## § 7 Concrete composition examples

Per `r4.md §8.3`: `compose oxxo xxox = oxxx`. -/

example : composeR2 oxxo xxox = oxxx := by decide

/-- Identity is a left identity for composition. -/
theorem composeR2_id_left (f : R 4) : composeR2 idR4 f = f := by
  show ofMatrix _ = f
  rw [← ofMatrix_asMatrix f]
  congr 1
  funext i j
  fin_cases i <;> fin_cases j <;>
    (simp [idR4, xoox, mk4, asMatrix] <;>
     (first | rfl | (cases asMatrix f ⟨0, by decide⟩ j <;>
                      cases asMatrix f ⟨1, by decide⟩ j <;> rfl)))

/-- Identity is a right identity for composition. -/
theorem composeR2_id_right (f : R 4) : composeR2 f idR4 = f := by
  show ofMatrix _ = f
  rw [← ofMatrix_asMatrix f]
  congr 1
  funext i j
  fin_cases i <;> fin_cases j <;>
    (simp [idR4, xoox, mk4, asMatrix] <;>
     (first | rfl | (cases asMatrix f i ⟨0, by decide⟩ <;>
                      cases asMatrix f i ⟨1, by decide⟩ <;> rfl)))

/-! ## § 8 Closure of the 6 rank-2 elements under composition

The set `{xoox, oxxo, xxox, xoxx, oxxx, xxxo}` (= `gl2List`) is closed
under `composeR2`.  We verify a few representative products by
`decide`; the full 36-entry table is implicit. -/

example : composeR2 oxxx oxxx = xxxo := by decide  -- rot₊ ∘ rot₊ = rot₋
example : composeR2 xxxo xxxo = oxxx := by decide  -- rot₋ ∘ rot₋ = rot₊
example : composeR2 oxxx xxxo = xoox := by decide  -- rot₊ ∘ rot₋ = id
example : composeR2 oxxo oxxo = xoox := by decide  -- swap² = id
example : composeR2 xxox xxox = xoox := by decide  -- shear₁² = id
example : composeR2 xoxx xoxx = xoox := by decide  -- shear₂² = id

/-- The GL(2, F_2) subgroup is closed under `composeR2`: for any two
    rank-2 elements, their product is also rank-2.  -/
theorem gl2_closure_under_compose :
    ∀ g ∈ gl2List, ∀ f ∈ gl2List, IsRank2 (composeR2 g f) := by
  decide

/-! ## § 9 The 16 = 2^4 = |Mat_{2×2}(F_2)| cardinality match

`R 4` viewed as `Mat_{2×2}(F_2)` has exactly 16 elements; the matrix
view `asMatrix : R 4 ≃ (Fin 2 → Fin 2 → Bool)` is the explicit
bijection. -/

/-- The matrix view bijection. -/
def matrixEquiv : R 4 ≃ (Fin 2 → Fin 2 → Bool) where
  toFun := asMatrix
  invFun := ofMatrix
  left_inv := ofMatrix_asMatrix
  right_inv := asMatrix_ofMatrix

/-- `|R 4| = |Mat_{2×2}(F_2)| = 16`. -/
theorem card_matrix_view :
    Fintype.card (R 4) = Fintype.card (Fin 2 → Fin 2 → Bool) := by
  exact Fintype.card_congr matrixEquiv

end SSBX.Foundation.R4
