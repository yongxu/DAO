/-
# Foundation.R.DirectSum — `R N ⊕ R M ≃ R (N + M)`

Per `wen-algebra` v0.6 §2.1 and `v4-foundation` v0.5 §11.1:

    R N ⊕ R M  ≅  R (N + M)

is the natural direct-sum isomorphism witnessed via `Fin.append`.

This file delivers:

* `R.append` / `R.takeLeft` / `R.takeRight` — concat / split functions.
* `R.directSumEquiv` — the full `Equiv` `R (N + M) ≃ R N × R M`.
* Cardinality theorem `|R (N + M)| = |R N| * |R M|`.
* The append respects the `AddCommGroup` structure (component-wise).
-/

import SSBX.Foundation.R.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Basic

namespace SSBX.Foundation.R

namespace R

/-! ## § 1 Concatenation / splitting -/

/-- Concatenate `u : R N` and `v : R M` to form `R (N + M)`: indices
    `0..N-1` come from `u`; indices `N..N+M-1` come from `v`. -/
def append {N M : ℕ} (u : R N) (v : R M) : R (N + M) :=
  Fin.append u v

/-- First `N` coordinates of an `R (N + M)` vector. -/
def takeLeft {N M : ℕ} (w : R (N + M)) : R N :=
  fun i => w (Fin.castAdd M i)

/-- Last `M` coordinates of an `R (N + M)` vector. -/
def takeRight {N M : ℕ} (w : R (N + M)) : R M :=
  fun j => w (Fin.natAdd N j)

@[simp] theorem takeLeft_apply {N M : ℕ} (w : R (N + M)) (i : Fin N) :
    takeLeft w i = w (Fin.castAdd M i) := rfl

@[simp] theorem takeRight_apply {N M : ℕ} (w : R (N + M)) (j : Fin M) :
    takeRight w j = w (Fin.natAdd N j) := rfl

@[simp] theorem takeLeft_append {N M : ℕ} (u : R N) (v : R M) :
    takeLeft (append u v) = u := by
  funext i
  simp [takeLeft, append, Fin.append_left]

@[simp] theorem takeRight_append {N M : ℕ} (u : R N) (v : R M) :
    takeRight (append u v) = v := by
  funext j
  simp [takeRight, append, Fin.append_right]

theorem append_takeLeft_takeRight {N M : ℕ} (w : R (N + M)) :
    append (takeLeft w) (takeRight w) = w := by
  funext i
  refine Fin.addCases (motive := fun j =>
    append (takeLeft w) (takeRight w) j = w j) ?_ ?_ i
  · intro k
    simp [append, takeLeft, Fin.append_left]
  · intro k
    simp [append, takeRight, Fin.append_right]

/-! ## § 2 The direct-sum equivalence -/

/-- The direct-sum equivalence `R (N + M) ≃ R N × R M`.

    Per `wen-algebra` v0.6 §2.1: this is the natural realization of
    `R_N ⊕ R_M ≅ R_{N+M}`. -/
def directSumEquiv {N M : ℕ} : R (N + M) ≃ R N × R M where
  toFun w := (takeLeft w, takeRight w)
  invFun p := append p.1 p.2
  left_inv := append_takeLeft_takeRight
  right_inv := by
    intro p
    cases p
    apply Prod.ext <;> simp

@[simp] theorem directSumEquiv_apply {N M : ℕ} (w : R (N + M)) :
    directSumEquiv w = (takeLeft w, takeRight w) := rfl

@[simp] theorem directSumEquiv_symm_apply {N M : ℕ} (p : R N × R M) :
    directSumEquiv.symm p = append p.1 p.2 := rfl

/-! ## § 3 Cardinality of the direct sum -/

/-- |R (N + M)| = |R N| * |R M|.  Per `wen-algebra` v0.6 §2.1. -/
theorem card_directSum (N M : ℕ) :
    Fintype.card (R (N + M)) = Fintype.card (R N) * Fintype.card (R M) := by
  rw [Fintype.card_congr (directSumEquiv (N := N) (M := M)),
      Fintype.card_prod]

/-- |R (N + M)| = 2^N * 2^M = 2^(N + M). -/
theorem card_directSum_pow (N M : ℕ) :
    Fintype.card (R (N + M)) = 2 ^ N * 2 ^ M := by
  rw [card_directSum, card_eq, card_eq]

/-! ## § 4 Compatibility with the additive group structure

`append` is additive: appending the XOR sums equals XORing the
appended vectors. -/

theorem append_add {N M : ℕ} (u₁ u₂ : R N) (v₁ v₂ : R M) :
    append (u₁ + u₂) (v₁ + v₂) = append u₁ v₁ + append u₂ v₂ := by
  funext i
  refine Fin.addCases (motive := fun j =>
    append (u₁ + u₂) (v₁ + v₂) j
      = Bool.xor (append u₁ v₁ j) (append u₂ v₂ j)) ?_ ?_ i
  · intro k
    show (Fin.append (u₁ + u₂) (v₁ + v₂)) (Fin.castAdd M k)
        = Bool.xor ((Fin.append u₁ v₁) (Fin.castAdd M k))
                   ((Fin.append u₂ v₂) (Fin.castAdd M k))
    simp [Fin.append_left]
  · intro k
    show (Fin.append (u₁ + u₂) (v₁ + v₂)) (Fin.natAdd N k)
        = Bool.xor ((Fin.append u₁ v₁) (Fin.natAdd N k))
                   ((Fin.append u₂ v₂) (Fin.natAdd N k))
    simp [Fin.append_right]

theorem append_zero {N M : ℕ} :
    append (0 : R N) (0 : R M) = (0 : R (N + M)) := by
  funext i
  refine Fin.addCases (motive := fun j =>
    append (0 : R N) (0 : R M) j = (0 : R (N + M)) j) ?_ ?_ i
  · intro k
    show (Fin.append (0 : R N) (0 : R M)) (Fin.castAdd M k) = false
    simp [Fin.append_left]
  · intro k
    show (Fin.append (0 : R N) (0 : R M)) (Fin.natAdd N k) = false
    simp [Fin.append_right]

end R

end SSBX.Foundation.R
