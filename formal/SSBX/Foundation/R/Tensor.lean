/-
# Foundation.R.Tensor — `R N ⊗_F₂ R M ≃ R (N * M)`

Per `wen-algebra` v0.6 §2.2 and `v4-foundation` v0.5 §11.2:

    R N ⊗_F₂ R M  ≅  R (N * M)

(dimension multiplies; cardinality is `2^(N*M)`).  The tensor product
over `F_2` of two `F_2`-vector spaces of dimensions `N` and `M` is an
`F_2`-vector space of dimension `N * M`.  We realize this via the
natural pair-indexing `Fin N × Fin M ≃ Fin (N * M)`.

NOTE: This file does **not** construct the universal tensor product
(which would require Mathlib's heavy `TensorProduct` machinery over
`ZMod 2`).  Instead, it gives the **standard pair-indexed tensor
view**: a function `pair : R N → R M → R (N * M)` that on basis vectors
realizes the `e_i ⊗ e_j ↔ e_{(i,j)}` correspondence, and the
cardinality equivalence `R (N * M) ≃ (Fin N × Fin M → Bool)`.

This is sufficient for the doctrine-level closure statement; full
universal-property tensor lives in `Foundation/R8/MathlibInstances.lean`
if/when needed (P2/P4 work).
-/

import SSBX.Foundation.R.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic

namespace SSBX.Foundation.R

namespace R

/-! ## § 1 The pair-indexed tensor view

Identify `R (N * M)` with `Fin N × Fin M → Bool` via the standard
`Fin.divNat / Fin.modNat` decomposition. -/

/-- `Fin (N * M) ≃ Fin M × Fin N` (Mathlib `finProdFinEquiv`-style;
    we provide an explicit version to control argument order so that
    `(i, j)` maps to row-major). -/
def finPairEquiv (N M : ℕ) : Fin (N * M) ≃ Fin N × Fin M :=
  (finProdFinEquiv (m := N) (n := M)).symm.trans (Equiv.refl _)

/-- The tensor product view: `R (N * M) ≃ (Fin N × Fin M → Bool)`. -/
def tensorViewEquiv (N M : ℕ) : R (N * M) ≃ (Fin N × Fin M → Bool) where
  toFun w := fun p => w ((finPairEquiv N M).symm p)
  invFun f := fun k => f (finPairEquiv N M k)
  left_inv w := by
    funext k
    simp
  right_inv f := by
    funext p
    simp

/-! ## § 2 Cardinality

`|R (N * M)| = |R N| * |R M|` in the *tensor* sense as
`(F_2)^N ⊗ (F_2)^M` having dimension `N * M`.  Note this is the
same numerical value as `|R N + M| = |R N| * |R M|` (direct sum) only
when one side is the zero space — the tensor *cardinality* is
`2^(N * M)` whereas the direct-sum cardinality is `2^(N + M)`.

Per `wen-algebra` v0.6 §2.6 the key distinction:

* direct sum: `|R N ⊕ R M| = 2^(N + M)`     (dimension adds)
* tensor:    `|R N ⊗ R M| = 2^(N * M)`     (dimension multiplies)

The squaring tower uses **direct sum** for cardinality doubling, NOT
tensor (which would give `R_{N²}` — much bigger). -/

theorem card_tensor (N M : ℕ) :
    Fintype.card (R (N * M)) = 2 ^ (N * M) := card_eq _

/-! ## § 3 The bilinear "pair" map

Given `u : R N` and `v : R M`, the bilinear tensor pair sends them to
the `R (N * M)` vector whose `(i, j)` coordinate is `u i ∧ v j`. -/

/-- The bilinear tensor pair: `(u ⊗ v)_{(i, j)} := u_i ∧ v_j`. -/
def pair {N M : ℕ} (u : R N) (v : R M) : R (N * M) :=
  fun k =>
    let p := finPairEquiv N M k
    Bool.and (u p.1) (v p.2)

@[simp] theorem pair_apply {N M : ℕ} (u : R N) (v : R M) (k : Fin (N * M)) :
    pair u v k = Bool.and (u (finPairEquiv N M k).1) (v (finPairEquiv N M k).2) := rfl

/-! ## § 4 Bilinearity at the F_2 level

`pair (u₁ + u₂) v = pair u₁ v + pair u₂ v` and similarly on the right;
both follow from `Bool.and` distributing over `Bool.xor`. -/

private theorem and_xor_left (a b c : Bool) :
    Bool.and (Bool.xor a b) c = Bool.xor (Bool.and a c) (Bool.and b c) := by
  cases a <;> cases b <;> cases c <;> rfl

private theorem and_xor_right (a b c : Bool) :
    Bool.and a (Bool.xor b c) = Bool.xor (Bool.and a b) (Bool.and a c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem pair_add_left {N M : ℕ} (u₁ u₂ : R N) (v : R M) :
    pair (u₁ + u₂) v = pair u₁ v + pair u₂ v := by
  funext k
  show Bool.and (Bool.xor _ _) _ = Bool.xor (Bool.and _ _) (Bool.and _ _)
  exact and_xor_left _ _ _

theorem pair_add_right {N M : ℕ} (u : R N) (v₁ v₂ : R M) :
    pair u (v₁ + v₂) = pair u v₁ + pair u v₂ := by
  funext k
  show Bool.and _ (Bool.xor _ _) = Bool.xor (Bool.and _ _) (Bool.and _ _)
  exact and_xor_right _ _ _

theorem pair_zero_left {N M : ℕ} (v : R M) :
    pair (0 : R N) v = (0 : R (N * M)) := by
  funext k
  show Bool.and ((0 : R N) (finPairEquiv N M k).1) (v (finPairEquiv N M k).2) = false
  rfl

theorem pair_zero_right {N M : ℕ} (u : R N) :
    pair u (0 : R M) = (0 : R (N * M)) := by
  funext k
  show Bool.and (u (finPairEquiv N M k).1) ((0 : R M) (finPairEquiv N M k).2) = false
  cases u (finPairEquiv N M k).1 <;> rfl

end R

end SSBX.Foundation.R
