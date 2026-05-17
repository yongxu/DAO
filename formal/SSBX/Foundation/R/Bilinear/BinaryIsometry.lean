/-
# Foundation.R.Bilinear.BinaryIsometry — explicit 2×2 isometry
  `⟨a, b⟩ ≃ ⟨1, a·b⟩` over `ZMod p` (odd prime `p`)

This file lifts the algebraic identities of
`Foundation/R/Bilinear/TwoSquareIdentity.lean` to a structural
`QuadraticMap.IsometryEquiv` witnessing the binary diagonal
redistribution

    ⟨a, b⟩  ≅  ⟨1, a·b⟩    (as quadratic forms on `Fin 2 → ZMod p`)

The explicit 2×2 matrix is

       M = [[α, -a·b·γ/a],
            [γ,      α/a]]

with `det M = (α² + a·b·γ²)/a = a/a = 1` whenever
`α² + a·b·γ² = a` (which `R.binary_2sq_exists_alpha_gamma` provides
for `a, b ∈ (ZMod p)*`).

The isometry preserves the quadratic form because of the polynomial
identity (cf. `R.binary_redistribute_quadratic_identity`):

       1·(α x − b γ y)² + a·b·(γ x + (α/a) y)² = a x² + b y².

## Provides

* `R.binaryRedistributeMatrix a b α γ` — the 2×2 matrix (4 entries
  in canonical form).
* `R.binaryRedistributeLinearEquiv a b α γ ha hαγ` — the underlying
  `LinearEquiv` of `(Fin 2 → ZMod p)` (invertible because `det M = 1`).
* `R.diag_quadratic_form a b` — `weightedSumSquares (ZMod p) ![a, b]`.
* `R.binaryIsometryRedistribute a b ha hb` — the main
  `QuadraticMap.IsometryEquiv` between `⟨a, b⟩` and `⟨1, a·b⟩`.

## Doctrinal anchor

* `docs-next/10_formal_形式/gut-roadmap.md` G11 (T5-B parametric over k).
* `Foundation/R/Bilinear/DiscriminantCharNeq2.lean` § 6
  (`classification_finite_fields_uniqueness` — this file provides the
  2×2 bridge ready for `Fin N` induction).
* `Foundation/R/Bilinear/TwoSquareIdentity.lean` — algebraic substrate.
-/

import SSBX.Foundation.R.Bilinear.TwoSquareIdentity
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Isometry
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation

namespace SSBX.Foundation.R

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace R

variable {p : ℕ} [hp : Fact (Nat.Prime p)] [hp2 : Fact (p ≠ 2)]

/-! ## § 1 The explicit 2×2 redistribution matrix -/

/-- The explicit 2×2 isometry matrix realising `⟨a, b⟩ → ⟨1, a·b⟩`:

       M = [[α,  -a·b·γ/a],
            [γ,       α/a]].

  Determinant `α·(α/a) - (-a·b·γ/a)·γ = (α² + a·b·γ²)/a`, which equals
  `1` precisely when `α² + a·b·γ² = a`. -/
def binaryRedistributeMatrix (a b α γ : ZMod p) :
    Matrix (Fin 2) (Fin 2) (ZMod p) :=
  ![![α, -a * b * γ / a], ![γ, α / a]]

@[simp] lemma binaryRedistributeMatrix_apply_zero_zero (a b α γ : ZMod p) :
    binaryRedistributeMatrix a b α γ 0 0 = α := rfl

@[simp] lemma binaryRedistributeMatrix_apply_zero_one (a b α γ : ZMod p) :
    binaryRedistributeMatrix a b α γ 0 1 = -a * b * γ / a := rfl

@[simp] lemma binaryRedistributeMatrix_apply_one_zero (a b α γ : ZMod p) :
    binaryRedistributeMatrix a b α γ 1 0 = γ := rfl

@[simp] lemma binaryRedistributeMatrix_apply_one_one (a b α γ : ZMod p) :
    binaryRedistributeMatrix a b α γ 1 1 = α / a := rfl

/-! ## § 2 The forward / inverse linear maps -/

/-- The forward map `(x, y) ↦ (α·x − b·γ·y, γ·x + (α/a)·y)`
    (using `a·b·γ/a = b·γ` for `a ≠ 0`). -/
def binaryRedistributeFwd (a b α γ : ZMod p) (v : Fin 2 → ZMod p) :
    Fin 2 → ZMod p :=
  ![α * v 0 - b * γ * v 1, γ * v 0 + (α / a) * v 1]

/-- The inverse map `(u, v) ↦ ((α/a)·u + b·γ·v, -γ·u + α·v)`.

    This is `M⁻¹` for `M` of determinant 1, i.e.
    `M⁻¹ = [[α/a, b·γ], [-γ, α]]`. -/
def binaryRedistributeInv (a b α γ : ZMod p) (v : Fin 2 → ZMod p) :
    Fin 2 → ZMod p :=
  ![(α / a) * v 0 + b * γ * v 1, -γ * v 0 + α * v 1]

@[simp] lemma binaryRedistributeFwd_zero (a b α γ : ZMod p) (v : Fin 2 → ZMod p) :
    binaryRedistributeFwd a b α γ v 0 = α * v 0 - b * γ * v 1 := rfl

@[simp] lemma binaryRedistributeFwd_one (a b α γ : ZMod p) (v : Fin 2 → ZMod p) :
    binaryRedistributeFwd a b α γ v 1 = γ * v 0 + (α / a) * v 1 := rfl

@[simp] lemma binaryRedistributeInv_zero (a b α γ : ZMod p) (v : Fin 2 → ZMod p) :
    binaryRedistributeInv a b α γ v 0 = (α / a) * v 0 + b * γ * v 1 := rfl

@[simp] lemma binaryRedistributeInv_one (a b α γ : ZMod p) (v : Fin 2 → ZMod p) :
    binaryRedistributeInv a b α γ v 1 = -γ * v 0 + α * v 1 := rfl

/-! ## § 3 The LinearEquiv

    Invertibility follows from `det M = 1`, equivalently from the
    pointwise identities `inv ∘ fwd = id` and `fwd ∘ inv = id`, which
    reduce via `field_simp` + `ring` to the hypothesis
    `α² + a·b·γ² = a`. -/

/-- The redistribution `LinearEquiv`, built directly from the forward
    and inverse maps.  Invertibility is verified pointwise via
    `α² + a·b·γ² = a` (the 2-square hypothesis from
    `binary_2sq_exists_alpha_gamma`). -/
def binaryRedistributeLinearEquiv (a b α γ : ZMod p) (ha : a ≠ 0)
    (hαγ : α ^ 2 + a * b * γ ^ 2 = a) :
    (Fin 2 → ZMod p) ≃ₗ[ZMod p] (Fin 2 → ZMod p) where
  toFun  := binaryRedistributeFwd a b α γ
  invFun := binaryRedistributeInv a b α γ
  map_add' u v := by
    funext i
    fin_cases i
    · show binaryRedistributeFwd a b α γ (u + v) 0
            = binaryRedistributeFwd a b α γ u 0 + binaryRedistributeFwd a b α γ v 0
      simp only [binaryRedistributeFwd_zero, Pi.add_apply]; ring
    · show binaryRedistributeFwd a b α γ (u + v) 1
            = binaryRedistributeFwd a b α γ u 1 + binaryRedistributeFwd a b α γ v 1
      simp only [binaryRedistributeFwd_one, Pi.add_apply]; ring
  map_smul' r v := by
    funext i
    fin_cases i
    · show binaryRedistributeFwd a b α γ (r • v) 0 = r * binaryRedistributeFwd a b α γ v 0
      simp only [binaryRedistributeFwd_zero, Pi.smul_apply, smul_eq_mul]; ring
    · show binaryRedistributeFwd a b α γ (r • v) 1 = r * binaryRedistributeFwd a b α γ v 1
      simp only [binaryRedistributeFwd_one, Pi.smul_apply, smul_eq_mul]; ring
  left_inv v := by
    funext i
    fin_cases i
    · show binaryRedistributeInv a b α γ (binaryRedistributeFwd a b α γ v) 0 = v 0
      simp only [binaryRedistributeInv_zero, binaryRedistributeFwd_zero,
        binaryRedistributeFwd_one]
      -- Goal: (α/a)·(α·v0 - b·γ·v1) + b·γ·(γ·v0 + (α/a)·v1) = v 0
      have key : (α / a) * (α * v 0 - b * γ * v 1)
                  + b * γ * (γ * v 0 + (α / a) * v 1)
                = ((α ^ 2 + a * b * γ ^ 2) / a) * v 0 := by
        field_simp; ring
      rw [key, hαγ, div_self ha, one_mul]
    · show binaryRedistributeInv a b α γ (binaryRedistributeFwd a b α γ v) 1 = v 1
      simp only [binaryRedistributeInv_one, binaryRedistributeFwd_zero,
        binaryRedistributeFwd_one]
      -- Goal: -γ·(α·v0 - b·γ·v1) + α·(γ·v0 + (α/a)·v1) = v 1
      have key : -γ * (α * v 0 - b * γ * v 1)
                  + α * (γ * v 0 + (α / a) * v 1)
                = ((α ^ 2 + a * b * γ ^ 2) / a) * v 1 := by
        field_simp; ring
      rw [key, hαγ, div_self ha, one_mul]
  right_inv v := by
    funext i
    fin_cases i
    · show binaryRedistributeFwd a b α γ (binaryRedistributeInv a b α γ v) 0 = v 0
      simp only [binaryRedistributeFwd_zero, binaryRedistributeInv_zero,
        binaryRedistributeInv_one]
      -- Goal: α·((α/a)·v0 + b·γ·v1) - b·γ·(-γ·v0 + α·v1) = v 0
      have key : α * ((α / a) * v 0 + b * γ * v 1)
                  - b * γ * (-γ * v 0 + α * v 1)
                = ((α ^ 2 + a * b * γ ^ 2) / a) * v 0 := by
        field_simp; ring
      rw [key, hαγ, div_self ha, one_mul]
    · show binaryRedistributeFwd a b α γ (binaryRedistributeInv a b α γ v) 1 = v 1
      simp only [binaryRedistributeFwd_one, binaryRedistributeInv_zero,
        binaryRedistributeInv_one]
      -- Goal: γ·((α/a)·v0 + b·γ·v1) + (α/a)·(-γ·v0 + α·v1) = v 1
      have key : γ * ((α / a) * v 0 + b * γ * v 1)
                  + (α / a) * (-γ * v 0 + α * v 1)
                = ((α ^ 2 + a * b * γ ^ 2) / a) * v 1 := by
        field_simp; ring
      rw [key, hαγ, div_self ha, one_mul]

/-! ## § 4 The diagonal quadratic form `⟨a, b⟩` -/

/-- The diagonal binary quadratic form `Q(x, y) := a·x² + b·y²`,
    realised as `weightedSumSquares (ZMod p) ![a, b]`. -/
noncomputable def diag_quadratic_form (a b : ZMod p) :
    QuadraticMap (ZMod p) (Fin 2 → ZMod p) (ZMod p) :=
  QuadraticMap.weightedSumSquares (ZMod p) ![a, b]

/-- Evaluation of `diag_quadratic_form` on an arbitrary `v : Fin 2 → ZMod p`:

      `(a·x² + b·y²)` where `(x, y) = (v 0, v 1)`. -/
@[simp] lemma diag_quadratic_form_apply (a b : ZMod p) (v : Fin 2 → ZMod p) :
    diag_quadratic_form a b v = a * (v 0 * v 0) + b * (v 1 * v 1) := by
  unfold diag_quadratic_form
  rw [QuadraticMap.weightedSumSquares_apply]
  simp [Fin.sum_univ_two, smul_eq_mul]

/-! ## § 5 The main theorem — `⟨a, b⟩ ≅ ⟨1, a·b⟩` -/

/-- **Main theorem.**  For `p` odd prime and `a, b ∈ (ZMod p)*`, the
    binary diagonal forms `⟨a, b⟩` and `⟨1, a·b⟩` are isometric as
    quadratic forms on `Fin 2 → ZMod p`.

    The isometry is the explicit 2×2 matrix
    `M = [[α, -a·b·γ/a], [γ, α/a]]` for any `α, γ` satisfying
    `α² + a·b·γ² = a` (existence: `binary_2sq_exists_alpha_gamma`).

    The proof of `(diag_quadratic_form 1 (a·b)) (M·v) = (diag_quadratic_form a b) v`
    is the polynomial identity `binary_redistribute_quadratic_identity`
    applied pointwise to `(v 0, v 1)`. -/
noncomputable def binaryIsometryRedistribute (a b : ZMod p)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    QuadraticMap.IsometryEquiv
      (diag_quadratic_form a b)
      (diag_quadratic_form 1 (a * b)) :=
  -- Extract α, γ with `α² + a·b·γ² = a` from the 2-square existence,
  -- using `Classical.choose` (since the codomain is `Type`, not `Prop`).
  let hex := binary_2sq_exists_alpha_gamma (a := a) (b := b) ha hb
  let α  := hex.choose
  let γ  := hex.choose_spec.choose
  let hαγ : α ^ 2 + a * b * γ ^ 2 = a := hex.choose_spec.choose_spec
  { binaryRedistributeLinearEquiv a b α γ ha hαγ with
    map_app' := by
      intro v
      -- Goal: `(diag_quadratic_form 1 (a*b)) (M·v) = (diag_quadratic_form a b) v`.
      show diag_quadratic_form 1 (a * b)
              (binaryRedistributeFwd a b α γ v)
            = diag_quadratic_form a b v
      simp only [diag_quadratic_form_apply, binaryRedistributeFwd_zero,
        binaryRedistributeFwd_one]
      -- Reduces to:
      --   `1·(α·v0 - b·γ·v1)² + a·b·(γ·v0 + (α/a)·v1)² = a·v0² + b·v1²`.
      have hsq := binary_redistribute_quadratic_identity (a := a) (b := b)
        ha hαγ (v 0) (v 1)
      -- `binary_redistribute_quadratic_identity` is stated with `(a·b·γ/a)·y`;
      -- rewrite to `b·γ·y` to match the forward map.
      have hsimp : a * b * γ / a = b * γ := by field_simp
      rw [hsimp] at hsq
      -- hsq : 1 * (α*v0 - b*γ*v1)^2 + a*b * (γ*v0 + (α/a)*v1)^2
      --     = a * v0^2 + b * v1^2
      -- Goal (after diag_quadratic_form_apply):
      --   1 * ((α*v0 - b*γ*v1) * (α*v0 - b*γ*v1))
      --     + a*b * ((γ*v0 + (α/a)*v1) * (γ*v0 + (α/a)*v1))
      --   = a * (v0 * v0) + b * (v1 * v1)
      -- Convert `x*x ↔ x^2` and align.
      linear_combination hsq }

end R

end SSBX.Foundation.R
