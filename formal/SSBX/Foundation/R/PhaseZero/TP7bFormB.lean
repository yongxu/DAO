/-
# Foundation.R.PhaseZero.TP7bFormB — T_P7b Wedderburn-Artin form (b)

Per `Foundation/R/PhaseZero/TP7bUniqueness.lean` doc:

> For the categorical-minimality form (b) (Wedderburn-Artin: every
> finite-dim simple non-commutative `F₂`-algebra is iso to `Matrix n D`
> for `D` a division algebra over `F₂`), see Mathlib's
> `IsSimpleRing.exists_ringEquiv_matrix_divisionRing`.  Installing
> `IsSimpleRing` / `IsArtinianRing` on `Mat2F2` so the Mathlib theorem
> applies directly is **orthogonal scaffolding deferred to Phase 1**.

This file discharges the form-(b) **existence direction** by routing
through the natural Mathlib instance carrier
`Matrix (Fin 2) (Fin 2) (ZMod 2)` (which has the full Ring + IsSimpleRing
+ IsArtinianRing instance suite available out-of-the-box).  Via the
existing `T_P7b_mat2f2_equiv_matrix_zmod2 : Mat2F2 ≃+* Matrix (Fin 2) (Fin 2) (ZMod 2)`,
the categorical-minimality decomposition transports to `Mat2F2` as a
corollary.

## What's discharged

1. **Wedderburn-Artin decomposition on the standard matrix carrier**:
   `Matrix (Fin 2) (Fin 2) (ZMod 2)` admits the form
   `Matrix (Fin n) (Fin n) D` via Mathlib's `IsSimpleRing.exists_ringEquiv_matrix_divisionRing`.
   The trivial witness is `n = 2, D = ZMod 2` (itself).

2. **Mat2F2 inherits**: via the existing iso, `Mat2F2` likewise admits
   the matrix-over-division-ring form.

## What's deferred

The full uniqueness — "for any simple non-commutative finite F₂-algebra
A with `|A| = 16`, A ≃+* Mat2F2" — requires chasing through Little
Wedderburn + cardinality arithmetic on `(n, k)` with `k * n² = 4` and
`n ≥ 2`.  The exposition (proof chain) is in
`§ 3` below; the formal proof is ~80–120 LOC of careful Mathlib API
work and is recorded as Phase 1+ scope.  The **operational content**
for R₄ is already in `T_P7b_uniqueness_card_eq_16` (form a).

## Doctrinal anchor

* `wen-substrate.md` v1.0.3 §8.8 (P7b minimum complete unit).
* `code-promise-gap.md` row 4c (Wedderburn-Artin form b status).
* Mathlib's `IsSimpleRing.exists_ringEquiv_matrix_divisionRing`,
  `littleWedderburn`.
-/

import SSBX.Foundation.R.PhaseZero
import SSBX.Foundation.R.PhaseZero.TP7bUniqueness
import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.LittleWedderburn

namespace SSBX.Foundation.R.PhaseZero

universe u

/-! ## § 1 Wedderburn-Artin on the standard matrix carrier -/

/-- **Form (b), existence side, for the standard matrix carrier**:
    `Matrix (Fin 2) (Fin 2) (ZMod 2)` admits a Wedderburn-Artin
    decomposition as a matrix ring over a division ring. -/
theorem T_P7b_form_b_matrix_existence :
    ∃ (n : ℕ) (_ : NeZero n) (D : Type) (_ : DivisionRing D),
      Nonempty (Matrix (Fin 2) (Fin 2) (ZMod 2) ≃+* Matrix (Fin n) (Fin n) D) :=
  IsSimpleRing.exists_ringEquiv_matrix_divisionRing _

/-- **Form (b), existence side, for Mat2F2** — via the existing iso
    `T_P7b_mat2f2_equiv_matrix_zmod2`, `Mat2F2` inherits the matrix-
    over-division-ring decomposition from `Matrix (Fin 2) (Fin 2) (ZMod 2)`.

    The trivial witness chain: `Mat2F2 ≃+* Matrix (Fin 2) (Fin 2) (ZMod 2)`
    already exhibits the form `(n = 2, D = ZMod 2)`. -/
theorem T_P7b_form_b_mat2f2_existence :
    Nonempty (Mat2F2 ≃+* Matrix (Fin 2) (Fin 2) (ZMod 2)) :=
  ⟨T_P7b_mat2f2_equiv_matrix_zmod2⟩

/-! ## § 2 Operational packaging — Mat2F2 as the form-(b) witness -/

/-- **T_P7b form (b), packaged**: bundle the categorical-minimality
    witness for `Mat2F2`.

    * Non-commutativity (`T_P7b_mat2f2_noncommutative`).
    * Cardinality 16 (`T_P7b_mat2f2_card`).
    * Direct iso to `Matrix (Fin 2) (Fin 2) (ZMod 2)`
      (`T_P7b_mat2f2_equiv_matrix_zmod2`) — this IS the
      Wedderburn-Artin decomposition for the case `n = 2, D = ZMod 2`.
    * Cardinality rigidity (`T_P7b_uniqueness_card_eq_16`): any
      `RingEquiv A ≃+* Mat2F2` forces `|A| = 16`. -/
theorem T_P7b_form_b_packaged :
    (∃ x y : Mat2F2, x * y ≠ y * x) ∧
    Fintype.card Mat2F2 = 16 ∧
    Nonempty (Mat2F2 ≃+* Matrix (Fin 2) (Fin 2) (ZMod 2)) := by
  refine ⟨T_P7b_mat2f2_noncommutative, T_P7b_mat2f2_card, ?_⟩
  exact ⟨T_P7b_mat2f2_equiv_matrix_zmod2⟩

/-- **Cardinality rigidity for arbitrary candidate carriers** — restated
    as a separate clause to avoid implicit-argument fragility in the
    bundled theorem above. -/
theorem T_P7b_form_b_card_rigidity
    {A : Type} [Mul A] [Add A] [Fintype A] (e : A ≃+* Mat2F2) :
    Fintype.card A = 16 :=
  T_P7b_uniqueness_card_eq_16 e

/-! ## § 3 The full uniqueness chain — exposition (formal proof deferred)

To complete the full form-(b) uniqueness statement

  **For any `[Ring A] [Fintype A] [IsSimpleRing A] [IsArtinianRing A]`
  with `Algebra (ZMod 2) A`, non-commutative, and `Fintype.card A = 16`,
  there exists `A ≃+* Mat2F2`.**

one chains:

1. **Wedderburn-Artin** on `A`: `A ≃+* Matrix (Fin n) (Fin n) D`
   for some `n : ℕ, NeZero n` and `D : Type, DivisionRing D`
   (Mathlib's `IsSimpleRing.exists_ringEquiv_matrix_divisionRing`).

2. **Finiteness of `D`**: since `Matrix (Fin n) (Fin n) D` is finite
   (via the iso to `A`) and `D` injects into it (e.g., as scalar
   matrices), `D` is finite.

3. **Little Wedderburn**: finite division ring `D` is a field
   (Mathlib's `littleWedderburn`); hence `D ≃+* GF(2^k)` for some
   `k ≥ 1`, using `Algebra (ZMod 2) D` (transported from
   `Algebra (ZMod 2) A`).

4. **Cardinality arithmetic**: `|A| = |D|^(n²) = 2^(k·n²) = 16`
   forces `k·n² = 4`.  Non-commutativity of `A` forces `n ≥ 2`
   (since `Matrix (Fin 1) D ≃+* D` is commutative for `D` a field).
   Hence `n = 2, k = 1`, giving `D ≃+* ZMod 2` and
   `A ≃+* Matrix (Fin 2) (Fin 2) (ZMod 2) ≃+* Mat2F2`.

Each step uses standard Mathlib machinery.  The total proof is
~80–120 LOC and is recorded as **Phase 1+ scope** here; the
operational content for `R 4` minimality is already in
`T_P7b_uniqueness_card_eq_16` (form a) plus the
`T_P7b_form_b_mat2f2_existence` witness above. -/

end SSBX.Foundation.R.PhaseZero
