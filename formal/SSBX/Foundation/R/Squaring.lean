/-
# Foundation.R.Squaring — the R_1 → R_2 → R_4 → R_8 squaring sub-tower

Per `wen-algebra` v0.6 §1.3 and `v4-foundation` v0.5 §1.3, §6.11, §10.12:

The squaring tower is a sub-sequence of root layers where each step
**doubles cardinality via direct sum**:

    R_1 ⊕ R_1 = R_2
    R_2 ⊕ R_2 = R_4
    R_4 ⊕ R_4 = R_8

(In general `R_{2N} ≅ R_N ⊕ R_N`.)

**Doctrinal note** (per `r8.md §1.6` and `v4-foundation §14.1`): the
squaring cardinality doubling is via **direct sum** (`R_{2N} = R_N ⊕ R_N`,
dimension addition), NOT tensor (which gives `R_{N²}`, dimension
multiplication).  Both views are valid; they correspond to different
operations.

This file packages the direct-sum view as `R (2 * N) ≃ R N × R N`
plus concrete witnesses at N ∈ {1, 2, 4}.
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.DirectSum

namespace SSBX.Foundation.R

namespace R

/-! ## § 1 The general squaring step `R (2 * N) ≃ R N ⊕ R N`

Per `wen-algebra` v0.6 §1.3, the squaring tower step is *direct sum*,
not tensor. -/

/-- `R (N + N) ≃ R N × R N` — the direct-sum form of the squaring step.

    Use this with the conversion `2 * N = N + N` when needed. -/
def squaringEquiv (N : ℕ) : R (N + N) ≃ R N × R N :=
  directSumEquiv (N := N) (M := N)

/-- Cardinality identity at the squaring step: `|R (N + N)| = |R N|^2`. -/
theorem squaringEquiv_card (N : ℕ) :
    Fintype.card (R (N + N)) = Fintype.card (R N) * Fintype.card (R N) := by
  rw [Fintype.card_congr (squaringEquiv N), Fintype.card_prod]

/-! ## § 2 The four squaring witnesses at N = 1, 2, 4

These are the concrete `R 2 ≃ R 1 × R 1`, `R 4 ≃ R 2 × R 2`,
`R 8 ≃ R 4 × R 4` equivalences. -/

/-- The atomic squaring step `R 2 ≃ R 1 × R 1`. -/
def R2_eq_R1_sq : R 2 ≃ R 1 × R 1 :=
  show R (1 + 1) ≃ R 1 × R 1 from directSumEquiv (N := 1) (M := 1)

/-- The first non-trivial squaring step `R 4 ≃ R 2 × R 2`. -/
def R4_eq_R2_sq : R 4 ≃ R 2 × R 2 :=
  show R (2 + 2) ≃ R 2 × R 2 from directSumEquiv (N := 2) (M := 2)

/-- The ceiling-reaching squaring step `R 8 ≃ R 4 × R 4`. -/
def R8_eq_R4_sq : R 8 ≃ R 4 × R 4 :=
  show R (4 + 4) ≃ R 4 × R 4 from directSumEquiv (N := 4) (M := 4)

/-! ## § 3 R 1 ≅ R 0 ⊕ R 0 special case

R_0 has a unique element (the empty function); R_1 ≃ R 0 × R 0 holds
**only** if we read R 0 × R 0 as `Unit × Unit ≃ Unit` — which has
cardinality 1, not 2.

So `R 1 ≃ R 0 ⊕ R 0` is **not** a direct-sum identity in the
cardinality sense (R 1 has 2 elements; R 0 × R 0 has 1).  The
v0.6 doctrine's `R_1 ≃ R_0 ⊕ R_0` is therefore *symbolic* (the
abelian-group direct sum of zero spaces is the zero space; R_1 is
"one bit above zero" not "zero ⊕ zero").

We record the correct general statement: `R N ≃ R 0 × R N` is the
trivial inclusion, witnessed by `directSumEquiv (N := 0) (M := N)`. -/

/-- R N ≃ R 0 × R N — the trivial "no-prefix" direct sum identity. -/
def R_eq_zero_plus (N : ℕ) : R (0 + N) ≃ R 0 × R N :=
  directSumEquiv (N := 0) (M := N)

/-! ## § 4 Cardinality sanity checks at each squaring step -/

theorem R2_card_eq_R1_sq :
    Fintype.card (R 2) = Fintype.card (R 1) * Fintype.card (R 1) := by
  rw [Fintype.card_congr R2_eq_R1_sq, Fintype.card_prod]

theorem R4_card_eq_R2_sq :
    Fintype.card (R 4) = Fintype.card (R 2) * Fintype.card (R 2) := by
  rw [Fintype.card_congr R4_eq_R2_sq, Fintype.card_prod]

theorem R8_card_eq_R4_sq :
    Fintype.card (R 8) = Fintype.card (R 4) * Fintype.card (R 4) := by
  rw [Fintype.card_congr R8_eq_R4_sq, Fintype.card_prod]

end R

end SSBX.Foundation.R
