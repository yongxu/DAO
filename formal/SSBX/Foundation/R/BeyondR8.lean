/-
# Foundation.R.BeyondR8 — R N for N > 8 via R 8 ⊕ R (N - 8) recursion

Per `wen-algebra` v0.6 §1.4 and `v4-foundation` v0.5 §1.5:

R-Family elements with N > 8 are constructed by stacking R_8 layers:

    R N = R_8 ⊕ R_8 ⊕ ... ⊕ R_{N mod 8}    (⌊N/8⌋ copies of R_8)

This file gives the algebraic recursion (witnessed by `R.directSumEquiv`)
and a few concrete instances.
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.DirectSum
import SSBX.Foundation.R.DirectDecomp

namespace SSBX.Foundation.R

namespace R

/-! ## § 1 The R_8 ⊕ R_{N-8} step -/

/-- For N ≥ 8, R N ≅ R 8 ⊕ R (N - 8).  The equivalence is provided as
    R (8 + (N - 8)) ≃ R 8 × R (N - 8), with the user responsible for
    the type-level `N = 8 + (N - 8)` cast. -/
def R_eq_eight_plus (M : ℕ) : R (8 + M) ≃ R 8 × R M :=
  directSumEquiv (N := 8) (M := M)

theorem R_card_eight_plus (M : ℕ) :
    Fintype.card (R (8 + M)) = Fintype.card (R 8) * Fintype.card (R M) :=
  card_directSum 8 M

/-! ## § 2 Worked examples -/

/-- R 9 ≅ R 8 ⊕ R 1. -/
def R9_decomp : R 9 ≃ R 8 × R 1 :=
  show R (8 + 1) ≃ R 8 × R 1 from R_eq_eight_plus 1

/-- R 16 ≅ R 8 ⊕ R 8. -/
def R16_decomp : R 16 ≃ R 8 × R 8 :=
  show R (8 + 8) ≃ R 8 × R 8 from R_eq_eight_plus 8

/-- R 24 ≅ R 8 ⊕ R 16. -/
def R24_decomp : R 24 ≃ R 8 × R 16 :=
  show R (8 + 16) ≃ R 8 × R 16 from R_eq_eight_plus 16

/-! ## § 3 Cardinality sanity -/

example : Fintype.card (R 9) = 512 := by rw [card_eq]; rfl
example : Fintype.card (R 16) = 65536 := by rw [card_eq]; rfl

/-! ## § 4 General N-mod-8 / N-div-8 form

For any N ≥ 8, write N = 8 * q + r where r = N mod 8 ∈ {0, …, 7}.
At the core-doctrine level we expose the *cardinality* form (the
full ⊕^q witness is a routine iteration of `R_eq_eight_plus`):

    |R (8 * q + r)| = (2^8)^q * 2^r. -/
theorem R_card_decomp (q r : ℕ) :
    Fintype.card (R (8 * q + r)) = (2 ^ 8) ^ q * 2 ^ r := by
  rw [card_eq]
  rw [show (2 : ℕ) ^ (8 * q + r) = (2 ^ 8) ^ q * 2 ^ r by
        rw [pow_add, pow_mul]]

end R

end SSBX.Foundation.R
