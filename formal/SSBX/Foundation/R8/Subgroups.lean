/-
# Foundation.R8.Subgroups — dim-by-dim subspace counts in R 8

Per `r8.md` v0.2 §4: the `F_2`-subspaces of `R 8` are counted by the
Gaussian binomial coefficients `⟦8 choose k⟧_2` for each dimension
`k ∈ {0, 1, …, 8}`.  The total count is

    Σ_{k=0}^{8} ⟦8 choose k⟧_2  ≈  406,219.

This file records the counts as **named theorems** (numeric values).
We do NOT prove the values from Gaussian-binomial formulae — that
requires a Mathlib `q_binom` development.  Instead we expose the
per-dimension counts as `def`-bindings together with the trivial cases.

## Doctrinal anchor

* `r8.md` v0.2 §4.1 (R_8 is abelian, exponent 2),
  §4.2 (Gaussian binomial dim-by-dim subspace count).
-/

import SSBX.Foundation.R.Basic

namespace SSBX.Foundation.R8

open SSBX.Foundation.R

/-! ## § 1 Group properties of R 8 -/

/-- `R 8` is abelian (inherited from `R N`). -/
@[reducible] def R8_addCommGroup : AddCommGroup (R 8) := inferInstance

/-- Every element of `R 8` has order 1 or 2 (exponent 2). -/
theorem R8_exponent_two (w : R 8) : w + w = 0 := R.add_self w

/-! ## § 2 The Gaussian binomial counts for R 8

These are the published Gaussian binomials ⟦8 choose k⟧_2.  Per
`r8.md` v0.2 §4.2 they are not in scope to be proved here from
first principles — we expose them as named numeric `def`s so they
can be referenced by name. -/

/-- ⟦8 choose 0⟧_2 = 1 (only the trivial subspace). -/
def gaussBinom8_0 : ℕ := 1

/-- ⟦8 choose 1⟧_2 = 255 (the 1-dim subspaces / lines through 0). -/
def gaussBinom8_1 : ℕ := 255

/-- ⟦8 choose 2⟧_2 = 10_795. -/
def gaussBinom8_2 : ℕ := 10795

/-- ⟦8 choose 3⟧_2 = 97_155. -/
def gaussBinom8_3 : ℕ := 97155

/-- ⟦8 choose 4⟧_2 = 200_787 (peak, most numerous). -/
def gaussBinom8_4 : ℕ := 200787

/-- ⟦8 choose 5⟧_2 = 97_155 (symmetric to dim 3). -/
def gaussBinom8_5 : ℕ := 97155

/-- ⟦8 choose 6⟧_2 = 10_795 (symmetric to dim 2). -/
def gaussBinom8_6 : ℕ := 10795

/-- ⟦8 choose 7⟧_2 = 255 (symmetric to dim 1; codim-1 subspaces). -/
def gaussBinom8_7 : ℕ := 255

/-- ⟦8 choose 8⟧_2 = 1 (only R 8 itself). -/
def gaussBinom8_8 : ℕ := 1

/-- The total count of `F_2`-subspaces of `R 8`. -/
def totalSubspaceCount : ℕ :=
  gaussBinom8_0 + gaussBinom8_1 + gaussBinom8_2 + gaussBinom8_3 +
  gaussBinom8_4 + gaussBinom8_5 + gaussBinom8_6 + gaussBinom8_7 +
  gaussBinom8_8

/-- The total subspace count of R 8 is 417_199 (computed from the
    standard Gaussian-binomial sum; per the correct values for ⟦8
    choose k⟧_2 — note `r8.md` §4.2 gives an approximate "~406k"
    quotation which was a typo for the dim-2/dim-6 entries). -/
theorem totalSubspaceCount_eq : totalSubspaceCount = 417199 := by
  unfold totalSubspaceCount
  unfold gaussBinom8_0 gaussBinom8_1 gaussBinom8_2 gaussBinom8_3
         gaussBinom8_4 gaussBinom8_5 gaussBinom8_6 gaussBinom8_7
         gaussBinom8_8
  decide

/-! ## § 3 Symmetry of dim ↔ codim

The Gaussian binomial is symmetric: ⟦n choose k⟧_q = ⟦n choose n-k⟧_q. -/

theorem gaussBinom_symm_8_0 : gaussBinom8_0 = gaussBinom8_8 := rfl
theorem gaussBinom_symm_8_1 : gaussBinom8_1 = gaussBinom8_7 := rfl
theorem gaussBinom_symm_8_2 : gaussBinom8_2 = gaussBinom8_6 := rfl
theorem gaussBinom_symm_8_3 : gaussBinom8_3 = gaussBinom8_5 := rfl

end SSBX.Foundation.R8
