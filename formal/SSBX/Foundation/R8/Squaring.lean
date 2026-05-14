/-
# Foundation.R8.Squaring — `R 8` as ceiling of the squaring tower, plus extension to R 16 / R 32 / …

Per `r8.md` v0.2 §12: the squaring tower `R_{2^k}` extends indefinitely
above `R 8`:

    R 8 → R 16 = R 8 ⊕ R 8 → R 32 = R 16 ⊕ R 16 → … → R_{2^k} → …

Self-similarity: each `R_{2^k}` has the same algebraic pattern (rank
stratification, σ blocks, q variants) as `R 8`, scaled up.

This file packages the `R 8 → R 16 → R 32 → …` extension as direct-sum
equivalences plus cardinality theorems.

## Doctrinal anchor

* `r8.md` v0.2 §12.1 (squaring tower recursive definition),
  §12.2 (self-similarity theorem statement),
  §12.5 (R 8 ceiling, R 16+ are derived).
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.DirectSum
import SSBX.Foundation.R.BeyondR8
import SSBX.Foundation.R.Squaring

namespace SSBX.Foundation.R8

open SSBX.Foundation.R

/-! ## § 1 R 16 = R 8 ⊕ R 8 (one squaring step above R 8) -/

/-- `R 16 ≃ R 8 × R 8`: the squaring of `R 8`. -/
def squareUp_R16 : R 16 ≃ R 8 × R 8 :=
  show R (8 + 8) ≃ R 8 × R 8 from R.directSumEquiv (N := 8) (M := 8)

/-- Cardinality of R 16: `|R 16| = |R 8|^2 = 256^2 = 65_536`. -/
theorem R16_card : Fintype.card (R 16) = 65536 := by rw [R.card_eq]; rfl

/-- The squaring step preserves cardinality: `|R 16| = |R 8|^2`. -/
theorem R16_card_eq_R8_sq :
    Fintype.card (R 16) = Fintype.card (R 8) * Fintype.card (R 8) := by
  rw [Fintype.card_congr squareUp_R16, Fintype.card_prod]

/-! ## § 2 R 32 = R 16 ⊕ R 16 -/

/-- `R 32 ≃ R 16 × R 16`: the squaring of `R 16`. -/
def squareUp_R32 : R 32 ≃ R 16 × R 16 :=
  show R (16 + 16) ≃ R 16 × R 16 from R.directSumEquiv (N := 16) (M := 16)

theorem R32_card : Fintype.card (R 32) = 4294967296 := by rw [R.card_eq]; rfl

theorem R32_card_eq_R16_sq :
    Fintype.card (R 32) = Fintype.card (R 16) * Fintype.card (R 16) := by
  rw [Fintype.card_congr squareUp_R32, Fintype.card_prod]

/-! ## § 3 R 32 expressed via R 8 -/

/-- `R 32 ≃ R 8 × R 8 × R 8 × R 8`: 4-fold direct sum of `R 8`. -/
def R32_as_R8_quad : R 32 ≃ (R 8 × R 8) × (R 8 × R 8) :=
  squareUp_R32.trans (squareUp_R16.prodCongr squareUp_R16)

/-! ## § 4 The general squaring tower step -/

/-- The general squaring step `R (2 * N) ≃ R N × R N` from the
    parametric layer.  Restated here for `R 8`-relative use. -/
def generalSquaringEquiv (N : ℕ) : R (N + N) ≃ R N × R N :=
  R.directSumEquiv (N := N) (M := N)

theorem generalSquaringEquiv_card (N : ℕ) :
    Fintype.card (R (N + N)) = Fintype.card (R N) * Fintype.card (R N) := by
  rw [Fintype.card_congr (generalSquaringEquiv N), Fintype.card_prod]

/-! ## § 5 Self-similarity at the cardinality level

Per `r8.md` v0.2 §12.2, each squaring step doubles the
*dimension* and squares the *cardinality*:

    dim(R_{2N}) = 2 · dim(R_N),   |R_{2N}| = |R_N|^2. -/

/-- Self-similarity: `|R_{2k+1}| = |R_{2k}|^2` where the tower level
    `k` indexes the position. -/
theorem tower_card_recurrence (N : ℕ) :
    Fintype.card (R (N + N)) = (Fintype.card (R N)) ^ 2 := by
  rw [generalSquaringEquiv_card]
  rw [sq]

/-- Closed form for tower-cardinality: `|R N| = 2^N`. -/
theorem tower_card_pow (N : ℕ) : Fintype.card (R N) = 2 ^ N := R.card_eq N

/-! ## § 6 The first few tower levels above R 8 -/

theorem R64_card : Fintype.card (R 64) = 2 ^ 64 := R.card_eq 64
theorem R128_card : Fintype.card (R 128) = 2 ^ 128 := R.card_eq 128

/-! ## § 7 R 8 is the ceiling of the *root* layers

Per `r8.md` v0.2 §12.5: `R 8` is the **root-layer ceiling**.  Layers
`R N` for `N > 8` are *constructed* (derived) from `R 8` by direct sum
recursion.

The `Foundation/R/BeyondR8.lean` module provides the witness
`R (8 + M) ≃ R 8 × R M`; we re-export the relevant instances here for
notational convenience. -/

/-- `R 9 ≅ R 8 ⊕ R 1`. -/
def R9_as_R8_R1 : R 9 ≃ R 8 × R 1 := R.R9_decomp

/-- `R 16 ≅ R 8 ⊕ R 8`. -/
def R16_as_R8_R8 : R 16 ≃ R 8 × R 8 := R.R16_decomp

/-- `R 24 ≅ R 8 ⊕ R 16`. -/
def R24_as_R8_R16 : R 24 ≃ R 8 × R 16 := R.R24_decomp

/-! ## § 8 Compatibility: R 8 squaring (downward) -/

/-- The downward squaring `R 8 ≃ R 4 × R 4` (i.e., R 8 = R 4 ⊕ R 4),
    re-exported from the parametric tower. -/
def R8_eq_R4_sq : R 8 ≃ R 4 × R 4 := R.R8_eq_R4_sq

/-- R 8 cardinality via R 4 squaring: `|R 8| = |R 4|^2 = 16^2 = 256`. -/
theorem R8_card_via_R4 : Fintype.card (R 8) = Fintype.card (R 4) * Fintype.card (R 4) :=
  R.R8_card_eq_R4_sq

end SSBX.Foundation.R8
