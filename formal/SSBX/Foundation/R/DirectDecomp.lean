/-
# Foundation.R.DirectDecomp — root-layer direct-sum decompositions

Per `wen-algebra` v0.6 §1.4 and `v4-foundation` v0.5 §1.4:

The root layers `R_3, R_5, R_6, R_7` decompose along the binary
expansion of their indices using the squaring-tower basis
`{R_1, R_2, R_4}`:

* `R_3 ≅ R_1 ⊕ R_2`        (3 = 1 + 2)
* `R_5 ≅ R_1 ⊕ R_4`        (5 = 1 + 4)
* `R_6 ≅ R_2 ⊕ R_4`        (6 = 2 + 4)
* `R_7 ≅ R_1 ⊕ R_2 ⊕ R_4`  (7 = 1 + 2 + 4)

Each is realized via `R.append` / `R.directSumEquiv` from `DirectSum.lean`.
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.DirectSum

namespace SSBX.Foundation.R

namespace R

/-! ## § 1 R_3 ≅ R_1 ⊕ R_2 (3 = 1 + 2) -/

/-- R_3 decomposes as R_1 ⊕ R_2 (binary 3 = 1 + 2). -/
def R3_decomp : R 3 ≃ R 1 × R 2 :=
  directSumEquiv (N := 1) (M := 2)

theorem R3_card_decomp : Fintype.card (R 3) = Fintype.card (R 1) * Fintype.card (R 2) :=
  card_directSum 1 2

/-! ## § 2 R_5 ≅ R_1 ⊕ R_4 (5 = 1 + 4) -/

/-- R_5 decomposes as R_1 ⊕ R_4. -/
def R5_decomp : R 5 ≃ R 1 × R 4 :=
  directSumEquiv (N := 1) (M := 4)

theorem R5_card_decomp : Fintype.card (R 5) = Fintype.card (R 1) * Fintype.card (R 4) :=
  card_directSum 1 4

/-! ## § 3 R_6 ≅ R_2 ⊕ R_4 (6 = 2 + 4) -/

/-- R_6 decomposes as R_2 ⊕ R_4. -/
def R6_decomp : R 6 ≃ R 2 × R 4 :=
  directSumEquiv (N := 2) (M := 4)

theorem R6_card_decomp : Fintype.card (R 6) = Fintype.card (R 2) * Fintype.card (R 4) :=
  card_directSum 2 4

/-! ## § 4 R_7 ≅ R_1 ⊕ R_2 ⊕ R_4 (7 = 1 + 2 + 4) -/

/-- R_7 decomposes as R_1 ⊕ (R_2 ⊕ R_4) via two steps. -/
def R7_decomp : R 7 ≃ R 1 × (R 2 × R 4) :=
  (directSumEquiv (N := 1) (M := 6)).trans
    (Equiv.refl (R 1) |>.prodCongr (directSumEquiv (N := 2) (M := 4)))

theorem R7_card_decomp :
    Fintype.card (R 7) = Fintype.card (R 1) * (Fintype.card (R 2) * Fintype.card (R 4)) := by
  rw [card_directSum 1 6, card_directSum 2 4]

/-! ## § 5 Sanity-check on cardinalities -/

example : Fintype.card (R 3) = 8 := by rw [card_eq]; rfl
example : Fintype.card (R 5) = 32 := by rw [card_eq]; rfl
example : Fintype.card (R 6) = 64 := by rw [card_eq]; rfl
example : Fintype.card (R 7) = 128 := by rw [card_eq]; rfl

end R

end SSBX.Foundation.R
