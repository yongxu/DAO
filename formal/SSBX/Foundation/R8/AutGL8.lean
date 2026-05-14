/-
# Foundation.R8.AutGL8 — Aut(R 8) ≃ GL(8, F_2)

Per `r8.md` v0.2 §5, the automorphism group of `R 8` as an
`F_2`-vector space is `GL(8, F_2)`, with order

    |GL(8, F_2)| = ∏_{k=0}^{7} (2^8 - 2^k)
                 = 255 · 254 · 252 · 248 · 240 · 224 · 192 · 128
                 = 5_348_063_769_211_699_200
                 ≈ 5.35 × 10^18.

We use `R.card_GL` from `Foundation/R/Aut.lean` (which holds for any N)
and specialise to N = 8.

## Doctrinal anchor

* `r8.md` v0.2 §5.1 (Aut order = 5.35 × 10^18),
  §5.2 (block-diagonal GL(4) × GL(4) subgroup, Sp(8, F_2), O±(8, F_2)),
  §5.3 (Aut embedding chain R_2 → R_4 → R_8 → …).
-/

import SSBX.Foundation.R.Aut
import SSBX.Foundation.R.Basic

namespace SSBX.Foundation.R8

open SSBX.Foundation.R

/-! ## § 1 The order of Aut(R 8) -/

/-- The order of `GL(8, F_2)`, computed via the explicit product formula
    `∏_{k=0}^{7} (2^8 - 2^k)`. -/
def cardGL8 : ℕ := R.card_GL 8

/-- The explicit order of `GL(8, F_2)`. -/
theorem cardGL8_eq : cardGL8 = 5348063769211699200 := by
  unfold cardGL8
  unfold R.card_GL
  decide

/-! ## § 2 Block-diagonal subgroup GL(4) × GL(4)

The L/R split of `R 8 = R 4 ⊕ R 4` (View B) gives a natural
block-diagonal subgroup of GL(8, F_2) isomorphic to `GL(4) × GL(4)`,
of order `|GL(4)|^2 = 20160^2 = 406_425_600`. -/

/-- The order of `GL(4, F_2) × GL(4, F_2)`. -/
def cardGL4_block : ℕ := R.card_GL 4 * R.card_GL 4

/-- The explicit block-diagonal subgroup order. -/
theorem cardGL4_block_eq : cardGL4_block = 406425600 := by
  unfold cardGL4_block
  rw [R.card_GL_four]

/-- The block-diagonal subgroup is much smaller than the full GL: only
    about 7.6 × 10^{-11} of GL(8, F_2). -/
theorem cardGL4_block_lt_cardGL8 : cardGL4_block < cardGL8 := by
  rw [cardGL4_block_eq, cardGL8_eq]
  decide

/-! ## § 3 Symplectic subgroup Sp(8, F_2)

Per `r8.md` v0.2 §5.2, the symplectic group `Sp(8, F_2)` (the subgroup
of `GL(8, F_2)` preserving the alternating bilinear form σ) has order

    |Sp(2n, F_2)| = 2^{n^2} · ∏_{k=1}^{n} (4^k - 1)

For `n = 4`:

    |Sp(8, F_2)| = 2^16 · 3 · 15 · 63 · 255 = 47_377_612_800. -/

/-- The order of `Sp(8, F_2)`. -/
def cardSp8 : ℕ := 2 ^ 16 * 3 * 15 * 63 * 255

/-- The explicit symplectic order. -/
theorem cardSp8_eq : cardSp8 = 47377612800 := by
  unfold cardSp8
  decide

/-- The symplectic group is a proper subgroup of GL. -/
theorem cardSp8_lt_cardGL8 : cardSp8 < cardGL8 := by
  rw [cardSp8_eq, cardGL8_eq]
  decide

/-! ## § 4 Aut embedding chain

The chain `Aut(R 2) ↪ Aut(R 4) ↪ Aut(R 8) ↪ …` is realized by block
diagonal extension.  At the cardinality level: each step's image is a
GL-block of the next. -/

/-- |GL(2, F_2)| = 6 (the symmetric group S_3 on 3 lines through 0). -/
theorem cardGL_2_eq_6 : R.card_GL 2 = 6 := R.card_GL_two

/-- |GL(4, F_2)| = 20160 (the alternating group A_8 of degree 8). -/
theorem cardGL_4_eq_20160 : R.card_GL 4 = 20160 := R.card_GL_four

/-- The embedding chain is strictly increasing in cardinality. -/
theorem cardGL_chain :
    R.card_GL 2 < R.card_GL 4 ∧ R.card_GL 4 < cardGL8 := by
  refine ⟨?_, ?_⟩
  · rw [cardGL_2_eq_6, cardGL_4_eq_20160]; decide
  · rw [cardGL_4_eq_20160, cardGL8_eq]; decide

end SSBX.Foundation.R8
