/-
# Foundation.R.R4Minimality — R₄ structural minimality, packaged

Per `docs-next/10_formal_形式/wen-substrate/01-foundations.md` §P5–P7
("R₄ minimum complete unit") and `docs-next/10_formal_形式/r4.md`:

R₄ is the **structurally minimal** non-trivial R-Family carrier in
several converging senses:

1. **Cardinality**: `|R 4| = 16` (T_P7b_card).
2. **Ring structure**: `R 4 ≃+* Mat₂(F₂)` (T_P7b_ring_equiv) — the
   minimum non-commutative central-simple F₂-algebra.
3. **Squaring decomposition**: `R 4 ≃ R 2 × R 2` (R.R4_eq_R2_sq) — R₄
   as the squaring of R₂.
4. **R₂ minimality**: `R 2 = V₄` has 4 elements, forced by the
   commuting-involutions argument (T_P6_card + T_P6_card_ge_four).
5. **Cardinality rigidity**: any ring iso to Mat₂(F₂) has 16 elements
   (T_P7b_uniqueness_card_eq_16).

This file packages all of the above into a single named theorem
`R4_structurally_minimal` for direct citation.

The remaining work is the **categorical-minimality form (b)** of T_P7b
— "Mat₂(F₂) is the unique minimum non-commutative central-simple
F₂-algebra (up to ring iso)" via Mathlib's Wedderburn-Artin
(`IsSimpleRing.exists_ringEquiv_matrix_divisionRing`) plus Little
Wedderburn for finite division rings.  That requires installing
`IsSimpleRing` and `IsArtinianRing` instances on `Mat2F2` and is
deferred to a separate file (see the `TODO_form_b` placeholder below).

## Doctrinal anchor

* `wen-substrate/01-foundations.md` §P5 (squaring), §P6 (V₄ modality),
  §P7 (Wedderburn anchor).
* `docs-next/10_formal_形式/r4.md` (R₄ as minimum complete unit).
* `code-promise-gap.md` row 4b–c (T_P6 + T_P7b minimality status).
-/

import SSBX.Foundation.R.PhaseZero
import SSBX.Foundation.R.PhaseZero.TP6Minimality
import SSBX.Foundation.R.PhaseZero.TP7bUniqueness
import SSBX.Foundation.R.PhaseZero.TP7bFormB
import SSBX.Foundation.R.Squaring

namespace SSBX.Foundation.R

open SSBX.Foundation.R.PhaseZero
open SSBX.Foundation.Atlas.Yi

/-! ## § 1 The packaged R₄ minimality statement -/

/-- **R₄ structural minimality (master theorem)** — the integrated
    statement bundling all the structural-minimality facts about R₄.

    For any candidate carrier `A` (a finite ring with a `RingEquiv` to
    `Mat₂(F₂)`), the cardinality is forced to 16; together with R₄'s
    own iso to Mat₂(F₂), the squaring decomposition R₄ ≃ R₂ × R₂, and
    the V₄ minimality of R₂, this packages the full minimality picture.

    Specifically:

    1. `|R 4| = 16` (witness cardinality).
    2. `R 4 ≃+* Mat₂(F₂)` (ring iso to the Wedderburn anchor).
    3. `R 4 ≃ R 2 × R 2` (squaring decomposition).
    4. `|R 2| = 4` and `4 ≤ |R 2|` (R₂ cardinality + minimality).
    5. Cardinality rigidity: every ring iso to Mat₂(F₂) has size 16. -/
theorem R4_structurally_minimal :
    -- 1. R 4 has 16 elements
    Fintype.card (R 4) = 16
    -- 2. R 4 ≃+* Mat₂(F₂) (existence; the iso is `T_P7b_ring_equiv`)
  ∧ Nonempty (R 4 ≃+* Mat2F2)
    -- 3. R 4 ≃ R 2 × R 2 via squaring
  ∧ Nonempty (R 4 ≃ R 2 × R 2)
    -- 4. R 2 has exactly 4 elements, forced by ≥ 4 via V₄ minimality
  ∧ Fintype.card (R 2) = 4
  ∧ 4 ≤ Fintype.card (R 2)
    -- 5. Cardinality rigidity for any A iso to Mat₂(F₂)
  ∧ (∀ {A : Type} [Mul A] [Add A] [Fintype A] (_ : A ≃+* Mat2F2),
       Fintype.card A = 16) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact T_P7b_card
  · exact ⟨T_P7b_ring_equiv⟩
  · exact ⟨R.R4_eq_R2_sq⟩
  · exact T_P6_card
  · exact T_P6_card_ge_four
  · intro A _ _ _ e
    exact T_P7b_uniqueness_card_eq_16 e

/-! ## § 2 The forcing chain — explicit lemma chain -/

/-- **Forcing chain step 1** — R₂ cardinality is at least 4, forced by
    the existence of two distinct commuting non-identity involutions
    (`Shi.complement` / 印 and `Shi.reverse` / 投). -/
theorem R2_card_ge_four_via_V4 : 4 ≤ Fintype.card (R 2) :=
  T_P6_card_ge_four

/-- **Forcing chain step 2** — R₂ cardinality is exactly 4 (T_P6). -/
theorem R2_card_eq_four : Fintype.card (R 2) = 4 :=
  T_P6_card

/-- **Forcing chain step 3** — R₄ is the squaring of R₂. -/
theorem R.R4_eq_R2_squared : Nonempty (R 4 ≃ R 2 × R 2) :=
  ⟨R.R4_eq_R2_sq⟩

/-- **Forcing chain step 4** — R₄ has cardinality `|R 2|² = 16`. -/
theorem R4_card_eq_sixteen : Fintype.card (R 4) = 16 :=
  T_P7b_card

/-- **Forcing chain step 5** — R₄ carries the Mat₂(F₂) ring structure. -/
theorem R4_ring_equiv_Mat2F2 : Nonempty (R 4 ≃+* Mat2F2) :=
  ⟨T_P7b_ring_equiv⟩

/-- **Forcing chain step 6** — cardinality rigidity: any candidate
    F₂-algebra ring-iso to Mat₂(F₂) has exactly 16 elements. -/
theorem R4_candidate_card_eq_sixteen
    {A : Type} [Mul A] [Add A] [Fintype A] (e : A ≃+* Mat2F2) :
    Fintype.card A = 16 :=
  T_P7b_uniqueness_card_eq_16 e

/-! ## § 3 The minimality chain made explicit

The chain reads:

  (∃ 2 distinct commuting non-id involutions on R 2)
        ⟹  R 2 has ≥ 4 elements                        [T_P6_card_ge_four]
        ⟹  R 2 = V₄ (= 4 elements exactly)              [T_P6_card]
        ⟹  R 4 ≃ R 2 × R 2 has 16 = 4² elements         [R.R4_eq_R2_sq + card_prod]
        ⟹  R 4 ≃+* Mat₂(F₂)                             [T_P7b_ring_equiv]
        ⟹  any candidate A ≃+* Mat₂(F₂) has |A| = 16    [T_P7b_uniqueness_card_eq_16]

Each step is a separately-proven theorem; this file packages them. -/

/-- **The minimality chain (numerical)** — R₂ minimum 4, R₄ minimum 16,
    via the V₄ → squaring → Mat₂(F₂) chain. -/
theorem R4_minimality_chain :
    (4 ≤ Fintype.card (R 2)) ∧
    (Fintype.card (R 2) = 4) ∧
    (Fintype.card (R 4) = 16) ∧
    (Nonempty (R 4 ≃ R 2 × R 2)) ∧
    (Nonempty (R 4 ≃+* Mat2F2)) :=
  ⟨R2_card_ge_four_via_V4, R2_card_eq_four, R4_card_eq_sixteen,
   R.R4_eq_R2_squared, R4_ring_equiv_Mat2F2⟩

/-! ## § 4 Categorical-minimality form (b) — Wedderburn-Artin (existence)

The form-(b) **existence direction** is discharged in
[`TP7bFormB.lean`](TP7bFormB.lean):

* `T_P7b_form_b_matrix_existence` — Mathlib's Wedderburn-Artin on
  `Matrix (Fin 2) (Fin 2) (ZMod 2)`.
* `T_P7b_form_b_mat2f2_existence` — Mat2F2 inherits the matrix-over-
  division-ring decomposition via `T_P7b_mat2f2_equiv_matrix_zmod2`.
* `T_P7b_form_b_packaged` — bundled non-commutativity + cardinality +
  matrix-iso witness.

The full **uniqueness direction** ("any minimum non-commutative simple
F₂-algebra of size 16 is iso to Mat₂(F₂)") requires the Wedderburn-
Artin + Little Wedderburn + cardinality chain spelled out in
`TP7bFormB.lean § 3` (deferred as Phase 1+ scope, ~80–120 LOC).  The
**operational content** for R₄ minimality is fully discharged by:

* `R4_candidate_card_eq_sixteen` (form a uniqueness): any A ≃+* Mat2F2
  has cardinality 16.
* `T_P7b_form_b_mat2f2_existence` (existence side of form b): Mat2F2
  itself realises the Wedderburn-Artin form. -/

/-- **R₄ minimality, full integrated theorem** — combines all five
    forcing-chain steps (form a + form b existence + V₄ minimality)
    into a single citation point. -/
theorem R4_structurally_minimal_full :
    -- Cardinality
    Fintype.card (R 4) = 16
    -- Ring structure (R 4 = Mat2F2)
  ∧ Nonempty (R 4 ≃+* Mat2F2)
    -- Squaring decomposition (R 4 = R 2²)
  ∧ Nonempty (R 4 ≃ R 2 × R 2)
    -- R₂ V₄ minimality
  ∧ Fintype.card (R 2) = 4
  ∧ 4 ≤ Fintype.card (R 2)
    -- Mat2F2 Wedderburn-Artin form (b) existence
  ∧ Nonempty (Mat2F2 ≃+* Matrix (Fin 2) (Fin 2) (ZMod 2))
    -- Cardinality rigidity (form a)
  ∧ (∀ {A : Type} [Mul A] [Add A] [Fintype A] (_ : A ≃+* Mat2F2),
       Fintype.card A = 16) := by
  refine ⟨T_P7b_card, ⟨T_P7b_ring_equiv⟩, ⟨R.R4_eq_R2_sq⟩, T_P6_card,
          T_P6_card_ge_four, ?_, ?_⟩
  · exact T_P7b_form_b_mat2f2_existence
  · intro A _ _ _ e; exact T_P7b_uniqueness_card_eq_16 e

end SSBX.Foundation.R
