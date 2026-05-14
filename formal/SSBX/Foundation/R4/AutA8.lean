/-
# Foundation.R4.AutA8 — `|Aut(R 4)| = 20160 = |A_8|`

Per `r4.md` v0.2 §6 ("Aut(R 4) ≅ A_8"):

The automorphism group of `R 4` as an `F_2`-vector space is

    Aut(R 4) = GL(4, F_2),  |GL(4, F_2)| = 20160 = |A_8|.

This is the classical "exceptional" isomorphism `GL(4, F_2) ≅ A_8`.
**Proving this isomorphism is out of scope** here — the project takes
it as a known mathematical fact.  This file:

1. Recovers `|Aut(R 4)| = 20160` directly from `card_GL 4` in
   `Foundation/R/Aut.lean §3`.
2. Records the equality `|Aut(R 4)| = 20160 = |A_8|` as a cardinality
   identity (`A_8` is not constructed here; we only state the numeric
   match).

The full `Aut(R 4) ≅ A_8` group isomorphism (and its A_8 action on
the 8 underlying combinatorial points; see r4.md §6.2) is a separate
construction not needed for the foundation layer.

## Doctrinal anchor

* `r4.md` v0.2 §6.1 (cardinality), §6.2 (A_8 isomorphism statement),
  §6.3 (Aut nesting tower).
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.Aut

namespace SSBX.Foundation.R4

open SSBX.Foundation.R

/-! ## § 1 The order of Aut(R 4)

`|Aut(R 4)| = |GL(4, F_2)| = (16-1)(16-2)(16-4)(16-8) = 15·14·12·8 = 20160`. -/

/-- The cardinality of the linear-automorphism group of `R 4`,
    reusing `card_GL 4` from `Foundation/R/Aut.lean §3`. -/
def autR4Card : ℕ := R.card_GL 4

@[simp] theorem autR4Card_eq : autR4Card = 20160 := R.card_GL_four

/-! ## § 2 |A_8| = 20160 -- numerical identity

`A_8` is the alternating group on 8 letters; `|A_8| = 8!/2 = 20160`.
Mathlib provides `alternatingGroup` over `Fin 8`, but constructing
the full isomorphism `Aut(R 4) ≅ A_8` is out of scope.

We record the bare numeric identity: `|Aut(R 4)| = |A_8| = 20160`. -/

/-- The order of the alternating group A_8 as a natural number: 8!/2. -/
def a8Card : ℕ := 8 * 7 * 6 * 5 * 4 * 3 * 2 * 1 / 2

@[simp] theorem a8Card_eq : a8Card = 20160 := by
  unfold a8Card; decide

/-- The exceptional cardinality match `|Aut(R 4)| = |A_8| = 20160`.

    This is the *numeric* witness of the classical isomorphism
    `GL(4, F_2) ≅ A_8`.  See `r4.md §6.2` for the abstract
    statement; full group-isomorphism proof is out of scope. -/
theorem autR4_card_eq_a8 : autR4Card = a8Card := by
  rw [autR4Card_eq, a8Card_eq]

/-! ## § 3 Aut tower nesting (cardinalities only)

Per `r4.md §6.3`: `Aut(R 2) ↪ Aut(R 4) ↪ Aut(R 8)`.  We record the
three cardinalities so downstream code can refer to them by name.
The actual embeddings live in higher layers (e.g. `Foundation/R8/`). -/

/-- `|Aut(R 2)| = |GL(2, F_2)| = 6 = |S_3|`. -/
@[simp] theorem autR2_card : R.card_GL 2 = 6 := R.card_GL_two

/-- `|Aut(R 4)| = |GL(4, F_2)| = 20160 = |A_8|`. -/
@[simp] theorem autR4_card : R.card_GL 4 = 20160 := R.card_GL_four

/-! ## § 4 The 6 / 20160 / `|GL(8, F_2)|` Aut tower

`|GL(8, F_2)|` is a much larger product; we record only the leading
two layers (R 2 and R 4) here.  The R 8 layer is `r8.md` material. -/

theorem aut_tower_R2_R4 :
    R.card_GL 2 ∣ R.card_GL 4 := by
  rw [R.card_GL_two, R.card_GL_four]
  decide

end SSBX.Foundation.R4
