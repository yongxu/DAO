/-
# Foundation.R.PhaseZero.TP6Minimality — T_P6 explicit minimality lemma

Per `docs-next/10_formal_形式/code-promise-gap.md` row 4b (T_P6, partial):

> Explicit minimality lemma ("≥3 independent modalities ⟹ ≥4 elements")
> still pending.

This file discharges the lemma in the **commuting-involutions form**:

  **Theorem.**  If a finite type `X` admits two distinct non-identity
  commuting involutions `f, g : X → X`, then `|X| ≥ 4`.

**Proof strategy** — transport to `Fin n` via the natural equivalence
`X ≃ Fin (Fintype.card X)`, then case-split on `n ≤ 3` and use `decide`
on `Equiv.Perm (Fin n)` (which has cardinality `n! ≤ 6`, finite and
decidable).  No commuting distinct non-id involutions exist on
`Fin n` for `n ≤ 3`:

* `n = 0, 1`: only one function (identity), no non-id involution.
* `n = 2`: only one non-id involution (the swap); `f = g`.
* `n = 3`: the three non-id involutions on `Fin 3` are the three
  transpositions, and **no two of them commute** (checked by `decide`
  over the finite type `Equiv.Perm (Fin 3)`).

## Application

`R 2` with `Shi.complement` and `Shi.reverse` is the canonical
application: two distinct non-identity commuting involutions, hence
the carrier has `≥ 4` elements.  Combined with `T_P6_card : |R 2| = 4`,
this confirms `R 2` is the **minimum** V₄-modal carrier.

## Doctrinal anchor

* `docs-next/10_formal_形式/code-promise-gap.md` row 4b (T_P6 pending).
* `docs-next/10_formal_形式/wen-substrate/01-foundations.md` §P6.
-/

import Mathlib.Logic.Equiv.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Group.End
import Mathlib.Tactic.IntervalCases
import SSBX.Foundation.Atlas.Yi.Shi
import SSBX.Foundation.R.PhaseZero

namespace SSBX.Foundation.R.PhaseZero

universe u

/-! ## § 1 No commuting distinct non-id involutions on `Fin n` for `n ≤ 3` -/

/-- On `Fin n` for `n ≤ 3`, no pair of distinct non-identity commuting
    involutions exists.  Checked by `decide` on each finite case. -/
private theorem no_commuting_distinct_involutions_fin_le_three :
    ∀ (n : ℕ), n ≤ 3 → ∀ (f g : Equiv.Perm (Fin n)),
      f * f = 1 → g * g = 1 → f * g = g * f →
      f ≠ 1 → g ≠ 1 → f ≠ g → False := by
  intro n hn
  interval_cases n
  all_goals intro f g hf hg hfg hf_ne hg_ne h_ne
  · -- Fin 0
    exact hf_ne (Subsingleton.elim _ _)
  · -- Fin 1
    exact hf_ne (Subsingleton.elim _ _)
  · -- Fin 2
    revert f g hf hg hfg hf_ne hg_ne h_ne; decide
  · -- Fin 3
    revert f g hf hg hfg hf_ne hg_ne h_ne; decide

/-! ## § 2 Transport via `X ≃ Fin (Fintype.card X)` -/

/-- A `Function.Involutive`-witnessed function lifts to an `Equiv.Perm`
    that's a group-level involution. -/
private theorem toPerm_mul_self {X : Type u} {f : X → X}
    (hf : Function.Involutive f) :
    (hf.toPerm f) * (hf.toPerm f) = 1 := by
  ext x; exact hf x

/-- Two commuting involutions lift to commuting permutations in the
    `Equiv.Perm` group. -/
private theorem toPerm_comm {X : Type u} {f g : X → X}
    (hf : Function.Involutive f) (hg : Function.Involutive g)
    (h_comm : ∀ x, f (g x) = g (f x)) :
    (hf.toPerm f) * (hg.toPerm g) = (hg.toPerm g) * (hf.toPerm f) := by
  ext x; exact h_comm x

/-- A non-identity function lifts to a non-identity permutation. -/
private theorem toPerm_ne_one_of_ne_id {X : Type u} {f : X → X}
    (hf : Function.Involutive f) (h_ne_id : f ≠ id) :
    hf.toPerm f ≠ 1 := by
  intro heq
  apply h_ne_id
  funext x
  -- After heq, both sides of the equation are functions; apply to x
  show f x = id x
  have := congrArg (·.toFun x) heq
  exact this

/-- Two distinct functions lift to distinct permutations. -/
private theorem toPerm_ne_of_ne {X : Type u} {f g : X → X}
    (hf : Function.Involutive f) (hg : Function.Involutive g)
    (h_ne : f ≠ g) :
    hf.toPerm f ≠ hg.toPerm g := by
  intro heq
  apply h_ne
  funext x
  exact congrArg (·.toFun x) heq

/-! ## § 3 The main theorem -/

/-- **T_P6 minimality lemma**: a finite type admitting two distinct
    non-identity commuting involutions has at least 4 elements.

    Proof strategy: lift `f, g` to `Equiv.Perm X` via
    `Function.Involutive.toPerm`, then transport via `Equiv.permCongrHom`
    (a `MulEquiv`) to `Equiv.Perm (Fin n)` where `n = Fintype.card X`.
    All the algebraic properties (involution, commutativity, distinctness,
    non-identity) transport automatically through the `MulEquiv`.  Then
    invoke `no_commuting_distinct_involutions_fin_le_three`. -/
theorem card_ge_four_of_two_commuting_involutions
    {X : Type u} [Fintype X] [DecidableEq X]
    {f g : X → X}
    (hf_inv : Function.Involutive f) (hg_inv : Function.Involutive g)
    (hf_ne_id : f ≠ id) (hg_ne_id : g ≠ id) (hfg_ne : f ≠ g)
    (h_comm : ∀ x, f (g x) = g (f x)) :
    4 ≤ Fintype.card X := by
  by_contra hlt
  push_neg at hlt
  set n := Fintype.card X
  let e : X ≃ Fin n := Fintype.equivFin X
  -- Lift f, g to Equiv.Perm X
  let fE : Equiv.Perm X := hf_inv.toPerm f
  let gE : Equiv.Perm X := hg_inv.toPerm g
  -- Algebraic properties on Equiv.Perm X side
  have hfE_sq : fE * fE = 1 := toPerm_mul_self hf_inv
  have hgE_sq : gE * gE = 1 := toPerm_mul_self hg_inv
  have hfgE_comm : fE * gE = gE * fE := toPerm_comm hf_inv hg_inv h_comm
  have hfE_ne_one : fE ≠ 1 := toPerm_ne_one_of_ne_id hf_inv hf_ne_id
  have hgE_ne_one : gE ≠ 1 := toPerm_ne_one_of_ne_id hg_inv hg_ne_id
  have hfE_gE : fE ≠ gE := toPerm_ne_of_ne hf_inv hg_inv hfg_ne
  -- Transport via the MulEquiv `Equiv.permCongrHom`
  let φ : Equiv.Perm X ≃* Equiv.Perm (Fin n) := e.permCongrHom
  let fE' : Equiv.Perm (Fin n) := φ fE
  let gE' : Equiv.Perm (Fin n) := φ gE
  -- Properties transport via the MulEquiv (preserves * and 1)
  have hfE'_sq : fE' * fE' = 1 := by
    show φ fE * φ fE = 1
    rw [← φ.map_mul, hfE_sq, φ.map_one]
  have hgE'_sq : gE' * gE' = 1 := by
    show φ gE * φ gE = 1
    rw [← φ.map_mul, hgE_sq, φ.map_one]
  have hfgE'_comm : fE' * gE' = gE' * fE' := by
    show φ fE * φ gE = φ gE * φ fE
    rw [← φ.map_mul, hfgE_comm, φ.map_mul]
  have hfE'_ne_one : fE' ≠ 1 := by
    intro heq
    apply hfE_ne_one
    have : φ fE = φ 1 := by rw [φ.map_one]; exact heq
    exact φ.injective this
  have hgE'_ne_one : gE' ≠ 1 := by
    intro heq
    apply hgE_ne_one
    have : φ gE = φ 1 := by rw [φ.map_one]; exact heq
    exact φ.injective this
  have hfE'_gE' : fE' ≠ gE' := by
    intro heq
    apply hfE_gE
    exact φ.injective heq
  -- Apply the Fin n no-commuting lemma
  exact no_commuting_distinct_involutions_fin_le_three n (by omega)
    fE' gE' hfE'_sq hgE'_sq hfgE'_comm hfE'_ne_one hgE'_ne_one hfE'_gE'

/-! ## § 4 Application to T_P6 (R 2 minimality) -/

open SSBX.Foundation.Atlas.Yi

/-- T_P6 minimality applied to `R 2`: the Klein-four involutions
    `Shi.complement` (印) and `Shi.reverse` (投) on `R 2` are distinct
    non-identity commuting involutions, hence the carrier has `≥ 4`
    elements. -/
theorem T_P6_card_ge_four :
    4 ≤ Fintype.card (R 2) := by
  apply card_ge_four_of_two_commuting_involutions
    (f := Shi.complement) (g := Shi.reverse)
  · exact Shi.complement_involutive
  · exact Shi.reverse_involutive
  · -- Shi.complement ≠ id
    intro heq
    have : Shi.complement Shi.dao = Shi.dao := congrFun heq Shi.dao
    rw [Shi.complement_dao] at this
    exact absurd this (by decide)
  · -- Shi.reverse ≠ id
    intro heq
    have : Shi.reverse Shi.dao = Shi.dao := congrFun heq Shi.dao
    rw [Shi.reverse_dao] at this
    exact absurd this (by decide)
  · -- complement ≠ reverse
    intro heq
    have : Shi.complement Shi.dao = Shi.reverse Shi.dao := congrFun heq Shi.dao
    rw [Shi.complement_dao, Shi.reverse_dao] at this
    exact absurd this (by decide)
  · -- complement and reverse commute
    intro s
    exact (T_P6_complement_reverse_commute s).symm

/-- **T_P6 packaged with minimality**: `R 2` is the unique 4-element
    V₄-modal carrier — cardinality + minimality both forced. -/
theorem T_P6_minimality_packaged :
    Fintype.card (R 2) = 4 ∧ 4 ≤ Fintype.card (R 2) :=
  ⟨T_P6_card, T_P6_card_ge_four⟩

end SSBX.Foundation.R.PhaseZero
