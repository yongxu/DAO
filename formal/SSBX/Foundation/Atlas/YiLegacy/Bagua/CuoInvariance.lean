/-
# CuoInvariance — 不一致性记录：原始无限制 KleeneInverter 必然不一致

This file documents WHY the project's `kleene_recursion_axiom` (in `GodelLi.lean`)
must restrict `decide` to be `CuoInvariantDecide`.  We prove that the
unrestricted form is **provably inconsistent in Lean**, justifying the
`CuoInvariantDecide` precondition added in § 3 of `GodelLi.lean`.

## Key fact

`Halts P h ↔ Halts P h.complement` (`halts_cuo_invariant`, proved in `GodelLi.lean § 2.5`).
This is a STRUCTURAL property of `BaguaTuring`'s instruction set: every YiInstr
is complement-equivariant on cur.

## Implication

If we DROPPED the `CuoInvariantDecide` precondition (call this
`KleeneInverterUnrestricted`), we could feed it the non-complement-invariant decider
`λ _ h => h.y1 = .yang`.  The axiom would yield D with
`Halts D h ↔ decide D h = false`.  At heaven (y1 = yang), ¬Halts D heaven.
At earth = complement heaven (y1 = yin), Halts D earth.  But `halts_cuo_invariant` forces
`Halts D heaven ↔ Halts D earth`.  Contradiction.

## What this file delivers

- `KleeneInverterUnrestricted`: the original (now-rejected) form, defined inline
- `nonCuoInvariantDecide`: the witness decider that breaks unrestricted Kleene
- `unrestricted_kleene_inverter_inconsistent`: derives `False` from
  `KleeneInverterUnrestricted` (i.e., proves `¬ KleeneInverterUnrestricted`)

This file is **the historical receipt** for why `kleene_recursion_axiom` in
`GodelLi.lean` carries the `CuoInvariantDecide` precondition.  Removing the
precondition would make the axiom False in Lean.

The complement-equivariance machinery (cuoCell, cuoState, halts_cuo_invariant, etc.)
has been **inlined into `GodelLi.lean § 2.5`** so it is available to the
consumer theorems that need to derive `CuoInvariantDecide` witnesses.
-/
import SSBX.Foundation.Atlas.YiLegacy.Bagua.GodelLi

namespace SSBX.Foundation.Bagua.CuoInvariance

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Bagua.GodelLi

/-! ## § 1 The unrestricted (rejected) form -/

/-- The original `KleeneInverter` form WITHOUT the `CuoInvariantDecide`
    precondition.  This is the form whose adoption as an axiom would make
    Lean inconsistent (proved in § 2 below). -/
def KleeneInverterUnrestricted : Prop :=
  ∀ (decide : List YiInstr → Hexagram → Bool),
    ∃ D : List YiInstr, ∀ h : Hexagram, Halts D h ↔ decide D h = false

/-! ## § 2 Inconsistency witness -/

/-- A specific non-complement-invariant Bool decider: outputs Bool from h.y1's value.
    `decide _ h = true` iff `h.y1` is yang.  Cuo flips y1, so this distinguishes
    `h` from `complement h` — making it a witness that no complement-invariant `D` can
    counter-decide it. -/
def nonCuoInvariantDecide : List YiInstr → Hexagram → Bool :=
  fun _ h => match h.y1 with | .yang => true | .yin => false

theorem nonCuoInvariantDecide_qian (P : List YiInstr) :
    nonCuoInvariantDecide P Hexagram.heaven = true := rfl

theorem nonCuoInvariantDecide_kun (P : List YiInstr) :
    nonCuoInvariantDecide P Hexagram.earth = false := rfl

/-- `earth = complement heaven` (proved by definitional equality). -/
theorem kun_eq_cuo_qian : Hexagram.earth = Hexagram.heaven.complement := rfl

/-- **MAIN INCONSISTENCY THEOREM**: the unrestricted form
    `KleeneInverterUnrestricted` is logically false in Lean.

    Sketch: take `decide _ h = (h.y1 = yang)` (non-complement-invariant).
    `KleeneInverterUnrestricted` would give D with
    `Halts D h ↔ decide D h = false`.  At `h = heaven`: decide = true, so
    ¬Halts D heaven.  At `h = earth = complement heaven`: decide = false, so Halts D earth.
    But `halts_cuo_invariant` gives `Halts D heaven ↔ Halts D earth`.  Contradiction.

    **Consequence**: any axiom of the form `axiom k : KleeneInverterUnrestricted`
    immediately collapses Lean to False.  This is why `kleene_recursion_axiom`
    in `GodelLi.lean` includes the `CuoInvariantDecide` precondition. -/
theorem unrestricted_kleene_inverter_inconsistent :
    ¬ KleeneInverterUnrestricted := by
  intro h_unrestricted
  obtain ⟨D, hD⟩ := h_unrestricted nonCuoInvariantDecide
  have h_qian : Halts D Hexagram.heaven ↔ nonCuoInvariantDecide D Hexagram.heaven = false :=
    hD Hexagram.heaven
  have h_kun : Halts D Hexagram.earth ↔ nonCuoInvariantDecide D Hexagram.earth = false :=
    hD Hexagram.earth
  rw [nonCuoInvariantDecide_qian] at h_qian
  rw [nonCuoInvariantDecide_kun] at h_kun
  -- h_qian : Halts D heaven ↔ true = false
  have h_not_qian : ¬ Halts D Hexagram.heaven := by
    intro hq
    exact Bool.noConfusion (h_qian.mp hq)
  -- h_kun : Halts D earth ↔ false = false → Halts D earth
  have h_kun_holds : Halts D Hexagram.earth := h_kun.mpr rfl
  -- complement-invariance: Halts D heaven ↔ Halts D earth
  have h_cuo_inv : Halts D Hexagram.heaven ↔ Halts D Hexagram.earth := by
    rw [kun_eq_cuo_qian]
    exact halts_cuo_invariant D Hexagram.heaven
  exact h_not_qian (h_cuo_inv.mpr h_kun_holds)

/-! ## § 3 Public summary

  The current `kleene_recursion_axiom` in `GodelLi.lean` is the complement-invariant
  RESTRICTED form.  Whether it is consistent in Lean depends on Church-Turing
  for complement-invariant Bool deciders (which this project takes as the meta-axiom).
  What this file proves UNCONDITIONALLY is the negative half: dropping the
  restriction would make Lean inconsistent. -/

/-- The unrestricted form is provably False; this is the receipt that
    `CuoInvariantDecide` precondition in `GodelLi.lean § 3` is REQUIRED. -/
theorem complement_invariance_summary :
    -- (1) Halts is complement-invariant (already in GodelLi)
    (∀ P h, Halts P h ↔ Halts P h.complement)
    ∧ -- (2) Unrestricted KleeneInverter is logically false in Lean
    (¬ KleeneInverterUnrestricted) :=
  ⟨halts_cuo_invariant, unrestricted_kleene_inverter_inconsistent⟩

end SSBX.Foundation.Bagua.CuoInvariance
