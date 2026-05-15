/-
# Foundation.R.StrategyA — Stone-duality discharge of T4 step 3 (classical-Boolean scope)

Per `wen-substrate.md` v1.1 §8.4.1 (Strategy A discharge: classical Boolean
case forces $\mathbb{F}_2$). This module formalizes the **partially-discharged
candidate** for Open Problem #1 (§8.4 — the "F₂ lynchpin"):

> Let 𝒮 be a structure satisfying D1 + P1-P3 where the operations on the
> distinction layer form a classical Boolean algebra. Then 𝒮 is interpretable
> in R-Family-over-𝔽₂ at carrier R_N^(𝔽₂) for some N, with the Boolean ring
> structure realized on the carrier.

The mathematical content reduces (via the Stone / Boolean-ring equivalence
already in Mathlib's `Mathlib.Algebra.Ring.BooleanRing`) to the following
chain for any **finite** Boolean ring α:

1. `BooleanRing.add_self` : `a + a = 0` for every `a : α`
   (i.e. the additive group has exponent 2).
2. `AddCommGroup.zmodModule` produces a `Module (ZMod 2) α` instance from (1).
3. `Module.card_eq_pow_finrank` over `(ZMod 2)` forces `|α| = 2 ^ N` for some
   `N` (= the `ZMod 2`-finrank).
4. Equinumerous finite types embed; we exhibit an injection `α ↪ R N` with
   `R N = Fin N → Bool`.

The discharge is therefore **fully Lean-formal** at the operational level:
"any finite classical-Boolean distinction layer embeds into `R N` for some
`N` determined by its `ZMod 2`-dimension". The "interpretation in R-Family"
of §8.4.1 is realized concretely as such an injection.

## Scope and limitations (per §8.4.2-§8.4.3)

Strategy A discharges T4 step 3 **only for the classical-Boolean scope**.
The following are *not* covered by this module — they remain open
sub-problems of Open Problem #1 and require different parametric base
rings $k$ in R-Family-over-$k$:

* **Intuitionistic / Heyting**: non-Boolean distributive lattices.
  Operations do not satisfy `a ⊔ aᶜ = ⊤`; structure is `HeytingAlgebra`
  rather than `BooleanAlgebra`.
* **Multi-valued (Łukasiewicz, fuzzy)**: continuous-valued [0,1] truth.
  Operations do not satisfy `mul_self : a * a = a`; structure is an
  MV-algebra, not a Boolean ring.
* **Quantum (orthomodular lattice)**: distributivity fails.
* **Modal**: extra operators that do not commute with the Boolean structure.

For each of these, §8.4.2 of `wen-substrate.md` describes a parametric
reduction to R-Family-over-different-$k$; those reductions are *not*
formalized here. This module honestly delimits its claim to the case
where the distinction-layer operations form a `BooleanRing`.

## Doctrinal anchor

* `wen-substrate.md` v1.1 §8.4 (Open Problem #1), §8.4.1 (Strategy A
  classical discharge), §8.4.4 (reformulated open problem).
* Mathlib: `Mathlib.Algebra.Ring.BooleanRing`,
  `Mathlib.Algebra.Module.ZMod`, `Mathlib.FieldTheory.Finiteness`.
-/

import SSBX.Foundation.R.Basic
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.EquivFin

namespace SSBX.Foundation.R

/-! ## § 1 Char-2 forcing

Boolean rings have additive exponent 2. This is Mathlib's
`BooleanRing.add_self`, re-exported here in our namespace for the
documentation hook. -/

/-- **Deliverable (1)** — char-2 forcing: every Boolean ring is of
    characteristic 2 in the additive-exponent sense `a + a = 0`.

    Per `wen-substrate.md` §8.4.1 chain step (a). Re-export of
    `BooleanRing.add_self`. -/
theorem booleanRing_char_two (α : Type*) [BooleanRing α] :
    ∀ a : α, a + a = 0 := fun a => BooleanRing.add_self a

/-- Equivalent restatement: `2 • a = 0` for every `a` in a Boolean ring.
    This is the form consumed by `AddCommGroup.zmodModule`. -/
theorem booleanRing_two_nsmul_eq_zero (α : Type*) [BooleanRing α] :
    ∀ a : α, (2 : ℕ) • a = 0 := by
  intro a
  rw [two_nsmul]
  exact BooleanRing.add_self a

/-! ## § 2 ZMod 2 module structure on a Boolean ring

Via `AddCommGroup.zmodModule` and the char-2 fact above. We package this
as a *local* `Module (ZMod 2) α` so that `Module.card_eq_pow_finrank` is
applicable. We deliberately do *not* register a global instance — Boolean
rings come with their own `CommRing α` instance and downstream code may
prefer that view. -/

/-- The `Module (ZMod 2)` structure on a Boolean ring, derived from
    `a + a = 0`. Use locally; not a global instance. -/
noncomputable def booleanRingZModModule (α : Type*) [BooleanRing α] :
    Module (ZMod 2) α :=
  AddCommGroup.zmodModule (booleanRing_two_nsmul_eq_zero α)

/-! ## § 3 Finite Boolean ring cardinality is a power of 2

The cardinality side of Stone's representation at the finite level. Via
`Module.card_eq_pow_finrank` over the prime field `ZMod 2`. -/

/-- **Deliverable (2)** — finite Boolean ring cardinality identification.
    Every finite Boolean ring has cardinality `2 ^ N` for some `N`.

    Per `wen-substrate.md` §8.4.1 chain step (c): "idempotency + ring
    axioms force characteristic 2; Birkhoff representation forces
    $\mathbb{F}_2^k$ structure" — at the cardinality level, which is the
    operational content for embedding into the R-Family. -/
theorem finite_booleanRing_card_eq_pow_two (α : Type*)
    [BooleanRing α] [Fintype α] :
    ∃ N : ℕ, Fintype.card α = 2 ^ N := by
  -- Equip α with a Module (ZMod 2) structure.
  letI : Module (ZMod 2) α := booleanRingZModModule α
  -- ZMod 2 is a finite field (need Fact (Nat.Prime 2) for the Field instance).
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype (ZMod 2) := ZMod.fintype 2
  refine ⟨Module.finrank (ZMod 2) α, ?_⟩
  have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := α)
  rw [ZMod.card] at h
  exact h

/-! ## § 4 Bridge to the R-Family

Any finite type of cardinality `2 ^ N` injects into `R N = Fin N → Bool`,
since `|R N| = 2 ^ N` (see `Foundation/R/Basic.lean: R.card_eq`). -/

/-- **Deliverable (3)** — embedding into R-Family. Every finite Boolean
    ring `α` embeds (as a type) into `R N` for the `N` from
    `finite_booleanRing_card_eq_pow_two`.

    The embedding is constructed at the *type* level — it is a witnessing
    injection `α ↪ R N`, sufficient for the §8.4.1 claim of "interpretable
    in R-Family-over-𝔽₂ at carrier `R N`". Strategy A's substantive claim
    is operational (interpretation exists), not the stronger structural
    claim that the ring structure transfers (which would require Stone's
    representation as a ring iso, a separate, heavier obligation). -/
theorem boolean_ring_embeds_into_R (α : Type*) [BooleanRing α] [Fintype α] :
    ∃ N : ℕ, ∃ ι : α → R N, Function.Injective ι := by
  obtain ⟨N, hcard⟩ := finite_booleanRing_card_eq_pow_two α
  refine ⟨N, ?_⟩
  -- |α| = 2^N = |R N|, so α ≃ R N as types; in particular α ↪ R N.
  have hRN : Fintype.card (R N) = 2 ^ N := R.card_eq N
  have hcards : Fintype.card α = Fintype.card (R N) := hcard.trans hRN.symm
  haveI : DecidableEq α := Classical.decEq α
  haveI : DecidableEq (R N) := Classical.decEq (R N)
  obtain ⟨e⟩ := (Fintype.truncEquivOfCardEq (α := α) (β := R N) hcards).nonempty
  exact ⟨e, e.injective⟩

/-! ## § 5 The Strategy A package theorem -/

/-- **Deliverable (4)** — Strategy A package. Re-statement of
    `boolean_ring_embeds_into_R` in the `Embedding`-typed form that
    matches the §8.4.1 reading: "𝒮 is interpretable in R-Family-over-𝔽₂
    at carrier `R N`".

    This is the **discharged** form of T4 step 3 in the
    classical-Boolean scope of `wen-substrate.md` §8.4.1.

    Limitations: see module header. Non-classical scopes
    (intuitionistic, multi-valued, quantum, modal) escape this discharge
    and remain open sub-problems per §8.4.2-§8.4.4. -/
theorem strategyA_discharge (α : Type*) [BooleanRing α] [Fintype α] :
    ∃ N : ℕ, Nonempty (α ↪ R N) := by
  obtain ⟨N, ι, hι⟩ := boolean_ring_embeds_into_R α
  exact ⟨N, ⟨⟨ι, hι⟩⟩⟩

/-! ## § 6 Trivial sanity check: `Bool` itself

`Bool` is the canonical 2-element Boolean ring (Mathlib provides
`BooleanRing Bool`). Strategy A applied to `Bool` should yield `N = 1`. -/

example : ∃ N : ℕ, Nonempty (Bool ↪ R N) := strategyA_discharge Bool

end SSBX.Foundation.R
