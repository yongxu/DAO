/-
Copyright (c) 2026 SSBX contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SSBX / GUT-C Path C γ.2 — DiamondH4 uniqueness sub-deliverable

# Foundation.Order.HeytingClassification — 4-element Heyting algebra classification

**Path C Phase γ.2 sub-deliverable**: the **uniqueness conjecture** for
`DiamondH4` introduced in `Foundation/Doctrine/Instance/Heyting.lean`.

Per gut-c-doctrine.md v0.2 §4.2.2:

> Conjecture (open): `R 4 Prop ≃ DiamondH4` (uniqueness as minimum
> non-Boolean 4-element Heyting anchor).

That literal statement is **false classically** — `Fin 4 → Prop` is
classically the 16-element Boolean powerset and cannot be iso to a
4-element chain.  The *intended* (and provable) reading is the abstract
**classification claim**:

> **DiamondH4_uniqueness**: every non-Boolean 4-element Heyting algebra
> is `OrderIso` to `DiamondH4`.

This file delivers that classification.

## The mathematics

Classical lattice theory (e.g., Birkhoff, *Lattice Theory*, 3rd ed.,
1967, Ch. II §4): the bounded distributive lattices of cardinality 4,
up to lattice iso, are exactly two:

* **2 × 2** (the Boolean diamond `Bool × Bool`) — *Boolean*;
  `¬¬a = a` for every `a`.
* **4-chain** `⊥ < a < b < ⊤` (linear) — *not Boolean*; the two middle
  elements are not complemented (their would-be complement equals `⊥`,
  but `mid ⊓ ⊥ = ⊥ ≠ mid` violates `mid ⊓ midᶜ = ⊥` only when
  `mid = ⊥`, so the Boolean axiom `mid ⊔ midᶜ = ⊤` fails).

Since every (bounded) finite distributive lattice carries a *unique*
Heyting algebra structure (the implication is order-determined:
`a ⇨ b = ⨆ { c | c ⊓ a ≤ b }`), the classification of 4-element
Heyting algebras coincides with the classification of 4-element
bounded distributive lattices.

The proof here is **structural**: given a 4-element `DistribLattice` +
`BoundedOrder` `H`, we extract the two non-extremal elements and case
on whether they are comparable (forcing linear chain ≅ DiamondH4) or
incomparable (forcing 2×2 boolean diamond, hence Boolean).

## What this file delivers

### §1 Imports + namespace
### §2 `Chain4` reference: `Fin 4` as the canonical linear 4-chain
### §3 `DiamondH4 ≃ Chain4` order-iso (DiamondH4 = linear case)
### §4 `H4_type` taxonomy: `boolean | linear`
### §5 The classification skeleton — structural case-split lemmas
### §6 The main uniqueness theorem (statement + partial proof)
### §7 Connection back to G5 Heyting.lean — discharges the flag

## Constraints honoured

* **0 new axioms**.
* Build target: `lake build SSBX.Foundation.Order.HeytingClassification`.
* **`sorry` count: 0** — the full DiamondH4 uniqueness theorem is
  formally proved. The combinatorial pieces (`H4_internal_card`,
  `H4_nonBoolean_middles_comparable`, and the final assembly
  `DiamondH4_uniqueness`) are all discharged using
  `Finset.card_eq_four`-style enumeration + universe-pigeonhole + the
  six order-theoretic helper lemmas in §7.1.
* No modification to `Foundation/Doctrine/Instance/Heyting.lean`.

## Doctrinal anchor

* `docs-next/00_start/gut-c-doctrine.md` v0.2 §4.2.2 (DiamondH4 discovery
  + uniqueness conjecture).
* `Foundation/Doctrine/Instance/Heyting.lean` §5 `P7b_heyting`
  (existence; this file delivers the uniqueness side).
* `Mathlib.Order.Heyting.Basic` `LinearOrder.toBiheytingAlgebra` (the
  Heyting structure on `Fin 4` matches `DiamondH4.himp` exactly).
-/

import SSBX.Foundation.Doctrine.Instance.Heyting
import Mathlib.Order.Heyting.Basic
import Mathlib.Order.Heyting.Hom
import Mathlib.Order.BooleanAlgebra.Defs
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Hom.Lattice
import Mathlib.Order.Hom.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Basic

namespace SSBX.Foundation.Order

open SSBX.Foundation.Doctrine.Instance

/-! ## §1 Setup notes

We rely on Mathlib's `LinearOrder.toBiheytingAlgebra` to give `Fin 4`
its canonical Heyting structure.  That structure has
`a ⇨ b = ⊤` if `a ≤ b` and `b` otherwise, which **literally matches**
the case-analysis pattern of `DiamondH4.himp` from
`Foundation/Doctrine/Instance/Heyting.lean` §5.  This congruence is
the cornerstone of `DiamondH4_iso_chain4` (§3).
-/

/-! ## §2 The reference chain: `Chain4 := Fin 4` -/

/-- The canonical 4-element linear chain `0 < 1 < 2 < 3`, used as
    reference object for the classification.  Inherits `LinearOrder`,
    `BoundedOrder`, `BiheytingAlgebra` (hence `HeytingAlgebra`) from
    Mathlib's `Fin n` instances. -/
abbrev Chain4 : Type := Fin 4

instance : LinearOrder Chain4 := Fin.instLinearOrder
instance : BoundedOrder Chain4 := Fin.instBoundedOrder
instance : Fintype Chain4 := Fin.fintype 4

/-- `Chain4` has 4 elements. -/
theorem Chain4_card : Fintype.card Chain4 = 4 := by decide

/-! ## §3 DiamondH4 ≃ Chain4 — the linear case identification

The 4-element chain `{⊥ < mid₁ < mid₂ < ⊤}` of `DiamondH4` corresponds
bit-for-bit to the chain `0 < 1 < 2 < 3` of `Fin 4`.  We expose:

* a constructive order-preserving `Equiv` `DiamondH4 ≃ Fin 4`;
* monotonicity in both directions;
* a `simp`-discoverable agreement on the implementation of `himp`
  (DiamondH4's hand-rolled table matches `Fin 4`'s Mathlib-derived one).
-/

namespace DiamondH4

/-- Map `DiamondH4` → `Fin 4` in the natural order. -/
def toFin4 : DiamondH4 → Fin 4
  | .bot  => ⟨0, by decide⟩
  | .mid1 => ⟨1, by decide⟩
  | .mid2 => ⟨2, by decide⟩
  | .top  => ⟨3, by decide⟩

/-- Inverse: `Fin 4` → `DiamondH4` (clamping out-of-range to `⊤`). -/
def ofFin4 : Fin 4 → DiamondH4
  | ⟨0, _⟩ => .bot
  | ⟨1, _⟩ => .mid1
  | ⟨2, _⟩ => .mid2
  | ⟨3, _⟩ => .top
  | ⟨_+4, h⟩ => absurd h (by omega)

/-- The roundtrip `DiamondH4 → Fin 4 → DiamondH4` is the identity. -/
theorem ofFin4_toFin4 : ∀ x : DiamondH4, ofFin4 (toFin4 x) = x
  | .bot => rfl
  | .mid1 => rfl
  | .mid2 => rfl
  | .top => rfl

/-- The roundtrip `Fin 4 → DiamondH4 → Fin 4` is the identity. -/
theorem toFin4_ofFin4 : ∀ x : Fin 4, toFin4 (ofFin4 x) = x
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨_+4, h⟩ => absurd h (by omega)

/-- **DiamondH4 ≃ Fin 4** as a plain `Equiv` (pre-order; the order
    transfer is the contents of §4 / `DiamondH4.linearOrderTransfer`). -/
def equivFin4 : DiamondH4 ≃ Fin 4 where
  toFun := toFin4
  invFun := ofFin4
  left_inv := ofFin4_toFin4
  right_inv := toFin4_ofFin4

end DiamondH4

/-! ## §4 Transferring `LinearOrder`/`HeytingAlgebra` from `Fin 4`

We use `DiamondH4.equivFin4` to *induce* a `LinearOrder` on `DiamondH4`
matching the intended `⊥ < mid₁ < mid₂ < ⊤` chain.  Mathlib's
`LinearOrder.lift'` provides the standard transfer construction.

The induced `BiheytingAlgebra` then has its `himp` computed via the
`LinearOrder.toBiheytingAlgebra` formula; and that formula coincides
with the explicit `DiamondH4.himp` table from
`Foundation/Doctrine/Instance/Heyting.lean` §5 (Lemma
`DiamondH4.himp_eq_transferred_himp` below — proof by `decide`).
-/

namespace DiamondH4

/-- The `≤` relation on `DiamondH4` induced by `Fin 4`'s. -/
instance : LE DiamondH4 := ⟨fun a b => toFin4 a ≤ toFin4 b⟩
/-- The `<` relation on `DiamondH4` induced by `Fin 4`'s. -/
instance : LT DiamondH4 := ⟨fun a b => toFin4 a < toFin4 b⟩

/-- `LinearOrder` on `DiamondH4` transferred from `Fin 4` via
    `DiamondH4.toFin4` (injectivity is `decide`). -/
instance instLinearOrder : LinearOrder DiamondH4 :=
  LinearOrder.lift' toFin4 (fun a b h => by
    cases a <;> cases b <;> simp [toFin4] at h <;> rfl)

/-- `⊥ = .bot` for the transferred order. -/
instance : OrderBot DiamondH4 where
  bot := .bot
  bot_le x := by
    show toFin4 .bot ≤ toFin4 x
    cases x <;> decide

/-- `⊤ = .top` for the transferred order. -/
instance : OrderTop DiamondH4 where
  top := .top
  le_top x := by
    show toFin4 x ≤ toFin4 .top
    cases x <;> decide

instance : BoundedOrder DiamondH4 where
  __ := (inferInstance : OrderBot DiamondH4)
  __ := (inferInstance : OrderTop DiamondH4)

/-- `BiheytingAlgebra` on `DiamondH4`, via `LinearOrder.toBiheytingAlgebra`.
    The `himp` derived from this matches `DiamondH4.himp`
    (see `himp_match` below). -/
instance instBiheytingAlgebra : BiheytingAlgebra DiamondH4 :=
  LinearOrder.toBiheytingAlgebra DiamondH4

instance instHeytingAlgebra : HeytingAlgebra DiamondH4 := inferInstance

/-- **`himp` agreement** — the hand-rolled `DiamondH4.himp` from
    `Foundation/Doctrine/Instance/Heyting.lean` §5 *equals* the
    `HImp.himp` derived from `LinearOrder.toBiheytingAlgebra`.

    Proof: exhaustive case-split on the 16 (a, b) pairs and `decide`. -/
theorem himp_match (a b : DiamondH4) :
    DiamondH4.himp a b = (a ⇨ b) := by
  cases a <;> cases b <;> decide

end DiamondH4

/-! ## §5 The `OrderIso`: `DiamondH4 ≃o Chain4`

With the transferred orders, the `Equiv` upgrades to an `OrderIso`.
The two structures are *literally the same chain*. -/

/-- **DiamondH4 ≃o Chain4** (= `Fin 4`) as an order-iso. -/
def diamondH4IsoChain4 : DiamondH4 ≃o Chain4 where
  toEquiv := DiamondH4.equivFin4
  map_rel_iff' := by
    intro a b
    -- `≤` on DiamondH4 is *defined* as `≤` on Fin 4 via toFin4.
    rfl

theorem DiamondH4_iso_linear :
    Nonempty (DiamondH4 ≃o Chain4) := ⟨diamondH4IsoChain4⟩

/-! ## §6 The classification taxonomy

We name the two iso classes for 4-element bounded distributive
lattices.  This is the **statement-level** classification target.
-/

/-- The two isomorphism classes of 4-element bounded distributive
    lattices.  Classical result (Birkhoff, *Lattice Theory* 1967,
    Ch. II §4):

    * `boolean` — `Bool × Bool` (the 2×2 powerset diamond, the unique
      Boolean 4-element distributive lattice);
    * `linear` — the 4-chain `⊥ < a < b < ⊤` (the unique non-Boolean
      4-element distributive lattice). -/
inductive H4_type : Type
  /-- The Boolean 4-element diamond `Bool × Bool`. -/
  | boolean : H4_type
  /-- The 4-element linear chain `⊥ < mid₁ < mid₂ < ⊤`. -/
  | linear  : H4_type
  deriving DecidableEq, Inhabited

/-! ## §7 The classification skeleton

The classification reduces to a structural case-analysis on the two
non-extremal elements `a, b : H` of a 4-element bounded
distributive lattice.  Either:

* `a ≤ b` or `b ≤ a` (comparable) — forces linear chain;
* otherwise (incomparable) — forces `a ⊓ b = ⊥` and `a ⊔ b = ⊤`,
  hence each is the other's complement, hence `H` is Boolean.

We *state* this structurally; the genuine combinatorial proof
requires choosing an enumeration `H ≃ Fin 4` and inducting, which is
a `Finite`-instance ceremony that does not fit the present scope.

The lemmas below capture the *forward* direction (`DiamondH4` is
in the linear class) cleanly; the *reverse* (the only-ways-it-
can-look claim) is the conjecture's research content. -/

section Classification

variable {H : Type} [DistribLattice H] [BoundedOrder H] [Fintype H] [DecidableEq H]

/-- A 4-element bounded distributive lattice has exactly two
    "internal" (= non-`⊥`, non-`⊤`) elements.  This is just
    `Fintype.card`-pigeonhole after removing the two extremes. -/
theorem H4_internal_card (h_card : Fintype.card H = 4)
    (h_bot_ne_top : (⊥ : H) ≠ ⊤) :
    -- Two extremes leave 2 = 4 − 2 internal elements.
    Fintype.card { x : H // x ≠ ⊥ ∧ x ≠ ⊤ } = 2 := by
  -- Strategy: rewrite the predicate `x ≠ ⊥ ∧ x ≠ ⊤` as
  -- `¬ (x = ⊥ ∨ x = ⊤)`, use `Fintype.card_subtype_compl`, and
  -- compute the complement to be `{⊥, ⊤}` with card = 2.
  have h_predicate :
      ∀ x : H, (x ≠ ⊥ ∧ x ≠ ⊤) ↔ ¬ (x = ⊥ ∨ x = ⊤) := by
    intro x; constructor
    · rintro ⟨hb, ht⟩ (h1 | h2)
      · exact hb h1
      · exact ht h2
    · intro h; exact ⟨fun h1 => h (Or.inl h1), fun h2 => h (Or.inr h2)⟩
  -- Reframe via an `Equiv` of subtypes
  have hEquiv :
      { x : H // x ≠ ⊥ ∧ x ≠ ⊤ } ≃ { x : H // ¬ (x = ⊥ ∨ x = ⊤) } :=
    Equiv.subtypeEquivRight h_predicate
  rw [Fintype.card_congr hEquiv]
  -- Now use Fintype.card_subtype_compl
  rw [Fintype.card_subtype_compl (fun x : H => x = ⊥ ∨ x = ⊤)]
  rw [h_card]
  -- It remains to show Fintype.card { x // x = ⊥ ∨ x = ⊤ } = 2.
  have h_two : Fintype.card { x : H // x = ⊥ ∨ x = ⊤ } = 2 := by
    -- Build an Equiv with `Bool`: ⊥ ↔ false, ⊤ ↔ true.
    have hE : { x : H // x = ⊥ ∨ x = ⊤ } ≃ Bool := by
      refine
        { toFun := fun x => if x.val = ⊥ then false else true,
          invFun := fun b => if b then ⟨⊤, Or.inr rfl⟩ else ⟨⊥, Or.inl rfl⟩,
          left_inv := ?_,
          right_inv := ?_ }
      · rintro ⟨x, hx | hx⟩
        · simp [hx]
        · simp [hx]
          intro h
          exact (h_bot_ne_top h.symm).elim
      · intro b
        cases b
        · simp
        · simp
          intro h
          exact (h_bot_ne_top h.symm).elim
    rw [Fintype.card_congr hE]
    decide
  rw [h_two]

/-! ### §7.1 Building blocks for `H4_nonBoolean_middles_comparable`

We isolate the key structural facts that drive the contradiction.
The crucial observations are:

* In any bounded distributive lattice, `a ⊓ b ≤ a` and `a ⊓ b ≤ b`.
* In a 4-element lattice with internal elements `{a, b}`, the inf
  `a ⊓ b` must inhabit `{⊥, a, b, ⊤}` (the universe).
* `a ⊓ b = ⊤` is impossible (would force `a = ⊤` via `⊤ ≤ a`).
* `a ⊓ b = a` ⇒ `a ≤ b` (comparable).
* `a ⊓ b = b` ⇒ `b ≤ a` (comparable).
* So in the *incomparable* case, `a ⊓ b = ⊥`.

These are clean three-line proofs each, recorded below. -/

/-- Inf-with-self-and-bound: `a ⊓ b = ⊤` ⇒ `a = ⊤`. -/
theorem H4_inf_eq_top (a b : H) (h : a ⊓ b = ⊤) : a = ⊤ := by
  apply le_antisymm le_top
  rw [← h]
  exact inf_le_left

/-- Inf-equals-left implies `a ≤ b`. -/
theorem H4_inf_eq_left (a b : H) (h : a ⊓ b = a) : a ≤ b := by
  rw [← h]; exact inf_le_right

/-- Inf-equals-right implies `b ≤ a`. -/
theorem H4_inf_eq_right (a b : H) (h : a ⊓ b = b) : b ≤ a := by
  rw [← h]; exact inf_le_left

/-- Dual: sup-equals-top would need to be `⊤`, etc. -/
theorem H4_sup_eq_bot (a b : H) (h : a ⊔ b = ⊥) : a = ⊥ := by
  apply le_antisymm _ bot_le
  rw [← h]; exact le_sup_left

theorem H4_sup_eq_left (a b : H) (h : a ⊔ b = a) : b ≤ a := by
  rw [← h]; exact le_sup_right

theorem H4_sup_eq_right (a b : H) (h : a ⊔ b = b) : a ≤ b := by
  rw [← h]; exact le_sup_left

/-- **Non-Boolean ⇒ comparable middles.**  In a 4-element bounded
    distributive lattice that is *not* Boolean, the two non-extremal
    elements must be comparable.

    *Reason*: incomparable + `BoundedOrder` + 4-element forces
    `a ⊓ b = ⊥` and `a ⊔ b = ⊤` (the only candidates for inf/sup of
    incomparable middles, given exactly 4 elements); then `a` and `b`
    are each other's complement, so the lattice is `Bool × Bool`,
    contradiction.

    The proof reduces the comparability question to:
    * the inf `a ⊓ b` lies in the 4-element universe `H`;
    * each of the four possibilities `a ⊓ b ∈ {⊥, a, b, ⊤}` collapses
      to either comparability or impossibility (via
      `H4_inf_eq_left/right/top`);
    * the dual argument for the sup gives `a ⊔ b ≠ ⊥` (else `a = ⊥`),
      and again only one of the four possibilities survives ⇒ `a ⊔ b = ⊤`;
    * then `a` and `b` are mutual complements, so we can construct a
      complement for every element of `H`, contradicting the
      non-Boolean hypothesis (since the existence of complements for
      every element + DistribLattice = BooleanAlgebra).

    The full assembly enumerates `H = {⊥, a, b, ⊤}` (via
    `H4_internal_card`) and provides the explicit `y` for the
    complement; this is straightforward but lengthy combinatorics.
    Recorded here as the named research-open piece.

    **Status**: the reduction-to-finite-cases is fully spelled out in
    the comments above; the remaining work is the cardinality-
    enumeration ceremony. -/
theorem H4_nonBoolean_middles_comparable
    (h_card : Fintype.card H = 4)
    (h_bot_ne_top : (⊥ : H) ≠ ⊤)
    (h_nonBoolean : ¬ ∀ x : H, ∃ y : H, x ⊓ y = ⊥ ∧ x ⊔ y = ⊤)
    (a b : H) (ha : a ≠ ⊥ ∧ a ≠ ⊤) (hb : b ≠ ⊥ ∧ b ≠ ⊤) (hab : a ≠ b) :
    a ≤ b ∨ b ≤ a := by
  -- Contrapositive route: assume incomparable, derive Boolean
  -- structure (using §7.1 building blocks), contradict h_nonBoolean.
  by_contra h_incomp
  push_neg at h_incomp
  obtain ⟨h_anb, h_bna⟩ := h_incomp
  -- Step 1: a ⊓ b ≠ a (else a ≤ b, contradicts h_anb).
  have h_inf_ne_a : a ⊓ b ≠ a := fun h => h_anb (H4_inf_eq_left a b h)
  -- Step 2: a ⊓ b ≠ b (else b ≤ a, contradicts h_bna).
  have h_inf_ne_b : a ⊓ b ≠ b := fun h => h_bna (H4_inf_eq_right a b h)
  -- Step 3: a ⊓ b ≠ ⊤ (else a = ⊤, contradicts ha.2).
  have h_inf_ne_top : a ⊓ b ≠ ⊤ := fun h => ha.2 (H4_inf_eq_top a b h)
  -- Dual:
  have h_sup_ne_a : a ⊔ b ≠ a := fun h => h_bna (H4_sup_eq_left a b h)
  have h_sup_ne_b : a ⊔ b ≠ b := fun h => h_anb (H4_sup_eq_right a b h)
  have h_sup_ne_bot : a ⊔ b ≠ ⊥ := fun h => ha.1 (H4_sup_eq_bot a b h)
  -- Step 4: every H-element is one of ⊥, a, b, ⊤.  We extract this
  -- via Finset.card_eq_four applied to the universe + an injective
  -- argument identifying the four witnesses with the four known
  -- distinct elements {⊥, a, b, ⊤} (distinctness: ⊥ ≠ ⊤ by h_bot_ne_top,
  -- ⊥ ≠ a by ha.1, ⊥ ≠ b by hb.1, a ≠ ⊤ by ha.2, b ≠ ⊤ by hb.2,
  -- a ≠ b by hab).
  -- Use Finset.card_eq_four characterisation: build the explicit
  -- {⊥, a, b, ⊤} finset and verify card = 4 via direct insertion
  -- (each element distinct from the others by hypothesis).
  have hb_ne_top : b ≠ ⊤ := hb.2
  have ha_ne_top : a ≠ ⊤ := ha.2
  have ha_ne_b : a ≠ b := hab
  have hbot_ne_b : (⊥ : H) ≠ b := fun h => hb.1 h.symm
  have hbot_ne_a : (⊥ : H) ≠ a := fun h => ha.1 h.symm
  have h_four_distinct :
      ({⊥, a, b, ⊤} : Finset H).card = 4 := by
    -- {⊥, a, b, ⊤} = insert ⊥ (insert a (insert b {⊤}))
    -- Compute card step by step.
    have h1 : (insert b ({⊤} : Finset H)).card = 2 := by
      rw [Finset.card_insert_of_notMem, Finset.card_singleton]
      simp [hb_ne_top]
    have h2 : (insert a (insert b ({⊤} : Finset H))).card = 3 := by
      rw [Finset.card_insert_of_notMem, h1]
      simp
      exact ⟨ha_ne_b, ha_ne_top⟩
    have h3 : (insert (⊥ : H) (insert a (insert b ({⊤} : Finset H)))).card = 4 := by
      rw [Finset.card_insert_of_notMem, h2]
      simp
      exact ⟨hbot_ne_a, hbot_ne_b, h_bot_ne_top⟩
    exact h3
  -- Since #{⊥, a, b, ⊤} = 4 = #univ, the two finsets are equal.
  have h_eq_univ : ({⊥, a, b, ⊤} : Finset H) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [h_four_distinct, h_card]
  -- Universe membership: every x : H is in {⊥, a, b, ⊤}.
  have h_universe : ∀ x : H, x = ⊥ ∨ x = a ∨ x = b ∨ x = ⊤ := by
    intro x
    have hx : x ∈ ({⊥, a, b, ⊤} : Finset H) := by
      rw [h_eq_univ]; exact Finset.mem_univ x
    simpa using hx
  -- Now apply to a ⊓ b:
  have h_inf_cases := h_universe (a ⊓ b)
  have h_inf_eq_bot : a ⊓ b = ⊥ := by
    rcases h_inf_cases with h | h | h | h
    · exact h
    · exact (h_inf_ne_a h).elim
    · exact (h_inf_ne_b h).elim
    · exact (h_inf_ne_top h).elim
  -- And to a ⊔ b:
  have h_sup_cases := h_universe (a ⊔ b)
  have h_sup_eq_top : a ⊔ b = ⊤ := by
    rcases h_sup_cases with h | h | h | h
    · exact (h_sup_ne_bot h).elim
    · exact (h_sup_ne_a h).elim
    · exact (h_sup_ne_b h).elim
    · exact h
  -- We now have a ⊓ b = ⊥ and a ⊔ b = ⊤: a, b are mutual complements.
  -- Construct an explicit complement for every x ∈ H, contradicting
  -- h_nonBoolean.
  apply h_nonBoolean
  intro x
  rcases h_universe x with hx | hx | hx | hx
  · -- x = ⊥: y = ⊤ works.
    exact ⟨⊤, by rw [hx]; simp, by rw [hx]; simp⟩
  · -- x = a: y = b works (by h_inf_eq_bot and h_sup_eq_top).
    exact ⟨b, by rw [hx]; exact h_inf_eq_bot, by rw [hx]; exact h_sup_eq_top⟩
  · -- x = b: y = a works.
    exact ⟨a, by rw [hx]; rw [inf_comm]; exact h_inf_eq_bot,
              by rw [hx]; rw [sup_comm]; exact h_sup_eq_top⟩
  · -- x = ⊤: y = ⊥ works.
    exact ⟨⊥, by rw [hx]; simp, by rw [hx]; simp⟩

end Classification

/-! ## §8 The main uniqueness theorem

Combining the classification skeleton (§7) and the
`DiamondH4 ≃o Chain4` iso (§5):

**Theorem**: every non-Boolean 4-element Heyting algebra (more
generally: 4-element bounded distributive lattice that is not
Boolean) is `OrderIso` to `DiamondH4`. -/

section Uniqueness

variable {H : Type} [DistribLattice H] [BoundedOrder H] [Fintype H] [DecidableEq H]

/-- **DiamondH4 uniqueness, weak form** — *every* non-Boolean
    4-element bounded distributive lattice is order-isomorphic to
    `DiamondH4`.

    **Status**: this is the **statement form** of the conjecture from
    `Foundation/Doctrine/Instance/Heyting.lean` §5 (P7b_heyting).  The
    proof reduces (via §7's two lemmas) to a finite case-analysis;
    the remaining gap is the named `H4_internal_card` +
    `H4_nonBoolean_middles_comparable` enumeration, which is the
    genuine combinatorial content of the classification.

    The *partial* proof here shows the reduction explicitly: granted
    the two §7 lemmas, the iso is constructed by ordering the four
    elements (`⊥ < a < b < ⊤`) and transferring to `Chain4 ≃o DiamondH4`. -/
theorem DiamondH4_uniqueness
    (h_card : Fintype.card H = 4)
    (h_bot_ne_top : (⊥ : H) ≠ ⊤)
    (h_nonBoolean : ¬ ∀ x : H, ∃ y : H, x ⊓ y = ⊥ ∧ x ⊔ y = ⊤) :
    Nonempty (H ≃o DiamondH4) := by
  -- Step 1: Extract two distinct internal elements via H4_internal_card.
  -- We use Fintype.equivOfCardEq to get an explicit Bool-indexing of
  -- the 2-element internal set, then read off the two elements.
  have h_int := H4_internal_card h_card h_bot_ne_top
  -- Get an equiv with Bool (card 2 = card Bool).
  have h_int_bool :
      Nonempty ({ p : H // p ≠ ⊥ ∧ p ≠ ⊤ } ≃ Bool) := by
    rw [← Fintype.card_eq]
    rw [h_int, Fintype.card_bool]
  obtain ⟨e_int⟩ := h_int_bool
  -- The two internal elements:
  let a : H := (e_int.symm false).val
  let b : H := (e_int.symm true).val
  have ha : a ≠ ⊥ ∧ a ≠ ⊤ := (e_int.symm false).property
  have hb : b ≠ ⊥ ∧ b ≠ ⊤ := (e_int.symm true).property
  have hab : a ≠ b := by
    intro h_eq
    have h_sub : (e_int.symm false) = (e_int.symm true) := Subtype.ext h_eq
    have h_eq2 : (false : Bool) = true := by
      have hc := congrArg e_int h_sub
      simpa using hc
    exact absurd h_eq2 (by decide)
  -- Step 2: By H4_nonBoolean_middles_comparable, a, b comparable.
  have h_comp := H4_nonBoolean_middles_comparable
    h_card h_bot_ne_top h_nonBoolean a b ha hb hab
  -- WLOG a ≤ b (swap a and b if necessary).
  -- We construct the iso for both cases uniformly.
  -- Step 3: H = {⊥, a, b, ⊤} as a 4-chain.  Extract this universe
  -- enumeration as in the H4_nonBoolean_middles proof.
  have hb_ne_top : b ≠ ⊤ := hb.2
  have ha_ne_top : a ≠ ⊤ := ha.2
  have ha_ne_b : a ≠ b := hab
  have hbot_ne_b : (⊥ : H) ≠ b := fun h => hb.1 h.symm
  have hbot_ne_a : (⊥ : H) ≠ a := fun h => ha.1 h.symm
  have h_four_distinct :
      ({⊥, a, b, ⊤} : Finset H).card = 4 := by
    have h1 : (insert b ({⊤} : Finset H)).card = 2 := by
      rw [Finset.card_insert_of_notMem, Finset.card_singleton]
      simp [hb_ne_top]
    have h2 : (insert a (insert b ({⊤} : Finset H))).card = 3 := by
      rw [Finset.card_insert_of_notMem, h1]
      simp
      exact ⟨ha_ne_b, ha_ne_top⟩
    have h3 : (insert (⊥ : H) (insert a (insert b ({⊤} : Finset H)))).card = 4 := by
      rw [Finset.card_insert_of_notMem, h2]
      simp
      exact ⟨hbot_ne_a, hbot_ne_b, h_bot_ne_top⟩
    exact h3
  have h_eq_univ : ({⊥, a, b, ⊤} : Finset H) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [h_four_distinct, h_card]
  have h_universe : ∀ x : H, x = ⊥ ∨ x = a ∨ x = b ∨ x = ⊤ := by
    intro x
    have hx : x ∈ ({⊥, a, b, ⊤} : Finset H) := by
      rw [h_eq_univ]; exact Finset.mem_univ x
    simpa using hx
  -- Step 4: Construct the iso.  Map the 4 elements in chain order
  -- to DiamondH4.{bot, mid1, mid2, top}.  Without loss of generality
  -- a ≤ b (otherwise swap a, b — but then internal elements are b, a
  -- and the same mapping works mod swap).
  --
  -- To avoid the WLOG ceremony, we use a direct order-preserving
  -- bijection: ⊥ → bot, smaller-of-{a,b} → mid1, larger → mid2,
  -- ⊤ → top.  Construction:
  rcases h_comp with h_a_le_b | h_b_le_a
  · -- Case a ≤ b: standard mapping.
    -- Set up additional order facts.
    have h_b_not_le_a : ¬ b ≤ a := by
      intro h
      exact hab (le_antisymm h_a_le_b h)
    have h_bot_le_a : (⊥ : H) ≤ a := bot_le
    have h_bot_le_b : (⊥ : H) ≤ b := bot_le
    have h_a_le_top : a ≤ ⊤ := le_top
    have h_b_le_top : b ≤ ⊤ := le_top
    have h_bot_le_top : (⊥ : H) ≤ ⊤ := bot_le
    have h_a_not_le_bot : ¬ a ≤ ⊥ := fun h => ha.1 (le_antisymm h bot_le)
    have h_b_not_le_bot : ¬ b ≤ ⊥ := fun h => hb.1 (le_antisymm h bot_le)
    have h_top_not_le_bot : ¬ (⊤ : H) ≤ ⊥ := fun h => h_bot_ne_top (le_antisymm bot_le h)
    have h_top_not_le_a : ¬ (⊤ : H) ≤ a := fun h => ha.2 (le_antisymm le_top h)
    have h_top_not_le_b : ¬ (⊤ : H) ≤ b := fun h => hb.2 (le_antisymm le_top h)
    refine ⟨{
      toFun := fun x =>
        if x = ⊥ then DiamondH4.bot
        else if x = a then DiamondH4.mid1
        else if x = b then DiamondH4.mid2
        else DiamondH4.top,
      invFun := fun y =>
        match y with
        | .bot => ⊥
        | .mid1 => a
        | .mid2 => b
        | .top => ⊤,
      left_inv := ?_,
      right_inv := ?_,
      map_rel_iff' := ?_
    }⟩
    · -- left_inv
      intro x
      rcases h_universe x with hx | hx | hx | hx
      · subst hx; simp
      · subst hx; simp [ha.1, ha_ne_b]
      · subst hx; simp [hb.1, ha_ne_b.symm, hb_ne_top]
      · subst hx
        have htop_ne_bot : (⊤ : H) ≠ ⊥ := fun h => h_bot_ne_top h.symm
        have htop_ne_a : (⊤ : H) ≠ a := fun h => ha_ne_top h.symm
        have htop_ne_b : (⊤ : H) ≠ b := fun h => hb_ne_top h.symm
        simp [htop_ne_bot, htop_ne_a, htop_ne_b]
    · -- right_inv
      intro y
      have hb_ne_a : b ≠ a := Ne.symm ha_ne_b
      cases y
      · simp
      · simp [ha.1, ha_ne_b]
      · simp [hb.1, hb_ne_a, hb_ne_top]
      · simp [show (⊤ : H) ≠ ⊥ from fun h => h_bot_ne_top h.symm,
              show (⊤ : H) ≠ a from fun h => ha_ne_top h.symm,
              show (⊤ : H) ≠ b from fun h => hb_ne_top h.symm]
    · -- map_rel_iff': order preservation.
      intro x y
      -- Exhaustive: 16 cases on (x, y) ∈ {⊥, a, b, ⊤}².
      -- For each case, both LHS and RHS reduce to true/false in a
      -- decidable way.  We use h_universe to enumerate.
      rcases h_universe x with hx | hx | hx | hx <;>
        rcases h_universe y with hy | hy | hy | hy <;>
        subst hx <;> subst hy <;>
        simp [ha.1, ha_ne_b, ha_ne_b.symm, hb.1, hb_ne_top, ha_ne_top,
          h_bot_le_a, h_bot_le_b, h_bot_le_top, h_a_le_top, h_b_le_top, h_a_le_b,
          h_b_not_le_a, h_a_not_le_bot, h_b_not_le_bot, h_top_not_le_bot,
          h_top_not_le_a, h_top_not_le_b,
          show (⊤ : H) ≠ ⊥ from fun h => h_bot_ne_top h.symm,
          show (⊤ : H) ≠ a from fun h => ha_ne_top h.symm,
          show (⊤ : H) ≠ b from fun h => hb_ne_top h.symm] <;>
        try decide
  · -- Case b ≤ a: symmetric.
    -- Set up additional order facts.
    have h_a_not_le_b : ¬ a ≤ b := by
      intro h
      exact hab (le_antisymm h h_b_le_a)
    have h_bot_le_a : (⊥ : H) ≤ a := bot_le
    have h_bot_le_b : (⊥ : H) ≤ b := bot_le
    have h_a_le_top : a ≤ ⊤ := le_top
    have h_b_le_top : b ≤ ⊤ := le_top
    have h_bot_le_top : (⊥ : H) ≤ ⊤ := bot_le
    have h_a_not_le_bot : ¬ a ≤ ⊥ := fun h => ha.1 (le_antisymm h bot_le)
    have h_b_not_le_bot : ¬ b ≤ ⊥ := fun h => hb.1 (le_antisymm h bot_le)
    have h_top_not_le_bot : ¬ (⊤ : H) ≤ ⊥ := fun h => h_bot_ne_top (le_antisymm bot_le h)
    have h_top_not_le_a : ¬ (⊤ : H) ≤ a := fun h => ha.2 (le_antisymm le_top h)
    have h_top_not_le_b : ¬ (⊤ : H) ≤ b := fun h => hb.2 (le_antisymm le_top h)
    refine ⟨{
      toFun := fun x =>
        if x = ⊥ then DiamondH4.bot
        else if x = b then DiamondH4.mid1
        else if x = a then DiamondH4.mid2
        else DiamondH4.top,
      invFun := fun y =>
        match y with
        | .bot => ⊥
        | .mid1 => b
        | .mid2 => a
        | .top => ⊤,
      left_inv := ?_,
      right_inv := ?_,
      map_rel_iff' := ?_
    }⟩
    · -- left_inv
      intro x
      have hb_ne_a : b ≠ a := Ne.symm ha_ne_b
      rcases h_universe x with hx | hx | hx | hx
      · subst hx; simp
      · subst hx; simp [ha.1, ha_ne_b]
      · subst hx; simp [hb.1, hb_ne_a]
      · subst hx
        have htop_ne_bot : (⊤ : H) ≠ ⊥ := fun h => h_bot_ne_top h.symm
        have htop_ne_a : (⊤ : H) ≠ a := fun h => ha_ne_top h.symm
        have htop_ne_b : (⊤ : H) ≠ b := fun h => hb_ne_top h.symm
        simp [htop_ne_bot, htop_ne_a, htop_ne_b]
    · -- right_inv
      intro y
      have hb_ne_a : b ≠ a := Ne.symm ha_ne_b
      cases y
      · simp
      · simp [hb.1, hb_ne_a]
      · simp [ha.1, ha_ne_b]
      · simp [show (⊤ : H) ≠ ⊥ from fun h => h_bot_ne_top h.symm,
              show (⊤ : H) ≠ a from fun h => ha_ne_top h.symm,
              show (⊤ : H) ≠ b from fun h => hb_ne_top h.symm]
    · -- map_rel_iff': symmetric chain order.
      intro x y
      have hb_ne_a : b ≠ a := Ne.symm ha_ne_b
      rcases h_universe x with hx | hx | hx | hx <;>
        rcases h_universe y with hy | hy | hy | hy <;>
        subst hx <;> subst hy <;>
        simp [ha.1, ha_ne_b, hb_ne_a, hb.1, hb_ne_top, ha_ne_top,
          h_bot_le_a, h_bot_le_b, h_bot_le_top, h_a_le_top, h_b_le_top, h_b_le_a,
          h_a_not_le_b, h_a_not_le_bot, h_b_not_le_bot, h_top_not_le_bot,
          h_top_not_le_a, h_top_not_le_b,
          show (⊤ : H) ≠ ⊥ from fun h => h_bot_ne_top h.symm,
          show (⊤ : H) ≠ a from fun h => ha_ne_top h.symm,
          show (⊤ : H) ≠ b from fun h => hb_ne_top h.symm] <;>
        try decide

end Uniqueness

/-- **DiamondH4 uniqueness as HeytingAlgebra** — packaged form using
    `Heyting` instances.  A 4-element `HeytingAlgebra` that is not
    Boolean is `OrderIso` to `DiamondH4`.

    Derived from `DiamondH4_uniqueness` via the fact that every
    `HeytingAlgebra` is a `DistribLattice` (Mathlib's
    `GeneralizedHeytingAlgebra.toDistribLattice`).  We rebuild the
    invocation explicitly so that the `DistribLattice` and
    `BoundedOrder` instances used by `DiamondH4_uniqueness` are
    *definitionally* the ones derived from `HeytingAlgebra`. -/
theorem DiamondH4_uniqueness_Heyting
    {H : Type} [HeytingAlgebra H] [Fintype H] [DecidableEq H]
    (h_card : Fintype.card H = 4)
    (h_bot_ne_top : (⊥ : H) ≠ ⊤)
    (h_nonBoolean : ¬ ∀ x : H, ∃ y : H, x ⊓ y = ⊥ ∧ x ⊔ y = ⊤) :
    Nonempty (H ≃o DiamondH4) :=
  -- `HeytingAlgebra` gives `DistribLattice` via the standard instance
  -- `GeneralizedHeytingAlgebra.toDistribLattice` and `BoundedOrder`
  -- via `HeytingAlgebra.toBoundedOrder`.
  @DiamondH4_uniqueness H _ _ _ _ h_card h_bot_ne_top h_nonBoolean

/-! ## §9 Connection to `R 4 Prop`

The original conjecture as stated in `Foundation/Doctrine/Instance/Heyting.lean`
§5 read `(TGUTRealisation.heyting).R 4 ≅_{HeytAlg} DiamondH4`.  Under
classical logic, `Fin 4 → Prop` has cardinality `2^4 = 16` (via `Prop ≃ Bool`
classically), so the literal `R 4 Prop ≃ DiamondH4` *as types* is false.

The **intended** statement (per the file's commentary) is the
classification of non-Boolean 4-element Heyting algebras: when
restricted to **4-element** Heyting algebras, non-Boolean ones are
all iso to `DiamondH4`.  Since `Fin 4 → Prop` is *not* itself 4-element
classically, the statement does **not** apply to `R 4 Prop`
directly.  The connection point is at the level of HeytAlg
sub-objects: the *minimum non-Boolean 4-element Heyting subalgebra*
of `Fin 4 → Prop` (e.g., generated by a single non-`⊥` non-`⊤`
proposition under classically-discarding intuitionistic operations)
is what `DiamondH4` represents.

The proper restatement is therefore: -/

/-- **Restated conjecture (provable form)** — among 4-element
    Heyting algebras, `DiamondH4` is the unique non-Boolean one
    (up to `OrderIso`).  This is `DiamondH4_uniqueness_Heyting`
    above. -/
theorem DiamondH4_canonical_non_Boolean_4_anchor :
    ∀ (H : Type) [HeytingAlgebra H] [Fintype H] [DecidableEq H],
      Fintype.card H = 4 →
      (⊥ : H) ≠ ⊤ →
      ¬ (∀ x : H, ∃ y : H, x ⊓ y = ⊥ ∧ x ⊔ y = ⊤) →
      Nonempty (H ≃o DiamondH4) :=
  fun _ _ _ _ h_card h_ne h_nonB =>
    DiamondH4_uniqueness_Heyting h_card h_ne h_nonB

/-! ## §10 Discharging the G5 P7b_heyting uniqueness flag

`Foundation/Doctrine/Instance/Heyting.lean` §5 `P7b_heyting` records
**existence**: `Nonempty DiamondH4` + non-Booleanness of `DiamondH4`.
This file delivers the **uniqueness** companion as the (now
**unconditionally proven**) statement `DiamondH4_uniqueness`.

The status note `**Uniqueness** of `DiamondH4` as "the" minimum
non-Boolean Heyting anchor is **OPEN**` in Heyting.lean's §5 is now
upgraded to:

> **Uniqueness** is **FULLY PROVEN** here: `DiamondH4_uniqueness`
> establishes the classification by Finset enumeration +
> case-exhaustion on 16 (x, y) pairs in the 4-element universe.

The combined existence + uniqueness witness: -/

/-- **The combined G5 P7b-Heyting anchor characterisation** —
    existence (from `Foundation/Doctrine/Instance/Heyting.lean` §5)
    + uniqueness (this file §8). -/
theorem DiamondH4_anchor_existence_and_uniqueness :
    -- existence: DiamondH4 is a 4-element non-Boolean Heyting algebra
    (Fintype.card DiamondH4 = 4 ∧
     (DiamondH4.himp (DiamondH4.himp DiamondH4.mid1 DiamondH4.bot) DiamondH4.bot
        ≠ DiamondH4.mid1)) ∧
    -- uniqueness (conditional): every 4-element non-Boolean Heyting
    -- algebra is `≃o DiamondH4`.
    (∀ (H : Type) [HeytingAlgebra H] [Fintype H] [DecidableEq H],
      Fintype.card H = 4 →
      (⊥ : H) ≠ ⊤ →
      ¬ (∀ x : H, ∃ y : H, x ⊓ y = ⊥ ∧ x ⊔ y = ⊤) →
      Nonempty (H ≃o DiamondH4)) :=
  ⟨⟨DiamondH4_card, DiamondH4_is_nonBoolean⟩,
   DiamondH4_canonical_non_Boolean_4_anchor⟩

/-! ## §11 Summary

What this file delivers (all PROVEN, **0 sorries, 0 axioms**):

1. **§3–§5**: clean `OrderIso DiamondH4 ≃o Chain4` (`Fin 4`) —
   `decide` discharges the order/himp agreement.
2. **§6**: the taxonomy `H4_type = boolean | linear`.
3. **§7**: classification skeleton (PROVEN) — the two combinatorial
   lemmas (`H4_internal_card`, `H4_nonBoolean_middles_comparable`)
   are fully discharged using `Finset.card_eq_four`-style enumeration
   + the 6 inf/sup helper lemmas in §7.1.
4. **§8**: the main `DiamondH4_uniqueness` theorem (PROVEN) — the
   iso `H ≃o DiamondH4` is constructed explicitly via case-analysis
   on `a ≤ b ∨ b ≤ a` (settled by §7), then 16-pair `simp` +
   `decide` discharges `map_rel_iff'`.
5. **§9–§10**: re-statement clarification (`R 4 Prop` *as a type* is
   16-element classically; the intended conjecture is the 4-element
   Heyting algebra classification, which is what we proved here).

**Bottom line**: the conjecture is now **fully formalised and
machine-checked**.  Every non-Boolean 4-element bounded distributive
lattice (equivalently, every non-Boolean 4-element Heyting algebra)
is order-isomorphic to `DiamondH4`.

The G5 P7b_heyting uniqueness flag is **discharged**. -/

end SSBX.Foundation.Order
