/-
# Foundation.R.UniquenessGeneral — T5 polymorphic: P1+P2 ⟹ R-family-over-δ

Per `docs-next/10_formal_形式/gut-roadmap.md` **Phase 2 (T5-A)** and the
2026-05-16 polymorphic generalization (`v0.2 §十一`):

> **GUT-B form**: any structure satisfying the *core* P-closure clauses
> (P1 base cardinality + P2 direct sum) over a δ-realisation is layerwise
> type-equivalent to R-family-over-δ.

This file lifts `T5_A` (the F₂-Boolean specialization in
`UniquenessF2.lean`) to the **δ-polymorphic** statement.  The
F₂-Boolean `T5_A` becomes the **δ = Bool corollary** of `T5_general`.

## Key observation

The proof of `T5_A` only uses:

* `p1_base_card : Fintype.card (carrier 1) = 2`  (= `Fintype.card Bool`)
* `p2_directSum : carrier (N+M) ≃ carrier N × carrier M`
* `fintype` and `decEq` instances
* `R.card_eq` for the target  (` = 2^N`)
* `Fintype.truncEquivOfCardEq`

Replacing `2` with `Fintype.card δ` and lifting `R.card_eq` to
`R.card_eq_general`, the same proof closes the polymorphic statement.
The `BooleanRing` field of `P1P7_Satisfier_F2` is **discarded** in the
F₂ proof (it is consumed by ring-iso refinements like
`T5_A_ringEquiv_at_4`, not by the layerwise statement).

## What this delivers

* `P1P7_Core (δ : Type*) [Fintype δ] [DecidableEq δ]` — the polymorphic
  minimum-data structure (4 fields: carrier family + Fintype/decEq +
  zero-card + base-card + direct-sum).
* `R.card_eq_general` — `|R N δ| = (|δ|)^N` for any Fintype δ.
* `T5_general` — `S.carrier N ≃ R N δ` layerwise.
* `T5_general_at_Bool` — corollary at δ = Bool (matches `T5_A` shape).
* `T5_general_at_Distinction` — corollary at δ = Distinction.
* `T5_general_at_Fin` — corollary at δ = Fin n (n-ary distinction).
* `T5_general_at_ZMod` — corollary at δ = ZMod p.

## Doctrinal anchor

* `docs-next/10_formal_形式/gut-roadmap.md` v0.2 §十一 (polymorphic T5
  generalization; F₂-Boolean → general δ).
* `docs-next/10_formal_形式/wen-substrate/02-parametric.md` (T2 weak
  vs T1 strong universality, parametric over δ).
* `Foundation/R/Basic.lean` — `R N δ := Fin N → δ` polymorphic carrier.
* `Foundation/R/UniquenessF2.lean` — `T5_A` F₂-Boolean specialization
  (now derivable as a corollary).
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.Distinction
import SSBX.Foundation.R.UniquenessF2
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card

namespace SSBX.Foundation.R.UniquenessGeneral

open SSBX.Foundation.R

/-! ## § 0 Polymorphic Fintype + Inhabited instances

Local instances making the polymorphic statements well-typed:

* `Fintype (R N δ)` for any `Fintype δ` — generalizes `R.instFintype`
  (which is hardcoded for `R N` = `R N Bool`).
* `Inhabited Distinction` — for δ=Distinction instances of T5_general. -/

/-- Polymorphic Fintype for `R N δ` over any Fintype δ. -/
instance instFintypeRGeneral (N : ℕ) (δ : Type) [Fintype δ] : Fintype (R N δ) :=
  inferInstanceAs (Fintype (Fin N → δ))

/-- Polymorphic DecidableEq for `R N δ` over any DecidableEq δ. -/
instance instDecEqRGeneral (N : ℕ) (δ : Type) [DecidableEq δ] :
    DecidableEq (R N δ) :=
  inferInstanceAs (DecidableEq (Fin N → δ))

/-- `Distinction` is inhabited at `Distinction.o`. -/
instance : Inhabited Distinction := ⟨Distinction.o⟩

/-! ## § 1 Polymorphic cardinality of `R N δ`

The R-family over any Fintype δ has cardinality `(Fintype.card δ)^N`.
This generalizes `R.card_eq` (which is the δ = Bool specialization
giving `2^N`). -/

/-- **Polymorphic R cardinality** — `|R N δ| = (|δ|)^N` for any Fintype δ.

    Generalizes `R.card_eq` from δ=Bool to arbitrary Fintype δ.  Per
    `Foundation/R/Basic.lean` v1.4 (R is δ-polymorphic via the default
    argument `δ := Bool`).  Note: `R` is `Type`-not-`Type*`-polymorphic
    (the carrier is `Fin N → δ` and only makes sense at the lowest
    universe level), so `δ : Type`. -/
theorem R.card_eq_general (N : ℕ) (δ : Type) [Fintype δ] :
    Fintype.card (R N δ) = (Fintype.card δ) ^ N := by
  show Fintype.card (Fin N → δ) = (Fintype.card δ) ^ N
  rw [Fintype.card_fun, Fintype.card_fin]

/-! ## § 2 The polymorphic structure `P1P7_Core`

The minimum data needed for layerwise type-equivalence:

* A carrier family `carrier : ℕ → Type` with Fintype + decidable
  equality per layer.
* Base layer has the same cardinality as δ (P1).
* Origin layer is unique-element (cardinality 1) — derivable from P2
  + base-card, but exposed as a structure field for ergonomic access.
* Direct-sum decomposition: `carrier (N+M) ≃ carrier N × carrier M` (P2).

This is the **δ-independent core** of `P1P7_Satisfier_F2` from
`UniquenessF2.lean`.  The F₂-specific extras (BooleanRing, P3 bilinear,
P5/P7b ring, P6/P7a alphabet) layer on top of this core.
-/

/-- **P1P7_Core δ** — δ-polymorphic minimum-data structure for the
    layerwise T5 statement.  Any δ with `[Fintype]` and
    `[DecidableEq]` works; the canonical cases are:

    * δ = Bool — F₂-Boolean classical (existing `P1P7_Satisfier_F2`)
    * δ = Distinction — abstract o/x substrate
    * δ = Fin n — n-ary distinction
    * δ = ZMod p — p-ary distinction (prime p)

    The conclusion of `T5_general` is: any `S : P1P7_Core δ` has
    `S.carrier N ≃ R N δ` for every N. -/
structure P1P7_Core (δ : Type) [Fintype δ] [DecidableEq δ] where
  /-- The carrier family — an arbitrary `ℕ → Type`, to be forced to
      `R · δ` by the structure axioms. -/
  carrier : ℕ → Type
  /-- Each layer is finite. -/
  fintype : ∀ N, Fintype (carrier N)
  /-- Each layer has decidable equality. -/
  decEq : ∀ N, DecidableEq (carrier N)
  /-- **P1 base cardinality** — the base layer has the same cardinality
      as δ.  For δ = Bool this gives `|carrier 1| = 2` (the F₂ anchor).

      Note: this is the *general* form of P1.  Specific δ-instances may
      additionally pin the *ring* or *order* structure on `carrier 1`. -/
  p1_base_card : Fintype.card (carrier 1) = Fintype.card δ
  /-- **P2 direct sum** — `carrier (N + M) ≃ carrier N × carrier M`. -/
  p2_directSum : ∀ N M, carrier (N + M) ≃ carrier N × carrier M

namespace P1P7_Core

variable {δ : Type} [Fintype δ] [DecidableEq δ]

/-- **Origin layer has cardinality 1.**  Derived from `p2_directSum 0 1`
    and `p1_base_card`: the equivalence `carrier 1 ≃ carrier 0 × carrier 1`
    plus `|carrier 1| = |δ|` forces `|carrier 0| = 1` (assuming `|δ| ≠ 0`,
    which is automatic for `Fintype δ` if `δ` is inhabited; we handle the
    empty-δ case explicitly via Nat division).

    For all canonical δ (Bool, Distinction, Fin (n+1), ZMod p), `δ` is
    inhabited, so this is non-vacuous. -/
theorem carrier_zero_card (S : P1P7_Core δ) [Inhabited δ] :
    letI : Fintype (S.carrier 0) := S.fintype 0
    Fintype.card (S.carrier 0) = 1 := by
  letI : Fintype (S.carrier 0) := S.fintype 0
  letI : Fintype (S.carrier 1) := S.fintype 1
  have e : S.carrier 1 ≃ S.carrier 0 × S.carrier 1 := S.p2_directSum 0 1
  have h1 : Fintype.card (S.carrier 1)
          = Fintype.card (S.carrier 0) * Fintype.card (S.carrier 1) := by
    have := Fintype.card_congr e
    rw [Fintype.card_prod] at this
    exact this
  have hC1 : Fintype.card (S.carrier 1) = Fintype.card δ := S.p1_base_card
  have hδ_pos : 0 < Fintype.card δ := Fintype.card_pos
  rw [hC1] at h1
  -- h1 : |δ| = |carrier 0| * |δ|.  Divide by |δ|.
  -- Use Nat.eq_one_of_mul_eq_self_right or similar.
  have : Fintype.card (S.carrier 0) * Fintype.card δ = 1 * Fintype.card δ := by
    rw [one_mul]; exact h1.symm
  exact Nat.eq_of_mul_eq_mul_right hδ_pos this

/-- **Successor cardinality step.**  For any `n : ℕ`,
    `|carrier (n + 1)| = |δ| * |carrier n|`.  Derived from
    `p2_directSum n 1` + `p1_base_card`. -/
theorem carrier_succ_card (S : P1P7_Core δ) (n : ℕ) :
    letI : Fintype (S.carrier n) := S.fintype n
    letI : Fintype (S.carrier (n + 1)) := S.fintype (n + 1)
    Fintype.card (S.carrier (n + 1))
      = Fintype.card δ * Fintype.card (S.carrier n) := by
  letI : Fintype (S.carrier n) := S.fintype n
  letI : Fintype (S.carrier 1) := S.fintype 1
  letI : Fintype (S.carrier (n + 1)) := S.fintype (n + 1)
  have h1 : Fintype.card (S.carrier (n + 1))
          = Fintype.card (S.carrier n) * Fintype.card (S.carrier 1) := by
    rw [Fintype.card_congr (S.p2_directSum n 1), Fintype.card_prod]
  have hC1 : Fintype.card (S.carrier 1) = Fintype.card δ := S.p1_base_card
  rw [h1, hC1]
  ring

/-- **Polymorphic cardinality at every layer** — `|carrier N| = (|δ|)^N`.

    By induction on N: base case is `carrier_zero_card`; inductive
    step is `carrier_succ_card`.  This is the polymorphic analogue of
    `P1P7_Satisfier_F2.carrier_card_eq` (= `2^N`). -/
theorem carrier_card_eq (S : P1P7_Core δ) [Inhabited δ] (N : ℕ) :
    letI : Fintype (S.carrier N) := S.fintype N
    Fintype.card (S.carrier N) = (Fintype.card δ) ^ N := by
  induction N with
  | zero =>
    letI : Fintype (S.carrier 0) := S.fintype 0
    simpa using S.carrier_zero_card
  | succ n ih =>
    letI : Fintype (S.carrier n) := S.fintype n
    letI : Fintype (S.carrier (n + 1)) := S.fintype (n + 1)
    have hSucc := S.carrier_succ_card n
    rw [hSucc, ih, pow_succ]
    ring

end P1P7_Core

/-! ## § 3 The polymorphic T5 theorem

The main result: any `P1P7_Core δ` is layerwise type-equivalent to
R-family-over-δ.  This is the **GUT-B layerwise form** — the
generalization of `T5_A` (F₂-Boolean) to any Fintype δ.
-/

/-- **T5-general (GUT-B layerwise form)** — δ-polymorphic uniqueness.

    For any δ with `[Fintype]`, `[DecidableEq]`, and `[Inhabited]`,
    any structure `S : P1P7_Core δ` is layerwise type-equivalent to
    R-family-over-δ:

        ∀ N : ℕ, Nonempty (S.carrier N ≃ R N δ)

    **Specializations** (corollaries below):

    * δ = Bool → matches `T5_A` from `UniquenessF2.lean`.
    * δ = Distinction → abstract o/x substrate equivalent to F₂.
    * δ = Fin (n + 1) → (n+1)-ary distinction tower.
    * δ = ZMod p (p prime) → p-ary modular substrate.

    Per `docs-next/10_formal_形式/gut-roadmap.md` v0.2 §十一. -/
theorem T5_general {δ : Type} [Fintype δ] [DecidableEq δ] [Inhabited δ]
    (S : P1P7_Core δ) (N : ℕ) :
    Nonempty (S.carrier N ≃ R N δ) := by
  letI : Fintype (S.carrier N) := S.fintype N
  letI : DecidableEq (S.carrier N) := S.decEq N
  have hCardR : Fintype.card (R N δ) = (Fintype.card δ) ^ N :=
    R.card_eq_general N δ
  have hCardCarrier : Fintype.card (S.carrier N) = (Fintype.card δ) ^ N :=
    S.carrier_card_eq N
  have hcards : Fintype.card (S.carrier N) = Fintype.card (R N δ) :=
    hCardCarrier.trans hCardR.symm
  exact (Fintype.truncEquivOfCardEq (α := S.carrier N) (β := R N δ) hcards).nonempty

/-! ## § 4 Specializations at canonical δ

We provide ergonomic corollaries at the four canonical δ-instances:
Bool, Distinction, Fin n, ZMod p.  Each is a direct application of
`T5_general` with the appropriate Fintype/DecidableEq instances.
-/

/-- **δ = Bool corollary** — F₂-Boolean classical case.  Matches the
    statement form of `T5_A` from `UniquenessF2.lean` modulo the
    `P1P7_Core Bool` vs `P1P7_Satisfier_F2` distinction.  The forgetful
    map `P1P7_Satisfier_F2 → P1P7_Core Bool` (defined below) makes
    `T5_A` an explicit corollary of `T5_general`. -/
theorem T5_general_at_Bool (S : P1P7_Core Bool) (N : ℕ) :
    Nonempty (S.carrier N ≃ R N) :=
  T5_general S N

/-- **δ = Distinction corollary** — the abstract o/x substrate case.

    Per `Foundation/R/Distinction.lean`: `Distinction` is the
    primitive 2-element type {o, x}.  Any `P1P7_Core Distinction` is
    layerwise equivalent to `R N Distinction = Fin N → Distinction`. -/
theorem T5_general_at_Distinction (S : P1P7_Core Distinction) (N : ℕ) :
    Nonempty (S.carrier N ≃ R N Distinction) :=
  T5_general S N

/-- **δ = Fin (n+1) corollary** — (n+1)-ary distinction tower.

    For δ = Fin (n+1), the R-family becomes `R N (Fin (n+1)) =
    Fin N → Fin (n+1)`, the canonical n+1-ary substrate.  Useful for
    encoding multi-valued logics (e.g. n = 2 gives ternary, n = 3
    gives quaternary, etc.). -/
theorem T5_general_at_Fin (n : ℕ) (S : P1P7_Core (Fin (n + 1))) (N : ℕ) :
    Nonempty (S.carrier N ≃ R N (Fin (n + 1))) :=
  T5_general S N

/-- **δ = ZMod (n+2) corollary** — modular-arithmetic substrate (n+2
    ≥ 2 to ensure non-trivial).

    For δ = ZMod p (p prime), `R N (ZMod p)` is the p-ary symplectic
    space — the natural carrier for stabilizer formalism over prime p.
    The Bool case (p = 2) recovers the F₂ canonical R-family. -/
theorem T5_general_at_ZMod (n : ℕ) (S : P1P7_Core (ZMod (n + 2))) (N : ℕ) :
    Nonempty (S.carrier N ≃ R N (ZMod (n + 2))) := by
  haveI : NeZero (n + 2) := ⟨by omega⟩
  exact T5_general S N

/-! ## § 5 Forgetful map from `P1P7_Satisfier_F2` to `P1P7_Core Bool`

The F₂-Boolean structure `P1P7_Satisfier_F2` (from `UniquenessF2.lean`)
contains the core data plus F₂-specific extras (BooleanRing, P3
bilinear, P5/P7b ring iso, P6/P7a alphabet).  The forgetful map below
strips the extras and produces a `P1P7_Core Bool`, witnessing that
**`T5_A` is a corollary of `T5_general`**.
-/

/-- **Forgetful map** — every `P1P7_Satisfier_F2` is a `P1P7_Core Bool`
    by forgetting the F₂-specific extras (BooleanRing, P3-7b
    structures). -/
def forgetF2ToCore (S : UniquenessF2.P1P7_Satisfier_F2) :
    P1P7_Core Bool where
  carrier := S.carrier
  fintype := S.fintype
  decEq := S.decEq
  p1_base_card := S.p1_base_card.trans Fintype.card_bool.symm
  p2_directSum := S.p2_directSum

/-- **`T5_A` as a corollary of `T5_general`**.

    The F₂-Boolean uniqueness theorem `T5_A` from `UniquenessF2.lean`
    is recovered by applying `T5_general` at δ = Bool to the forgetful
    image `forgetF2ToCore`. -/
theorem T5_A_from_general (S : UniquenessF2.P1P7_Satisfier_F2) (N : ℕ) :
    Nonempty (S.carrier N ≃ R N) :=
  T5_general (forgetF2ToCore S) N

/-! ## § 6 Aggregator — what GUT-B layerwise delivers

This file generalizes the **layerwise type-equivalence** form of
`T5_A` from F₂-Boolean to **any Fintype + DecidableEq + Inhabited δ**.

What is *not* generalized here (left to T5-B / T5-C refinement passes):

* **Ring-iso refinement at `N = 4`** — F₂-specific via `Mat2F2`.  For
  general δ, the analogous "operation algebra at the smallest
  non-commutative layer" depends on whether δ has a ring / field
  structure (algebraic class) or not (general δ).
* **Bilinear classification (P3)** — F₂-specific via `dot`/`sigma`/`arf`.
  For δ = k a field with char(k) = 2, the same forms apply; for
  char(k) ≠ 2, the Arf invariant is replaced by the discriminant.
* **P6/P7a alphabet pinning** — uses the cardinality-4 / 8 anchors,
  which generalize as `(|δ|)² = 4` only for δ = Bool.

What **is** generalized (this file's content):

* `R.card_eq_general` — polymorphic cardinality `|R N δ| = (|δ|)^N`.
* `P1P7_Core δ` — polymorphic minimum-data structure.
* `T5_general` — δ-polymorphic layerwise type-equivalence.
* Four canonical δ-corollaries: Bool, Distinction, Fin (n+1), ZMod (n+2).
* `T5_A_from_general` — the F₂ case is now a derived corollary.

This satisfies the **GUT-B (parametric, layerwise form)** claim of
`gut-roadmap.md` v0.2 §十一. -/

/-- **GUT-B layerwise aggregator** — the polymorphic content of this
    file packaged as a single theorem.  For any Fintype + DecidableEq +
    Inhabited δ and any `P1P7_Core δ`:

    * the carrier at every layer is in bijection with `R N δ`;
    * carrier cardinality matches the F-polynomial `(|δ|)^N`;
    * the F₂ specialization `T5_A` is derived (corollary
      `T5_A_from_general` above).

    Per `docs-next/10_formal_形式/gut-roadmap.md` v0.2 §十一 GUT-B
    (parametric layerwise form). -/
theorem GUT_B_layerwise {δ : Type} [Fintype δ] [DecidableEq δ] [Inhabited δ]
    (S : P1P7_Core δ) :
    (∀ N : ℕ, Nonempty (S.carrier N ≃ R N δ))
  ∧ (∀ N : ℕ,
      letI : Fintype (S.carrier N) := S.fintype N
      Fintype.card (S.carrier N) = (Fintype.card δ) ^ N)
  ∧ (∀ N : ℕ, Fintype.card (R N δ) = (Fintype.card δ) ^ N) :=
  ⟨T5_general S, S.carrier_card_eq, fun N => R.card_eq_general N δ⟩

end SSBX.Foundation.R.UniquenessGeneral
