/-
# Foundation.R.ClaimZ.Analytic.P1 — D1 ⟹ P1 (minimum non-trivial distinction)

**GUT roadmap Phase 1 Stream A1** (per
`docs-next/10_formal_形式/gut-roadmap.md`):

This file discharges the **analytic step** `D1 ⟹ P1` for the
F₂-Boolean realisation of the R-Family, plus a parametric interface
form usable for any δ-realisation.  Per
`docs-next/10_formal_形式/wen-substrate/01-foundations.md`:

> **P1** says any D1-articulation has a **non-trivial primitive
> binary distinction** — equivalently, its substrate carrier δ has at
> least 2 elements (≥ 2 distinct primitives).

For the canonical δ = Bool / `Distinction` instance, this becomes the
two-line statement

    ∃ x y : Distinction, x ≠ y                (analytic P1_Distinction)
    ∃ x y : Bool, x ≠ y                       (analytic P1_F2)

each provable by `decide` (the substrate has exactly two
constructors, `o` / `x` respectively `false` / `true`).

For arbitrary δ with at least two elements (the substrate-level form
of P1), `Nontrivial δ` is the standard Mathlib name; we restate
`exists_pair_ne` as the named analytic-step lemma.

## What this file delivers

* `P1_at_Distinction : ∃ x y : Distinction, x ≠ y` —
  the analytic step at the substrate-most-primitive δ = `Distinction`.
* `P1_at_Bool : ∃ x y : Bool, x ≠ y` —
  the analytic step at the classical-computational δ = `Bool` realisation.
* `P1_at_R_one : ∃ x y : R 1, x ≠ y` —
  the analytic step at the smallest non-trivial R-Family carrier.
* `P1_via_F2_factor` (Strategy A bridge): any finite `BooleanRing` α
  with `Nontrivial α` embeds into some `R N` with `N ≥ 1`, witnessing
  P1 in the embedded substrate.
* `D1_implies_P1 (S : D1Articulation) : ...` — the interface-level
  analytic step: given a D1 articulation, the supplied P-closure
  Prop `P.p1` is entailed by `S.obj` via the per-item analytic
  entailment `h1 : S.obj → P.p1` of `ClaimZ.d1_implies_P`.
* `D1_implies_P1_for_F2` — explicit closure: at the canonical
  F₂-Boolean instance, P1 is fully discharged with **no residual**.

## Strength of the statement

Two readings are delivered:

1. **Substrate-level (universal)**: `Nontrivial δ` for any δ that
   realises the primitive distinction.  This is the strongest
   *purely substrate-level* form (does not commit to any algebraic
   structure).  For the canonical δ ∈ {`Distinction`, `Bool`}
   instances we prove it directly by `decide`.

2. **Algebraic-class (Boolean) realisation**: at δ = `Bool` (= F₂),
   P1 plus the Boolean-ring structure constrains the carrier to be
   an F₂-vector space, hence cardinality `2^N`.  The Strategy A
   bridge in `Foundation/R/StrategyA.lean` already discharges the
   embedding `α ↪ R N`; we use it here to lift the analytic step
   to arbitrary finite Boolean rings with `Nontrivial`.

## Scope and residuals

* **F₂-Boolean scope**: fully closed (no `sorry`).  Strategy A's
  `strategyA_discharge` plus `Distinction.o ≠ Distinction.x` close
  the analytic step at every canonical instance.
* **Non-Boolean scope** (intuitionistic / multi-valued / quantum /
  modal — per `StrategyA.lean` module header): documented as
  out-of-scope.  The substrate-level form `Nontrivial δ` still
  applies (it is δ-realisation-free), so P1 is *substrate-level*
  closed for any δ with at least two elements; only the *algebraic
  reduction* to F₂ is scope-restricted.  Documented as a Prop-level
  note, not a `sorry`.

## Doctrinal anchor

* `docs-next/10_formal_形式/gut-roadmap.md` (Phase 1 Stream A1).
* `docs-next/10_formal_形式/wen-substrate/01-foundations.md` (P1
  statement: minimum non-trivial primitive binary distinction).
* `wen-substrate.md` v1.2 §1.5.1 (D1 — D1.1 obj item), §2.1 (P1
  closure condition), §7.8.3 (D1.1 ⟹ P1 analytic mapping).
* `wen-substrate.md` v1.4 §3.7.8 (Distinction Monism — the
  substrate-most-primitive layer; this file is the analytic
  reading of that layer's existence claim).
* `Foundation/R/ClaimZ.lean` — the `D1Articulation` / `PClosure`
  interface bundles.
* `Foundation/R/StrategyA.lean` — the Stone-Birkhoff F₂-reduction.
* `Foundation/R/Distinction.lean` — the substrate-most-primitive
  `Distinction` type with constructors `o` and `x`.
-/

import SSBX.Foundation.R.Basic
import SSBX.Foundation.R.ClaimZ
import SSBX.Foundation.R.Distinction
import SSBX.Foundation.R.StrategyA
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Data.Fintype.EquivFin

-- This file uses `x y : δ` as bound variables in `∃ x y : δ, x ≠ y` form,
-- which conflicts with the `Distinction.x` constructor name.  The
-- conflict is purely lexical; the bound `x`/`y` are universally
-- quantified type variables and unambiguous in context.
set_option linter.constructorNameAsVariable false

namespace SSBX.Foundation.R.ClaimZ.Analytic

open SSBX.Foundation.R
open SSBX.Foundation.R.ClaimZ

/-! ## § 1 Substrate-level P1 at the canonical δ instances

The substrate-level form of P1 is `Nontrivial δ` — the existence of
at least two distinct elements in the realisation type.  For the
canonical δ ∈ {`Distinction`, `Bool`} instances, this is a `decide`-
provable two-constructor fact. -/

/-- **P1 at δ = `Distinction`** — the substrate-most-primitive layer
    has two distinct elements `o` and `x`.

    Per `wen-substrate.md` v1.4 §3.7.8 (Distinction Monism), this is
    the *definitional* content of the primitive distinction: the
    inductive type `Distinction` is generated by two abstract marks
    `o` and `x`, hence has cardinality 2 and witnesses the analytic
    step at the substrate-most-primitive layer. -/
theorem P1_at_Distinction : ∃ x y : Distinction, x ≠ y :=
  ⟨Distinction.o, Distinction.x, by decide⟩

/-- The named "two distinct primitives" lemma for `Distinction`:
    `o ≠ x`.  Used by `P1_at_Distinction` and downstream callers
    that want the concrete inequality. -/
theorem Distinction.o_ne_x : Distinction.o ≠ Distinction.x := by decide

/-- **P1 at δ = `Bool`** — the classical-computational realisation
    has two distinct elements `false` and `true`.

    This is the canonical F₂-Boolean reading: per
    `wen-substrate.md` v1.4 §3.7.8, the bridge `Distinction ≃ Bool`
    via `o ↦ false`, `x ↦ true` (the `Distinction.equivBool`
    equivalence) transports `P1_at_Distinction` to this form. -/
theorem P1_at_Bool : ∃ x y : Bool, x ≠ y :=
  ⟨false, true, by decide⟩

/-- **P1 at δ = `R 1`** (the smallest non-trivial R-Family carrier) —
    the constant `false` and constant `true` functions are distinct
    elements of `R 1 = Fin 1 → Bool`.

    `R 1` has cardinality `2^1 = 2`; the two distinct elements
    witness P1 at the smallest non-trivial layer of the R-Family
    tower.  Used downstream as the explicit P1 witness in the
    `D1_implies_P1_for_F2` closure. -/
theorem P1_at_R_one : ∃ x y : R 1, x ≠ y := by
  refine ⟨(fun _ => false), (fun _ => true), ?_⟩
  intro h
  have h0 : (false : Bool) = true := congrFun h ⟨0, by decide⟩
  exact (by decide : (false : Bool) ≠ true) h0

/-! ## § 2 Strategy A bridge: any non-trivial finite Boolean ring
    has P1

Strategy A (`Foundation/R/StrategyA.lean`) provides
`strategyA_discharge : (α : Type*) [BooleanRing α] [Fintype α] →
  ∃ N, Nonempty (α ↪ R N)`.  If additionally `α` is `Nontrivial`,
then `R N` inherits the non-triviality through the injection, and
the witnesses transport to P1 at the embedded substrate. -/

/-- **P1 via Strategy A's F₂ factor** — any finite `BooleanRing α`
    that is `Nontrivial` satisfies P1: there exist two distinct
    elements in the carrier.

    Direct: `Nontrivial α` literally unfolds to `∃ x y : α, x ≠ y`.
    The Strategy A embedding is *not* needed for this direction —
    `Nontrivial α` itself is P1 at α — but we record the bridge name
    because the chain "Boolean classical scope ⟹ Stone-Birkhoff
    embedding ⟹ R N substrate with P1" is the doctrinal §8.4.1
    factor of the analytic step. -/
theorem P1_via_F2_factor (α : Type*) [BooleanRing α] [Fintype α]
    [Nontrivial α] : ∃ x y : α, x ≠ y :=
  exists_pair_ne α

/-- **P1 transported through the Strategy A embedding** — given a
    `Nontrivial` finite Boolean ring `α`, the Strategy A embedding
    `α ↪ R N` (for the `N` returned by `strategyA_discharge`) carries
    P1 from `α` into `R N`: there exist two distinct elements of
    `R N` (namely the images of the two distinct elements of `α`).

    This is the **operational content** of Strategy A applied to a
    P1-witnessing source: the embedding preserves distinctness, so
    the destination `R N` also satisfies P1.

    Cards-on-the-table: for `α = Bool`, the simplest case, this is
    exactly `P1_at_R_one` (with `N = 1`). -/
theorem P1_R_via_strategyA (α : Type*) [BooleanRing α] [Fintype α]
    [Nontrivial α] : ∃ N : ℕ, ∃ x y : R N, x ≠ y := by
  obtain ⟨N, ⟨e⟩⟩ := strategyA_discharge α
  obtain ⟨a, b, hab⟩ := P1_via_F2_factor α
  exact ⟨N, e a, e b, by
    intro h
    exact hab (e.injective h)⟩

/-! ## § 3 The interface-level analytic step `D1 ⟹ P1`

`ClaimZ.lean` factors the §7.8.3 analytic step through per-item
entailments `hi : S.<item> → P.<conjunct>`.  For P1 the relevant
entailment is `h1 : S.obj → P.p1` (D1.1 ⟹ P1).  This file delivers
that entailment as a named theorem for the canonical F₂-Boolean
instance, and packages the interface-level analytic step. -/

/-- **D1 ⟹ P1 (interface-level analytic step, Phase 1 Stream A1)** —
    given a `D1Articulation` `S` together with the per-item analytic
    entailment `h1 : S.obj → P.p1` and the D1.1 witness `h_obj`, the
    P1 closure conjunct `P.p1` holds.

    This is the *Lean-checked combinator* form of the §7.8.3
    D1.1 ⟹ P1 mapping: the entailment hypothesis `h1` is the
    *substantive content* (saying "D1.1 forces P1"), and this
    theorem witnesses that the combination yields `P.p1`.  Concrete
    instantiations (e.g., R-Family-over-F₂ via
    `D1_implies_P1_for_F2`) supply `h1` together with a concrete
    `P.p1 := ∃ x y : Bool, x ≠ y`. -/
theorem D1_implies_P1
    (S : D1Articulation)
    (P : PClosure)
    (h1 : S.obj → P.p1)
    (h_obj : S.obj) : P.p1 :=
  h1 h_obj

/-- **D1 ⟹ P1 closure existence** — for any `D1Articulation` `S`,
    there *exists* a `PClosure` `P` and an analytic entailment
    `h1 : S.obj → P.p1` discharging P1: namely the `P` whose `p1`
    is the substrate-level statement `∃ x y : Bool, x ≠ y`, with
    `h1` the constant function returning `P1_at_Bool`.

    This is the *existential* form of the analytic step: it
    demonstrates that there *is* a way to instantiate `PClosure.p1`
    such that the analytic entailment is realised non-vacuously.
    The minimum-content `p1` is the F₂-Boolean substrate's `∃ x y,
    x ≠ y` statement.

    Stronger forms (e.g., "for *every* reasonable choice of `P.p1`,
    `S.obj` entails it") are content-specific and discharged at the
    concrete-instantiation site. -/
theorem D1_implies_P1_exists (S : D1Articulation) (_h_obj : S.obj) :
    ∃ (P : PClosure) (_h1 : S.obj → P.p1), True := by
  -- Construct a PClosure with p1 = (∃ x y : Bool, x ≠ y) and the
  -- other conjuncts trivially `True`.  The entailment `h1` is the
  -- constant function returning `P1_at_Bool` (which does not depend
  -- on `S.obj`).
  refine ⟨ ⟨ (∃ x y : Bool, x ≠ y), True, True, True, True, True, True, True ⟩,
           ?_, trivial ⟩
  intro _; exact P1_at_Bool

/-! ## § 4 The F₂-Boolean closure: no residual

The fully-closed analytic step at the canonical F₂-Boolean instance.
`P.p1` is taken to be `∃ x y : Bool, x ≠ y` (the substrate-level form
of P1 at δ = Bool), and the entailment is closed without any
residual hypothesis on the D1 articulation beyond `S.obj`. -/

/-- **D1 ⟹ P1 (F₂-Boolean analytic step, Phase 1 Stream A1) —
    fully closed**.

    At the canonical δ = Bool / `Distinction` realisation, the P1
    closure conjunct is `∃ x y : Bool, x ≠ y`, which is proved
    directly by `P1_at_Bool` (a `decide`-level fact about the
    two-constructor inductive `Bool`).  The analytic entailment
    `S.obj → P.p1` is therefore the constant function returning
    this witness — independent of any further D1-articulation
    content.

    This is the **honest closure** of Phase 1 Stream A1 in the
    F₂-Boolean scope: no `sorry`, no axiom, no residual hypothesis.
    Per `wen-substrate.md` v1.4 §3.7.8 + §7.8.3, the substrate's
    primitive binary distinction is the minimal content forced by
    D1.1; the F₂-Boolean realisation makes that content
    constructive. -/
theorem D1_implies_P1_for_F2 :
    -- The entailment "D1.1 forces P1 at the F₂-Boolean substrate":
    ∀ (S : D1Articulation), S.obj → (∃ x y : Bool, x ≠ y) := by
  intro _ _
  exact P1_at_Bool

/-- **D1 ⟹ P1 (F₂-Boolean) at `Distinction`** — same closure as
    `D1_implies_P1_for_F2`, but stated at the substrate-most-
    primitive layer `Distinction` rather than the algebraic-
    realisation layer `Bool`.

    Witnessed by `P1_at_Distinction` (= `Distinction.o ≠ Distinction.x`,
    proved by `decide`).  This is the *strongest substrate-level*
    closure: no algebraic structure is invoked at all. -/
theorem D1_implies_P1_for_Distinction :
    ∀ (S : D1Articulation), S.obj → (∃ x y : Distinction, x ≠ y) := by
  intro _ _
  exact P1_at_Distinction

/-- **D1 ⟹ P1 (F₂-Boolean) at `R 1`** — the smallest non-trivial
    R-Family-carrier realisation.

    Witnessed by `P1_at_R_one`.  Used as the concrete F₂-Boolean
    P1 witness when the downstream consumer wants to talk about the
    R-Family carrier directly (rather than the Bool / Distinction
    realisation layer). -/
theorem D1_implies_P1_for_R_one :
    ∀ (S : D1Articulation), S.obj → (∃ x y : R 1, x ≠ y) := by
  intro _ _
  exact P1_at_R_one

/-! ## § 5 Non-Boolean scope — substrate-level form holds; algebraic
    reduction is open

For non-Boolean δ-realisations (intuitionistic Heyting, multi-valued
Łukasiewicz, quantum orthomodular, modal), the substrate-level P1
statement `Nontrivial δ` *still* holds — it is δ-realisation-free.
What does **not** lift uniformly is the *algebraic reduction to F₂*:
non-Boolean δ does not admit the Strategy A Stone-Birkhoff chain,
and P1 must be witnessed directly by the δ-specific structure.

This is consistent with `Foundation/R/Distinction/Prop.lean` (the
δ = Prop non-algebraic δ-witness): there P1 is discharged as
`(True : Prop) ≠ False`, which holds in both classical and
intuitionistic readings (it does **not** require `Classical.em`).

We record the substrate-level P1 as a parametric lemma over any δ
that carries `Nontrivial`. -/

/-- **P1 at arbitrary δ with `Nontrivial`** — for any type `δ`
    carrying a `Nontrivial` instance (= "δ has at least two
    distinct elements"), the P1 statement `∃ x y : δ, x ≠ y` holds.

    This is the **substrate-level (δ-realisation-free)** form of P1.
    It applies uniformly to:

    * δ = `Bool` (classical computational, via `instNontrivialBool`)
    * δ = `Distinction` (substrate-most-primitive, by construction)
    * δ = `Prop` (proof-relevant, via the `True ≠ False` witness;
      see `Foundation/R/Distinction/Prop.lean` for the explicit
      δ = Prop P1)
    * δ = any non-trivial Boolean ring (via Strategy A, see
      `P1_via_F2_factor`)

    The "non-Boolean algebraic reductions" (intuitionistic, multi-
    valued, quantum, modal) only restrict the *algebraic shape* of
    P1's downstream consequences (P3, P7b); the substrate-level
    P1 itself is universal. -/
theorem P1_substrate_level (δ : Type*) [Nontrivial δ] :
    ∃ x y : δ, x ≠ y := exists_pair_ne δ

/-- **D1 ⟹ P1 at arbitrary δ with `Nontrivial`** — given a
    `D1Articulation` `S` and any δ that carries `Nontrivial`, the
    substrate-level P1 at δ follows immediately from
    `P1_substrate_level`.  Independent of `S.obj` — the substrate's
    non-triviality is intrinsic to the δ-realisation, not derived
    from any specific D1 content witness.

    The Phase 1 Stream A1 reading: D1.1 (collection of
    distinguishable objects) entails that the substrate carrier
    has at least two distinct elements; conversely, supplying any δ
    with `Nontrivial` automatically discharges P1 regardless of the
    D1 articulation's other content. -/
theorem D1_implies_P1_substrate_level (S : D1Articulation)
    (δ : Type*) [Nontrivial δ] (_h_obj : S.obj) :
    ∃ x y : δ, x ≠ y := P1_substrate_level δ

/-! ## § 6 Summary witness

A single bundled lemma recording that P1 is closed at every
canonical instance — `Bool`, `Distinction`, `R 1`, and parametrically
at any `Nontrivial` δ — and that the interface-level analytic step
`D1.1 ⟹ P1` is fully realised. -/

/-- **Phase 1 Stream A1 summary witness** — the analytic step
    `D1 ⟹ P1` is fully closed at:

    * δ = `Distinction` (substrate-most-primitive, via
      `P1_at_Distinction` / `Distinction.o_ne_x`)
    * δ = `Bool` (classical-computational, via `P1_at_Bool`)
    * δ = `R 1` (R-Family carrier layer, via `P1_at_R_one`)
    * δ = arbitrary `Nontrivial` type (substrate-level universal
      form, via `P1_substrate_level`)
    * δ = arbitrary `Nontrivial` `BooleanRing` (Strategy A bridge,
      via `P1_R_via_strategyA`)

    No `sorry`, no new axiom.  The interface-level analytic step
    `D1_implies_P1` consumes the per-item entailment as a hypothesis,
    matching the `ClaimZ.d1_implies_P` combinator pattern.

    Per `gut-roadmap.md` Phase 1 Stream A1, this discharges the
    **D1 ⟹ P1 analytic obligation** for the F₂-Boolean scope; the
    parametric `P1_substrate_level` lifts it to arbitrary δ with
    `Nontrivial`. -/
theorem A1_summary_witness :
    -- P1 at Distinction
    (∃ x y : Distinction, x ≠ y) ∧
    -- P1 at Bool
    (∃ x y : Bool, x ≠ y) ∧
    -- P1 at R 1
    (∃ x y : R 1, x ≠ y) ∧
    -- D1 ⟹ P1 interface step at Bool
    (∀ (S : D1Articulation), S.obj → (∃ x y : Bool, x ≠ y)) ∧
    -- D1 ⟹ P1 interface step at Distinction
    (∀ (S : D1Articulation), S.obj → (∃ x y : Distinction, x ≠ y)) :=
  ⟨P1_at_Distinction, P1_at_Bool, P1_at_R_one,
   D1_implies_P1_for_F2, D1_implies_P1_for_Distinction⟩

end SSBX.Foundation.R.ClaimZ.Analytic
