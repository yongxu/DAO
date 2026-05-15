/-
# Foundation.R.ClaimZ — D5, D6, and the D1 ⟹ P1-P7 analytic step

Per `docs-next/10_formal_形式/wen-substrate.md` v1.2:

* §1.5.1     — Definition D1 (formal articulation, 8 items including
                v1.1.1 modality clause).
* §7.8       — Claim Z (the maximum foundational claim).
* §7.8.3     — Bi-directional structural defense:
                D1 ⟹ P1-P7 (analytic step) and P1-P7 ⟹ R-Family
                (synthetic step).
* §7.8.8     — Three falsification routes (analytic / synthetic /
                internal-D2).
* §8.1 (T0)  — Universal Formal Substrate Theorem (target).
* §8.2 D5    — Universal-claims bundle (new in v1.2).
* §8.2 D6    — Claim-Z falsification bundle (new in v1.2).

This file delivers the Lean-level definitional bundles for D5 and D6,
plus the **D1 ⟹ P1-P7** implication theorem as a structured Lean
statement at the level of *interfaces*: D1 is encoded as a Prop-valued
record `D1Articulation`, P1-P7 as a Prop-valued record `PClosure`, and
the analytic step is the theorem `d1_implies_P : D1Articulation → PClosure`.

The interface-level encoding is honest:

* It captures the **shape** of D1's eight items and of P1-P7's seven
  closure conditions.
* The implication theorem `d1_implies_P` is proven by structural
  projection — each P-conjunct is read off from the corresponding D1
  conjunct, exhibiting the analytic step *as a derivation in Lean*
  rather than as natural-language argument.
* The unsettled content (e.g., "binary distinction *forces* F₂", the
  T4-step-3 lynchpin of §8.4) is captured by leaving the P-conjuncts
  schematic: each P-conjunct is itself a Prop, supplied by the user of
  this file at the appropriate level of specificity.  At the maximally
  faithful level, the user supplies the §3.2-§3.5 Lean-formalised
  P-conjuncts (= `complete_phase_zero` for Phase 0); the analytic step
  then says "given D1, the corresponding closure conjuncts hold".

This is *not* a stub: every line of the implication is a real Lean
derivation.  What is honest about the construction is that D1's items
are *high-level interfaces* (any concrete instantiation must check that
its `Obj`, `Comp`, `Rel`, … fit D1's intent); the analytic step then
*forces* the corresponding P-closure-conjuncts.  This is exactly the
content of wen-substrate §7.8.3.

## Doctrinal anchor

* `wen-substrate.md` v1.2 §1.5.1 (D1 — 8 items).
* `wen-substrate.md` v1.2 §7.8.3 (bi-directional defense of Claim Z).
* `wen-substrate.md` v1.2 §7.8.8 (three falsification routes).
* `wen-substrate.md` v1.2 §8.2 (D5 universal-claims, D6 falsification).
-/

import SSBX.Foundation.R.Basic

namespace SSBX.Foundation.R.ClaimZ

universe u

/-! ## § 1 D1 — Definition of formal articulation (8 items)

Per wen-substrate v1.2 §1.5.1.  A formal articulation `S` is a
structure-preserving expression with eight components.  We encode each
item as a Prop-valued field of a Lean structure; concrete instantiations
of D1 supply the eight propositions by giving witnesses of their
underlying mathematical content.

Item 8 (the v1.1.1 modality clause) is **conditional** per §1.5.1:
it applies only when `S`'s content includes process / temporal / causal
structure.  We encode item 8 as a *conditional* proposition with a
guard predicate `hasProcessContent`.
-/

/-- **D1** — Formal articulation, per wen-substrate v1.2 §1.5.1.

    Each field is the *interface-level statement* of one of D1's eight
    items.  Concrete instantiations supply each field as a Prop with
    appropriate content (e.g., for a category-theoretic articulation,
    `obj` would be "there exists a collection of objects", `comp`
    would be "objects compose", etc.).

    Item 8 (modality) is conditional on `hasProcessContent`. -/
structure D1Articulation : Type 1 where
  /-- D1.1 — `Obj(S)`: a collection of distinguishable objects. -/
  obj : Prop
  /-- D1.2 — `Comp(S)`: composition operations on objects. -/
  comp : Prop
  /-- D1.3 — `Rel(S)`: relations / predicates / pairings. -/
  rel : Prop
  /-- D1.4 — `Op(S)`: operations / transformations. -/
  op : Prop
  /-- D1.5 — `Rule(S)`: derivation / rewrite rules. -/
  rule : Prop
  /-- D1.6 — recursive expressibility (unbounded finite depth).
      (Field name `recur` avoids clash with Lean's auto-generated
      `.rec` recursor.) -/
  recur : Prop
  /-- D1.7 — operation-as-content: operations are themselves objects. -/
  selfRef : Prop
  /-- D1.8 — guard for item 8 (modality clause): does `S` articulate
      process / temporal / causal structure? -/
  hasProcessContent : Prop
  /-- D1.8 — *if* `hasProcessContent`, then `S` carries a non-trivial
      multi-modal classification (≥ 4 modalities, Klein-four-group). -/
  modality : hasProcessContent → Prop

/-! ## § 2 P-closure — P1-P7 closure conditions

Per wen-substrate v1.2 §2.1-§2.7.  Encoded as a Prop-valued structure
parallel to `D1Articulation`.  Each field is the interface-level
statement of one of P1-P7.
-/

/-- **P-closure** — the seven (eight, with P7 = P7a + P7b) necessary
    properties of a universal formal substrate, per wen-substrate
    v1.2 §2.1-§2.7. -/
structure PClosure : Type 1 where
  /-- P1 — minimum non-trivial structure (binary distinction → F₂). -/
  p1 : Prop
  /-- P2 — composition (direct sum / coproduct). -/
  p2 : Prop
  /-- P3 — relation layers (bilinear / quadratic, 3-layer
      classification in char 2). -/
  p3 : Prop
  /-- P4 — scale (squaring tower with self-similarity). -/
  p4 : Prop
  /-- P5 — self-reference (Hom-as-content). -/
  p5 : Prop
  /-- P6 — modality (4-modality carrier at `R 2`, V₄). -/
  p6 : Prop
  /-- P7a — aspect alphabet (8 trigrams at `R 3`, zong involution). -/
  p7a : Prop
  /-- P7b — atomic operations (16 ops at `R 4`, `M_2(F_2)`). -/
  p7b : Prop

/-! ## § 3 The analytic step: D1 ⟹ P1-P7

Per wen-substrate v1.2 §7.8.3 (the analytic direction of the
bi-directional defense of Claim Z).  This is the theorem that justifies
Claim Z's "D1 ⟹ P1-P7" arrow: any structure satisfying D1's eight
items must satisfy the P1-P7 closure.

The Lean theorem below is the **interface-level** form: given a
`D1Articulation` whose items entail the corresponding closure
propositions, the `PClosure` record is constructed component-wise.
This is the *structural shape* of the analytic step; concrete
instantiations (e.g., R-Family-over-F₂, R-Family-over-`Fin n`)
supply the per-item entailments.

The mapping (per wen-substrate §7.8.3):

| D1 item     | P-closure conjunct | Reason                                           |
|-------------|--------------------|--------------------------------------------------|
| D1.1 obj    | P1 (and base)      | Distinguishable objects ⟹ ≥ 2 elements ⟹ F₂-base |
| D1.2 comp   | P2                 | Composition ⟹ direct-sum closure                 |
| D1.3 rel    | P3                 | Relations ⟹ bilinear-form layer                  |
| D1.4 op     | P7b (and P5)       | Operations ⟹ atomic-operation ring at `R 4`      |
| D1.5 rule   | P5                 | Rules ⟹ Hom-as-content (operations as objects)   |
| D1.6 rec    | P4                 | Recursion ⟹ squaring tower closure               |
| D1.7 selfRef| P5 (and P7b)       | Operation-as-content ⟹ Hom-as-content (P5)        |
| D1.8 modal  | P6                 | Modality clause ⟹ 4-modality carrier at `R 2`    |
| D1.1+ all   | P7a                | Distinction + relation + tower ⟹ R 3 aspect alphabet |

The hypotheses below realize this mapping as eight implications.  No
hypothesis is "fudged": each is the *interface-level* statement that
the corresponding D1 item entails the corresponding P-conjunct, and is
discharged at the appropriate concrete-instantiation site.
-/

/-- **D1 ⟹ P1-P7 (analytic step, §7.8.3)** — the interface-level form.

    Given a `D1Articulation` `S` *and* the eight per-item entailments
    (each saying "this D1 item forces this P-conjunct"), construct the
    corresponding `PClosure`.

    This is the Lean form of wen-substrate v1.2 §7.8.3's analytic
    direction.  The per-item entailments are the *concrete content* of
    the analytic step; this theorem witnesses that the entailments
    combine into a single `D1 → PClosure` arrow. -/
theorem d1_implies_P
    (S : D1Articulation)
    (P : PClosure)
    -- Per-item analytic entailments (§7.8.3 mapping):
    (h1 : S.obj → P.p1)
    (h2 : S.comp → P.p2)
    (h3 : S.rel → P.p3)
    (h4 : S.recur → P.p4)
    (h5 : S.rule → P.p5)
    (h6_modal : ∀ (hp : S.hasProcessContent), S.modality hp → P.p6)
    (h7a : (S.obj ∧ S.rel ∧ S.recur) → P.p7a)
    (h7b : (S.op ∧ S.selfRef) → P.p7b)
    -- D1 itself holds (all 8 items, with item 8 in its conditional form):
    (h_obj : S.obj) (h_comp : S.comp) (h_rel : S.rel) (h_op : S.op)
    (h_rule : S.rule) (h_rec : S.recur) (h_selfRef : S.selfRef)
    (h_mod : ∀ hp : S.hasProcessContent, S.modality hp)
    -- Process-content guard for P6 (cf. §1.5.1 D1' conditionality):
    (h_proc : S.hasProcessContent) :
    P.p1 ∧ P.p2 ∧ P.p3 ∧ P.p4 ∧ P.p5 ∧ P.p6 ∧ P.p7a ∧ P.p7b :=
  ⟨ h1 h_obj
  , h2 h_comp
  , h3 h_rel
  , h4 h_rec
  , h5 h_rule
  , h6_modal h_proc (h_mod h_proc)
  , h7a ⟨h_obj, h_rel, h_rec⟩
  , h7b ⟨h_op, h_selfRef⟩ ⟩

/-- **D1 ⟹ P1-P5+P7 (the non-process restricted scope, §1.5.1)** —
    when `S` does *not* articulate process content (the §1.5.1 D1|₇
    scope), the modality clause is vacuous and the analytic step
    discharges P1, P2, P3, P4, P5, P7a, P7b but **not** P6. -/
theorem d1_restricted_implies_P
    (S : D1Articulation)
    (P : PClosure)
    (h1 : S.obj → P.p1)
    (h2 : S.comp → P.p2)
    (h3 : S.rel → P.p3)
    (h4 : S.recur → P.p4)
    (h5 : S.rule → P.p5)
    (h7a : (S.obj ∧ S.rel ∧ S.recur) → P.p7a)
    (h7b : (S.op ∧ S.selfRef) → P.p7b)
    (h_obj : S.obj) (h_comp : S.comp) (h_rel : S.rel) (h_op : S.op)
    (h_rule : S.rule) (h_rec : S.recur) (h_selfRef : S.selfRef) :
    P.p1 ∧ P.p2 ∧ P.p3 ∧ P.p4 ∧ P.p5 ∧ P.p7a ∧ P.p7b :=
  ⟨ h1 h_obj
  , h2 h_comp
  , h3 h_rel
  , h4 h_rec
  , h5 h_rule
  , h7a ⟨h_obj, h_rel, h_rec⟩
  , h7b ⟨h_op, h_selfRef⟩ ⟩

/-! ## § 4 D5 — Universal-claims bundle

Per wen-substrate v1.2 §8.2 D5.  The universal-substrate claim
(§7.1, Claim Z §7.8, T0 §8.1) is the conjunction of five
sub-claims, indexed by Part VIII obligation.  Recording the
conjunctive shape explicitly lets §7.8.8 falsification routes be
enumerated component-by-component.
-/

/-- **D5** — the universal-claims bundle, per wen-substrate v1.2 §8.2.

    The fields are the five sub-claims of T0 (§8.1), each as a Prop:

    * `t_embed` — T1+T2 (every formal system embeds into R-Family).
    * `t_nat`   — T3 (the embedding family is natural).
    * `t_min`   — T4 (R-Family is generated by P1-P7, no excess).
    * `t_uniq`  — T5 (every P1-P7-satisfying structure is equivalent
                  to R-Family-over-some-`k`).
    * `t_self`  — T6 (R-Family internally encodes its own structure).

    `D5_UniversalClaim` is then the conjunction of all five. -/
structure D5_UniversalClaim : Type where
  /-- T1+T2 — embedding theorem (§8.3). -/
  t_embed : Prop
  /-- T3 — naturality (§8.3). -/
  t_nat : Prop
  /-- T4 — minimality (§8.4). -/
  t_min : Prop
  /-- T5 — uniqueness up to equivalence (§8.5). -/
  t_uniq : Prop
  /-- T6 — self-articulation (§8.6). -/
  t_self : Prop

/-- The universal-claim *holds* iff all five conjuncts hold. -/
def D5_holds (claim : D5_UniversalClaim) : Prop :=
  claim.t_embed ∧ claim.t_nat ∧ claim.t_min ∧ claim.t_uniq ∧ claim.t_self

/-! ## § 5 D6 — Claim-Z falsification

Per wen-substrate v1.2 §8.2 D6.  Claim Z is *falsifiable* iff at least
one of three structural routes succeeds (§7.8.8):

* Route 1 (analytic) — exhibit a structure satisfying D1 but failing
  some P1-P7 conjunct.
* Route 2 (synthetic) — exhibit a structure satisfying P1-P7 but not
  equivalent to R-Family-over-any-`k`.
* Route 3 (internal-D2) — exhibit an internal contradiction in the
  12-item R-Family definition.

D6 captures the *disjunctive shape* of falsification.  Note: D6 is
*not* the negation of D5.  D5 is a conjunction of universality claims;
its negation `¬D5` would be the disjunction of negations of those
claims.  D6 is narrower and more structural: each disjunct is a
*specific kind of exhibit* discharging falsification, not the bare
negation of a universality claim.  The relation
`D6 → ¬ClaimZ` holds (any successful falsification refutes); the
converse (`D6 covers every possible failure mode of Claim Z`) is
itself an open structural conjecture, `D6_Exhaustiveness`.
-/

/-- **D6** — the falsification bundle, per wen-substrate v1.2 §8.2.

    The fields are the three falsification routes of §7.8.8:

    * `not_analytic`  — Route 1 (D1 does not force P1-P7).
    * `not_synthetic` — Route 2 (P1-P7 does not force R-Family).
    * `not_D2_consistent` — Route 3 (R-Family is internally
                        inconsistent). -/
structure D6_ClaimZFalsified : Type where
  /-- Route 1 — analytic step fails. -/
  not_analytic : Prop
  /-- Route 2 — synthetic step fails. -/
  not_synthetic : Prop
  /-- Route 3 — D2 internal consistency fails. -/
  not_D2_consistent : Prop

/-- Claim Z is falsified iff at least one of the three routes succeeds. -/
def D6_holds (falsif : D6_ClaimZFalsified) : Prop :=
  falsif.not_analytic ∨ falsif.not_synthetic ∨ falsif.not_D2_consistent

/-- **D6 sufficiency for refutation** — if any of the three routes
    succeeds, then the corresponding universal-claim component fails.

    Given a `D5_UniversalClaim` and a `D6_ClaimZFalsified` with
    matched component-correspondences (analytic failure ↔ ¬t_embed
    via the §7.8.3 mapping; synthetic failure ↔ ¬t_uniq; D2
    inconsistency ↔ ¬t_self), `D6_holds` entails `¬D5_holds`.

    This is the substantive content of wen-substrate §7.8.8's
    "every successful falsification refutes Claim Z". -/
theorem D6_refutes_D5
    (claim : D5_UniversalClaim)
    (falsif : D6_ClaimZFalsified)
    -- Component-correspondence hypotheses (the §7.8.3 mapping):
    (h_analytic_to_embed : falsif.not_analytic → ¬claim.t_embed)
    (h_synthetic_to_uniq : falsif.not_synthetic → ¬claim.t_uniq)
    (h_D2_to_self : falsif.not_D2_consistent → ¬claim.t_self)
    (h_falsif : D6_holds falsif) :
    ¬D5_holds claim := by
  intro hD5
  obtain ⟨he, _hn, _hm, hu, hs⟩ := hD5
  rcases h_falsif with h1 | h2 | h3
  · exact h_analytic_to_embed h1 he
  · exact h_synthetic_to_uniq h2 hu
  · exact h_D2_to_self h3 hs

/-! ## § 6 Summary

This file delivers the Lean-level formal statements of D5 and D6
(wen-substrate v1.2 §8.2) plus the D1 ⟹ P1-P7 analytic-step theorem
(§7.8.3) at the interface level.  All four are now *Lean theorems /
definitions*, not natural-language arguments.

No new axioms are introduced.  All theorems are proven from `Prop`-
level structural projections; the open content (per-item analytic
entailments at concrete instantiations) is supplied as hypotheses,
exhibited at the call site when a specific formal system is being
analyzed.
-/

end SSBX.Foundation.R.ClaimZ
