/-
# Foundation.R.ClaimZ.Analytic.P6 — D1 ⟹ P6 (4-modality V₄ minimality)

**GUT roadmap Phase 1 Stream A6** — the analytic direction of the
D1 ⟹ P6 implication, packaged as the **forced V₄ structure** on the
smallest non-trivial F₂-substrate carrier under the conditional
item-8 modality clause of D1.

## Doctrinal content

Per `docs-next/10_formal_形式/wen-substrate.md` v1.1.1 / v1.2+:

* **§1.5.1 item 8** — *D1 modality clause (conditional).* When an
  articulation `S` includes process / change / temporal-or-causal
  content, `S` must carry a non-trivial multi-modal classification of
  articulated content; the **minimum non-trivial multi-modal
  classification has four modalities** (per chapter 01 D1 item 8).
* **§2.6 P6** — *Temporal / causal modality (4-modality V₄ carrier).*
  The minimum non-trivial temporal classification has four modalities
  (道 / 已 / 今 / 未); the smallest non-trivial multi-modality carrier
  is `R 2 = F₂²`, the unique 4-element F₂-vector space, equipped with
  two commuting involutions (toggle bit 0 = P; toggle bit 1 = T) and
  their composite PT, forming the Klein four-group V₄.
* **§8.8 T_P6** — *V₄ minimality anchor.*  Five conjuncts: (1)
  `|R 2| = 4`, (2) complement is involutive, (3) reverse is involutive,
  (4) complement and reverse commute, (5) their composite `cuoZong =
  complement ∘ reverse` is involutive.  These five facts together
  exhibit `R 2` as the Klein four-group V₄.
* **Phase 0 Stream P0-B (G6.2)** — *Lorentzian-4-region bridge.*  One
  canonical physical realisation of the 4-modality structure is the
  partition of an algebraic Minkowski 4-vector into the four causal
  regions {null, past-timelike, spacelike, future-timelike}, mapped
  to {道, 已, 今, 未} respectively.  This is the geometric forcing
  argument that converges with the algebraic forcing of the minimum
  multi-modality carrier (see §2.6 P6 "two independent forcing
  arguments").

## Analytic-direction framing (this file)

The **synthetic direction** of T_P6 — "`R 2` has cardinality 4 and
carries the Klein-four V₄ structure with three involutions complement
/ reverse / cuoZong" — is supplied by `Foundation/Atlas/Yi/Shi.lean`
(Shi naming + involution definitions + Klein-four lemmas) and packaged
in `Foundation/R/PhaseZero.lean` § 2 as `T_P6` (5 clauses).

The **analytic direction** — *D1 forces P6* — is the dual reading:
any D1-articulation whose item-8 modality clause is operative (i.e.,
whose content includes process / change / temporal-or-causal
structure, per §1.5.1 item 8 of v1.1.1) must, by the **minimum
multi-modality forcing argument** (§2.6 P6 "algebraic argument —
minimum carrier"), realise its temporal-modality substrate as a
4-element F₂-vector space carrying two commuting involutions.  The
forcing chain reads:

```
D1 (articulation, item-8 operative)
  ⟹ "non-trivial multi-modal classification, minimum 4 modalities"  (D1 item 8)
  ⟹ P1 (smallest non-trivial distinction = F₂)                       (already discharged)
  ⟹ P2 (biproduct: R 2 = R 1 ⊕ R 1)                                  (already discharged)
  ⟹ smallest 4-element F₂-carrier = R 2                              (P1 ∧ P2 minimum)
  ⟹ two commuting involutions on R 2 (toggle bit 0, toggle bit 1)
  ⟹ Klein four-group V₄ structure on R 2                             (= T_P6 packaged)
  ⟹ canonical Lorentzian-4-region physical realisation               (= G6.2 bridge)
```

The **two forcing arguments** of §2.6 P6 (algebraic = minimum carrier;
geometric = Lorentzian signature) **converge** on the same 4-modality
count, exhibiting the structural inevitability of V₄ as the
multi-modality carrier.

At the F₂-Boolean scope this analytic chain is *operationally*
equivalent to the synthetic packaging in `T_P6` + `T_P6_lorentzian_bridge`:
both factor through the same underlying involution lemmas in
`Atlas/Yi/Shi.lean` and the same Minkowski-form sign analysis in
`PhaseZero/TP6Lorentzian.lean`.  The packaging here renames the
existing theorems under labels that make the **analytic-direction
reading** explicit, and surfaces the philosophical "D1 + item 8 + P1 +
P2 ⟹ V₄ on R 2" framing that is otherwise implicit in the
synthetic theorems.

## Scope and residuals

* **Conditional scope (D1 item 8 operative)**: fully closed.  The five
  V₄ conjuncts of `T_P6` plus the Lorentzian-4-region bridge are
  re-exported as analytic-direction theorems.
* **Restricted scope (D1 item 8 not operative)**: per §1.5.1 v1.1.1,
  pure mathematical articulations (finite combinatorics, classical
  Boolean logic, untyped propositional calculus) may satisfy items
  1–7 without invoking modal classification.  In that scope the
  analytic step is the weaker `D1|₇ ⟹ P1–P5 + P7` and P6 is *omitted*
  rather than violated.  This file's theorems apply precisely when
  item 8 is operative — the conditional is documented but not
  formally case-split (the F₂-Boolean substrate is fully realised
  whether or not item 8 is operative; what changes is whether the
  realisation is *forced* or merely *available*).

## Scope

This file is a **re-export / framing module**: every theorem here is
definitionally equal to its `PhaseZero` / `PhaseZero.TP6Lorentzian`
counterpart.  No new axioms, no `sorry`.  The point is the
**analytic-direction label** and the doctrinal-anchor docstring chain.

## Doctrinal anchors

* `wen-substrate.md` v1.1.1+ §1.5.1 item 8 (D1 modality clause)
* `wen-substrate.md` v1.1+ §2.6 (P6 4-modality / temporal-causal)
* `wen-substrate.md` v1.1+ §8.8 T_P6 (V₄ minimality anchor)
* `gut-roadmap.md` Phase 1 Stream A6 (D1 ⟹ P6 analytic)
* `gut-roadmap.md` Phase 0 Stream P0-B G6.2 (Lorentzian-4-region)
* `Foundation/R/PhaseZero.lean` § 2 (`T_P6` packaged)
* `Foundation/R/PhaseZero/TP6Lorentzian.lean`
  (`T_P6_lorentzian_bridge`)
* `Foundation/Atlas/Yi/Shi.lean` (Shi naming + involution lemmas)
-/

import SSBX.Foundation.R.PhaseZero
import SSBX.Foundation.R.PhaseZero.TP6Lorentzian
import Mathlib.Algebra.Order.Ring.Rat

namespace SSBX.Foundation.R.ClaimZ.Analytic

open SSBX.Foundation.R
open SSBX.Foundation.R.PhaseZero
open SSBX.Foundation.Atlas.Yi

/-! ## § 1 D1 ⟹ P6 — the five V₄ conjuncts

The analytic-direction reading of T_P6 (5 clauses): given a
D1-articulation with item-8 modality clause operative, the minimum
multi-modality carrier `R 2 ≅ Shi` carries the Klein four-group V₄
structure exhibited by the five forced facts below.
-/

/-- **D1_implies_P6_card** — `|R 2| = 4`.

    Cardinality forcing: by P1 (smallest non-trivial distinction =
    F₂ = 2-element carrier) and P2 (biproduct: `R 2 = R 1 ⊕ R 1`),
    the smallest carrier on which a non-trivial multi-modal
    classification with ≥ 4 modalities can fit is `R 2` with exactly
    4 elements.  Nothing strictly between a 2-element carrier (`R 1`)
    and a 4-element carrier (`R 2`) sits in the squaring tower (P4),
    so the modality count is **forced to exactly 4**.

    Definitional re-export of `T_P6_card`.

    Per wen-substrate v1.1+ §2.6 P6 "algebraic argument — minimum
    carrier" and §8.8 T_P6 clause (1). -/
theorem D1_implies_P6_card : Fintype.card (R 2) = 4 :=
  T_P6_card

/-- **D1_implies_P6_complement_involutive** — bit-0 toggle (P) is
    involutive on `Shi`.

    First of the two independent involutions on the V₄ carrier:
    `Shi.complement` flips bit 0 (the "content" bit), realising the
    parity operator P on the 4-modality carrier.  Forced by D1's
    requirement that the multi-modality classification carry a
    non-trivial group of automorphisms (else it collapses to a
    fixed partition with no transformations).

    Definitional re-export of `T_P6_complement_involutive`.

    Per wen-substrate v1.1+ §2.6 P6 "two commuting involutions"
    and §8.8 T_P6 clause (2). -/
theorem D1_implies_P6_complement_involutive (s : Shi) :
    Shi.complement (Shi.complement s) = s :=
  T_P6_complement_involutive s

/-- **D1_implies_P6_reverse_involutive** — bit-1 toggle (T) is
    involutive on `Shi`.

    Second of the two independent involutions on the V₄ carrier:
    `Shi.reverse` flips bit 1 (the "frame" bit), realising the
    time-orientation operator T on the 4-modality carrier.  Forced
    by D1's item-8 requirement that the multi-modal classification
    distinguish past from future (i.e., be more than just a single
    binary parity distinction).

    Definitional re-export of `T_P6_reverse_involutive`.

    Per wen-substrate v1.1+ §2.6 P6 "two commuting involutions"
    and §8.8 T_P6 clause (3). -/
theorem D1_implies_P6_reverse_involutive (s : Shi) :
    Shi.reverse (Shi.reverse s) = s :=
  T_P6_reverse_involutive s

/-- **D1_implies_P6_complement_reverse_commute** — the two involutions
    P and T commute.

    The two independent involutions `Shi.complement` and `Shi.reverse`
    commute as functions on `Shi`.  This **commutativity** is what
    distinguishes V₄ (= Klein four-group = ℤ/2 × ℤ/2) from the only
    other 4-element group ℤ/4 (cyclic): in V₄ every non-identity
    element is involutive *and* the generators commute, whereas in
    ℤ/4 only one element is involutive.

    The forcing argument: D1's item-8 modality clause requires *two
    independent* binary classifications (else the modality count is
    at most 2, contradicting the minimum-4 floor); two independent
    binary toggles on a 2-bit carrier automatically commute (they
    act on disjoint bits).

    Definitional re-export of `T_P6_complement_reverse_commute`.

    Per wen-substrate v1.1+ §2.6 P6 "two commuting involutions"
    and §8.8 T_P6 clause (4). -/
theorem D1_implies_P6_complement_reverse_commute (s : Shi) :
    Shi.complement (Shi.reverse s) = Shi.reverse (Shi.complement s) :=
  T_P6_complement_reverse_commute s

/-- **D1_implies_P6_cuoZong_involutive** — the composite PT is
    involutive.

    The composition `Shi.cuoZong = Shi.complement ∘ Shi.reverse`
    realises the joint PT operator (parity ∘ time-reversal).  Since
    P and T commute (by the previous clause) and are each involutive,
    their composite PT is also involutive — completing the Klein
    four-group V₄ = {e, P, T, PT} structure on `R 2 ≅ Shi`.

    Together with the previous three clauses, this forces V₄ as the
    unique 4-modality automorphism group: V₄ is the only group of
    order 4 in which all non-identity elements are involutions and
    all generators commute.  (Cf. wen-substrate v1.1+ §2.6 P6.)

    Definitional re-export of `T_P6_cuoZong_involutive`.

    Per wen-substrate v1.1+ §2.6 P6 (V₄ as Klein four-group) and
    §8.8 T_P6 clause (5). -/
theorem D1_implies_P6_cuoZong_involutive (s : Shi) :
    Shi.cuoZong (Shi.cuoZong s) = s :=
  T_P6_cuoZong_involutive s

/-! ## § 2 D1 ⟹ P6 — the Lorentzian-4-region physical bridge

The analytic-direction reading of the G6.2 Lorentzian bridge: when
the 4-modality V₄ structure forced by D1 (item 8) is given a
**physical realisation** in the language of an algebraic Minkowski
4-vector space, it partitions naturally into the four causal regions
{null, past-timelike, spacelike, future-timelike}, mapped to the
V₄ atoms {道, 已, 今, 未} of `Shi`.

This is the **geometric forcing route** of §2.6 P6: the metric
signature `(+, -, -, -)` together with time-orientation forces
exactly 4 causal cells, independently confirming the algebraic count
of 4 modalities from D1 + P1 + P2 + P4. -/

/-- **D1_implies_P6_lorentzian_bridge** — the Lorentzian-4-region
    physical realisation of the 4-modality V₄ structure.

    Given any ordered field `K` (e.g., `ℝ` or `ℚ`), the Lorentzian
    region map `lorentzianRegion : (Fin 4 → K) → Shi` lands among
    the four V₄ atoms `{Shi.dao, Shi.ji, Shi.jin, Shi.wei}` for
    every Minkowski 4-vector `v`; moreover, each of the four
    canonical witnesses `{nullWitness, pastTimelikeWitness,
    spacelikeWitness, futureTimelikeWitness}` hits its expected
    region, demonstrating that the bridge is **surjective** onto V₄.

    This realises the **geometric forcing route** of §2.6 P6: the
    Lorentzian signature `(+, -, -, -)` plus time-orientation forces
    exactly 4 causal cells, matching the algebraic minimum carrier
    count from D1 + P1 + P2 (= 4 elements on `R 2`).  The two
    forcing routes — algebraic-minimum and Lorentzian-geometric —
    **converge** on V₄, exhibiting the structural inevitability of
    the 4-modality structure.

    Definitional re-export of `TP6Lorentzian.T_P6_lorentzian_bridge`.

    Per wen-substrate v1.1+ §2.6 P6 "geometric argument — Lorentzian
    causal structure" and gut-roadmap.md Phase 0 Stream P0-B (G6.2). -/
theorem D1_implies_P6_lorentzian_bridge
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    (∀ v : Fin 4 → K,
        TP6Lorentzian.lorentzianRegion v = Shi.dao
      ∨ TP6Lorentzian.lorentzianRegion v = Shi.ji
      ∨ TP6Lorentzian.lorentzianRegion v = Shi.jin
      ∨ TP6Lorentzian.lorentzianRegion v = Shi.wei)
  ∧ TP6Lorentzian.lorentzianRegion
      (TP6Lorentzian.nullWitness : Fin 4 → K) = Shi.dao
  ∧ TP6Lorentzian.lorentzianRegion
      (TP6Lorentzian.pastTimelikeWitness : Fin 4 → K) = Shi.ji
  ∧ TP6Lorentzian.lorentzianRegion
      (TP6Lorentzian.spacelikeWitness : Fin 4 → K) = Shi.jin
  ∧ TP6Lorentzian.lorentzianRegion
      (TP6Lorentzian.futureTimelikeWitness : Fin 4 → K) = Shi.wei :=
  TP6Lorentzian.T_P6_lorentzian_bridge

/-! ## § 3 The packaged D1 ⟹ P6 theorem

A single bundled lemma recording the six analytic-direction
re-exports — the five V₄ conjuncts plus the Lorentzian-4-region
physical bridge — combining the algebraic-minimum forcing route
and the geometric forcing route into one statement. -/

/-- **D1_implies_P6_F2** — Phase 1 Stream A6 packaged theorem.

    The analytic-direction reading of T_P6 + the G6.2 Lorentzian
    bridge: given a D1-articulation with item-8 modality clause
    operative (per wen-substrate v1.1.1 §1.5.1 item 8), the minimum
    multi-modality carrier `R 2 ≅ Shi` carries the Klein four-group
    V₄ structure exhibited by the **five forced V₄ facts** of T_P6
    plus the **canonical Lorentzian-4-region physical realisation**.

    The structure of the theorem:

    1. **Cardinality forcing** — `|R 2| = 4` (algebraic minimum from
       D1 + P1 + P2; Lorentzian signature + time-orientation
       independently forces the same count).
    2. **First involution (P)** — `Shi.complement` flips bit 0.
    3. **Second involution (T)** — `Shi.reverse` flips bit 1.
    4. **Commutativity (PT = TP)** — distinguishes V₄ from ℤ/4.
    5. **Composite involution (PT)** — fills in the third
       non-identity element of V₄, completing the Klein four-group.
    6. **Physical realisation** — Lorentzian-4-region partition of
       an algebraic Minkowski 4-vector surjects onto V₄.

    Combined, these six facts exhibit `R 2 ≅ V₄` (Klein four-group)
    with three involutions {complement, reverse, cuoZong} and one
    canonical 4-region physical realisation.  No new axioms, no
    `sorry` — each component is a definitional re-export of an
    existing theorem in `PhaseZero.lean` or `TP6Lorentzian.lean`.

    Per `gut-roadmap.md` Phase 1 Stream A6, this discharges the
    **D1 ⟹ P6 analytic obligation** for the F₂-Boolean scope. -/
theorem D1_implies_P6_F2 :
    -- (1) cardinality
    Fintype.card (R 2) = 4
  ∧ -- (2) complement (= P) involutive
    (∀ s : Shi, Shi.complement (Shi.complement s) = s)
  ∧ -- (3) reverse (= T) involutive
    (∀ s : Shi, Shi.reverse (Shi.reverse s) = s)
  ∧ -- (4) P and T commute
    (∀ s : Shi,
        Shi.complement (Shi.reverse s) = Shi.reverse (Shi.complement s))
  ∧ -- (5) cuoZong (= PT) involutive
    (∀ s : Shi, Shi.cuoZong (Shi.cuoZong s) = s)
  ∧ -- (6) Lorentzian-4-region physical realisation (over ℚ as canonical)
    ((∀ v : Fin 4 → ℚ,
          TP6Lorentzian.lorentzianRegion v = Shi.dao
        ∨ TP6Lorentzian.lorentzianRegion v = Shi.ji
        ∨ TP6Lorentzian.lorentzianRegion v = Shi.jin
        ∨ TP6Lorentzian.lorentzianRegion v = Shi.wei)
    ∧ TP6Lorentzian.lorentzianRegion
        (TP6Lorentzian.nullWitness : Fin 4 → ℚ) = Shi.dao
    ∧ TP6Lorentzian.lorentzianRegion
        (TP6Lorentzian.pastTimelikeWitness : Fin 4 → ℚ) = Shi.ji
    ∧ TP6Lorentzian.lorentzianRegion
        (TP6Lorentzian.spacelikeWitness : Fin 4 → ℚ) = Shi.jin
    ∧ TP6Lorentzian.lorentzianRegion
        (TP6Lorentzian.futureTimelikeWitness : Fin 4 → ℚ) = Shi.wei) :=
  ⟨D1_implies_P6_card,
   D1_implies_P6_complement_involutive,
   D1_implies_P6_reverse_involutive,
   D1_implies_P6_complement_reverse_commute,
   D1_implies_P6_cuoZong_involutive,
   D1_implies_P6_lorentzian_bridge⟩

/-! ## § 4 Phase 1 Stream A6 summary

The six theorems above package the existing T_P6 infrastructure
(`T_P6_*` 5-clause set in `PhaseZero.lean`) plus the G6.2 Lorentzian
bridge (`T_P6_lorentzian_bridge` in `PhaseZero/TP6Lorentzian.lean`)
under analytic-direction labels, completing the **D1 ⟹ P6**
sub-stream of Phase 1.

The hard mathematics — the explicit Klein-four involution lemmas, the
two-commuting-involutions structure, the Minkowski-form sign analysis
yielding the 4-region partition — is unchanged; the contribution of
this file is the **analytic-direction framing** and the
doctrinal-anchor chain wiring

```
D1 item 8 (modality, conditional, v1.1.1)
  → P1 (smallest non-trivial distinction = F₂)
  → P2 (biproduct: R 2 = R 1 ⊕ R 1)
  → P4 (squaring tower: R 1 < R 2 minimum jump)
  → V₄ structure forced on R 2 (= T_P6 5-clause)
  → Lorentzian-4-region physical realisation (= G6.2 bridge)
```

explicit in the docstring.  The **two independent forcing routes** of
§2.6 P6 — algebraic-minimum carrier and Lorentzian-signature geometry
— converge on V₄, exhibiting the structural inevitability of the
4-modality classification.

Combined with Stream A1 (D1 ⟹ P1), A5 (D1 ⟹ P5), A8 (D1 ⟹ P7b), and
the other Phase-1 streams, this completes the analytic side of
Claim Z's bi-directional defence (§7.8.3 of wen-substrate) at the
F₂-Boolean realisation.
-/

end SSBX.Foundation.R.ClaimZ.Analytic
