# wen-substrate — Foundational document set

> R-Family **is** the universal formal substrate. R-Family **is** what "formal" means.

This folder is the multi-chapter form of `wen-substrate.md`, restructured 2026-05-16 around the framework's current understanding. The single-file form has been replaced by [`wen-substrate.md`](../wen-substrate.md), which now points here.

## How to read this

The eight substantive chapters can be read in order or out of order. They split along natural topical lines, not the legacy §X.Y outline of the original document. Each chapter stands alone — references between chapters are explicit links, not implicit "see Part X" pointers.

| Chapter | Topic | Read it if you want to know |
|---|---|---|
| [01-foundations](01-foundations.md) | What "universal / formal / substrate" mean; the necessary properties P1–P7; R-Family as the smallest carrier that satisfies them; how R₁ → R₈ supports the cosmological reading (无极 → 万物 → 道法自然) | the framework's core derivation, end-to-end |
| [02-parametric](02-parametric.md) | R-Family is parametric over an arbitrary commutative-ring base k; F₂, ℝ, ℂ, ℤ_p, ℂ_p are different bases of one structural pattern; encoding (T1) vs articulation (T2). Under chapter 03's distinction-monism reading, "base k" is one *class* of realisation δ (the algebraic class) | how the discrete-vs-continuous distinction becomes a base-choice, not a separate theory |
| [03-operation-monism](03-operation-monism.md) | Below the base sits the squaring operator Σ : X ↦ X × X with iteration; below the operator sits the primitive **distinction** `o` / `x` of which `Bool`, qubit basis, ⊥ / ⊤, 阳 / 阴, silent / sayable are all realisations. R-Family **is** that operation, iterated on that distinction. Spencer-Brown / Bateson / Wheeler / yi-jing lineage. Operation-monism + distinction-monism (Daoist 有名是无名的截面) distinct from substance-monisms | what "one-元" means without committing to any substance |
| [04-partialcell](04-partialcell.md) | The substrate at the type level: `PartialCell N := Fin N → Option Bool` as the face-lattice of the N-cube; merge / restrict / mergeAll as a partial commutative monoid; Wen.Core ISA built on it | the actual algebra the Lean machine runs on |
| [05-coverage](05-coverage.md) | R-Family articulates mathematics, language, computation, physics, spacetime; cognition + AI alignment; phenomenology; decidability; the informational–physical bridge; redefines "formal" itself | the case for universality, sub-domain by sub-domain |
| [06-universal-grammar](06-universal-grammar.md) | Classical Chomskyan UG as an R-Family substrate claim; the conditional-form sharpening (if a UG exists, it is isomorphic to the X²-256 lattice); the four necessary conditions; Open Problem #2 (uniqueness) | what was formally discharged in Lean for the UG question |
| [07-claim](07-claim.md) | Comparison with alternative foundations (ZFC, type theory, category theory, Boolean algebra, linear algebra); the seven standing objections; the direct claim; Claim Z as the maximum form ("formal" ≡ "R-Family-articulable") with bi-directional defense and falsification routes | where the framework sits in the landscape and how to attack it |
| [08-obligations](08-obligations.md) | The full proof structure: T0 universal-substrate theorem, definitional D1–D6, universality T1–T3, minimality T4 (with Strategy A discharge for the classical-Boolean scope), uniqueness T5, self-articulation T6, semantic overlay T7–T8, Phase 0 sub-theorems (T_P3 / T_P6 / T_P7a / T_P7b), three-phase roadmap, and the complete version history v0.6 → v1.3 | what is proven, what is programmatic, and where the Lean discharge currently stands |

## Companion documents (siblings, not subordinates)

These docs in the same directory carry specific D-series obligations and continue to be canonical for their scope:

- [`r-family-definition.md`](../r-family-definition.md) — D2: single-source 12-item definition of R-Family
- [`r-family-parametric-bases.md`](../r-family-parametric-bases.md) — D3: parametric concretization (companion to chapter 02)
- [`universal-claims.md`](../universal-claims.md) — D5: proof structure for the six universal claims (covers material that lives across chapters 05 and 07)
- [`claim-z-falsification.md`](../claim-z-falsification.md) — D6: three falsification routes for Claim Z (covers material in chapter 07)
- [`code-promise-gap.md`](../code-promise-gap.md) — cross-section gap audit (Lean code vs. document promises)

The chapters in this folder cross-link to these companions where relevant; they do not duplicate or absorb them.

## Anchor migration table

External references — 89 Lean docstring cites across 18 files, plus ~100 markdown hrefs across 12 companion docs — currently name old `§X.Y` anchors from the single-file `wen-substrate.md`. Every distinct anchor that any external file uses is mapped below to its new home. Until those refs are mechanically rewritten (a follow-up pass), readers landing on an external `§X.Y` cite should consult this table.

| Old anchor | Topic | New location |
|---|---|---|
| §1 (Part I) | foundational definitions | [01-foundations.md](01-foundations.md) |
| §1.5.1 | D1 formal articulation (8 items) | [01-foundations.md § D1 — formal articulation](01-foundations.md#d1--formal-articulation) |
| §1.5.4 | equivalence of substrates | [01-foundations.md § Equivalence and embedding](01-foundations.md#equivalence-and-embedding) |
| §1.5.5 | partial-system embedding | [01-foundations.md § Equivalence and embedding](01-foundations.md#equivalence-and-embedding) |
| §2.1 | P1 minimum non-trivial structure | [01-foundations.md § P1 — minimum non-trivial structure](01-foundations.md#p1--minimum-non-trivial-structure) |
| §2.3 | P3 bilinear / quadratic-refinement layers | [01-foundations.md § P3 — relational layers](01-foundations.md#p3--relational-layers) |
| §2.5 | P5 Hom-as-content + ring structure on R₄ | [01-foundations.md § P5 — self-reference](01-foundations.md#p5--self-reference) |
| §2.6 | P6 temporal/causal modality | [01-foundations.md § P6 — temporal-causal modality](01-foundations.md#p6--temporal-causal-modality) |
| §2.7 | P7a aspect alphabet + P7b atomic ring ops | [01-foundations.md § P7 — aspect alphabet and atomic operations](01-foundations.md#p7--aspect-alphabet-and-atomic-operations) |
| §3.1 | R-Family 12-item definition | [01-foundations.md § R-Family arrives](01-foundations.md#r-family-arrives) |
| §3.4.1 | embedding vs equivalence | [01-foundations.md § Equivalence and embedding](01-foundations.md#equivalence-and-embedding) |
| §3.5.3 | R₄ / R₆ as invariant physical structure | [01-foundations.md § R-tower as cosmological ladder](01-foundations.md#r-tower-as-cosmological-ladder) |
| §3.5.6 | 道法自然 — substrate follows itself | [01-foundations.md § Self-validation loop](01-foundations.md#self-validation-loop) |
| §3.6, §3.6.1–§3.6.10 | parametric R-Family over base k | [02-parametric.md](02-parametric.md) |
| §3.7, §3.7.1–§3.7.6 | operation monism, Σ operator | [03-operation-monism.md](03-operation-monism.md) |
| §3.8 (not externally cited yet) | PartialCell substrate | [04-partialcell.md](04-partialcell.md) |
| §4 (Part IV header) | demonstration of universal coverage | [05-coverage.md](05-coverage.md) |
| §4.1.5, §4.1.5b | Hilbert space as R-Family-over-ℂ | [05-coverage.md § Quantum mathematics and Hilbert space](05-coverage.md#quantum-mathematics-and-hilbert-space) |
| §4.6.5 | programmatic-status of §4.7–§4.12 | [05-coverage.md § Status of the coverage claims](05-coverage.md#status-of-the-coverage-claims) and [06-universal-grammar.md § Status](06-universal-grammar.md#status) |
| §4.7, §4.7.1 | classical UG mapping | [06-universal-grammar.md § Classical UG as R-Family substrate](06-universal-grammar.md#classical-ug-as-r-family-substrate) |
| §4.7bis, §4.7bis.5 | X²-256 lattice as conditional UG; Open Problem #2 | [06-universal-grammar.md § Conditional form — the X²-256 lattice](06-universal-grammar.md#conditional-form--the-x-256-lattice) |
| §4.8, §4.8.1, §4.8.2 | R-Family as substrate of computable cognition | [05-coverage.md § Computable cognition and AI alignment](05-coverage.md#computable-cognition-and-ai-alignment) |
| §4.9, §4.9.2, §4.9.5 | R-Family as algebraic phenomenology | [05-coverage.md § Algebraic phenomenology](05-coverage.md#algebraic-phenomenology) |
| §4.10, §4.10.3 | R-Family and decidable formal systems | [05-coverage.md § Decidability boundary](05-coverage.md#decidability-boundary) |
| §4.11, §4.11.5 | informational–physical bridge | [05-coverage.md § Informational and physical reality](05-coverage.md#informational-and-physical-reality) |
| §4.12 | R-Family as what "formal" means | [05-coverage.md § "Formal" redefined](05-coverage.md#formal-redefined) |
| §5, §5.6 | comparison with alternatives | [07-claim.md § Comparison with alternative foundations](07-claim.md#comparison-with-alternative-foundations) |
| §6 (Part VI) | objections and responses | [07-claim.md § Objections and responses](07-claim.md#objections-and-responses) |
| §7.8, §7.8.3, §7.8.4, §7.8.7, §7.8.8 | Claim Z and its falsification | [07-claim.md § Claim Z](07-claim.md#claim-z) |
| §8.1 | T0 theorem statement | [08-obligations.md § T0 — universal formal substrate theorem](08-obligations.md#t0--universal-formal-substrate-theorem) |
| §8.2 | D1–D6 definitional obligations | [08-obligations.md § Definitional obligations](08-obligations.md#definitional-obligations) |
| §8.3 | T1 / T2 / T3 universality | [08-obligations.md § Universality obligations](08-obligations.md#universality-obligations) |
| §8.4, §8.4.1, §8.4.3, §8.4.4 | T4 minimality and Strategy A discharge | [08-obligations.md § Minimality — T4 and Strategy A](08-obligations.md#minimality--t4-and-strategy-a) |
| §8.5 | T5 uniqueness | [08-obligations.md § Uniqueness — T5](08-obligations.md#uniqueness--t5) |
| §8.6 | T6 self-articulation | [08-obligations.md § Self-articulation — T6](08-obligations.md#self-articulation--t6) |
| §8.7 | T7 / T8 semantic overlay | [08-obligations.md § Semantic overlay — T7 and T8](08-obligations.md#semantic-overlay--t7-and-t8) |
| §8.8 | Phase 0 sub-theorems (T_P3 / T_P6 / T_P7a / T_P7b) | [08-obligations.md § Phase 0 sub-theorems](08-obligations.md#phase-0-sub-theorems) |
| §8.9 | three-phase proof programme | [08-obligations.md § Three-phase roadmap](08-obligations.md#three-phase-roadmap) |
| §8.10 | priority order | [08-obligations.md § Three-phase roadmap](08-obligations.md#three-phase-roadmap) |

External references using old `§X.Y` anchors will not auto-resolve until the mechanical rewrite pass runs. That pass uses this table as input.

## The four-level abstraction tower

R-Family is articulated at four nested generalities, each correct and refining the previous; choice between levels is *expository*, not foundational.

| level | object of definition | Lean realisation |
|---|---|---|
| concrete F₂ (chapter 01) | `R N := Fin N → Bool`, fixed at the F₂ instance | [`Foundation/R/Basic.lean`](../../../formal/SSBX/Foundation/R/Basic.lean) |
| algebraic-parametric (chapter 02) | `RFamily k N := Fin N → k`, ring / field k — the algebraic class of δ-realisations | [`Foundation/R/Parametric.lean`](../../../formal/SSBX/Foundation/R/Parametric.lean) |
| operation monism (chapter 03) | `RTower X k`, k-fold iteration of Σ over a seed type X — no algebraic structure required | [`Foundation/R/OperationMonism.lean`](../../../formal/SSBX/Foundation/R/OperationMonism.lean) |
| **distinction monism (chapter 03)** | **`R' N δ := Fin N → δ`, with δ any realisation of the primitive distinction — substrate itself is δ-independent** | [`Foundation/R/Distinction.lean`](../../../formal/SSBX/Foundation/R/Distinction.lean) |

Distinction monism is the most fundamental: *the substrate is the act of distinction, iterated by Σ*. The realisations of the primitive distinction — `false` / `true`, |0⟩ / |1⟩, ⊥ / ⊤, 阳 / 阴, silent / sayable, no / yes — are siblings, not separate substrates.

## Status snapshot at split time (2026-05-16)

Where each chapter's claims currently stand in the Lean codebase:

- **Foundations (chapter 01)** — P1–P7 packagings discharged immediately in [`Foundation/R/PhaseZero.lean`](../../../formal/SSBX/Foundation/R/PhaseZero.lean); residual obligations (P3 uniqueness up to iso, P6 Lorentzian connection, P7b Wedderburn uniqueness clause) tracked there.
- **Parametric (chapter 02)** — carrier-only in [`Foundation/R/Parametric.lean`](../../../formal/SSBX/Foundation/R/Parametric.lean); P1–P7-over-k bridges deferred.
- **Operation monism + distinction monism (chapter 03)** — [`Foundation/R/OperationMonism.lean`](../../../formal/SSBX/Foundation/R/OperationMonism.lean) + [`OperationMonismBridge.lean`](../../../formal/SSBX/Foundation/R/OperationMonismBridge.lean) provide the Σ-tower additive to the carrier-level R-Family; [`Foundation/R/Distinction.lean`](../../../formal/SSBX/Foundation/R/Distinction.lean) (~230 LOC, zero sorry, zero axiom) provides the primitive `Distinction` type with `Equiv` to `Bool`, the δ-parametric carrier `R' N δ := Fin N → δ`, and the bridge `R' N Bool = R N`.
- **PartialCell (chapter 04)** — full Phases A–D algebra in [`Foundation/R/PartialCell.lean`](../../../formal/SSBX/Foundation/R/PartialCell.lean); Wen.Core ISA in [`Foundation/Wen/Core/`](../../../formal/SSBX/Foundation/Wen/Core/).
- **Universal grammar (chapter 06)** — existence formally discharged across six Lean files under [`Foundation/Wen/X2Codes*.lean`](../../../formal/SSBX/Foundation/Wen/) (0 sorry); uniqueness in the DualIso form proven; uniqueness in the full-Iso form is false without atom hypothesis (explicitly documented in chapter 06).
- **Strategy A (chapter 08)** — T4 step 3 partially discharged in [`Foundation/R/StrategyA.lean`](../../../formal/SSBX/Foundation/R/StrategyA.lean) for the classical-Boolean scope; non-classical extensions parametric.
- **Claim Z (chapter 07)** — falsification structure formalised in [`Foundation/R/ClaimZ.lean`](../../../formal/SSBX/Foundation/R/ClaimZ.lean); F₂-specific discharge in [`ClaimZF2.lean`](../../../formal/SSBX/Foundation/R/ClaimZF2.lean) (explicit residual T3 obligation noted there). Under chapter 03's distinction monism, Claim Z reads: "formal" ≡ "expressible in terms of observed distinctions, iterated by Σ" — strictly stronger than the chapter-02 form because the residual "but which k?" dissolves into the realisation variable δ.
