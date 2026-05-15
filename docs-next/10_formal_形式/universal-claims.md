# Universal Claims — proof structure for wen-substrate v1.1 §4.7-§4.12 (D5)

> **Status**: D5 companion to [`wen-substrate.md`](./wen-substrate.md) v1.1.
> Scope: makes the six maximum-strength universal claims of §4.7-§4.12
> proof-structure explicit. Each claim is restated, given concrete
> sub-obligations, falsification routes, and current status.
> v0.1 · 2026-05-16 · doc-only; no code changes.

---

## Preface

`wen-substrate.md` v1.1 §4.7-§4.12 makes six **maximum-strength universal
claims**, each of the form "R-Family IS X" rather than "R-Family
articulates X":

1. **§4.7** — R-Family IS Chomsky's Universal Grammar (UG)
2. **§4.8** — R-Family IS the substrate of all computable cognition
3. **§4.9** — R-Family IS the algebraic structure of phenomenology
4. **§4.10** — R-Family IS the substrate of decidable formal systems
5. **§4.11** — R-Family IS the bridge between informational and physical reality
6. **§4.12** — R-Family IS what "formal" means (subsumed into §7.8 Claim Z)

Per §4.6.5 these six claims are stated **at full strength** as
**programmatic hypotheses**: the "IS" framing articulates the bold
hypothesis; the discharge into theorem-status is the subsequent
programmatic work. The same epistemic stance as Boole 1854 ("logic IS
algebra of $\mathbb{F}_2$") or Lawvere 1960s ("mathematics IS
categorical"): identity-claim stated boldly, with proof obligations
explicit, awaiting domain-by-domain discharge.

**D5's job** is to give each universal claim its own **proof
structure** — concrete sub-obligations, explicit falsification routes,
honest open/partial/proven status. This document is the companion that
wen-substrate v1.1 §4.6.5 promises and §8.10 item 12 (domain-specific
T's) cross-references.

**Cross-references**.
- [`wen-substrate.md`](./wen-substrate.md) v1.1 §4.6.5 (programmatic
  status), §4.7-§4.12 (the six claims), §7.8 (Claim Z), §8.9
  (three-phase programme), §8.10 item 12 (domain-specific T's).
- [`r-family-definition.md`](./r-family-definition.md) — D2 single
  source of truth for R-Family-over-$\mathbb{F}_2$ structure.
- [`r-family-parametric-bases.md`](./r-family-parametric-bases.md) — D3
  parametric framework over arbitrary base $k$.
- [`code-promise-gap.md`](./code-promise-gap.md) — D7 transparency
  document mapping wen-substrate claims to Lean backing.

**Convention** for each claim:

1. **Claim restatement** — verbatim or paraphrased from wen-substrate.
2. **What it would mean to prove** — the theorem statement that would
   discharge the "IS".
3. **Decomposition into sub-obligations** — concrete, named items.
4. **Falsification routes** — what concrete evidence would refute the
   claim, calibrated per §7.8.8 style.
5. **Status** — proven / partial / open / speculative, per
   sub-obligation, with file paths to Lean evidence where present.

**Reading order**. §1-§6 cover the six claims in wen-substrate order;
§7 collects cross-cutting concerns (T2 / T3 / T5 obligations that
recur); §8 gives a priority ordering for proof discharge; §9 is a
reading guide for three audiences.

---

## §1 Universal Grammar — wen-substrate §4.7

### §1.1 Claim restatement

**§4.7 claim**: Chomsky's Universal Grammar is the **R-Family substrate
applied to natural language**. UG's universal aspects are R-Family
inherited; language-specific parameters are R-Family decomposition
choices. Formally: R-Family-over-$\mathbb{F}_2$ (at the language-finite
scale, where the 256 atomic 字 inventory of $R_8$ gives the lexicon) and
R-Family-over-$\mathbb{C}$ (for continuous semantic embedding, e.g. LLM
internals per §4.7.5) jointly realize UG.

### §1.2 What it would mean to prove

A **structure-preserving translation** $\iota_{\mathrm{UG}} :
\mathrm{UG} \to \text{R-Family-over-}k$, natural in the choice of UG
framework (Minimalist, GB, HPSG, LFG, ...), such that every
cross-linguistic universal of human language emerges as an R-Family
invariant under $\iota_{\mathrm{UG}}$.

### §1.3 Sub-obligations

- **U1 — Abstract UG-like substrate definition**. Give a D1-style
  abstract characterization of "linguistic substrate" (carrier of
  morphemes; composition; recursive embedding; movement; agreement;
  T/A/M; θ-roles; phase boundaries; principles vs parameters). U1 is
  the linguistics analog of D1 (formal articulation): until U1 is
  fixed, the target of $\iota_{\mathrm{UG}}$ is moving.

- **U2 — Translation from a specific UG framework**. Pick one
  framework (Minimalist Program is the canonical first target;
  Chomsky 1995). Construct $\iota_{\mathrm{UG-Min}} : \mathrm{MP} \to
  \text{R-Family}$ explicitly: Merge ↦ direct sum, Move ↦ symplectic
  preservation, X-bar ↦ squaring tower, phases ↦ hexagram quadrant
  boundaries (per §4.7.1 table). Verify each generative rule of MP is
  preserved under translation.

- **U3 — Cross-linguistic adequacy**. Verify $\iota_{\mathrm{UG}}$
  respects typological universals: tense/aspect/mood (per §4.7.1, 4
  temporal modalities 道/已/今/未 in $R_8$), case marking, agreement,
  movement, binding (§4.7.1 σ-form). Test against the
  Greenberg-universals list and the
  Cinque-Rizzi cartographic hierarchies. The structure-preserving
  embedding must cover at least the well-attested typological
  parameters (head-initial vs head-final, pro-drop, wh-movement,
  etc.).

- **U4 — Parameters as decomposition choices**. Formalize the claim
  that language-specific parameters correspond to specific R-Family
  decomposition choices within the universal substrate. Concretely:
  parameter $P$ on language $L$ ↦ a choice of summand decomposition
  in the squaring tower or a choice among Arf-classified quadratic
  refinements at $R_4$. A given language is then a tuple of
  R-Family-decomposition choices.

### §1.4 Falsification routes

- **(FR-UG1)** Exhibit a linguistic universal $U$ (well-attested in
  the typological literature) that is provably **not** expressible as
  any R-Family invariant. Candidate: a universal that requires
  uncountably many parameters at finite scale, contradicting the
  countable R-Family-over-$\mathbb{F}_2$ structure at $R_8$.

- **(FR-UG2)** Exhibit a natural language $L$ whose grammar provably
  has no R-Family-articulable structure (e.g., a hypothetical
  language with non-computable grammar). This would refute the
  universality of $\iota_{\mathrm{UG}}$.

### §1.5 Status

| Sub-obligation | Status | Notes |
|---|---|---|
| U1 (abstract UG substrate) | □ open | no formalism yet |
| U2 (MP → R-Family) | □ open | §4.7.1 table is informal mapping |
| U3 (cross-linguistic adequacy) | □ open | no empirical verification |
| U4 (parameters as decomposition) | □ open | conceptual only |

No Lean infrastructure for §4.7 exists. Phase II per §8.9 (structural
articulation, 6-12 months per major formal system case).

### §1.6 Reading suggestion

Pair this section with:

- Chomsky (1995) *The Minimalist Program* — for the target UG
  framework.
- Cinque & Rizzi (2010) "The Cartography of Syntactic Structures" —
  for typological-universal targets.
- Adger (2003) *Core Syntax* — pedagogical entry point.
- wen-substrate §4.7 — original claim and §4.7.1 mapping table.

---

## §2 Computable cognition — wen-substrate §4.8

### §2.1 Claim restatement

**§4.8 claim**: AI cognition (and all computable cognition, biological
or artificial) is **R-Family operations at its computational layer**.
Different architectures (transformers, RNNs, neural-symbolic systems,
biological brains) are different R-Family decomposition choices over
the same substrate.

### §2.2 What it would mean to prove

A three-layer theorem:

- **Weak**: every Turing-computable function is realizable as an
  R-Family operation. (Church-Turing-level claim.)
- **Medium**: cognitive architectures, examined via mechanistic
  interpretability, exhibit R-Family-natural structure in their
  internals (attention as σ-form, embedding as $R_N$, layer composition
  as morphism composition).
- **Strong**: biological brain computation, where computational,
  exhibits R-Family structure at appropriate $N$.

### §2.3 Sub-obligations

- **C1 — Weak universality (Church-Turing-level)**. Every
  Turing-computable function $f : \{0,1\}^* \to \{0,1\}^*$ admits an
  R-Family realization via encoding in $\bigcup_N R_N$. This is part
  of T1 in wen-substrate §8.3 and is essentially established by
  standard arguments (Gödel coding + Turing-machine simulation in
  $R_8$ ISA, partially in Lean).

- **C2 — Medium claim (mech-interp)**. Cognitive architectures
  naturally exhibit R-Family operations under mechanistic
  interpretability:
  - Attention mechanisms ↔ σ-form weighted relations (§4.8.1).
  - Embedding spaces ↔ $R_N$-vector representations for $N$ in
    hundreds-to-thousands.
  - Layer composition ↔ morphism composition (Hom-as-content).
  - Output sampling ↔ $R_8$-like symbol distribution.

  C2 requires partnership with the AI mechanistic-interpretability
  community (Olah et al.; Anthropic interpretability team; circuits
  work).

- **C3 — Strong claim (biological brain)**. Brain computation, where
  computational, exhibits R-Family structure. This is the most
  ambitious sub-obligation: requires the brain's computational
  substrate (cortical microcircuits, hippocampal indexing, basal
  ganglia decision making) to admit R-Family decomposition.

### §2.4 Falsification routes

- **(FR-C1)** Exhibit a cognitive process provably **non-Turing**
  (i.e., requiring hypercomputation). This would refute weak
  universality. Penrose-style arguments (gravitational
  micro-tubule consciousness) are candidates but currently rejected
  by mainstream computational neuroscience.

- **(FR-C2)** Mech-interp evidence that transformer circuits **do
  not** decompose into R-Family operations — e.g., a circuit whose
  internal structure is provably orthogonal to R-Family-natural
  composition. Would refute the medium claim.

- **(FR-C3)** A brain region with computation provably outside
  R-Family-naturally-articulable structure. Would refute the strong
  claim while leaving weak and medium intact.

### §2.5 Status

| Sub-obligation | Status | Notes |
|---|---|---|
| C1 (weak / Church-Turing) | ⚠ partial | T1 partially Lean-formalized; standard arguments suffice |
| C2 (mech-interp) | □ open | conceptual mapping in §4.8.1; no empirical work |
| C3 (biological brain) | □ open | speculative; no neural data |

### §2.6 Reading suggestion

- Olah et al. — Anthropic / Distill mechanistic-interpretability
  papers.
- Marr (1982) *Vision* — for the three-levels-of-analysis frame
  (computational / algorithmic / implementational) that distinguishes
  C1 / C2 / C3.
- Anthropic *Towards Monosemanticity* (2023) — concrete
  mech-interp methodology.
- wen-substrate §4.8 — original claim, §4.8.1 mapping table, §4.8.2
  alignment implications.

---

## §3 Phenomenology — wen-substrate §4.9

### §3.1 Claim restatement

**§4.9 claim**: The $R_4$ Mian matrix (4本 × 4征 = 16 phenomenology
cells) is the **minimum complete classification of phenomenal
categories**. Extended by $R_6$ (64 hexagrams) and $R_8$ (256 events),
R-Family articulates the algebraic structure of phenomenology itself
— matching Husserlian, Heideggerian, Whiteheadian, and Buddhist
classifications under structure-preserving translation.

### §3.2 What it would mean to prove

Two-part theorem:

- **Completeness**: every phenomenological category $C$ identifiable
  in the Husserl / Heidegger / Whitehead / Buddhist traditions maps
  into one of the 16 cells of $R_4$ Mian (or hierarchically, into
  $R_6$ / $R_8$ for processual / event-bearing categories).
- **Minimality**: 16 cells is the smallest classification capturing
  all structurally-distinct phenomenal categories. Any coarser
  decomposition collapses real distinctions; any finer decomposition
  is redundant.

### §3.3 Sub-obligations

- **Ph1 — 16-cell matrix completeness**. For every phenomenological
  category $C$ in (Husserl noesis/noema, Heidegger
  ready/present-at-hand, Whitehead actual-occasions / eternal-objects,
  Buddhist 五蕴), exhibit a mapping $\phi_C : C \to \mathrm{cell}(R_4
  \text{ Mian})$ such that:
  - The mapping is well-defined (a category $C$ maps to one
    structural cell, modulo $D_4$-symmetry per §3.5.4).
  - Structurally-distinct categories map to structurally-distinct
    cells.

- **Ph2 — 16-cell minimum**. Show that any classification with
  $< 16$ cells loses a structural distinction present in at least
  one tradition. (E.g., coarsening 4本 to 2本 collapses
  ready-vs-present-at-hand-vs-categorical structure.)

- **Ph3 — Cross-traditional alignment**. The mappings $\phi_C$
  across traditions are pairwise compatible: noesis vs noema
  (Husserl) ↔ ready vs present-at-hand (Heidegger) ↔ actual occasion
  vs eternal object (Whitehead) all decompose along the same (本,
  征) axes. Formally: there is a single category-theoretic structure
  $(本, 征)$ on $R_4$ Mian such that each tradition's pairs are
  projections of this structure.

- **Ph4 — Boundary delimitation**. Phenomenal categories provably
  **outside** the 16 cells are **non-formal**: they include qualia,
  intrinsic lived experience, the "hard problem" content per §4.9.6
  item 5. This obligation is the negative counterpart to Ph1: the
  16-cell coverage exactly matches the formal-phenomenological
  boundary.

### §3.4 Falsification routes

- **(FR-Ph1)** Exhibit a phenomenal category $C$ that is **formal**
  (i.e., has well-defined structural content, not pure quale) and
  provably outside the 16-cell coverage. Would refute Ph1
  completeness.

- **(FR-Ph2)** Exhibit two traditions whose classifications **do not
  align** under any (本, 征) projection — e.g., a Husserlian noematic
  type provably distinct from any Heideggerian ready-vs-present
  mode that does not factor through the same cell. Would refute Ph3.

### §3.5 Status

| Sub-obligation | Status | Notes |
|---|---|---|
| Ph1 (completeness) | □ open | conceptual mapping in §4.9.2-§4.9.4 |
| Ph2 (minimality) | □ open | no formal argument |
| Ph3 (cross-tradition alignment) | □ open | informal sketches in §4.9.2-§4.9.4 |
| Ph4 (boundary) | □ open | conceptual claim about hard problem |

All four sub-obligations are pure conceptual claims at present. Phase
III per §8.9 (uniqueness; needs philosophy collaboration).

### §3.6 Reading suggestion

- Husserl *Ideas I* (1913) — for noesis/noema.
- Heidegger *Being and Time* §§15-21 (1927) — for
  ready-vs-present-at-hand.
- Whitehead *Process and Reality* (1929) — for actual occasions /
  eternal objects.
- Zahavi *Husserl's Phenomenology* (2003) — pedagogical entry to
  Husserl.
- wen-substrate §4.9 — original claim, §4.9.2-§4.9.5 detailed
  mappings.

---

## §4 Decidability — wen-substrate §4.10

### §4.1 Claim restatement

**§4.10 claim**: Decidable formal systems are R-Family operations
over $\bigcup_N R_N$. The decidability boundary corresponds to the
bounded/unbounded distinction **within countable R-Family**, *not* to
the finite/uncountable cardinality boundary. Specifically:

- Bounded $R_N$ predicates: trivially decidable.
- $\bigcup_N R_N$ (unbounded finite): RE / co-RE / undecidable
  territory, via self-reference (halting, Gödel sentences).
- $R_\infty = \hat{R}$ (continuum): different territory; not where
  undecidability arises.

### §4.2 What it would mean to prove

A four-part theorem:

- **Layer decidability**: predicates on any fixed $R_N$ are decidable
  (trivially, by finite enumeration).
- **Halting at $\bigcup_N R_N$ undecidable**: standard
  diagonalization; already established at the R-Family-over-$R_8$ ISA
  level in Lean.
- **Complexity hierarchy**: PSPACE / EXPTIME / polynomial hierarchy
  correspond to R-Family resource-bounded decomposition layers.
- **Gödel in parametric form**: incompleteness theorem stated and
  proved in R-Family terms with explicit handling of the
  $\bigcup_N R_N$ vs $R_\infty$ boundary.

### §4.3 Sub-obligations

- **D-1 — Bounded $R_N$ decidability**. Predicates on a fixed finite
  $R_N$ are trivially decidable. Lean-formalizable as a one-liner
  using `Fintype.decidableForallFintype`; trivial in scope but
  expected as a baseline.

- **D-2 — Halting undecidability at $\bigcup_N R_N$**. **✓ done** at
  the $R_8$ ISA level in
  `formal/SSBX/Foundation/Atlas/Yi/Diagonal.lean` —
  `halts_undecidable_under_kleene` proves no total decider for
  `Halts : List Instr → R 8 → Prop` exists, via the standard Kleene
  recursion-based diagonal argument.

- **D-3 — Complexity hierarchy as R-Family resource-bounded
  decomposition**. Map PSPACE / EXPTIME / polynomial hierarchy to
  R-Family-decomposition layers: PSPACE = decidable in space
  bounded by polynomial in $\log |R_N|$; EXPTIME = decidable in time
  bounded by exponential in $\log |R_N|$; polynomial hierarchy =
  quantifier-alternation depth over $\bigcup_N R_N$. Phase III
  obligation; needs Mathlib complexity-theory bridge or new
  development.

- **D-4 — Gödel in R-Family parametric form**. State Gödel
  incompleteness in R-Family terms: any formal system $\Sigma$ that
  embeds Robinson arithmetic into $\bigcup_N R_N$ has true
  R-Family-articulable statements that $\Sigma$ cannot derive within
  any bounded $R_N$ proof procedure. Lean-tractable via existing
  Gödel mechanization (e.g., Carneiro's `Mathlib.ModelTheory` or
  freshly-built embedding).

### §4.4 Falsification routes

- **(FR-D1)** Decidability boundary at a different layer than
  $\bigcup_N R_N$ — e.g., a Turing-computable function that requires
  reaching $R_\infty = \hat{R}$ for its decision procedure. Would
  refute §4.10's layer-mapping precision.

- **(FR-D2)** Halting decidable for some Turing-equivalent R-Family
  operation. Would refute the standard Turing-computability theory
  and trivially refute D-2.

### §4.5 Status

| Sub-obligation | Status | Notes |
|---|---|---|
| D-1 (bounded $R_N$ decidability) | ✓ trivial | Lean-formalizable as one-liner |
| D-2 (halting undecidable) | ✓ done | `Foundation/Atlas/Yi/Diagonal.lean` |
| D-3 (complexity hierarchy) | □ open | Mathlib complexity bridge needed |
| D-4 (Gödel parametric) | □ open | tractable via existing Gödel mechanization |

**§4.10 is the most concrete of the six universal claims**. Lean
evidence already exists for D-2 (the headline undecidability result);
D-1 is trivial; D-3 / D-4 are Phase II-Lean-tractable. This makes
§4.10 the **natural first target for Phase II proof discharge** per
the priority ordering in §8 below.

### §4.6 Reading suggestion

- Sipser *Introduction to the Theory of Computation* (3rd ed.) — for
  the standard layer landscape.
- Soare *Turing Computability* (2016) — for the deeper RE / co-RE /
  $\Sigma_n^0 / \Pi_n^0$ hierarchy.
- Smullyan *Gödel's Incompleteness Theorems* (1992) — for the Gödel
  side.
- `formal/SSBX/Foundation/Atlas/Yi/Diagonal.lean` — the Lean witness
  for D-2.
- wen-substrate §4.10 — original claim with v0.9 precision
  correction (countable vs continuum layers).

---

## §5 Physical-informational substrate — wen-substrate §4.11

### §5.1 Claim restatement

**§4.11 claim** (explicitly self-rated *most speculative* in §4.11.5):
Physical reality has informational substrate. R-Family provides the
**specific algebraic structure** of this informational substrate.
Wheeler's "it from bit" is true; R-Family is the specific "it from
bit" structure. Spans:

- Stabilizer QM as R-Family-over-$\mathbb{F}_2$ (§4.1.5).
- Hilbert QM as R-Family-over-$\mathbb{C}$ (§4.1.5b, carrier-level).
- $p$-adic QM as R-Family-over-$\mathbb{C}_p$ (Vladimirov-Volovich-Khrennikov
  programme).
- Bekenstein bound / black-hole entropy / AdS-CFT as R-Family
  quantities.
- Spacetime emergence from $R_4$ ring structure.

### §5.2 What it would mean to prove

For each physical-informational layer, exhibit a structure-preserving
translation $\iota_{\mathrm{phys}}^{(k)} : \mathrm{Phys}^{(k)} \to
\text{R-Family-over-}k$ with the appropriate base:

- $k = \mathbb{F}_2$: stabilizer quantum computation.
- $k = \mathbb{C}$: full unitary QM with Hermitian inner product.
- $k = \mathbb{C}_p$: $p$-adic quantum mechanics.

And, more speculatively, exhibit gravitational / holographic /
cosmological structure as derived layers.

### §5.3 Sub-obligations

- **P-1 — Stabilizer QM = R-Family-over-$\mathbb{F}_2$**.
  **✓ established** per wen-substrate §4.1.5. Stabilizer states
  generated by Pauli operators, Clifford gates, Pauli measurements
  on $n$ qubits form a structure isomorphic to R-Family-over-$\mathbb{F}_2$
  at $R_{2n}$ with symplectic form $\sigma$. Reference: Gottesman
  1998 stabilizer formalism + Aaronson-Gottesman 2004 efficient
  simulation.

- **P-2 — Hilbert QM = R-Family-over-$\mathbb{C}$ (carrier + full
  Hermitian enrichment)**. Carrier-level identity $\mathbb{C}^{2^n}
  = R_{2^n}^{(\mathbb{C})}$ holds per §4.1.5b. **Open**: full
  Hermitian inner product, unitary group, spectral theorem as
  R-Family-over-$\mathbb{C}$ P3-enrichment (per §4.1.5b
  carrier-vs-structure note). Mathlib bridge feasible:
  `Mathlib.Analysis.InnerProductSpace` + `Foundation.R.Parametric`
  composition is the natural site.

- **P-3 — $p$-adic QM = R-Family-over-$\mathbb{C}_p$**. The
  Vladimirov-Volovich-Khrennikov programme constructs quantum
  mechanics over $p$-adic number fields. The carrier identity
  $\mathbb{C}_p^{2^n} = R_{2^n}^{(\mathbb{C}_p)}$ is parametric per
  §3.6. Full mechanization requires a Mathlib $\mathbb{C}_p$ bridge
  (not currently present in Mathlib in usable form), then composition
  with `RFamily $\mathbb{C}_p$ N`. Long-term target.

- **P-4 — Bekenstein bound / black-hole entropy / AdS-CFT**.
  Information density bounded by $R_N$ cardinality (Bekenstein
  bound); $S = A/4$ as R-Family operations on horizon bits
  (black-hole entropy); boundary-bilinear-form vs bulk-operator
  duality (AdS-CFT). **Speculative**; doc's weakest individual
  claims. Would require concrete realization beyond a mapping
  table.

- **P-5 — Spacetime emergence from $R_4$ ring structure**.
  Wedderburn-forced ring structure on $R_4 \cong M_2(\mathbb{F}_2)$
  per wen-substrate §2.7 provides an algebraic invariant arena
  isomorphic to a $2 \times 2$ matrix algebra; this is proposed
  (§4.11.2 item 3) as the algebraic skeleton from which spacetime
  emerges. **Speculative**; no concrete spacetime-emergence
  construction yet.

### §5.4 Falsification routes

- **(FR-P1)** Physical theory that requires non-R-Family substrate
  — e.g., a confirmed physical phenomenon requiring genuinely
  non-computable continuum mathematics not reducible to
  $R_\infty = \hat{R}$. Would refute the substrate claim.

- **(FR-P2)** Experimental test distinguishing
  R-Family-over-$\mathbb{F}_2$ / -$\mathbb{C}$ / -$\mathbb{C}_p$
  quantum predictions. Currently most experiments are consistent
  with standard ($\mathbb{C}$-based) QM; a clean experimental
  signature of $\mathbb{C}_p$-QM would constrain (or strengthen)
  the parametric-base claim.

### §5.5 Status

| Sub-obligation | Status | Notes |
|---|---|---|
| P-1 (stabilizer QM = $\mathbb{F}_2$) | ✓ established | §4.1.5; Pauli/Clifford = symplectic R-Family |
| P-2 (Hilbert QM = $\mathbb{C}$ carrier) | ⚠ partial | carrier per §4.1.5b; full Hermitian open |
| P-3 ($p$-adic QM = $\mathbb{C}_p$) | □ open | needs Mathlib $\mathbb{C}_p$ bridge |
| P-4 (Bekenstein / BH entropy / AdS-CFT) | ◇ speculative | mapping table only |
| P-5 (spacetime from $R_4$) | ◇ speculative | no construction |

Legend: ✓ established · ⚠ partial · □ open · ◇ speculative.

### §5.6 Reading suggestion

- Gottesman (1998) "The Heisenberg Representation of Quantum
  Computers" — for stabilizer formalism (P-1).
- Aaronson & Gottesman (2004) "Improved Simulation of Stabilizer
  Circuits" — for the efficient-simulation theorem behind P-1.
- Vladimirov & Volovich (1989) "$p$-adic quantum mechanics" *Comm.
  Math. Phys.* 123 — for P-3 foundational reference.
- Khrennikov (2009) *Interpretations of Probability* / (2018)
  *Ultrametric Pseudodifferential Equations and Applications* —
  monograph references for $p$-adic mathematical physics.
- Bekenstein (1981) "Universal upper bound on the entropy-to-energy
  ratio for bounded systems" — for the Bekenstein bound.
- Wheeler (1990) "Information, Physics, Quantum: The Search for
  Links" — for "it from bit".
- wen-substrate §4.11 — original claim, §4.11.5 self-rated
  speculative status.

---

## §6 Formality itself (Claim Z) — wen-substrate §4.12 / §7.8

### §6.1 Claim restatement

**§4.12 / §7.8 claim** — the **maximum** claim, subsuming §4.7-§4.11
as instances:

$$\text{"formal" and "R-Family-articulable" are co-extensive — by
bi-directional structural analysis.}$$

That is: "formal" picks out a specific kind of articulation captured
by **D1** (§1.5.1); D1 ⟹ P1-P7 by analytic step; P1-P7 ⟹
R-Family-pattern-over-some-$k$ by synthetic step; therefore D1 ⟺
R-Family-over-some-$k$ articulation. Per §7.8.3 this is a
**structural-analytic theorem**, not a stipulation and not an
empirical generalization.

Note: **Claim Z is not a sixth domain**. It is the meta-claim that
the other five (UG, cognition, phenomenology, decidability,
physical-informational) plus all other formal articulations live in
R-Family. The five §1-§5 claims are **instances** of Claim Z.

### §6.2 What it would mean to prove

Three sub-theorems composing the bi-directional argument:

- **Analytic step (→)**: D1 ⟹ P1-P7.
- **Synthetic step (←)**: P1-P7 ⟹ R-Family-over-some-$k$
  instantiation.
- **Composition**: D1 ⟺ R-Family-over-some-$k$ articulation.

### §6.3 Sub-obligations

- **Z-A (analytic step)**. Show D1's seven items (eight, conditional
  on D1 item 8 per v1.1.1) force P1-P7 by structural analysis. In
  v1.1, **partially discharged** via Strategy A (§8.4.1): for the
  classical-Boolean scope, D1 + classical operations force Boolean
  algebra → Stone's representation → Boolean ring → idempotency
  forces char 2 → Birkhoff representation $\mathbb{F}_2^k$ →
  R-Family-over-$\mathbb{F}_2$. This **discharges** the analytic
  step for ~80% of practical scope (classical logic, classical
  math, Boolean circuits, classical computation).

  **Open**: intuitionistic constructive content; quantum logic at
  $C^*$-level; modal logics; substructural logics. Per §8.4.4
  these are now **specific research targets** with known
  logical-algebraic structure, not "deepest open question" vagueness.

- **Z-S (synthetic step)**. Show P1-P7 ⟹ R-Family-over-some-$k$
  instantiation. Depends on:
  - **T4** (minimality, Part VIII §8.4): partially discharged via
    Strategy A in v1.1 for the classical-Boolean case; non-classical
    extensions open per §8.4.4.
  - **T5** (uniqueness, Part VIII §8.5): open. Establishes any
    minimum universal substrate satisfying P1-P7 is equivalent to
    R-Family-over-some-$k$. T5 is comparable in difficulty to
    standard cross-foundation interpretability theorems (ZFC ↔
    ETCS, type theory ↔ category theory).

- **Z-C (composite)**. D1 ⟺ R-Family-over-some-$k$ articulation.
  Follows by composition once Z-A and Z-S are discharged. Partial
  composition holds for the classical-Boolean scope.

### §6.4 Falsification routes

Per wen-substrate §7.8.8, three concrete routes:

- **(FR-Z1, analytic)** Exhibit a structure $S$ that satisfies D1
  by independent characterization yet provably **fails** at least
  one of P1-P7. Would refute the analytic arrow. To date: no such
  structure exhibited.

- **(FR-Z2, synthetic)** Exhibit a structure that satisfies P1-P7
  closure conditions yet provably **fails** to instantiate
  R-Family-over-any-$k$. Would refute T5 (uniqueness) and break the
  synthetic arrow. To date: no such structure exhibited.

- **(FR-Z3, D2 inconsistency)** Show R-Family itself (as the
  12-item D2 structure) is internally inconsistent — e.g.,
  Hom-as-content forces something contradicting the squaring tower.
  Would trivially refute the claim. To date: no inconsistency found
  at $\mathbb{F}_2$ instance (Lean codebase `Foundation/SSBX/`);
  parametric instances inherit consistency from analogous Mathlib
  treatments of $\mathbb{R}, \mathbb{C}, \mathbb{C}_p$.

### §6.5 Status

| Sub-obligation | Status | Notes |
|---|---|---|
| Z-A (analytic, classical scope) | ✓ partial | §8.4.1 Strategy A discharge |
| Z-A (analytic, non-classical scope) | □ open | §8.4.4 research targets |
| Z-S (synthetic, T4) | ⚠ partial | classical case discharged; non-classical open |
| Z-S (synthetic, T5) | □ open | Phase III; hardest single obligation |
| Z-C (composite) | ⚠ partial | composes Z-A and Z-S; classical scope |
| FR-Z3 D2 consistency | ⚠ partial | $\mathbb{F}_2$ verified; parametric pending |

### §6.6 Reading suggestion

- wen-substrate §7.8 (full Claim Z section), especially §7.8.3
  (bi-directional structural argument) and §7.8.8 (falsification
  routes).
- wen-substrate §8.4.1-§8.4.4 (Strategy A discharge + parametric
  extensions).
- Stone (1936) "The theory of representation for Boolean algebras"
  — the foundational reference for Z-A in classical scope.
- Birkhoff (1933) "On the combination of subalgebras" — for
  Birkhoff representation in Z-A.
- Gödel (1933) & Gentzen (1936) — for the intuitionistic →
  classical reduction relevant to Z-A non-classical extensions.

---

## §7 Cross-cutting concerns

The six universal-claim sub-obligations share several **structural
factors** that recur across domains. Identifying these makes the
proof programme tractable: progress on a cross-cutting obligation in
one domain transfers to others.

### §7.1 T2 — Structure-preserving articulation

**T2** (case-by-case articulation theorems per wen-substrate §8.3) is
the **common factor** across:

- **U2** (MP → R-Family translation)
- **C2** (cognitive architectures → R-Family operations under
  mech-interp)
- **Ph1** (phenomenological categories → 16-cell mapping)
- **D-3** (complexity hierarchy → R-Family resource-bounded
  decomposition)
- **P-1** (stabilizer QM → R-Family-over-$\mathbb{F}_2$) — already
  established
- **P-2** (Hilbert QM → R-Family-over-$\mathbb{C}$) — carrier
  established

Each is an instance of T2 — a structure-preserving translation from a
specific formal system into R-Family-over-some-$k$. **Tackle T2
case-by-case**, starting with the most concrete (P-1 already done;
D-3 / D-4 Lean-tractable next).

### §7.2 T3 — Naturality

**T3** (naturality theorem per §8.3) ensures the translations
$\iota_{\mathrm{UG}}, \iota_{\mathrm{cog}}, \iota_{\mathrm{phen}},
\iota_{\mathrm{dec}}, \iota_{\mathrm{phys}}$ are **canonical** — i.e.,
they commute with the canonical morphisms in each source category and
do not depend on arbitrary choices.

T3 is a Phase II–III obligation; it presupposes that several T2
instances are in hand so that naturality across instances can be
verified.

### §7.3 T5 — Uniqueness

**T5** (uniqueness, §8.5) underwrites **Z-S** (the synthetic step of
Claim Z). T5 is Phase III, the hardest single obligation, and
ultimately gives all five domain claims their **uniqueness** force:
without T5, each domain claim could in principle hold by other
substrates too; T5 closes that gap.

### §7.4 Recommended attack order for cross-cutting

Per wen-substrate §8.10 priority + the case analysis above:

1. **Start with §4.10 decidability** — most concrete, D-2 already
   Lean-proven, D-1 trivial, D-3 / D-4 tractable. This gives T2
   case-study experience on the cleanest target.
2. **Then §4.11 P-2** — Hilbert space Hermitian-enrichment via
   Mathlib bridge; technically demanding but well-mapped territory.
3. **Then iterate** across U2 / C2 / Ph1 with the methodology
   established by 1-2.

---

## §8 Priority ordering for proof discharge

Per wen-substrate §8.9 (three-phase programme) and §8.10 (priority
list), and the case analysis of §1-§6 above, a concrete priority
ordering for the six universal claims is:

1. **§4.10 D-3 / D-4** (decidability extensions: complexity
   hierarchy + Gödel parametric). **Lean-tractable**; builds on
   `Foundation/Atlas/Yi/Diagonal.lean` D-2; standard mathematical
   machinery available. Estimated effort: 6-12 months. Phase II.

2. **§4.11 P-2** (Hilbert QM full Hermitian enrichment over the
   R-Family-over-$\mathbb{C}$ carrier). Mathlib bridge feasible:
   `Mathlib.Analysis.InnerProductSpace` × `Foundation.R.Parametric`.
   Estimated effort: 6-12 months. Phase II.

3. **§4.7 U1-U2** (UG formalization, MP → R-Family translation).
   Requires linguistics formalism choice (Minimalist Program
   canonical first target). Long-running collaboration with
   linguistics community. Estimated effort: 1+ year. Phase II-III.

4. **§4.8 C2** (mech-interp evidence of R-Family structure in
   cognitive architectures). Requires partnership with AI
   interpretability community (Anthropic interpretability team,
   distill.pub community, Olah et al. circuits programme).
   Estimated effort: ongoing empirical partnership. Phase II-III.

5. **§4.9 Ph1-Ph4** (phenomenology completeness, minimality,
   cross-tradition alignment, boundary). Requires philosophy
   collaboration (phenomenologists familiar with Husserl /
   Heidegger / Whitehead). Estimated effort: 1+ year and a
   discipline-bridging programme. Phase III.

6. **§4.11 P-3** ($p$-adic QM Mathlib bridge). Long-term; needs
   Mathlib $\mathbb{C}_p$ infrastructure to mature first.
   Estimated effort: multi-year. Phase III.

**Strategic note**. §4.10 (decidability) is by far the most concrete
target. Lean evidence already exists for the headline D-2 result.
Phase II progress on §4.10 produces immediately reusable T2
methodology that transfers to §4.11 P-2 and onward.

---

## §9 Reading guide

This document is structured for **three audiences**:

### §9.1 Foundational reviewers

- Read §6 (Claim Z) first — it gives the meta-claim that frames the
  other five.
- Then §7 (cross-cutting concerns) — T2 / T3 / T5 obligations recur
  across domains.
- Then §1-§5 in order — each is an **instance** of Claim Z at a
  specific domain.
- Reference wen-substrate §4.6.5 (programmatic status), §4.7-§4.12
  (original claims), §7.8 (Claim Z), §8.9 (three-phase programme),
  §8.10 (priority list).

### §9.2 Domain experts (linguistics / cognition / philosophy / physics)

Read your domain section directly:

- **Linguists**: §1 (Universal Grammar), pair with wen-substrate
  §4.7 and the linguistics references in §1.6.
- **AI / cognitive scientists**: §2 (computable cognition), pair
  with wen-substrate §4.8 and the mech-interp references in §2.6.
- **Phenomenologists**: §3 (phenomenology), pair with
  wen-substrate §4.9 and the philosophy references in §3.6.
- **Logicians / TCS**: §4 (decidability), pair with wen-substrate
  §4.10 and `Foundation/Atlas/Yi/Diagonal.lean`.
- **Physicists**: §5 (physical-informational substrate), pair with
  wen-substrate §4.11 and the physics references in §5.6.

Each domain section is structured: claim restatement → sub-obligations
→ falsification routes → status → reading suggestion. Skim the status
table to see what's done vs open in your domain.

### §9.3 Formalizers (Lean / Mathlib contributors)

- §4 (decidability) is the most concrete target. D-2 is done; D-1
  is trivial; D-3 / D-4 are next.
- §5 (physical-informational) P-2 (Hilbert enrichment) is the
  natural second target via Mathlib `InnerProductSpace` bridge.
- Cross-reference [`code-promise-gap.md`](./code-promise-gap.md)
  (D7) for the section-by-section map of wen-substrate claims to
  Lean backing.
- Cross-reference [`r-family-definition.md`](./r-family-definition.md)
  (D2) for the structured R-Family-over-$\mathbb{F}_2$ definition
  to build T2 case studies on top of.
- Cross-reference [`r-family-parametric-bases.md`](./r-family-parametric-bases.md)
  (D3) for the parametric framework needed for P-2 / P-3.

---

*D5 · universal-claims · v0.1 · 2026-05-16 · companion to
wen-substrate.md v1.1 §4.7-§4.12 / §7.8 / §8.9-§8.10*
