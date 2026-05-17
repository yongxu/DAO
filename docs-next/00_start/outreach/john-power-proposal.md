# Framework Validation Request: SMCC-Enriched Lawvere Theory for "Universal Sayability"

> **Recipient**: Prof. John Power (Macquarie University)
> **Sender**: Yongxu Ren · renyongxu@gmail.com
> **Version**: v0.1 draft · 2026-05-17
> **Format**: 5-page proposal (markdown source; convertible to plain-text email)
> **Status**: outreach draft pending finalization

---

**Subject**: Framework validation request — SMCC-enriched Lawvere theory for "Universal Sayability"

Dear Professor Power,

I am writing as an independent mathematical researcher (renyongxu@gmail.com) working on a foundational uniqueness theorem for the structure of formal articulation. Over the last two years I have developed and formally verified — in Lean 4 + Mathlib, 0 sorry / 0 new axioms — a recursive type-family `R N δ` whose first few layers I claim are forced by a small set of structural axioms (P1-P7). I am writing to you specifically because the natural framework for the remaining open case (full δ-realisation across non-algebraic substrates) appears to be a *biproduct-enriched Lawvere theory*, and you are the most direct authority on enriched Lawvere theories worldwide (Power 1999 TAC, Hyland-Power 2007 ENTCS, Lack-Power 2009, Garner-Power 2018 LMCS). Before I commit a 12-month Lean implementation to instantiate this framework, I would value 30-60 minutes of your time to flag whether it is well-formed or fundamentally misconceived.

**Executive summary**. The proposed framework, which I call **GUT-C Path C**, defines `T_GUT` as a biproduct-enriched Lawvere theory whose generators encode our axioms P1-P7. The base 2-category of T_GUT-models is taken to be SMCCs with biproducts. The 4 intended δ-instances are: `FinVect_{F_q}` (algebraic — corresponds to our existing 0-sorry GUT-A/B), `HeytAlg` (Heyting / intuitionistic), `FdHilb` (quantum dagger), and `Frm` (topological / locale-theoretic). In each base, the universal P-axioms specialise to known invariants (Arf / discriminant; Heyting implication; dagger-symmetric form; frame morphism classification respectively). The intended single Universal Sayability theorem is

> ★ For any SMCC `C` with biproducts and chosen `δ ∈ Obj(C)`, every T_GUT-model `M : T_GUT → C` is naturally equivalent to the canonical model `R_C : N ↦ δ^⊗N`.

The novel contribution I think this framework offers is a concrete attack on Coecke-Heunen 2016 and Heunen-Karvonen 2019's identified open problem **O1** (dagger structure and cartesian closure cannot coexist on the same objects of a single category). I attempt to address O1 by *factorization*: the T_GUT skeleton is the universal part, and dagger structure arises only as a property of the `FdHilb` factor — never as a generator in T_GUT itself. Our Lean infrastructure (0-sorry on the algebraic case and partial scaffolding for `R → Pauli → Hilb`) is intended as concrete evidence that this factorization is not merely hand-wavy.

I lay out below: §1 the technical background (so you can decide quickly whether we are past the "is this serious?" hurdle); §2 the precise framework definition; §3 the O1 attack; §4 six specific questions where your expertise is critical; §5 the explicit ask. I have tried throughout to be direct about what I do and do not know.

---

## §1. Background context (what we have done)

Our framework is a recursive type-family `R N δ` defined by `R 0 δ ≃ Unit` and `R (N+1) δ ≃ δ × R N δ`. The canonical case `δ = Bool` gives `R N Bool ≃ (Fin N → Bool)`. The structural claim — Universal Sayability — is that any formal articulation of "sayable content" satisfying axioms P1-P7 is structure-preservingly equivalent to `R N δ` for an appropriate realisation of δ. Axioms P1-P7 are: minimum distinction (P1), composition / direct sum (P2), relations / bilinear classification (P3), recursion / squaring (P4), Hom-as-content (P5), 4-fold modality (P6), atomic involution and Wedderburn anchor (P7a / P7b). They are forced from a single articulation seed (D1) consisting of eight items.

**What is closed (0 sorry / 0 new axioms in Lean 4 + Mathlib):**

- **GUT-A** (F₂-Boolean scope + a non-algebraic δ = Prop sibling): both directions of D1 ⟷ P1-P7 closure, formally proven.
- **GUT-B** (polymorphic): layerwise type equivalence proven for any `[Fintype δ] [DecidableEq δ] [Inhabited δ]`; ring isomorphism at carrier 4 proven for any `Field k`. Concrete demos at δ = `Distinction`, `ZMod 3`, `Fin 5`; cross-instance bridge `R N Bool ≃ R N (ZMod 2)`; discriminant-based bilinear classification for char(k) ≠ 2 finite fields (`DiscriminantCharNeq2.lean`, completed 2026-05-17).
- **Five-sense R₄ minimality**: `R 4` is structurally minimal in 5 independent senses (cardinality 16, ring iso `Mat₂(F₂)`, squaring decomposition, V₄ Shi forcing on R₂, cardinality rigidity for any P1-P7 candidate), collected in `R4Minimality.lean`.
- **Metalogic identification** (separate paper, `lawvere-identification.md` v0.6): the bi-directional closure D1 ⟷ P1-P7 is rigorously identified as **D1 = lfp(Φ')** — the Knaster-Tarski least fixed point of a carrier-growing requirements-extraction operator Φ' on a candidates lattice 𝒜. Literal Lawvere 1969 fails by cardinality (`|T^T| > |T|` for any non-trivial finite T) and we replace point-surjectivity with *self-internalisation* (hom-closure + product-closure of R-Vec on `{R N}` — proved as `linHomEquivR_NM : LinHom N M ≃ R (N · M)` and `squaringEquiv : R (N + N) ≃ R N × R N`).
- **Empirical falsification record**: HoTT, ETCS, and SDG have been formally tested as falsifier candidates in Lean (`D6_Tests.lean`); each fails to falsify with a documented structural reason.

**What is open (the GUT-C gap)**:

The current statement requires *all* P1-P7 to hold uniformly. For non-algebraic δ this breaks: P3 (bilinear classification) and P7b (Wedderburn anchor `R 4 ≅ Mat₂(F_q)`) are fundamentally algebraic-specific. For δ = Prop, P3 and P7b fail entirely; for δ = FdHilb, only symplectic forms / dagger-symmetric forms specialise; for δ = Frm, only the frame morphism / lattice version applies. The patchwork approach of "make P-properties class-parametric" (what we call Path A) runs into a deeper problem: even the *concept* of "bilinear" or "Wedderburn anchor" does not lift naturally to non-algebraic contexts.

It is this gap that motivates the framework reformulation in §2.

I should also be candid about one preliminary metalogic worry. Our companion paper `lawvere-identification.md` carries a non-paradoxicality argument that the candidate lattice 𝒜 has no global negation; if a reviewer can construct an operator on 𝒜 that recovers Russell-style paradox at the *meta*-level, the metalogic embedding I describe here is in trouble. I am noting this so that you know we are not assuming the metalogic question is settled — only that, as of v0.6 of `lawvere-identification.md`, the non-paradoxicality argument is the one we are willing to be tested against.

---

## §2. The framework: T_GUT as a biproduct-enriched Lawvere theory

### §2.1 Definition

Following the precise conventions of Power 1999 (TAC 6 no. 7, §2-§3) for V-enriched Lawvere theories — and Hyland-Power 2007 (ENTCS 172) for the dual finitary-monad correspondence — we propose:

> **Definition (T_GUT)**. Let `V` be the (large) 2-category of SMCCs with biproducts. T_GUT is the small V-enriched Lawvere theory whose objects are an ℕ-indexed family `{X_N : N ∈ ℕ}` with chosen generator `δ_T := X_1`, equipped with V-enriched-finite products giving `X_N ≅ δ_T^⊗N`. Morphisms are generated by the family corresponding to P1-P7, modulo the equations listed in §2.2.

Generators (intended correspondence with our P-axioms):

| Generator | Type | Encodes |
|---|---|---|
| `id_δ : δ_T → δ_T` | identity | P1 (distinction) |
| `compose_{N,M} : δ_T^⊗N ⊗ δ_T^⊗M → δ_T^⊗(N+M)` | direct sum embedding | P2 (composition / biproduct) |
| `relate_{N,M} : δ_T^⊗N → δ_T^⊗M` | morphism family | P3 (relations) |
| `square_N : δ_T^⊗N → δ_T^⊗(2N)` | doubling | P4 (squaring / scale) |
| `hom_{N,M} : (δ_T^⊗N ⊸ δ_T^⊗M) → δ_T^⊗(N·M)` | curry/uncurry | P5 (Hom-as-content) |
| `modal_{V_4} : δ_T → δ_T^⊗2 ⊗ δ_T^⊗2` | V₄ embedding | P6 (4-fold modality) |
| `atom_3 : δ_T^⊗3 → δ_T^⊗3` with `atom_3^2 = id` | involution | P7a |
| `wedderburn_4 : δ_T^⊗4 ≅ End(δ_T^⊗2)` | endomorphism iso | P7b (generalised) |

### §2.2 Selected equations (intended)

- (P4 squaring closure): `square_N = (id ⊗ id) ∘ Δ_N` where Δ_N is the diagonal of δ_T^⊗N.
- (P5 currying): `hom_{N,M}(curry f) = ε_f` natural in `f : δ_T^⊗N → δ_T^⊗M`.
- (P7b Wedderburn): `wedderburn_4 ∘ wedderburn_4^{-1} = id` with appropriate naturality in the M-direction.

### §2.3 Universal Sayability across SMCCs

> **Theorem (proposed; not yet proved)**. Let `C` be an SMCC with biproducts and chosen `δ ∈ Obj(C)`. Let `R_C : T_GUT → C` be the canonical T_GUT-model sending `δ_T ↦ δ` (i.e., `X_N ↦ δ^⊗N`). Then for any V-functor T_GUT-model `M : T_GUT → C`, there exists a natural T_GUT-model isomorphism `M ≅ R_C`.

### §2.4 Intended specialisations

| Base `C` | δ | `M ≅ R_C` means |
|---|---|---|
| `FinVect_{F_q}` | F_q (= 1-dim) | M = R-family-over-F_q — recovers existing 0-sorry GUT-A/B |
| `HeytAlg` | Prop | M = Heyting R-family — NEW (GUT-Heyting) |
| `FdHilb` | ℂ² (qubit) | M = quantum stabiliser-style R-family — NEW (GUT-Quantum) |
| `Frm` | Ω (Sierpinski) | M = topological R-family — NEW (GUT-Topological) |

The intended payoff: a single theorem, in standard enriched-categorical language, that subsumes algebraic / Heyting / quantum / topological as instances. The `FinVect_{F_q}` case should reduce — under straightforward translation — to our existing `T5_general` theorem (currently in `UniquenessGeneral.lean`).

### §2.5 Why we believe biproduct-enrichment is the right level

All 4 target bases are SMCCs with biproducts. All have a canonical δ generator. In each, the construction `δ^⊗N` is intrinsic. Per our Mathlib survey (run as a parallel subagent against current Mathlib4 as of 2026-05), 70-80% of the categorical substrate already exists: `MonoidalClosed`, `HasFiniteBiproducts`, `FGModuleCat`-as-SMCC, `MarkovCategory`, `CopyDiscardCategory`, the bicategory of V-enriched categories. What is missing — `LawvereTheory`, `EnrichedLawvereTheory`, weighted enriched limits — is the substrate we propose to contribute upstream (~1600-2600 LOC across 3 PRs identified in our GUT-C doctrine document).

We are aware this means about 6-12 months of upstream contribution work runs in parallel with the framework instantiation. We are budgeting for this.

---

## §3. The novel contribution: attacking Open Problem O1

### §3.1 The problem (from the literature)

Coecke-Heunen 2016 (*Information and Computation* 250, "Pictures of complete positivity in arbitrary dimension") and Heunen-Karvonen 2019 (TAC 34, "Limits in dagger categories") identify a structural obstruction: **dagger structure does not interact cleanly with cartesian closure**. Specifically, products in a dagger category are biproducts, but a category cannot simultaneously be cartesian (for Heyting-internal reasoning) AND dagger compact (for quantum) on the *same* objects without collapsing.

For our framework this is acute, because the intended specialisations include both `HeytAlg` (cartesian-closed Heyting) and `FdHilb` (dagger compact). If T_GUT must carry both structures uniformly, the framework is dead on arrival.

### §3.2 The proposed resolution: factorization

Our move is to *not* place dagger structure inside `T_GUT` itself. Instead:

- **T_GUT (universal level)**: a biproduct-enriched Lawvere theory with the generators of §2.1. It does NOT carry a dagger generator.
- **Per-instance factor**: the dagger structure on `FdHilb` (and its compatibility with `wedderburn_4` etc.) arises from the *base category C*, not from T_GUT. The T_GUT-model `M : T_GUT → FdHilb` is required to be a V-functor — nothing more.

The intended consequence: dagger and cartesian closure coexist not "on the same objects of T_GUT" but as *separate δ-realisations* of one R-tower. The `FdHilb` factor provides dagger; the `HeytAlg` factor provides cartesian closure; the universal T_GUT skeleton stays neutral.

### §3.3 Why this might work

The structural reason this looks plausible is that the algebraic and quantum cases already give us a hint:

- For `δ = Bool`: the R-tower is finite F₂-Boolean. Wedderburn anchor gives `R 4 ≅ Mat₂(F₂)`. (`R4Minimality.lean`, line 110.)
- For `δ = qubit`: the Pauli quotient `𝒫_n / ⟨iI⟩ ≅ R_{2n}` over F₂. We have a partially built functor `R N → PauliN → Matrix (Fin 2^n) (Fin 2^n) ℂ` in `Foundation/Wen/Embeddings/HilbertPauliFunctor.lean` (definitions full, theorems for tensor-product compatibility scaffolded but not yet 0-sorry).

The Pauli/Wedderburn parallel suggests that the *same* R-tower bones support both classical-algebraic and quantum-dagger specializations — but dagger structure is added on the `FdHilb` side, not extracted from R itself. This is precisely the factorization claim.

### §3.4 Why this might fail

The most concrete worry: even if the *generators* of T_GUT carry no dagger, the *V-functoriality* requirement on a T_GUT-model `M : T_GUT → FdHilb` may implicitly force dagger-compatibility on M (because the morphisms in the dagger compact category `FdHilb` itself carry dagger). If so, the "factorization" claim is illusory — the dagger leaks into M.

This is the specific question I most want your view on (§4 Q2).

---

## §4. Specific questions for Professor Power

These are the six places where your expertise on enriched Lawvere theories vastly exceeds mine. I have tried to phrase them precisely enough that brief answers (yes / no / partial — with one-line reasoning) would already be valuable.

### Q1. Is the proposed T_GUT a well-formed V-enriched Lawvere theory under Power 1999 §3?

Specifically:

(a) **P5 (Hom-as-content) as a universal axiom**. Our existing Lean theorem `linHomEquivR_NM : LinHom N M ≃ R (N · M)` is provable in `FinVect_{F_q}`. The intended universal axiom is `hom_{N,M} : (δ_T^⊗N ⊸ δ_T^⊗M) → δ_T^⊗(N·M)` plus a coherence equation that the round-trip with curry is the identity. Is this a well-typed generator + equation in your enriched-Lawvere framework? Does it require weighted enriched limits (Kelly 1982), or do conical limits suffice?

(b) **P7b Wedderburn anchor**. In `FinVect_{F_q}`, P7b is `R 4 ≅ Mat₂(F_q)`. The intended universal form is `wedderburn_4 : δ_T^⊗4 ≅ End(δ_T^⊗2)`. Is "minimum endomorphism object" expressible as a δ-independent axiom in your framework? Or does P7b need to be replaced by a different axiom (e.g., a Morita-equivalence statement) for the universal level?

### Q2. Is Open Problem O1 within scope of SMCC-enriched Lawvere?

Specifically:

(a) Is the factorization strategy described in §3.2-§3.3 sound — i.e., can we keep dagger structure entirely outside T_GUT and have it appear only on the `FdHilb` factor via V-functoriality?

(b) Or does this require a stronger framework, e.g., a hypothetical *dagger-enriched* Lawvere theory? Has anyone in the categorical quantum community (Selinger, Coecke, Heunen, your own past collaborators) proposed such an extension?

(c) If a dagger-enriched-Lawvere extension is needed, is it (i) routine, (ii) hard, or (iii) infeasible with current categorical machinery?

### Q3. Does the T_GUT-model in `HeytAlg` recover a known structure?

We expect the `HeytAlg` instance to give Heyting algebras with some additional modal structure (corresponding to P6). Does this match anything in your recent operational-semantics work (Garner-Power 2018)?

In particular: is there a published characterization of "Heyting algebras enriched with 4-fold modality matching V₄ ⊂ S_4"? If yes, we want to compare. If no, our `HeytAlg` instantiation may yield a candidate definition.

### Q4. Is the proposed Universal Sayability theorem a Power-style theorem, or does it need a different framework?

The intended theorem (§2.3) says: for any SMCC C with biproducts and chosen δ, *every* T_GUT-model is naturally equivalent to the canonical model `R_C := N ↦ δ^⊗N`. This has the flavour of a "free models are unique up to natural equivalence" statement, which is standard for Lawvere theories. But the *naturality of δ across bases* introduces a 2-categorical (or higher) dimension that we are not sure is captured by standard enriched-Lawvere.

(a) Is this theorem provable using the framework of Power 1999 + Hyland-Power 2007 alone?

(b) Or does it require something like the doctrine of *2-Lawvere theories* (which I associate with Hyland-Power 2002 and Lack-Power 2009)?

(c) Or — most demanding — does the cross-base universality require (∞, 1)-enrichment in the sense of Lurie HTT? (We would prefer to avoid this; see Q5.)

### Q5. Is V = (∞, 1)-enrichment necessary, or is strict-1-categorical enough?

Our Lean codebase is built on strict-1-categorical Mathlib (with HoTT-style truncation only for proof-relevant `Prop`-targets). We would strongly prefer the framework to be strict-1-categorical for both implementation reasons (Lean / Mathlib) and conceptual reasons (less novel categorical infrastructure required).

(a) Is there an in-principle obstruction to strict-1-categorical T_GUT covering all 4 of our intended bases?

(b) Per Berman 2019 (arXiv:1903.02991), ∞-Lawvere ≃ finitary monads on spaces — for non-cartesian V, the relationship to Lurie's ∞-operads is conjectural. Does our framework run into this conjecture, or stay safely below it?

### Q6. Are there published results we are missing?

This is the most open-ended question, and likely the most valuable for us. Specifically:

(a) Are there results in your collaboration with Lack, Garner, Hyland, or Tanaka that would either *invalidate* the framework (i.e., a known no-go theorem we are reproducing) or *directly assist* it (i.e., a published universal-property characterization we can cite)?

(b) Has anyone published a precise statement of "biproduct-enriched Lawvere theory" as a doctrine in its own right? (Our literature search finds component pieces but no single canonical reference.)

(c) The Bohrification programme (Heunen-Spitters-Landsman 2009 *Comm. Math. Phys.* 291) is asymmetric — quantum encoded via internal intuitionistic logic of a topos built from commutative subalgebras. Is the symmetric unification (HeytAlg and FdHilb as parallel instances) something the categorical-quantum community has discussed, even informally?

---

## §5. What we are asking (concrete)

We are asking for **30-60 minutes of your time** to read this proposal and the companion documents (§6) and respond, at your convenience, on whether:

1. The framework as proposed is well-formed within enriched-Lawvere methodology, OR
2. It has a fundamental misframing that should be addressed before any Lean implementation, OR
3. It is a known no-go that has been investigated and abandoned by the categorical-quantum / categorical-logic communities.

We would value any one of those three responses; (2) and (3) would save us the most time. A short email with one-line answers to even a subset of §4's questions would be enormously useful at the framework-validation stage.

**Co-authorship signal**: if your input is substantive — that is, if it materially shapes the framework definition, the resolution of O1, or the encoding of P5/P7b as universal axioms — we would consider it natural to invite you as co-author on the resulting framework paper. We would discuss this explicitly before any submission. The intended target venue is *Theory and Applications of Categories* or *Logical Methods in Computer Science*, both of which carry your own work.

**On adversarial engagement**: we explicitly invite the response "this framework is wrong because X" with any X you find compelling. The whole point of this outreach is to test the framework before we commit 12-24 months of Lean engineering. A clear "no, because Y" — with Y identified — is the most valuable possible outcome.

**On declining**: we entirely understand if you do not have time. If you can recommend a graduate student, postdoc, or younger colleague better placed to respond, that would also be welcome.

---

## §6. Pointers

For full context (in order of recommended reading):

1. **`gut-c-doctrine.md` v0.2** (~3000 words) — the framework proposal in full, with literature integration, Mathlib survey, and risk analysis. The proposal in this letter is a condensed version of that document. Location: `docs-next/00_start/gut-c-doctrine.md`.

2. **`lawvere-identification.md` v0.6** (~33000 words; ~95% publication-ready) — the metalogic identification of D1 = lfp(Φ') in the Knaster-Tarski / Lawvere lineage. This is the companion paper covering the *vertical* (fixed-δ) direction of the framework; the present proposal covers the *horizontal* (cross-δ) direction. Location: `docs-next/00_start/lawvere-identification.md`.

3. **Lean codebase** (~3830 jobs, 0 sorry / 0 new axioms as of 2026-05-16):
   - `formal/SSBX/Foundation/R/Basic.lean` — R-family definition
   - `formal/SSBX/Foundation/R/R4Minimality.lean` — five-sense R₄ minimality (master theorem)
   - `formal/SSBX/Foundation/R/UniquenessGeneral.lean` — `T5_general` polymorphic uniqueness
   - `formal/SSBX/Foundation/R/UniquenessAlgebraic.lean` — ring iso for any field at carrier 4
   - `formal/SSBX/Foundation/R/Bilinear/DiscriminantCharNeq2.lean` — char(k) ≠ 2 case
   - `formal/SSBX/Foundation/R/D6_Tests.lean` — HoTT / ETCS / SDG falsification records
   - `formal/SSBX/Foundation/Wen/Embeddings/StabilizerQM.lean` — `𝒫_n / ⟨iI⟩ ≅ R_{2n}` over F₂
   - `formal/SSBX/Foundation/Wen/Embeddings/HilbertPauliFunctor.lean` — partial R → Pauli → Hilb functor
   - `formal/SSBX/Foundation/Closure/PhiOperator.lean` — Knaster-Tarski Φ operator (5/8 sorries discharged)

   Builds with `lake build SSBX` against Lean 4 + Mathlib (pinned in `lake-manifest.json`).

4. **`representation-closure.md` v0.1.3** — the philosophical synthesis (three-layer chain: concept / structure / instance), included for context on the cross-cultural lexical anchor work that motivates the V₄ 4-fold modality. Optional. Location: `docs-next/00_start/representation-closure.md`.

5. **`peer-engagement-draft.md` v0.1** (~3300 words) — the general outreach summary directed to multiple authors (you, Heunen, Shulman, Awodey, Jacobs/Klin). This present letter is the specific tailoring for you. Location: `docs-next/00_start/peer-engagement-draft.md`.

The whole repository is available at the contact below; we are happy to provide a tarball of the formal artifact, a Docker image with the Lean toolchain preconfigured, or a guided walkthrough.

---

## Closing

I am aware that this letter is written by a non-specialist asking a substantial question of an expert. I have tried to be technically specific everywhere I can be, and to flag honestly the places where my own framework understanding is shaky. I have done enough Lean formalisation work that I do not think I am wasting your time on a category-error-level confusion, but I am aware that the *framework* layer is exactly where category theorists like yourself will catch the kinds of errors that Lean cannot. That is precisely why I am writing.

The deepest reason I am taking the trouble to ask before committing to Lean implementation: the metalogic identification (`D1 = lfp(Φ')`) in our companion paper relies on Lawvere methodology already (Lawvere 1969's paradox-vs-fixed-point dichotomy, used to argue D1 is on the benign side of the dichotomy because 𝒜 has no global negation). If your enriched-Lawvere framework gives us the right machinery for the *horizontal* (cross-δ) direction, then the two papers together would constitute a comprehensive metalogic-and-doctrine treatment of articulation universality that is substantially stronger than either alone. If it does not — if O1 turns out to be fundamental in a way our factorization does not resolve, or if some other framework (dagger compact, ∞-topos, something else) is needed — we would much rather know now than in 12 months.

Thank you for your time. I am at renyongxu@gmail.com for any clarifying questions, or for a Zoom / Google Meet call if that would be easier than email. I am based in Beijing (UTC+8) and can accommodate any time zone.

Yours sincerely,

Yongxu Ren
renyongxu@gmail.com
https://github.com/[repository] (URL to follow)

---

## Appendix: Diagram (the proposed picture)

```
                            T_GUT
                  (V-enriched Lawvere theory;
                  generators encode P1-P7;
                  NO dagger generator)
                            │
                            │ V-functor T_GUT-model M
                            │ (per Power 1999 §3)
                            ▼
       ┌─────────┬──────────┴──────────┬──────────┐
       │         │                     │          │
  FinVect_{F_q}  HeytAlg            FdHilb       Frm
  (algebraic)  (Heyting,         (quantum,    (topological,
                cartesian-       dagger        locale)
                closed)          compact)
       │         │                     │          │
       ▼         ▼                     ▼          ▼
   R-family   Heyting R-fam       Pauli/         Topological
   over F_q   (NEW)               stabiliser     R-family
   (proved                        R-family       (NEW)
   GUT-A/B)                       (NEW)
                                      │
                                      ▼
                              ★ O1 resolution: dagger
                              is a property of the FdHilb
                              factor, not a generator of
                              T_GUT. The two flank cases
                              (HeytAlg cartesian-closed,
                              FdHilb dagger compact)
                              never sit "on the same
                              object" — they are
                              parallel δ-realisations
                              of one R-tower skeleton.
```

---

*Word count: ~3700. Format: markdown source for ease of editing; final version converted to plain-text email at send time. Draft v0.1 · 2026-05-17.*
