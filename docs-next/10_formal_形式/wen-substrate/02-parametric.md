# 02 — Parametric universality

> R-Family is parametric over a **realisation δ** of the primitive distinction. This chapter handles the **algebraic-class** δ-realisations — δ = k for k a ring or field. The non-algebraic δ-realisations (quantum basis labels, propositional `Prop`, per-language vocabularies, traditional 阳 / 阴) are first-class siblings, developed in chapter 03's distinction-monism discussion.

**Vocabulary discipline used throughout.** δ is the realisation parameter of the primitive distinction; k is the algebraic-class subset (δ = k carrying ring or field structure). F₂ is the minimum of the algebraic class. The substrate itself is realisation-free — see [01-foundations.md](01-foundations.md)'s "Four nested abstraction levels" table and [03-operation-monism.md](03-operation-monism.md)'s distinction-monism section for the substrate-level discussion.

Chapter 01 develops the substrate at the canonical δ = Bool ≅ F₂ realisation. This chapter lifts the same P1–P7 closure conditions to R-Family-over-k for arbitrary algebraic-class k. The lift is what makes the discrete-versus-continuous distinction a *base choice*, not a theory choice. Hilbert space, real analysis, p-adic analysis, modular arithmetic, finite Galois theory — they are not separate substrates "alongside" R-Family; they are different algebraic-class realisations of the same R-Family pattern. Non-algebraic realisations sit alongside as siblings, sharing the same realisation-free substrate level.

This chapter also separates two senses of "universal" that the rest of the document uses interchangeably and should not: encoding-universality (T1) and articulation-universality (T2). Both are real; they are not the same thing.

---

## Realisation classes and the algebraic case

The substrate's content splits cleanly into two layers — and that split sits inside a broader **realisation-class** split. The full picture: at the substrate level (chapter 03's distinction monism), R-Family is parametric over an arbitrary δ-realisation; the algebraic-class subset (δ = k for k a ring or field) is what this chapter develops. The Layer-A / Layer-B split below is *the algebraic-class face* of the broader δ-substrate.

**Layer A — the structural pattern (parametric, independent of k; lifts to a δ-independent substrate-level pattern under chapter 03).** R-Family-over-k is not the carrier family {k^N}_N alone. It is the structured object

$$\mathcal{R}^{(k)} = \bigl(\{k^N\}_N,\; \oplus_k,\; \mathrm{Hom}_k,\; \mathrm{Rel}^{(k)},\; \mathrm{Tower}^{(k)},\; \mathrm{Modality}^{(k)},\; \mathrm{Self}^{(k)}\bigr)$$

— the carrier family **plus** the P1–P7-over-k closure structure acting on the carriers: direct-sum composition, Hom-as-content recursion, the bilinear / quadratic relational layers (char-dependent), the squaring tower with cross-scale self-similarity, the modality carrier at R₂^{(k)}, the aspect-alphabet zong involution at R₃^{(k)}, and the atomic-operations ring at R₄^{(k)} ≅ M₂(k). The *pattern* is what is universal; without the closure structure, you have free k-modules, not R-Family-over-k. The expanded Layer-A inventory:

- Carriers indexed by ℕ₀, with cardinality \|R_N^{(k)}\| = \|k\|^N.
- Direct sum R_M^{(k)} ⊕_k R_N^{(k)} ≅ R_{M+N}^{(k)}.
- Hom-as-content Hom_k(R_n^{(k)}, R_m^{(k)}) ≅ R_{mn}^{(k)} as k-modules.
- Squaring tower with self-similarity (Δ, π, f^{⊕2}).
- Bilinear / quadratic relational layers (char-dependent details, below).
- Modality carrier R₂^{(k)} ≅ k².
- Atomic-operation algebra R₄^{(k)} ≅ M₂(k), the smallest non-commutative matrix k-algebra.
- Inverse-limit completion R̂^{(k)} = lim_← R_{2^j}^{(k)} with truncation bonding maps.

**Layer B — the choice of base k (varies per instance).** Pick k ∈ {F₂, F_p, F_{2^n}, F̄₂, ℝ, ℂ, ℍ, ℤ_p, ℚ_p, ℂ_p, ℤ/nℤ, …}. The choice determines cardinality (finite vs countable vs continuum), topology (discrete vs Cantor vs Euclidean vs p-adic), characteristic (2 vs p vs 0), algebraic closure, presence of i with i² = −1, Archimedean / non-Archimedean absolute value, and so on.

R-Family is universal as a Layer-A pattern; specific R-Family-over-k instances are Layer-A pattern applied to a Layer-B choice. Every formal articulation finds its native R-Family-over-k instance for the appropriate k.

---

## Instantiation table

The following enumerates **algebraic-class** δ-realisations (δ = k carrying ring or field structure). Non-algebraic δ-realisations are siblings developed in chapter 03; see the table at the end of this section.

| base k | R_N^{(k)} | char | topology | discrete? | native articulation domain |
|---|---|---|---|---|---|
| F₂ | F₂^N | 2 | discrete (Cantor at R_∞) | ✓ | Boolean logic, stabilizer QM (Pauli mod phase), finite computational formal systems |
| F_p (p ≠ 2) | F_p^N | p | discrete | ✓ | p-state classical structures, q-deformed objects |
| F_{2^n} | F_{2^n}^N | 2 | discrete | ✓ | finite Galois extensions of char-2 base |
| F̄₂ | F̄₂^N | 2 | discrete (countable) | ✓ | algebraic geometry over char 2 |
| **ℤ₂** (2-adic integers) | ℤ₂^N | **0** (residue char 2) | profinite (Cantor) | discrete↔continuous bridge | 2-adic arithmetic |
| ℚ₂ | ℚ₂^N | 0 (residue char 2) | p-adic locally compact | continuous | p-adic analysis |
| **ℂ₂** (Tate) | ℂ₂^N | 0 (residue char 2, residue field F̄₂) | p-adic, totally disconnected, complete | continuous | non-Archimedean amplitude (research direction) |
| **ℝ** | ℝ^N | 0 | Euclidean | continuous | classical mechanics, real analysis, calculus |
| **ℂ** | ℂ^N | 0 | Euclidean | continuous | **standard quantum mechanics (Hilbert space)** |
| ℍ (quaternions) | ℍ^N | 0 | Euclidean (non-commutative) | continuous | quaternionic / spin QM |
| ℤ/nℤ | (ℤ/n)^N | 0 / n | discrete | ✓ | modular / cyclic arithmetic |

Four rows carry the foundationally significant instances:

- **F₂** — minimum-base, discrete, fully computable, Lean-formalisable.
- **ℝ** — classical-physics base, continuous, Archimedean.
- **ℂ** — quantum Hilbert base, continuous, Archimedean, complex amplitudes.
- **ℂ₂** — non-Archimedean amplitude base, characteristic 0 with residue field F̄₂ of characteristic 2 (Tate's p-adic complex). Connection to the F₂ R-Family is *via the residue map* (𝒪_{ℂ₂} → F̄₂), not by characteristic identity. Mathematically a natural non-Archimedean alternative; physically a research branch (p-adic QM), not standard physics.

For the p-adic and Tate rows, the field / ring itself has characteristic 0; the connection to char-p R-Family is via the residue field of its ring of integers, not by characteristic identity. The "char" column reports the characteristic of k itself; residue characteristic is given parenthetically.

### Non-algebraic δ-realisations (siblings; full table in chapter 03)

The algebraic-class table above is one column of a broader δ-realisation table. Non-algebraic δ-realisations live alongside as siblings, each carrying its own per-domain structure rather than ring/field structure. Compactly:

| δ-realisation | δ type | algebraic? | additional structure |
|---|---|---|---|
| classical / Boolean (= F₂) | `Bool` | yes (field) | XOR, AND, ¬ |
| real / continuous | ℝ | yes (field) | order, completeness |
| complex / Hilbert | ℂ | yes (field) | Hermitian inner product (P3-enrichment) |
| p-adic | ℂ_p | yes (field) | non-Archimedean absolute value |
| quantum basis labels | `{|0⟩, |1⟩}` | **no** | ℂ-amplitude algebra attached separately |
| propositional / logical | `Prop` | **no** | proof-relevance |
| semantic / linguistic | per-language `L` vocabulary | **no** | per-language syntax / semantics |
| yi-jing traditional | 阳 / 阴 | **no** | classical-Chinese tradition overlay |

The algebraic-class rows admit the P1–P7 parametric story below. The non-algebraic rows require domain-specific relational structure in place of P3's F₂-bilinear / ℝ-bilinear / Hermitian forms; see chapter 03 for the substrate-level framing.

---

## P1–P7 parametric

Each necessary property of chapter 01 has a parametric formulation. "Suitable base" k means a non-trivial commutative ring (or field, for the cleanest statement).

**P1 — minimum distinction.** Any non-trivial base k supports binary distinction (k contains {0, 1} as elements). Among fields, **F₂ is uniquely minimum** — the smallest non-trivial field. For non-minimal bases (ℝ, ℂ, ℂ_p, …), P1 reads as "k extends the binary distinction with additional algebraic / topological content" (continuous amplitudes, multiplicative inverses, transcendentals, non-Archimedean absolute values, etc.). The minimality property singles out F₂ as the substrate floor; richer bases sit above as enrichments.

**P2 — composition.** R_M^{(k)} ⊕_k R_N^{(k)} ≅ R_{M+N}^{(k)} for every k, M, N. Fully parametric. Direct sum is the canonical biproduct in k-Mod for any base.

**P3 — relations, char-dependent.** This is the only P that has different shape across characteristics:

- *char(k) ≠ 2* (k = ℝ, ℂ, ℚ_p, …). Two-layer classification — symmetric (L₀) + alternating (L₁). The polarisation q(v) := ½ B(v, v) recovers a quadratic refinement from any bilinear form, so L₂ collapses into L₁. Classical: inner products + symplectic forms over ℝ or ℂ.
- *char(k) = 2* (k = F₂, F̄₂, F_{2^n}, …). Three-layer classification — L₀ + L₁ + L₂ as *independent* quadratic-refinement family (no polarisation shortcut since ½ does not exist), with Arf-invariant binary classification of L₂. This is the version of P3 used in chapter 01.

The structure of "relational layers" is parametric; only the count and specific form depend on char(k).

**P4 — squaring tower + self-similarity.** R_{2N}^{(k)} = R_N^{(k)} ⊕ R_N^{(k)} with Δ_N, π_i, f^{⊕2} as before. Fully parametric, no char dependence.

**P5 — Hom-as-content.** Hom_k(R_n^{(k)}, R_m^{(k)}) ≅ R_m^{(k)} ⊗_k (R_n^{(k)})^* ≅ R_{mn}^{(k)}. Ring structure on R₄^{(k)} ≅ End_k(R₂^{(k)}) ≅ M₂(k) as k-algebras, with the structural identity unfolding into different classical mathematical / physical structures depending on base:

- *char(k) = 2*: M₂(F₂) is the unique minimum non-commutative central simple F₂-algebra (Wedderburn-Artin) — 16 elements, GL₂(F₂) ≅ S₃.
- *k = ℝ*: M₂(ℝ) contains SL₂(ℝ) — the hyperbolic / Möbius group, foundational to 2D real Lie theory.
- *k = ℂ*: M₂(ℂ) contains the Pauli matrices and the complexified Lorentz Lie algebra 𝔰𝔩₂(ℂ), foundational to relativistic spinor physics.
- *k = ℂ_p*: M₂(ℂ_p) gives the p-adic spinor algebra over a non-Archimedean characteristic-0 base with residue characteristic p.

The same structural identity R₄^{(k)} ≅ M₂(k) — same closure condition P5, same forced ring structure — unfolds into different classical mathematical / physical structures depending on the base. The Wedderburn-Artin uniqueness statement applies parametrically: M₂(k) is the minimum non-commutative matrix algebra over any base k.

**P6 — 4-modality carrier.** R₂^{(k)} ≅ k² as k-module. For different k:

- *k = F₂*: 4 discrete elements with two commuting involutions — the classical R-Family modality structure (chapter 01).
- *k = ℝ*: continuous 2-plane; the discrete 4-element subgroup at {0, 1} × {0, 1} persists as the algebraic core; spinor representation also lives here.
- *k = ℂ*: 2-dim complex space = **spinor space**; the Pauli matrices {I, X, Y, Z} act on it; Pauli mod phase recovers the discrete 4-element structure from the F₂-shadow.
- *k = ℂ_p*: p-adic spinor space over a characteristic-0 non-Archimedean base with residue characteristic p; Pauli-analog operators exist since ℂ_p contains all roots of unity.

The 4-modality structural pattern persists across bases; specific instantiations vary from a discrete 4-element carrier (char 2) to continuous spinor representations (char 0).

**P7a — aspect alphabet at R₃^{(k)}.** R₃^{(k)} ≅ k³ with the squaring-tower-induced zong involution ζ : R₃^{(k)} → R₃^{(k)} (reverse of coordinates). The 本 / 征 split is:

- *k = F₂*: exactly 4 fixed elements (本-trigrams) + 4 zong-paired elements (征-trigrams).
- *continuous k*: Fix(ζ) = symmetric subspace ≅ k²; Comp(ζ) = antisymmetric subspace ≅ k; together R₃^{(k)}. The 4 + 4 partition becomes a (2 + 1)-dim split for continuous k — different cardinalities, same structural pattern (fixed vs anti-fixed of the involution).

**P7b — atomic operations at R₄^{(k)} ≅ M₂(k).** 16 atomic operations in the F₂ case; for continuous k, a continuum of atomic operations parameterised by M₂(k). The pattern 本-axis × 征-axis = atomic operation lifts uniformly across bases:

- *k = F₂*: 16 discrete atomic operations (the phenomenology matrix of chapter 01).
- *k = ℝ / ℂ*: continuous Lie-algebra atomic operations 𝔤𝔩₂(k); the 16 discrete cells of the F₂ case sit inside as the integer lattice.
- *k = ℂ_p*: p-adic continuous atomic operations 𝔤𝔩₂(ℂ_p).

---

## Minimality and "the" universal substrate, reframed

If R-Family is parametric, in what sense is the "**the** universal formal substrate" claim still meaningful?

**Three-tier claim.**

0. **R-Family at the substrate (distinction-monism) level is realisation-free.** Below the algebraic class, R-Family is the act of distinction iterated by Σ; no commitment to ring, field, amplitude algebra, or any other realisation structure. This is the layer chapter 03 develops; the substrate-level claim is "every formal articulation is `R' N δ`-articulable for an appropriate δ".
1. **R-Family-over-F₂ is the minimum algebraic-class realisation.** It is the smallest specific algebraic-class instance — the smallest base k admitting P1–P7 with ring structure. By P1, no smaller specific algebraic substrate suffices: anything smaller than F₂ cannot carry the algebraic P3 / P5 / P7b structure.
2. **R-Family (as parametric algebraic-class pattern) is universal across the algebraic class.** It is the structural pattern that any *algebraic-class* formal articulation (Boolean, real, complex, p-adic, modular, finite-field) instantiates as R-Family-over-k for an appropriate k.

Tier 0 answers "what is universal across **all** realisations, including non-algebraic ones?" — the substrate-level pattern of chapter 03. Tier 1 answers "what is the smallest algebraic-class realisation?" — F₂ R-Family. Tier 2 answers "what is universal across the algebraic class?" — the parametric R-Family pattern. Claim Z (chapter 07) is most precisely the statement:

> Every formal articulation is R-Family-over-some-k for an appropriate base k. The structural pattern (P1–P7) is universal; the choice of k is determined by the articulation's content (discrete vs continuous, classical vs quantum, Archimedean vs p-adic).

### Discrete and continuous as base properties

| property of base k | examples | R-Family instance |
|---|---|---|
| discrete, finite | F_p, ℤ/n | discrete finite R-Family-over-k |
| discrete, countable | F̄₂, F₂[[x]] | countable R-Family-over-k |
| profinite (char-0 lift of finite) | ℤ_p | discrete-continuous bridge |
| continuous, Archimedean | ℝ, ℂ, ℍ | continuous Archimedean R-Family |
| continuous, non-Archimedean | ℚ_p, ℂ_p | p-adic continuous R-Family |

So:

- "R-Family is discrete" was over-specific. The right statement is "R-Family-over-F₂ is discrete; R-Family-over-ℝ is continuous; etc."
- "Hilbert space is not in R-Family" was wrong. The right statement is "Hilbert space's carrier ℂ^N is the carrier of R-Family-over-ℂ at index N; with the full P1–P7-over-ℂ closure plus the Hermitian P3-enrichment, ℂ^N IS R-Family-over-ℂ at N." The carrier-only identification is necessary but not sufficient — see "Hilbert space and Hermitian P3-enrichment" below.
- "Continuous structures need enrichment" was a category error. Continuous structures live in R-Family-over-{ℝ, ℂ, ℂ_p, …}; those *are* R-Family instances, not enrichments of R-Family.

One structural pattern, many base instances. Discrete and continuous are not different substrates — they are different bases for the same parametric substrate.

---

## Hilbert space and Hermitian P3-enrichment

With the parametric framing, the duality between R-Family and Hilbert space is a single carrier-level identity:

$$\text{Hilbert space carrier } \mathbb{C}^{2^n} \;=\; R_{2^n}^{(\mathbb{C})} \quad \text{(R-Family-over-}\mathbb{C}\text{ at index } 2^n\text{).}$$

The relations between the bases that matter for quantum mechanics:

- 𝒫_n / ⟨iI⟩ ≅ R_{2n}^{(F₂)} — operator labels mod phase, R-Family-over-F₂ (stabilizer / discrete).
- ℋ_n ≅ R_n^{(ℂ)} — Hilbert state space carrier, R-Family-over-ℂ (standard QM).
- p-adic QM (Vladimirov-Volovich-Khrennikov, research direction) — R-Family-over-ℂ_p.

The two standard QM instances are F₂ (stabilizer / Pauli labels) and ℂ (full Hilbert). The ℂ_p instance is an optional research branch, one of several R-Family-natural amplitude bases, not the canonical R-Family amplitude domain. All three share the same parametric R-Family pattern, connected by mod-phase functor (Hilbert → Pauli labels) and representation functor (Pauli labels → Hilbert representation).

**Carrier identity vs full Hilbert-space structure.** The identity ℂ^{2^n} = R_{2^n}^{(ℂ)} holds *at the carrier level*. Hilbert space's distinctive content (Hermitian inner product, unitary group U(2^n), spectral theorem) is *additional Hermitian P3-enrichment* over the R-Family-over-ℂ carrier — separate from the core P1–P7 closure in char-2 form. The substantive content of the Hilbert identification is the **parametric lifting** of P1–P7 from F₂ to ℂ, not the trivial ℂ^N = ℂ^N carrier identification.

---

## Connection to modern unified frameworks

R-Family's parametric structure aligns with several modern mathematical frameworks that already unify discrete and continuous structures. These provide the technical machinery to articulate "R-Family across bases" rigorously.

- **Condensed Mathematics** (Clausen-Scholze, 2019+). Condensed sets / abelian groups / modules unify topological and algebraic structures via sheaves on profinite sets. R-Family-over-F₂ at the R_∞ inverse limit sits naturally as a condensed F₂-module; R-Family-over-ℝ and -ℂ sit as condensed ℝ- and ℂ-modules. All R-Family instances live in one ambient condensed category, with discrete-continuous unification provided by condensed theory's foundations.
- **Adic spaces** (Huber, 1996). Adic spaces generalise p-adic analytic geometry with both algebraic (formal scheme) and analytic (rigid analytic) fibres. R-Family-over-ℤ₂ is naturally an adic object whose special fibre is R-Family-over-F₂ (discrete) and whose generic fibre is R-Family-over-ℚ₂ (continuous p-adic). The adic framework already unifies these as different fibres of the same object.
- **Topos theory + synthetic differential geometry** (Lawvere-Kock-Joyal). Each topos provides an internal logic and internal R-Family. Different toposes give different R-Family flavours: discrete topos → R-Family-over-F₂; smooth topos → smooth (real-analytic) R-Family; étale topos → Galois-theoretic R-Family; condensed topos → R-Family across all bases simultaneously.
- **Stable ∞-categories / spectra** (Lurie). The R-Family squaring tower R_N → R_{2N} is the discrete shadow of a stable ∞-categorical structure. Different bases give different stable ∞-categories with shared axioms. Derived algebraic geometry over k gives one R-Family flavour; spectra give another.

R-Family does not need a new mathematical framework to support its parametric unification — the unification is already done in 21st-century foundations. R-Family's contribution is making the structural pattern foundationally explicit and listing the seven closure conditions (P1–P7) any base-instance must satisfy.

---

## T1 vs T2 — two senses of "universality"

A precise foundational document must distinguish two senses in which R-Family is "universal". They are different mathematical claims with different strengths. Conflating them is a real risk in any cross-base framework.

**Sense A — encoding universality (T1-level, single-base).** Every finitely-presented formal system admits an *encoding* as a binary string, hence as an element of ⋃_N R_N^{(F₂)}. This is essentially Gödel-coding + Turing-completeness; any computable / finitely-presentable structure can be coded as a finite binary string. R-Family-over-F₂ at the unbounded finite layer ⋃_N R_N supports this. **No other base is needed for sense A** — F₂ encoding-universality already covers everything formally describable at the encoding level. But sense A is **lossy**: it captures the syntax / bit pattern, not the natural algebraic operations. Continuous mathematics encoded as floating-point bit strings loses its analytic structure; quantum amplitudes encoded as binary expansions lose complex multiplication; etc. The encoding is faithful as a bijection of representations, but it does not preserve native operations.

**Sense B — native articulation (T2-level, multi-base).** Every formal articulation S admits a *structure-preserving translation* into some R-Family-over-k instance, with k chosen so that S's natural operations correspond to R-Family-over-k's natural operations (composition → composition, relation → bilinear, etc.). This is the strong universality. Native articulation requires the *appropriate base*: discrete combinatorial systems → R-Family-over-F₂; classical mechanics → R-Family-over-ℝ; Hilbert QM → R-Family-over-ℂ (standard physics); optional non-Archimedean / p-adic-amplitude research branch → R-Family-over-ℂ_p. The structure-preservation is what makes the R-Family articulation *natural* rather than a contingent encoding.

| | sense A (encoding, T1) | sense B (articulation, T2) |
|---|---|---|
| base required | F₂ alone | appropriate k per articulation |
| what's preserved | bit-pattern identity | native operations |
| universality claim | Turing-level | T2-level (parametric) |
| Lean code coverage | current implementation | future ℝ / ℂ / ℂ_p ports |
| used at | most coverage demonstrations (chapter 05) | parametric reframings (this chapter; quantum sub-section of chapter 05) |

Both senses are valid. Chapter 05's coverage demonstrations operate primarily at the **encoding** level — they show that mathematical / computational / linguistic content can be expressed in R-Family-over-F₂ via standard codings. This chapter and the Hilbert sub-section of chapter 05 operate at the **native articulation** level — they show that the appropriate R-Family instance directly represents the content's structure. The Claim Z statement of chapter 07 combines both: R-Family is universal in the encoding sense (T1, Turing-level) **and** in the articulation sense (T2, parametric).

**T2 in its δ-polymorphic layerwise form is now formally discharged** (2026-05-16, commit `a980e92`): see the "Polymorphic T5 — layerwise uniqueness over any Fintype δ" section below for the full statement. The discharge promotes "every formal articulation IS R-Family-over-some-k" from articulated hypothesis (the v1.3 status) to a Lean-verified layerwise theorem at any Fintype δ — F₂-Boolean is now the canonical specialisation, not the restriction. The ring-iso refinement at R₄ (i.e., the *full* GUT articulation theorem with algebraic structure preserved) remains δ-specific to F₂ for now; parametric extension to algebraic-class k is the remaining open item.

When a section says "X is R-Family", check which sense is meant. If X is an arbitrary computable / formal object, encoding sense: X embeds in ⋃_N R_N^{(F₂)}. If X is a structured object with native operations (Hilbert space, real manifold, p-adic field), articulation sense: X IS R-Family-over-k for the appropriate k.

---

## Polymorphic T5 — layerwise uniqueness over any Fintype δ

The T2-direction uniqueness theorem — "any P1–P7 closure-satisfying substrate IS R-Family" — has been formally discharged in its **layerwise δ-polymorphic form** (commit `a980e92`, 2026-05-16). The framework is no longer F₂-Boolean restricted at the layerwise level: F₂-Boolean is now the `δ = Bool` *specialization* of a polymorphic uniqueness claim that holds for arbitrary realisations.

**The polymorphic claim form.** For any realisation `δ : Type` carrying `[Fintype δ] [DecidableEq δ] [Inhabited δ]`:

$$\forall\,S : \mathrm{P1P7\_Core}\,\delta,\ \forall\,N,\ \mathrm{Nonempty}\bigl(S.\mathrm{carrier}\,N \simeq R\,N\,\delta\bigr).$$

`P1P7_Core δ` is the polymorphic minimum-data structure: a carrier family `carrier : ℕ → Type` plus `Fintype` / `DecidableEq` instances plus the core closure clauses (zero-cardinality, base-cardinality `|carrier 1| = |δ|`, direct-sum `carrier (m+n) ≃ carrier m × carrier n`). No ring structure is assumed; this is the algebra-free layerwise core.

The Lean theorem:

```lean
theorem T5_general {δ : Type} [Fintype δ] [DecidableEq δ] [Inhabited δ]
    (S : P1P7_Core δ) (N : ℕ) :
    Nonempty (S.carrier N ≃ R N δ)
```

**The four canonical δ-corollaries.** Each is a one-line specialization of `T5_general`:

| δ | corollary | nature of δ |
|---|---|---|
| `Bool` | `T5_general_at_Bool` | classical binary distinction (F₂ canonical case) |
| `Distinction` | `T5_general_at_Distinction` | substrate-primitive inductive type (chapter 03's o / x) |
| `Fin (n+1)` | `T5_general_at_Fin n` | n+1-state classical structures (multi-valued logic) |
| `ZMod (n+2)` | `T5_general_at_ZMod n` | modular arithmetic carrier (cyclic groups) |

The F₂-Boolean theorem `T5_A : ∀ S : P1P7_Satisfier_F2, ∀ N, S.carrier N ≃ R N` (commit `23441fc`) is now a *derived* corollary at δ = Bool via the forgetful map `forgetF2ToCore : P1P7_Satisfier_F2 → P1P7_Core Bool` and `T5_A_from_general`.

**Lean anchor.** [`Foundation/R/UniquenessGeneral.lean`](../../../formal/SSBX/Foundation/R/UniquenessGeneral.lean) delivers:

- `P1P7_Core δ` — polymorphic minimum-data structure.
- `R.card_eq_general` — `|R N δ| = (|δ|)^N` polymorphic cardinality.
- `T5_general` — layerwise type-equiv for any δ with Fintype + DecidableEq + Inhabited.
- Four δ-corollaries: `T5_general_at_Bool`, `T5_general_at_Distinction`, `T5_general_at_Fin n`, `T5_general_at_ZMod p`.
- `T5_general_squaring_compatible` — polymorphic squaring tower R_{2N} ≃ R_N × R_N respected.
- `canonicalRFamily δ : P1P7_Core δ` — the R-family itself as a canonical instance (non-vacuous sanity check).
- `GUT_B_layerwise` — aggregator packaging the polymorphic content as a single theorem.

**What this re-positions.** The framework is no longer "F₂-Boolean classical" specifically. The layerwise uniqueness statement holds for *any* Fintype δ; F₂-Boolean is the canonical realization but not the restriction. What remains δ-specific (post-this-discharge) is:

- **Ring iso at carrier 4** (`T5_A_ringEquiv_at_4`) — requires δ with ring structure; discharged for F₂ via `R 4 ≃+* Mat₂F₂`. Generalisation to char(k)=2 fields is trivial; char(k)≠2 needs Wedderburn-over-k (open as GUT-B/C ring iso).
- **Bilinear classification (P3)** — Arf invariant is char(k)=2 specific; discriminant replaces it for char(k)≠2.
- **P6/P7a alphabet pinning** — uses 4-element / 8-element cardinality, which generalize to `(|δ|)² = 4` only for δ = Bool.

These are the open items for the **full** parametric GUT claim (T5-B + T5-C scope; in progress).

---

## Code vs theory

Current Lean implementation in `formal/SSBX/Foundation/`: **δ-polymorphic with the canonical δ = Bool realisation as default** (Route 3B refactor, 2026-05-16):

```lean
def R (N : ℕ) (δ : Type := Bool) : Type := Fin N → δ
```

`R N` continues to mean `R N Bool = Fin N → Bool ≅ F_2^N` via the default argument — backward-compatible with all pre-v1.4 code that writes `R N` without an explicit δ. Polymorphic uses write `R N δ` explicitly (e.g., `R N (ZMod 2)`, `R N ℝ`, `R N Distinction`).

The primitive `Distinction` inductive type lives at [`Foundation/R/Distinction.lean`](../../../formal/SSBX/Foundation/R/Distinction.lean) (~230 LOC, zero sorry, zero axiom), together with the classical-computational bridge `Distinction.equivBool : Distinction ≃ Bool`. The substrate-level δ-parametric carrier `R' (N : ℕ) (δ : Type) : Type := Fin N → δ` from `Distinction.lean` is definitionally equal to the polymorphic `R N δ` from `Basic.lean` (they coincide on Bool by default).

The k-parametric carrier (algebraic-class) is in [`Foundation/R/Parametric.lean`](../../../formal/SSBX/Foundation/R/Parametric.lean):

```lean
def RFamily (k : Type _) (N : ℕ) : Type _ := Fin N → k

example (N : ℕ) : RFamily Bool N = R N := rfl
```

with `Fintype`, `DecidableEq`, and `Inhabited` instances when k carries the appropriate Mathlib structure. Hypothetical further instances awaiting Mathlib bridges:

```lean
-- Future:
-- def RR  (N : ℕ) := RFamily ℝ N           -- ℝ R-Family
-- def RC  (N : ℕ) := RFamily ℂ N           -- Hilbert ℂ^N = ℂ R-Family
-- def RCp (p N : ℕ) := RFamily (ℂ_[p]) N   -- p-adic R-Family
```

**Why the F₂ realisation is the discharged default in Lean.** Three reasons:

1. *Computability.* Lean's `decide` / `native_decide` tactics require finite computable types. F₂ is fully computable (every operation terminates with concrete result); ℝ and ℂ are not (they are non-computable as Mathlib types, using classical reals).
2. *Verification scope.* Phase I of the proof programme (chapter 08) is the finite / computable case — Lean is the right tool here. Continuous instances are theoretically meaningful but admit only partial Lean verification via Mathlib's classical real / complex theories.
3. *Mathlib coverage.* ℤ_p, ℚ_p are in Mathlib; ℂ_p is partial (under construction). Full p-adic R-Family Lean port is future work.

The theory is δ-parametric (substrate-level realisation-free); the algebraic-class refinement is k-parametric (this chapter); the canonical instance discharged in Lean is δ = Bool (F₂). This is the correct three-level separation:

- **Substrate** — `R N δ` for any δ (realisation-free; chapter 03's distinction monism). δ-polymorphic Lean primitive in `Foundation/R/Basic.lean` (with `δ := Bool` as the default).
- **Algebraic-class parametric** — R-Family-over-k for k a ring or field (this chapter). k-parametric carrier in `Foundation/R/Parametric.lean`.
- **Minimum discharged instance** — R-Family-over-F₂ via `δ = Bool` default (Occam-minimal, fully computable, Lean-verifiable). The bulk of the Lean codebase under `Foundation/R/{Basic, DirectSum, Tensor, Hom, Bilinear, Aut, ...}.lean` operates at this discharged default.
- **Other algebraic-class instances** — R-Family-over-ℝ, ℂ, ℂ_p (theoretical, require Mathlib classical foundations or specialised p-adic Lean libraries).
- **Non-algebraic δ-realisations** — quantum basis labels, propositional `Prop`, per-language vocabularies, traditional 阳 / 阴 (theoretical, awaiting per-realisation bridge files).

The fact that non-F₂ R-Family instances are not yet Lean-verified does **not** mean they are not R-Family. They are R-Family-over-δ for the appropriate δ by the substrate-level definition. The Lean coverage is a *verification frontier*, not a *theoretical limit*.

---

## Status

- [`Foundation/R/Basic.lean`](../../../formal/SSBX/Foundation/R/Basic.lean) — **δ-polymorphic** `def R (N : ℕ) (δ : Type := Bool) : Type := Fin N → δ` (Route 3B refactor, 2026-05-16). Default `δ := Bool` preserves backward compatibility for the ~2090 `R N` call-sites across the Lean codebase. δ = Bool–specific structure (`Add` / `Zero` / `Neg` / `Sub` via `Bool.xor`, `AddCommGroup` via XOR, cardinality `R N = 2^N`) installed for the default realisation. Build verified: `lake build SSBX.Foundation.R.Basic` ✓, `SSBX.Foundation.R.Bilinear` ✓, `SSBX.Foundation.Wen.Kernel` ✓.
- [`Foundation/R/Distinction.lean`](../../../formal/SSBX/Foundation/R/Distinction.lean) — primitive `Distinction` type with `Distinction.equivBool` bridge (~230 LOC, 0 sorry, 0 axiom). Provides the substrate-most-primitive layer (chapter 03).
- [`Foundation/R/Parametric.lean`](../../../formal/SSBX/Foundation/R/Parametric.lean) — `RFamily k N := Fin N → k` together with `Fintype`, `DecidableEq`, `Inhabited` instances and a `coord` reader. The algebraic-class parametric carrier; commits to the structure that `R N δ` lacks (algebraic axioms on δ = k).
- [`Foundation/R/UniquenessGeneral.lean`](../../../formal/SSBX/Foundation/R/UniquenessGeneral.lean) — **polymorphic T5 (layerwise)** discharged 2026-05-16 (commit `a980e92`). `T5_general` proves `∀ S : P1P7_Core δ, ∀ N, Nonempty (S.carrier N ≃ R N δ)` for any `[Fintype δ] [DecidableEq δ] [Inhabited δ]`. Four δ-corollaries (`Bool`, `Distinction`, `Fin (n+1)`, `ZMod (n+2)`) plus `T5_general_squaring_compatible`, `canonicalRFamily δ`, `forgetF2ToCore`, `T5_A_from_general`, `GUT_B_layerwise` aggregator. The F₂-Boolean `T5_A` from `UniquenessF2.lean` is now a derived δ = Bool corollary. 0 sorry, 0 axiom.
- [`Foundation/R/UniquenessF2.lean`](../../../formal/SSBX/Foundation/R/UniquenessF2.lean) — F₂-Boolean uniqueness `T5_A` plus `T5_A_ringEquiv_at_4` (ring iso at the smallest non-trivial layer) and `T5_A_squaring_compatible`. The ring-iso refinement remains δ-specific to F₂ pending parametric Wedderburn-over-k.
- The detailed P1–P7-over-k bridge files (direct sum, Hom-as-content, squaring tower, bilinear / quadratic relational structure, M₂(k) atomic operations) are **deferred to per-instance bridges**. For δ = Bool (the discharged default), the full P1–P7 content lives in `Foundation/R/{Basic, DirectSum, Tensor, Hom, Bilinear, Aut, Phantom, DirectDecomp, BeyondR8, Squaring, SubTower}.lean`.
- The companion document [`r-family-parametric-bases.md`](../r-family-parametric-bases.md) is the D3 single-source for the parametric concretisation (instantiation tables, char-dependent P3 detail, Hilbert reframing detail, p-adic research direction).

## Open / TODO

- Per-instance algebraic-class bridge files for k ∈ {ℝ, ℂ} via Mathlib's classical structures. Mathematically routine; mechanically substantial.
- p-adic instance (k = ℂ_p) blocked on full Mathlib ℂ_p infrastructure (currently partial).
- The Hermitian P3-enrichment that lifts R-Family-over-ℂ to standard Hilbert structure (unitary group, spectral theorem) is not yet packaged as a Lean theorem; it is presented at the prose level above and in `r-family-parametric-bases.md`.
- Cross-base functor library (mod-phase functor Hilbert → Pauli labels; representation functor Pauli labels → Hilbert) is not implemented in Lean.
- Connection to condensed mathematics / adic spaces / topos theory is documentary, not formal: there is no R-Family-internal-to-topos-T construction in Lean, only the prose argument that one would land in the appropriate topos.
- **Non-algebraic δ-realisation bridges** (Route 3B follow-on): per-realisation instance files for `δ = Prop` (propositional), `δ = qubit basis` (quantum, with ℂ-amplitude attached as separate enrichment), `δ` parameterised by a language L (semantic, with `Sayable_L` / `Silent_L` predicates), `δ = 阳/阴` (traditional, via Atlas overlay). The polymorphic `R N δ` admits these immediately; the structural / relational layers atop them are the open work.
