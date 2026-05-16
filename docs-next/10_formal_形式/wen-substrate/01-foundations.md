# 01 — Foundations

> R-Family is the universal formal substrate; the substrate itself is **the act of distinction, iterated by Σ**. This chapter says exactly what each of those words means, what necessary properties such a substrate must carry, what structure those properties pick out, and how the picked-out structure unfolds into a cosmological ladder R₀ → R₁ → ⋯ → R∞ — first at the substrate level (realisation-free), then in the canonical δ = Bool realisation that the rest of the chapter uses for concreteness.

The argument is one connected derivation:

1. Fix what "universal formal substrate" means (definitions D1–D6).
2. Show that any such substrate must satisfy seven necessary properties P1–P7.
3. Observe that the structure picked out by P1–P7 — the **R-Family** — is forced, not chosen.
4. Read the resulting R-tower (R₀, R₁, R₂, R₃, R₄, R₆, R₈, …, R∞) as the cosmological ladder from undifferentiated origin to infinite recursive depth, with physical content (spacetime, dynamics, events) appearing at the R₄ / R₆ / R₈ layers.

The companion chapters cover everything that lies on top of or beside this spine: chapter 02 lifts to parametric R-Family-over-k, chapter 03 reframes the substrate as an operation rather than a carrier, chapter 04 gives the type-level algebra the Lean code runs on, chapters 05–06 demonstrate coverage, chapters 07–08 carry the claim and the proof obligations.

### Four nested abstraction levels — what is "the substrate"?

The framework operates at four nested levels of abstraction, from most fundamental (level 0) to most concrete (level 3):

| level | name | what is primitive | example |
|---|---|---|---|
| 0 | **distinction monism** | the act of distinguishing `o` from `x` — the primitive binary distinction δ, no algebra assumed | `δ : Type` with at least two elements |
| 1 | **distinction-tuple substrate** | sequences of distinctions; cells are `R'_N := Fin N → δ`; Σ = direct-sum concatenation | distinction-tuples over any δ |
| 2 | **algebraic-class realisation** | δ carries a ring / field structure so cells become δ-modules; Hom-spaces inherit linear structure | δ = F₂, ℝ, ℂ, finite field |
| 3 | **canonical δ = Bool realisation** | the algebraic-minimum case: δ = Bool ≅ F₂, cells are F₂-vector spaces, R₄ ≅ M₂(F₂) | what the Lean code in `Foundation/R/Basic.lean` runs on |

Chapter 03 develops level 0 (distinction monism) in full. Chapter 02 develops level 2 (parametric R-Family-over-k). This chapter (01) develops the substrate at **level 3 — the canonical δ = Bool realisation** — for definiteness, while explicitly marking which claims hold at level 1 (substrate-level, realisation-free) versus which require level 2 or level 3 algebraic structure. The convention used below: `R'_N` denotes the substrate-level distinction-tuple cell over an unspecified δ; `R_N` denotes the δ = Bool reading `R_N := F₂^N`. The chapter writes "R_N" throughout for the canonical realisation; "R'_N" appears only when the substrate-level / realisation distinction is actively being established.

---

## What "universal", "formal", "substrate" mean

### Universal

A substrate is *universal* if every formally describable structure can be articulated within it. The distinction that matters: **articulation** is not the same as **encoding**.

- *Encoding* — an arbitrary bit pattern stands in for a structure. Lossy. Depends on the encoding choice. Trivial of every Turing-complete medium.
- *Articulation* — the substrate's own operations correspond to the target structure's natural operations. The translation preserves what the structure *is*, not merely how it can be serialised.

A universal formal substrate must do articulation, not just encoding. This is the distinction that separates the substantive claim from the empty observation that "everything reduces to bits".

### Formal

*Formal* means: expressible in mathematical / symbolic language; admitting precise specification; subject to logical operation. It is the standard reading. It includes all of mathematics, logic, language (qua structure, not meaning-as-experience), computation, physical theory, and any formal system. It excludes embodied / phenomenal aspects (qualia as lived), indeterminate metaphysical claims, and pure sensory content qua sensation.

### Substrate

A *substrate* is the foundation upon which other structures are articulated. To count as one, it must be:

- More fundamental than what it articulates;
- Self-contained (no external scaffold required);
- Self-articulating (its own structure expressible within itself);
- Stable (extending it does not change its character).

A universal formal substrate is what you get when the substrate's articulation reach is universal in the sense above.

---

## Why the question matters

If a universal formal substrate exists, formal systems share a common foundation, cross-tradition translation becomes systematic, and AI cognition (insofar as it is formal) has a determinate substrate. If no such substrate exists, formal systems are inherently plural and every cross-tradition translation is lossy. The history of foundational thinking — Russell, Frege, Bourbaki, Lawvere — has assumed substrates exist. We continue that lineage.

---

## D1 — formal articulation

A *formal articulation* is a structure-preserving expression of distinctions, compositions, relations, operations, and rules of transformation. Concretely, an articulation S consists of:

1. **Objects** — a collection of distinguishable objects Obj(S).
2. **Composition** — operations Comp(S) combining objects into larger objects.
3. **Relations** — predicates / pairings Rel(S).
4. **Operations** — transformations Op(S).
5. **Rules** — derivation / rewrite rules Rule(S).
6. **Recursion** — expressions of unbounded finite depth.
7. **Operation-as-content** — operations themselves expressible as objects.
8. **Modality (conditional)** — when S articulates content with process / change / temporal-or-causal dimension, S must carry a non-trivial multi-modal classification of articulated content. The minimum non-trivial multi-modal classification has four modalities.

Item 8 is *conditional*: it applies only to articulations whose content includes process / temporal / causal structure. Pure mathematical articulations (set-theoretic articulation of finite combinatorics, classical Boolean logic, untyped propositional calculus) may satisfy items 1–7 without invoking modal classification; in that restricted scope the analytic step D1 ⟹ P1–P7 (chapter 07) omits P6 and yields the weaker D1|₇ ⟹ P1–P5 + P7. When item 8 is operative, the 4-modality structure of P6 enters.

The standard formal frameworks — algebraic theory, Lawvere theory, finite-limit theory, institution, doctrine, computable presentation, syntax/semantics adjunction — each implement items 1–7 (item 8 applies if the framework includes process content).

## D2 — universal formal substrate

A *universal formal substrate* is a closed generative framework R such that every formal articulation S admits a structure-preserving translation S → R that preserves the relevant structure (distinctions, composition, relations, operations, derivation). The substrate is **closed** (generates its own continuation), **generative** (produces all needed structure internally), and **universal** (every formal articulation lands inside it under appropriate translation).

The 12-item explicit content of this definition lives in [`r-family-definition.md`](../r-family-definition.md), which is the canonical D2 single-source document. The structure-level summary appears below ("R-Family arrives").

## D3 — minimality

A universal formal substrate R is *minimal* iff it is generated from the smallest distinction and only those closure operations necessary for universal formal articulation:

$$R \;=\; \mathrm{Closure}\bigl(\text{smallest distinction};\; \{\oplus,\, \mathrm{Rel},\, \mathrm{Op},\, \mathrm{Rec},\, \mathrm{Self}\}\bigr)$$

where ⊕ is additive composition / direct sum, Rel is the relational layer, Op is operations-as-content, Rec is recursion / scale, Self is self-articulation. Minimality here is **not** "fewest symbols": a binary alphabet {0, 1} is already smallest at the encoding level (Turing-completeness over binary strings). Minimality is **closure-generative**: the smallest grammar generated from a minimum distinction under the minimum set of closure operations required for formal *articulation*, not merely encoding. The two are distinct.

## Equivalence and embedding

Two universal formal substrates R, R' are *equivalent* (R ≃ R') iff there exist structure-preserving translations φ : R → R' and ψ : R' → R that compose to identities under the relevant notion of structure preservation. Depending on context, ≃ specialises to strict isomorphism, categorical equivalence, Morita equivalence, bi-interpretability, or conservative translation equivalence. Equivalence does not require literal symbol-for-symbol identity: two substrates can have very different surface presentations and still articulate the same formal structure.

A *partial* formal system — one that articulates a restricted slice of formal structure without itself claiming universality — relates to R-Family by **embedding** S ↪ R: a structure-preserving translation that need not be surjective. Most concrete foundations sit here: propositional logic embeds into F₂-Boolean operations on R_N; first-order logic embeds into syntax-tree encodings over ⋃ R_N; lambda calculus, type theory (Martin-Löf, CIC, HoTT), algebraic theories, finite automata, stabilizer quantum mechanics, ZFC fragments for finite mathematics, programming languages — all embed as substructures. A *complete* minimum universal substrate — one that itself satisfies P1–P7 — relates by **equivalence** S ≃ R-Family.

The unified claim:

> Local formal systems embed into R-Family. Complete minimum universal substrates are equivalent to R-Family.

The embedding-vs-equivalence verdict for any specific foundation is provisional: if a system later admits an extended formulation satisfying P1–P7 in full, T5 (chapter 08) would reclassify it from "embeds" to "equivalent". HoTT and ETCS are obvious candidates for such reclassification once their modality / atomic-operation layers are made explicit.

---

## Necessary properties of any universal formal substrate

These are not optional features. They are forced by D1–D2. The chapter argues for each in turn, then synthesises.

### P1 — minimum non-trivial structure

A substrate cannot be empty (would articulate nothing) and cannot be trivial (a single element makes no distinctions). It must carry at least one binary distinction.

*Substrate level.* The smallest non-trivial structure is a primitive binary distinction — two abstract marks of an observable difference, conventionally `o` / `x`, with no algebraic commitment. This is **distinction monism** (cf. chapter 03's distinction-monism section): the framework's root primitive is the act of distinguishing, not any particular algebra.

*Algebraic-class realisation.* When the binary distinction additionally carries algebraic structure — i.e. when δ is taken in the algebraic class of realisations (chapter 02) — the smallest non-trivial field carrying this distinction is **F₂ = {0, 1}**, with addition modulo 2 (XOR) as the distinguishing operation. F₂ is the algebraic-class minimum realisation of the primitive binary distinction, not the substrate itself: every realisation δ admits a Boolean cross-section, and F₂ is the cross-section that additionally carries the minimum non-trivial ring structure.

→ **P1 forces the primitive binary distinction `o` / `x`; F₂ is its algebraic-minimum realisation.**

### P2 — composition

A substrate must allow structures to combine into larger structures; otherwise no complex structure can be articulated.

*Substrate level.* The substrate-level composition is **concatenation of distinction-tuples**. Define R'_N := Fin N → δ — a cell is a length-N tuple of distinctions. Concatenation gives R'_N ⊕ R'_M ≅ R'_{N+M}, additive in tuple length. This holds for any δ-realisation.

*δ = Bool realisation.* At δ = Bool the substrate-level cell R'_N becomes the F₂-vector space R_N := F₂^N, and concatenation is the linear-algebra direct sum with dim(V ⊕ W) = dim V + dim W. From here on the chapter writes R_N := F₂^N; this is the canonical reading of the substrate-level R'_N.

→ **P2 forces direct sum and the carriers R₂, R₃, R₄, ….**

### P3 — relational layers

Pure composition gives only collections of elements; a substrate must also allow elements to relate. Relations are formally captured by bilinear forms. The substrate-level claim is that relational structure is required; the *specific* three-layer classification below works at the δ = Bool realisation (it is the F₂-shape of the relational layers). Other algebraic δ-realisations (ℝ, ℂ, characteristic-zero fields; see chapter 02) yield the analogous classification with different equivalence-class counts — e.g. over ℝ the quadratic-refinement signature replaces the Arf binary invariant. The substrate-level reading: "the three relational layers exist whenever δ carries enough algebraic structure to support bilinear forms; at δ = Bool they organise as L₀ / L₁ / L₂-Arf."

The natural bilinear / quadratic structures on R_{2n} organise into three layers, exhaustively:

- **L₀ — symmetric (dot product):** ⟨u, v⟩ = Σᵢ uᵢ vᵢ, the unique non-degenerate symmetric F₂-bilinear form up to isomorphism. Captures geometric relations.
- **L₁ — alternating (symplectic):** on the canonical splitting R_{2n} = R_n ⊕ R_n with u = (u₁, u₂), v = (v₁, v₂), the form σ((u₁,u₂),(v₁,v₂)) = u₁·v₂ + u₂·v₁ is the unique non-degenerate alternating F₂-bilinear form up to isomorphism (alternating means σ(w, w) = 0; in characteristic 2 this is strictly stronger than antisymmetric).
- **L₂ — quadratic refinement (affine family):** for the fixed σ above, a *quadratic refinement* is a function q : R_{2n} → F₂ satisfying the polarisation identity q(u + v) + q(u) + q(v) = σ(u, v). The canonical refinement is q₀(u) = Σᵢ uᵢ uᵢ₊ₙ. All other refinements differ from q₀ by an F₂-linear functional ℓ : R_{2n} → F₂, so refinements form an F₂-affine space of dimension 2n with q_a(u) = q₀(u) + ⟨a, u⟩, giving exactly 2^{2n} refinements. Under symplectic isometries the refinements split into exactly two equivalence classes distinguished by the Arf invariant Arf(q_a) = Σᵢ aᵢ aᵢ₊ₙ.

L₀ and L₁ are individual forms (each unique up to iso). L₂ is a parametric family of quadratic forms whose equivalence-class structure has cardinality 2 via Arf. The classification has exactly three algebraic layers ⟺ four equivalence classes (1 symmetric + 1 alternating + 2 Arf-labelled quadratic-refinement classes), and is complete: no further independent layers exist.

→ **P3 forces the three relational layers — L₀ dot, L₁ symplectic σ, L₂ Arf-classified quadratic-refinement affine family.**

### P4 — scale and self-similarity

A substrate must accommodate structures of all sizes uniformly. The squaring tower is **substrate-level**: it operates on `R'_N` for any δ-realisation, since the squaring construction R'_{2N} = R'_N ⊕ R'_N uses only tuple-concatenation (P2). The named values R₂, R₄, R₈, … in this chapter are the δ = Bool readings of the substrate-level tower.

Operations f_N : R_N → R_N defined for each N should commute with direct sum: f_{2N}(u ⊕ v) = f_N(u) ⊕ f_N(v). Concretely, define a *squaring tower* R₁ ⊂ R₂ ⊂ R₄ ⊂ R₈ ⊂ ⋯, where R_{2N} = R_N ⊕ R_N. The tower is infinite — given (i) R₁ = F₂, (ii) direct sum as composition, (iii) closure, there is no maximum N.

The squaring tower carries strict cross-scale self-similarity:

- **Diagonal embedding** Δ_N : R_N ↪ R_{2N}, x ↦ x ⊕ x. Every scale is contained in its successor.
- **Factor projections** π₁, π₂ : R_{2N} ↠ R_N extracting the two summands. With Δ they realise R_N as both a subspace and a quotient of R_{2N}.
- **Operation lift** every f : R_N^k → R_N lifts to f^{⊕2} : R_{2N}^k → R_{2N} block-wise, with the commutativity square Δ ∘ f = f^{⊕2} ∘ Δ^k. The same operational structure appears at every scale 2^k.

These three pieces are forced by P2 + P4 alone — no extra structure is needed; **self-similarity is a consequence of the squaring tower, not an axiom**. The substrate is fractal in this precise sense.

→ **P4 forces the squaring tower R₁ → R₂ → R₄ → R₈ → ⋯ with cross-scale self-similarity (Δ, π_i, f^{⊕2}).**

### P5 — self-reference

A substrate must articulate its own operations; otherwise an external scaffold is needed (which would then be the actual substrate). Operations f : R_n → R_m must themselves be expressible as elements of the substrate.

*Substrate level — Hom-as-content.* The Hom-as-content statement is realisation-free in form: operations from R'_n to R'_m are themselves R'-cells of the appropriate size, and the canonical isomorphism Hom(R'_n, R'_m) ≅ R'_{nm} is the substrate-level claim. It rests only on the squaring-tower closure (P4) and the existence of a canonical pairing between operations and their content.

*Algebraic-class realisation.* When δ carries algebraic structure, the Hom space additionally carries δ-linear structure: Hom_δ(R'_n, R'_m) ≅ R'_{nm} as δ-modules. The cardinality count and the *ring* structure on the endomorphism algebra both depend on this algebraic-class hypothesis.

At δ = Bool, for F₂-linear f, the space Hom_{F₂}(R_n, R_m) has 2^{nm} elements. Basis-free, Hom_{F₂}(R_n, R_m) ≅ R_m ⊗_{F₂} R_n^*. After choosing bases for R_n, R_m, this is canonically isomorphic to R_{nm}. We write the canonical isomorphism with ≅, not =; the substrate's standard coordinate model makes it concrete and computable, but the foundational claim is the isomorphism, not literal equality. In particular Hom(R₂, R₂) ≅ R₄, Hom(R₄, R₄) ≅ R₁₆, Hom(R₈, R₈) ≅ R₆₄.

This is **Hom-as-content**: morphism spaces of R-Family are themselves R-Family elements. At non-algebraic δ-realisations (quantum basis labels, Prop-valued δ, semantic sayable / silent — chapter 02 catalogue), Hom-as-content still holds at the substrate level but the *ring* structure on R₄ requires the algebraic-class realisation.

**Ring structure as forced consequence (δ = Bool form).** The smallest non-trivial Hom space is R₄ ≅ Hom(R₂, R₂) = End(R₂), and End(R₂) carries a canonical ring structure (composition of endomorphisms = matrix multiplication). The moment one accepts Hom-as-content *at the algebraic-class realisation*, R₄ acquires the structure of M₂(F₂):

$$R_4 \;\cong\; M_2(\mathbb{F}_2) \quad \text{as } \mathbb{F}_2\text{-algebras, under the } \mathrm{End}(R_2) \text{ identification.}$$

This is forced — not chosen — within the algebraic class. By Wedderburn-Artin (a finite-dimensional-algebra-over-a-field theorem, hence algebraic-class-bound), M₂(F₂) is the unique minimal non-commutative central simple F₂-algebra; the substrate at δ = Bool is forced to articulate it at R₄. Iterating, every R_N has an internal endomorphism algebra of dimension N²: End(R_N) ≅ R_{N²}, with End(R_2^k) ≅ R_{4^k} ≅ M_{2^k}(F₂). In the limit, the inverse limit R̂ := lim_← R_{2^k} has cardinality 2^{ℵ₀} (continuum) and is topologically Cantor space.

→ **P5 forces Hom-as-content (Hom(R_n, R_m) ≅ R_{nm}) at the substrate level; the canonical ring structure on R₄ ≅ End(R₂) ≅ M₂(F₂) is the δ = Bool form, with Wedderburn minimality as an algebraic-class theorem; the inverse limit R̂ follows.**

### P6 — temporal / causal modality

Formal description includes physics. Physics has time. A universal formal substrate must accommodate temporal / causal structure. The 4-modality classification structure (道 / 已 / 今 / 未) is **substrate-level**: it is the count + partition structure of R'_2 over any δ that has at least two elements (which holds by P1, since δ ⊇ {`o`, `x`}), together with the two commuting involutions and their composite. The F₂-vector-space presentation and the two-bit `oo / xo / ox / xx` notation below are the δ = Bool reading. The Lorentzian-geometric argument is similarly independent of δ-realisation — it appeals only to the metric signature structure of any 4-dimensional Lorentzian tangent space.

The minimum non-trivial temporal classification has four modalities, conventionally:

| modality | meaning |
|---|---|
| 道 (eternal) | scale-invariant, applies at any time |
| 已 (past) | causally determined, cannot be changed |
| 今 (present) | locus of action, currently being determined |
| 未 (future) | possibility space, open to action |

**Why exactly four?** Two independent forcing arguments converge.

*Algebraic argument — minimum carrier.* A non-trivial modality classification needs more than binary (else it reduces to a single bit). By P1 + P2 + P4, the smallest non-trivial multi-modality carrier is R₂ = F₂^2 with 4 elements; nothing strictly between a 2-element carrier (R₁) and a 4-element carrier (R₂) fits the squaring tower. So the modality count is forced to 4, sitting on R₂.

*Geometric argument — Lorentzian causal structure.* At any event of a Lorentzian manifold, the tangent space decomposes by signature (+, −, −, −) into 3 metric-distinguished regions plus a null boundary, with timelike further split by time-orientation into past and future. Counted carefully: (timelike-past, timelike-future, spacelike, null) = 4 distinguished cells, forced by metric signature plus time-orientation.

The two arguments give the same count of 4 by independent routes. R₂ carries the 4 modalities as a 4-element F₂-vector space with two commuting involutions (toggle bit 0 = P; toggle bit 1 = T; their composite = PT):

| R₂ bit pattern | role | modality |
|---|---|---|
| `oo` | identity | 道 (eternal / spacelike) |
| `xo` | P | 已 (past) |
| `ox` | T | 未 (future) |
| `xx` | PT | 今 (present / lightlike boundary) |

R₂ is a *universal* 4-element carrier. In the cosmological emergence sequence (无极 → 太极 → 两仪 → 四象) it represents 四象 (yin-yang combinations), not the temporal modalities. The temporal / causal modalities emerge at the event level R₈ = R₆ ⊕ R₂, where the R₂ component carries temporal placement. Same algebraic carrier, different semantic role.

→ **P6 forces R₂ (substrate-level: R'_2 over the binary distinction) as the carrier of 4 temporal / causal modalities at the R₈ layer, by both algebraic and geometric routes.**

### P7 — aspect alphabet and atomic operations

A substrate must have atomic operations from which complex operations are constructed. An atomic operation has two semantic axes:

- **Kind (本):** what is being operated on (object / morphism / composition / void).
- **Manner (征):** how it acts dynamically (limit / momentum / event / fixpoint).

This split is not arbitrary; it tracks the **categorical / analytical bifurcation of mathematics itself**. Categorical mathematics (type theory, set theory, category theory) operates on the static "kind" axis; analytical mathematics (calculus, dynamics, measure theory) operates on the "manner-of-change" axis. Any substrate aspiring to articulate both must carry both axes. P7 has two sub-claims at adjacent layers.

**P7a — aspect alphabet at R₃.** *Substrate level:* the count R'_3 = 8 (three independent axes of binary distinction) and the 4 + 4 zong-involution split into 本 / 征 are combinatorial facts about the distinction-tuple structure, independent of δ-realisation. *δ = Bool:* the F₂-vector-space presentation, the ζ involution, and the bit-pattern enumeration below are the canonical Boolean form. Each operational axis is a 4-element classification (P6 per-axis). The alphabet of single-axis aspects — collecting all kind-aspects together with all manner-aspects — is

$$R_3 = \mathbb{F}_2^3 = 8 \text{ elements} = 4 \text{ kind-aspects} \cup 4 \text{ manner-aspects},$$

forced by P1 + P2 + P4 as the smallest carrier of single-axis operational aspects. The 4 + 4 partition is algebraically forced: it is the fixed-point / non-fixed-point decomposition under the natural zong involution ζ : R₃ → R₃, ζ(b₀, b₁, b₂) = (b₂, b₁, b₀) (reverse-order of bits, forced by the squaring-tower symmetry R₃ = R₁ ⊕ R₂).

- **本 (zong-fixed):** 4 elements {`ooo`, `oxo`, `xox`, `xxx`} satisfying b₀ = b₂. Mnemonic: 乾 ☰ / 离 ☲ / 坎 ☵ / 坤 ☷.
- **征 (zong-paired):** 4 elements {`oox`, `oxx`, `xoo`, `xxo`} organised as two zong-pairs. Mnemonic: 兑 ☱ / 震 ☳ / 巽 ☴ / 艮 ☶.

The 4 + 4 split is a theorem, not a labelling. The specific identification of the 4 本 trigrams with ⊤ / ⊥ / ⟶ / ∘ and the 4 征 trigrams with limit / momentum / event / fixpoint is the cultural mnemonic; the *count and partition* are algebraic.

**P7b — atomic operations at R₄.** A complete atomic operation requires both kind and manner simultaneously. *Substrate level:* the **count** 4 × 4 = 16 atomic operations is substrate-level (the product of two 4-element classifications, independent of δ). *δ = Bool:* the joint carrier identification R₄ = R₂ ⊕ R₂ as F₂-vector space and the ring-structure identification R₄ ≅ M₂(F₂) require the algebraic-class realisation. The joint atomic operation space is

$$R_4 = R_2 \oplus R_2 \cong R_2 \times R_2 = (4 \text{ kinds}) \times (4 \text{ manners}) = 16 \text{ atomic operations.}$$

Two independent forcing arguments converge again:

- *Direct sum of axes (substrate-level count).* Each axis is R₂ (P6 per-axis). The joint carrier is R₂ ⊕ R₂ = R₄.
- *Endomorphism algebra (Wedderburn — δ = Bool form).* By P5, R₄ ≅ End(R₂) ≅ M₂(F₂) as F₂-algebras. By Wedderburn-Artin and Wedderburn's little theorem (over F₂, the only finite division ring is F₂ itself), the simple finite-dim F₂-algebras are exactly M_n(F₂); among non-commutative such algebras, M₂(F₂) is the smallest. So M₂(F₂) is the unique minimal non-commutative central simple F₂-algebra — 16 elements. This uniqueness clause is algebraic-class-bound (finite-dim-algebra-over-a-field).

The two arguments are not coincidence: R₄ as vector space is identified with its own endomorphism algebra under Hom-as-content + the smallest non-trivial Hom. The 16 atomic operations *are* the 16 linear endomorphisms of R₂ (this identification holds at δ = Bool; the substrate-level count holds without it).

→ **P7a forces R₃ = 8 aspect alphabet, split 4 本 + 4 征 by the zong involution (substrate-level count + partition; F₂³ + ζ are δ = Bool form). P7b forces R₄ = 16 atomic operations (substrate-level count); in the δ = Bool realisation R₄ ≅ M₂(F₂) is the Wedderburn-minimum ring structure on the count.**

### Synthesis — three facets of one combinatorial fact

P6, P7a, P7b are three structurally distinct manifestations of the same combinatorial fact applied at three different layers: the minimum non-trivial **binary-distinction classification** with k independent axes has 2^k elements, organised as R'_k = δ^k. At the canonical δ = Bool realisation this is F₂^k. For k ∈ {2, 3, 4}:

| k | \|R_k\| | layer | property | what gets forced |
|---|---|---|---|---|
| 2 | 4 | modality | P6 | R₂ as 4-modality carrier (道 / 已 / 今 / 未 at the R₈ layer) |
| 3 | 8 | aspect alphabet | P7a | R₃ partitioned 4 + 4 by the zong involution (本 vs 征) |
| 4 | 16 | atomic operations | P7b | R₄ ≅ M₂(F₂) as joint kind × manner space + smallest non-commutative algebra |

They share machinery (minimum F₂-classification at k independent axes) but have structurally distinct *content*: group structure (P6), involution structure (P7a), ring structure (P7b). The recurrence of "forced 4-fold" is not redundancy — it is the substrate's combinatorial-fact engine running at three different scales.

| property | what it forces |
|---|---|
| P1 | primitive binary distinction `o` / `x`; F₂ is the algebraic-minimum realisation |
| P2 | direct sum (substrate-level concatenation of distinction-tuples) and the R_N tower |
| P3 | three relational layers: L₀ dot · L₁ σ · L₂ Arf-classified quadratic family (δ = Bool form) |
| P4 | squaring tower R_N → R_{2N} (substrate-level) with cross-scale self-similarity (Δ, π_i, f^{⊕2}) |
| P5 | Hom-as-content (substrate-level: Hom(R_n, R_m) ≅ R_{nm}) and the ring structure R₄ ≅ M₂(F₂) (δ = Bool form) |
| P6 | R₂ as the carrier of 4 temporal / causal modalities (substrate-level count + 4-fold structure) |
| P7a | R₃ = 8 aspect alphabet, split 4 本 + 4 征 by the zong involution (substrate-level count + partition) |
| P7b | R₄ = 16 atomic operations (substrate-level count); R₄ ≅ M₂(F₂) at δ = Bool |

---

## R-Family arrives

Taken together, P1 + P2 + ⋯ + P7b define a specific structure. That structure is **R-Family**. The 12-item explicit definition (canonical at [`r-family-definition.md`](../r-family-definition.md)) packages it as — with each item annotated as substrate-level (holds for any δ-realisation) or δ = Bool (algebraic-class realisation specific):

1. **Base elements** R_N := F₂^N for all N ∈ ℕ₀ (including R₀). *Substrate level:* R'_N := Fin N → δ; chapter-01 default realisation δ = Bool gives R_N := F₂^N.
2. **Undifferentiated origin** R₀ = {0} — 无极. *Substrate level.*
3. **Composition** direct sum R_M ⊕ R_N ≅ R_{M+N}. *Substrate level* (concatenation of distinction-tuples); ⊕ is the δ = Bool linear-algebra reading.
4. **Three bilinear / quadratic layers** L₀ symmetric ⟨·,·⟩, L₁ alternating σ, L₂ Arf-classified quadratic-refinement family {q_a}. *Algebraic-class realisation specific* (requires δ to carry bilinear structure); the Arf binary classification is the δ = Bool form.
5. **Squaring tower with cross-scale self-similarity** R₀ → R₁ → R₂ → R₄ → R₈ → ⋯ → R_∞ with Δ_N, π_i, f^{⊕2} commuting across scales. *Substrate level.*
6. **Self-referential morphism spaces** Hom_{F₂}(R_n, R_m) ≅ R_m ⊗ R_n^* ≅ R_{nm}. *Substrate level in form;* the δ-linear structure on the Hom space is algebraic-class.
7. **Canonical ring structure at R₄** R₄ ≅ End(R₂) ≅ M₂(F₂), forced by item 6 at the smallest non-trivial Hom space. *δ = Bool form of the algebraic-class realisation;* the substrate level says R₄ holds the 16 atomic operations, and the ring structure is realisation-specific.
8. **Recursive depth** R_∞ = R̂ = lim_← R_{2^k} — 万物. *Substrate level* (the inverse limit construction works on R'_{2^k}; the Cantor-space-cardinality identification holds at δ = Bool).
9. **R₂ as universal 4-modality carrier** takes different semantic content in different roles: 四象 cosmologically; the two-involution group on hexagrams; 4 征 trigrams in R₆; 道 / 已 / 今 / 未 in R₈. *Substrate level* (count + 4-role pattern); the F₂² presentation is realisation-specific.
10. **Aspect alphabet at R₃** = 8 trigrams partitioned 4 本 + 4 征 by zong involution. *Substrate level* (count + partition); F₂³ presentation + ζ involution are realisation-specific.
11. **Atomic operations at R₄** ≅ M₂(F₂) = 16 atomic operations as (本, 征) pairs / linear endomorphisms of R₂. *Substrate level count = 16;* M₂(F₂) ring structure is δ = Bool.
12. **Self-following** R-Family generates itself from R₀ to R_∞ via internal operations — 道法自然. *Substrate level.*

**R-Family is not a choice.** Each property forces a step; the resulting structure is what the steps add up to.

- P1 says: must have the binary distinction; F₂ is the algebraic-minimum realisation. No choice.
- P2 says: must have composition. Direct sum (substrate-level concatenation of distinction-tuples) is the only natural composition. No choice.
- P3 says: must have relations. The three bilinear / quadratic layers are mathematically exhaustive (at δ = Bool, the L₀ / L₁ / L₂-Arf form; other algebraic δ give the analogous classification). No choice.
- P4 says: must scale uniformly. The squaring tower with Δ / π / operation-lift self-similarity is what direct-sum-closure produces. No choice.
- P5 says: must self-refer. Hom-as-content is substrate-level; the R₄ ≅ M₂(F₂) ring structure as forced consequence by Wedderburn is the δ = Bool form of this self-reference. No choice within the algebraic class.
- P6 says: must have temporal / causal structure. R₂ as 4-modality carrier is the smallest such carrier by both routes. No choice.
- P7a says: must have an aspect alphabet. R₃ = 8 with the 4 + 4 zong split is the smallest single-axis carrier. No choice.
- P7b says: must have joint atomic operations. R₄ = 16 is the smallest joint carrier (substrate level); at δ = Bool, R₄ ≅ M₂(F₂) is the smallest non-commutative central simple F₂-algebra. No choice.

That R-Family also corresponds to known structures in quantum stabilizer formalism (Gottesman 1997), Wedderburn-Artin ring theory, symplectic geometry over F₂, topological SPT phases (Kitaev 2001, Kapustin 2014), symmetric monoidal categories, and the structure of the classical 易经 is *evidence of unforced emergence*, not coincidence. These traditions independently arrived at parts of R-Family because they were each exploring universal formal structure.

---

## R-tower as cosmological ladder

> The cells in the table below are abstract R'_N carriers at the substrate level; the named values, 字 trigram / hexagram identifications, and M₂(F₂) reading are the canonical **δ = Bool** realisation with the 易经 Atlas overlay. The cosmological ladder itself — R₀ → R₁ → ⋯ → R_∞ via the squaring tower — is substrate-level and runs for any δ-realisation; the cardinality column below counts elements at δ = Bool.

The squaring tower realises the 易经 cosmological sequence:

| 中国哲学 | R-Family | cardinality | content |
|---|---|---|---|
| 无极 | R₀ | 1 | undifferentiated origin |
| 太极 | R₁ | 2 | first distinction (existence) |
| 两仪 (阴阳) | elements of R₁ | (the two) | dual aspects |
| 四象 | R₂ — 太阳 / 少阳 / 少阴 / 太阴 | 4 | yin-yang combinations |
| 八卦 | R₃ — 4 本 + 4 征 | 8 | aspect alphabet |
| 时空 | R₄ ≅ M₂(F₂) | 16 | spacetime as invariant arena |
| 六十四卦 | R₆ = R₄ ⊕ R₂ (R₂ = 4 征 dynamical modalities) | 64 | spacetime + dynamics |
| 字 / 文 | R₈ = R₆ ⊕ R₂ (R₂ = 道 / 已 / 今 / 未 temporal modalities) | 256 | symbol / articulation |
| generation | R₁₆, R₃₂, … | 2^N | higher composite structures |
| 万物 | R_∞ | continuum | infinite recursive depth |

R₂ — the 4-element carrier — appears in four distinct roles across the tower with the same algebraic content and different semantic load: cosmological emergence (四象), Shi-level transformations on R₈ (the codebase's `Atlas/Yi/ShiV4.lean` realises this as `complement`, `reverse`, `cuoZong` plus identity, two commuting involutions and their composite), R₆ dynamical modalities (the 4 征 trigrams: 震 momentum / 艮 fixpoint / 巽 limit / 兑 event), and R₈ temporal modalities (道 / 已 / 今 / 未).

The classical 老子第四十二章 — **道生一, 一生二, 二生三, 三生万物** — maps onto: 道 = scale-invariant operations (the operative principle), 一 = R₁, 二 = R₂, 三 = R₃, 万物 = the full tower R₄, R₆, R₈, …, R_∞. The mathematical articulation matches the classical cosmological articulation, with R₄ / R₆ / R₈ as three critical articulation-enabling levels.

### R₄ and R₆ as 道 in algebraic form

Between the atomic operations of R₃ and the symbol space of R₈ sit two layers — R₄ (spacetime) and R₆ (spacetime + dynamics) — that carry the **invariant physical structure**, the algebraic embodiment of 道 understood as that-which-does-not-change.

**R₄ — the invariant arena.** R₄ admits two complementary views:

- *View A — vector space.* By definition R₄ := F₂^4. Reading the 4 bits as 4 spacetime coordinates gives 16 possible (x, y, z, t) configurations in binary discretisation: the points of spacetime.
- *View B — ring.* P5 (Hom-as-content) equips R₄ with a canonical ring structure: R₄ ≅ End(R₂) ≅ M₂(F₂) as F₂-algebras, with addition = XOR (inherited from the vector-space layer) and multiplication = composition of endomorphisms (concretely matrix multiplication once a basis for R₂ is chosen).

The ring structure is not intrinsic to R₄ as a bare vector space; it is added by P5 (the smallest non-trivial Hom forces an End-structure on its carrier). Once P5 is in force the ring structure is canonical up to basis choice. R₄ is then **simultaneously the manifold of spacetime points (view A) and the algebra of spacetime-preserving transformations (view B)** at the discrete F₂-algebra level. The unit group GL₂(F₂) ≅ S₃ is the structural-discrete analog of the Lorentz / Galileo symmetry pattern. (The full continuous Lorentz group lives over R-Family-over-ℝ or -ℂ as SO(1,3) or SL₂(ℂ); see chapter 02.)

**R₆ — spacetime + dynamics.** R₆ = R₄ ⊕ R₂ with 64 elements. Every R₆ element is a pair (state, dynamics-modality): the R₄ part is the spacetime state; the R₂ part is the type of change, with the 4 elements identified as 艮 (fixpoint / halt), 震 (momentum / rate), 巽 (limit / approach), 兑 (event / discrete transition). These are precisely the 4 analytical (征) atoms from the R₃ decomposition. R₆ is the discrete analog of phase space (configuration + momentum), playing the kinematic role.

**Why this *is* 道.** The defining property of 道 is invariance: the laws do not change. The ring structure on R₄ — which elements multiply how, which are invertible, the GL₂(F₂) ≅ S₃ unit group — does not depend on when or where you instantiate it: time-translation invariant, space-translation invariant, scale-invariant. The relationship between state and change in R₆ — that momentum-type change leads to certain transitions, that events partition continuous evolution, that fixpoints terminate dynamics — is not a property of any specific moment, it is the eternal law of how state and dynamics relate.

R₄ and R₆ are 道 *written in algebraic form*: not 道 as ineffable principle, but 道 as the invariant algebraic structure that governs reality at every scale and moment. This is precisely why the R₂ slot of R₈ = R₆ ⊕ R₂ carries the temporal modalities: when that slot is 道 (`oo`, eternal), the R₈ element represents the invariant law itself; when it is 已 / 今 / 未, the R₈ element represents that same law applied in past / present / future. All four temporal modalities reference the same R₆ law-content. The law is invariant (R₆); only the temporal placement changes (R₂). This is how physical law actually works.

| layer | what it carries | status |
|---|---|---|
| R₄ | spacetime points + transformations | the invariant arena |
| R₆ | state + dynamics | the invariant laws |
| R₈ | law + temporal placement | the full event |

R₄ is *where things happen*. R₆ is *how things happen*. R₈ is *a specific happening, placed in time*.

### R₄ phenomenology matrix — 4 本 × 4 征 = 16 cells

R₄ admits a third view beyond vector space and ring: the phenomenology matrix. It works at the δ = Bool realisation where R₄ ≅ M₂(F₂) carries the ring structure; the 4 × 4 (本, 征) factorisation reads off the row-index / column-index decomposition of the 2 × 2 matrix presentation. The 4 × 4 = 16 count is substrate-level; the matrix presentation is δ = Bool. It organises R₄'s 16 elements as a 4 × 4 matrix of (本, 征) pairs, where each cell names a specific phenomenological category. By P7b,

$$R_4 = R_2 \oplus R_2 \cong R_2^{(\text{本-axis})} \times R_2^{(\text{征-axis})} = 4 \times 4 = 16,$$

with each factor R₂ carrying 4 aspects: the 本-axis takes 4 kind-aspects (物 matter / 動 motion / 間 relation / 事 event), the 征-axis takes 4 manner-aspects (幾 limit / 勢 momentum / 機 event / 時 halt).

| 本 \ 征 | 幾 (limit) | 勢 (momentum) | 機 (event) | 時 (halt) |
|---|---|---|---|---|
| **物 (matter)** | 動 (subtle motion) | 行 (locomotion) | 化 (transmutation) | 流 (flow) |
| **動 (motion)** | 萌 (inception) | 長 (growth) | 發 (emergence) | 續 (continuation) |
| **間 (relation)** | 緣 (affinity) | 通 (passing-through) | 會 (encounter) | 系 (lineage) |
| **事 (event)** | 兆 (omen) | 趨 (trend) | 變 (change) | 史 (history) |

Each cell name is a single 字 capturing the phenomenological essence of that (本, 征) combination. The three views B (ring), C (phenomenology), and A (vector space) are mutually consistent: under the basis identification R₄ ≅ End(R₂), the (本, 征) factorisation corresponds to the row-index / column-index decomposition of a 2 × 2 matrix.

Column patterns make the phenomenology coherent: the 幾 column lists subtle-emergent phenomena (things barely arising); the 勢 column lists directional-momentum phenomena (things going somewhere); the 機 column lists transformative-event phenomena (things changing form); the 時 column lists durational-persistence phenomena (things continuing). Row patterns give matter's basic dynamics, motion's lifecycle, relational dynamics, event temporality respectively.

R₆ = R₄ ⊕ R₂ extends the matrix by an inner / outer trigram-type label: the 64 hexagrams classify into 4 quadrants {本本, 本征, 征本, 征征} of 16 each. This trigram-type label (zong-fixed vs zong-paired in R₃) is distinct from the 本-axis / 征-axis *factorisation* of R₄ above — though both descend from P7a's zong split. The trigram label gives 4 + 4 = 8 trigrams (single-axis aspects); the axis factorisation gives 4 × 4 = 16 atomic operations (joint kind + manner). Different layers; both forced.

### R₈ as articulation level

R₈ is *not* the smallest possible formal-language layer. R₁ = {0, 1} is already Turing-complete at the encoding level; any formal language can be encoded over R₁^* as a finite-string substrate. R₈ is the smallest layer at which the substrate's own structural conjunction of hexagram-situations and modalities crosses into the byte / character / qubit-label regime where it has historically been recognised as an articulation unit:

- 256 elements = R₆ ⊕ R₂ = (situation, temporal modality)
- byte-level computing = R₈ ≅ {0, 1}^8
- ASCII / extended-ASCII / single-byte character encodings
- the Chinese character inventory's most-frequent 256-character core
- the 4-qubit Pauli label space (smallest universal quantum register's label space)

This makes the substrate **self-referential at a culturally meaningful level**: the project name 文 refers precisely to this layer. The substrate is named after the level at which naming has, across multiple independent traditions, naturally crystallised. The internal structure of R₈ — its 16 × 16 grid, the D₄ operator group, four canonical diagonals (true X² main / anti-diagonal / palindrome / comp-palindrome), four high-symmetry quartets at the diagonal intersections, Hamming-weight concentric bands 1-8-28-56-70-56-28-8-1 — is developed in the companion document [`40_reference_参考/wen-x2-16x16-structure.md`](../../40_reference_参考/wen-x2-16x16-structure.md), with the 16 × 16 grid view complementing the 4 × 4 phenomenology of R₄ one squaring step down.

---

## Self-validation loop — 道法自然

A universal formal substrate must be **self-following**: if it required external scaffolding, that scaffolding would be the actual substrate. The Daoist phrase from 老子第二十五章 — 「人法地, 地法天, 天法道, 道法自然」 — captures this property as a doctrinal statement: 道 follows 自然 (itself, spontaneous nature), not external authority. R-Family is self-following in four distinct ways.

**(1) Hom-as-content self-reference.** Hom_{F₂}(R_n, R_m) ≅ R_m ⊗ R_n^* ≅ R_{nm}. Operations on R-Family are themselves R-Family elements. No external morphism scaffolding.

**(2) Squaring tower self-generation.** R_{2N} = R_N ⊕ R_N. Each layer generates itself from the previous via direct sum. No external push.

**(3) Internal cosmological passage.** R₀ → R₁ → R₂ → ⋯ → R_∞ is internal to R-Family. No external cosmology, no external Demiurge, no external First Cause.

**(4) Atomic operations self-contained at two layers.** The aspect alphabet R₃ = 8 (P7a) and the joint atomic operation space R₄ ≅ M₂(F₂) = 16 (P7b) together suffice for all subsequent operational structure. The ring multiplication on R₄ — the composition law of atomic operations — is itself forced by P5 at the smallest non-trivial Hom space, making the entire atomic-operation algebra internal.

A concrete witness of (4) at the R₈ layer: the locked-core set of 19 characters that serve as both position-字 (cell coordinates in the R₈ Cartesian grid) and operator-字 (named generators in the D₄ symmetry group and its extensions). The dual identity is not a coincidence of vocabulary — it is forced by Hom_{F₂}(R₄, R₄) ≅ R₈ (substrate-level statement: Hom(R'_4, R'_4) ≅ R'_8 holds for any δ-realisation; the F₂-linear and M₂(F₂)-ring readings are the δ = Bool form): operations on R₄ live within R₈, hence each operator necessarily admits a cell address. The R₈ Cartesian grid / D₄ symmetry concrete witness below is δ = Bool.

**Compare with other foundational candidates.** ZFC depends on first-order logic as external; type theory depends on a syntactic system (Lean kernel, Coq kernel) as external; category theory depends on metalanguage; pure Boolean algebra is too poor to articulate itself. None is fully self-following. R-Family alone is.

The cosmological loop closes:

```
                              道法自然
                                ↻
                                
        +───→  R₀ (无极)  ←─ identity (always available)
        ↓
        R₁ (太极 — first distinction)
        ↓
        R₂ (四象 — yin-yang combinations)
        ↓
        R₃ (八卦 — 4 本 + 4 征, atomic operations)
        ↓
   ★    R₄ (时空 — spacetime: points + transformations)  ★
        |    = M₂(F₂) = invariant arena of physical law
        |    = 4 本 × 4 征 = 16 phenomenology cells
        ↓
   ★    R₆ = R₄ ⊕ R₂ (六十四卦 — state + dynamics)        ★
        |    R₂ here: 4 征 dynamical modalities
        |    = 道 in algebraic form, invariant laws
        ↓
   ★★★  R₈ = R₆ ⊕ R₂ (字 / 文 — symbol/articulation)   ★★★
        |    R₂ here: 道 / 已 / 今 / 未 temporal modalities
        |    = where causality is added to invariant law
        |    = byte = canonical character set
        |    = complete event = where law meets time
        |    = where substrate self-articulates
        ↓
        R₁₆, R₃₂, … (compositions of symbols)
        ↓
        R_∞ (万物 — infinite recursive depth)
        ↑
        ↑ Hom-as-content recursion
        ↑ (operations live in R-Family)
        ↑
        +─── R_n ⟶ R_m via Hom(R_n, R_m) ≅ R_{nm}
                ↻
              (self-referential)
```

The structure begins at R₀ (undifferentiated) and generates R₁, R₂, …, R_∞ by internal operations. Key emergence levels at R₄ / R₆ / R₈ carry spacetime / dynamics / causality. The universal-4-carrier role of R₂ across multiple decompositions reuses the same algebra in different semantic roles. The whole structure is closed, self-following, complete in the precise sense above.

---

## Status

What is currently discharged in Lean, at the time this chapter was written:

- **P1–P7 packagings** are immediately available in [`Foundation/R/PhaseZero.lean`](../../../formal/SSBX/Foundation/R/PhaseZero.lean):
  - T_P3 — three-layer bilinear classification (L₀ symmetric, L₁ alternating, L₂ Arf-binary) discharged as concrete forms with their decomposition and Arf-codomain cardinality; the uniqueness-up-to-iso clause (no further independent symmetric / alternating non-degenerate forms over F₂) remains as a residual.
  - T_P6 — R₂ cardinality 4, the two commuting involutions (`complement`, `reverse`) and their composite `cuoZong`, the four canonical names {道, 已, 今, 未} pairwise distinct, all packaged on [`Foundation/Atlas/Yi/ShiV4.lean`](../../../formal/SSBX/Foundation/Atlas/Yi/ShiV4.lean); the uniqueness lemma + Lorentzian-4-region connection remain as residuals.
  - T_P7a — the zong involution on R₃ and the 4 + 4 split into 本 / 征.
  - T_P7b — R₄ ≅ End(R₂) ≅ Mat₂(F₂) as both `Equiv` and `RingEquiv`; the Mathlib bridge to `Matrix (Fin 2) (Fin 2) (ZMod 2)` plus the Wedderburn-Artin uniqueness clause remain as residuals.
- **R-Family carrier and direct-sum structure** are in [`Foundation/R/Basic.lean`](../../../formal/SSBX/Foundation/R/Basic.lean), [`DirectSum.lean`](../../../formal/SSBX/Foundation/R/DirectSum.lean), and the surrounding modules.
- **R₂ as Shi := R 2** and the 4-element V-naming sit in [`Foundation/Atlas/Yi/ShiV4.lean`](../../../formal/SSBX/Foundation/Atlas/Yi/ShiV4.lean); they are semantic naming on top of the carrier, kept in the Atlas namespace.

Foundation-level material on the squaring tower self-similarity (Δ, π_i, f^{⊕2} commutativity) and the parametric extension to bases other than F₂ live in their own chapters: see [02-parametric.md](02-parametric.md) for the parametric extension; see [04-partialcell.md](04-partialcell.md) for the type-level realisation in the Wen.Core machine.

## Open / TODO

- The L₂ Arf-classification "two equivalence classes" claim is currently only delivered as the *codomain cardinality* of `arf` in Lean; the symplectic-isometry equivalence of refinements within each Arf class is the standard Atiyah / Arf result, available in Mathlib's central-simple-algebra library but not yet wired in.
- The R₆ phase-space identification with classical mechanics is presented at the structural level (state + change modality), not via an explicit kinematic mapping to Hamiltonian flow.
- The R₂-as-universal-4-carrier claim is presented across four roles (四象 / Shi-transformations / R₆ dynamics / R₈ temporal modalities) but the cross-role equivariance theorem (single carrier acting consistently under each interpretation) is not formally proven.
- The Lean V₄-naming in `ShiV4.lean` is a legacy artefact from an earlier version of the framework where V₄ rhetoric was foregrounded; the algebraic content (R₂, two commuting involutions, their composite) is what is currently load-bearing.
- The δ-uniform substrate-level Hom-as-content statement (Hom(R'_n, R'_m) ≅ R'_{nm} for arbitrary δ-realisation) is currently asserted at prose level only; the δ = Bool case is discharged in [`Foundation/R/PhaseZero.lean`](../../../formal/SSBX/Foundation/R/PhaseZero.lean) and the distinction-monism root layer lives in [`Foundation/R/Distinction.lean`](../../../formal/SSBX/Foundation/R/Distinction.lean). A δ-parametric Lean discharge of Hom-as-content sits as future work alongside the chapter 02 parametric track.
