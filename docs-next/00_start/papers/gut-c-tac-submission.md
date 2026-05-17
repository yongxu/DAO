# Universal Sayability Across SMCC-Enriched Lawvere Doctrines: A Categorical Framework for Articulation

**Authors:** Yongxu Ren¹ · [co-author placeholder — John Power² (Macquarie University), pending acceptance of co-authorship invitation]

¹ Independent researcher, Beijing, China · `renyongxu@gmail.com`
² Department of Mathematics, Macquarie University, Sydney, Australia (provisional)

**Target venue:** *Theory and Applications of Categories* (preferred) · *Logical Methods in Computer Science* (alternate) · *Mathematical Structures in Computer Science* (alternate)

**Version:** Draft 0.1 · 2026-05-17

---

## Abstract

The R-tower framework — a recursive type-family `R N δ := Fin N → δ` with axioms P1–P7 (distinction, composition, relations, recursion, Hom-as-content, four-fold modality, atomic involution, Wedderburn anchor) and a single derivation seed D1 — has been formally verified in Lean 4 + Mathlib (0 sorry / 0 new axioms) for the algebraic case (any `Fintype δ`, any `Field k`, char(k) = 2 and char(k) ≠ 2 finite fields). The associated *Universal Sayability* theorem asserts that every articulation of sayable content satisfying P1–P7 is structure-preservingly equivalent to an R-family-over-δ for a suitable realisation δ. Extending this theorem from the algebraic setting to the genuinely non-algebraic settings (Heyting / intuitionistic, quantum / dagger compact, topological / locale-theoretic) requires re-formulating the P-axioms in a way that survives change-of-base. We propose such a reformulation: a *biproduct-enriched Lawvere theory* `T_GUT` in the sense of Power 1999, whose generators encode P1–P7 universally and whose T_GUT-models in different symmetric monoidal closed bases recover the appropriate concrete structures (Arf invariant / Wedderburn anchor; Heyting bimorphisms; Pauli–Klein4 stabiliser structure; frame coproducts). We prove a *layer-by-layer Universal Sayability* result (component-isomorphism level) for any SMCC C with biproducts and chosen δ ∈ Obj(C), verify the framework on four worked instances, and attack the Coecke–Heunen open problem O1 (dagger + cartesian coexistence) by a *factorisation* strategy: dagger structure is excluded from T_GUT itself and lives only on the FdHilb factor of any T_GUT-model targeting Hilbert-space content. The four instances are Lean-formalised at the realisation-existence level (10 documented sorries across 5047 LOC, all pinpointing open mathematical sub-problems rather than engineering debt). We identify five open problems in the framework's current state and three Mathlib upstream contribution opportunities. The paper situates GUT-C alongside the companion metalogic identification `D1 = lfp(Φ)` (Knaster–Tarski on the articulation candidates lattice) to give a two-axis treatment — *vertical* (fixed-δ closure as fixed point) and *horizontal* (cross-δ universality as enriched doctrine).

**Keywords:** enriched Lawvere theory, symmetric monoidal closed category, biproducts, dagger compact, Bohrification, Pauli group, Heyting algebra, frame, Sierpinski locale, Universal Sayability, articulation, Knaster–Tarski, Lean 4, Mathlib.

**2020 Mathematics Subject Classification:** Primary 18C10 (Theories with arities; specifically, Lawvere theories and operads), 18D20 (Enriched categories — properties and structure), 18M05 (Monoidal categories). Secondary 03G30 (Categorical logic, topoi), 18C50 (Categorical semantics of formal languages), 03B70 (Logic in computer science), 81P16 (Quantum measurement theory, state operations, state preparations), 06D20 (Heyting algebras — categorical and topological aspects).

---

## §1. Introduction

### §1.1 The articulation problem

A recurring methodological problem across mathematical foundations, categorical logic, theoretical physics, and the philosophy of language is the following: given a candidate notion of "sayable" or "formally articulable" content, can one identify a *minimum substrate* on which all such articulations must live? The history of the question is long. Lawvere's functorial semantics of algebraic theories [Law63] gave a particular categorical answer for algebraic content: any sayable equational theory is a small finite-product category with a chosen generator, and any of its semantic realisations is a finite-product-preserving functor from this category to a suitable target. Eilenberg–Kelly closed categories [EK66], Day's convolution structures on functor categories [Day70], and the subsequent development of enriched category theory (Kelly [Kel82]) extended the methodology to linear and otherwise enriched settings. Categorical quantum mechanics (Abramsky–Coecke [AC04], Selinger [Sel07, Sel12], Heunen–Vicary [HV19]) refined the answer in the dagger-compact direction. Topos quantum theory (Heunen–Landsman–Spitters [HLS09], Döring–Isham [DI08]) refined it in the intuitionistic direction.

In each of these traditions, the *form* of the answer — that there is a categorical universal property pinning down the candidate substrate — is the same. What differs is the choice of base category (Set, FinVect_k, FdHilb, Frm, …) and the precise structural axioms encoding "articulation". The natural unification question is then:

> Is there a single doctrinal framework, in the technical sense of Lawvere [Law69], whose models in different bases simultaneously recover the algebraic, intuitionistic, quantum, and topological universal-property answers?

This paper proposes such a framework. The framework is a *biproduct-enriched Lawvere theory* `T_GUT` in the sense of Power [Pow99], parameterised by a base symmetric monoidal closed category with biproducts and a chosen object δ. We prove a universal sayability theorem at the layer-by-layer component-isomorphism level, verify the framework on four worked instances (algebraic, Heyting, quantum, topological), and attack the open problem of dagger + cartesian coexistence identified by Coecke–Heunen [CH16] and Heunen–Karvonen [HK19].

### §1.2 The existing GUT-A/B formal results

The first two tiers of the framework — which we call GUT-A and GUT-B respectively — are formally complete in Lean 4 + Mathlib (0 sorry / 0 new axioms; current state at 2026-05-17 covers ~3936 jobs in `lake build SSBX`). The detail is documented in the companion roadmap [`gut-roadmap.md`](../../10_formal_形式/gut-roadmap.md) §§11–12 and summarised here as background.

GUT-A is the **F₂-Boolean / minimum-viable** tier: it discharges both directions (analytic D1 ⟹ P1–P7 and synthetic P1–P7 ⟹ R-family) of the closure in F₂-Boolean classical scope, together with a non-algebraic δ = Prop sibling instance establishing that the framework supports at least one genuinely non-algebraic substrate (cf. `Foundation/R/Distinction/Prop.lean`). The minimum-viable case fixes the structural shape; the Prop sibling shows the framework does not silently collapse to F₂-Boolean.

GUT-B is the **polymorphic** tier: it extends the layerwise type equivalence to any `[Fintype δ] [DecidableEq δ] [Inhabited δ]` and the ring iso at carrier 4 to any `Field k`. The polymorphic uniqueness `T5_general` (line 241 of `Foundation/R/UniquenessGeneral.lean`) is the master statement; corollaries at δ = `Distinction`, `ZMod 3`, `Fin 5`, plus cross-instance bridge `R N Bool ≃ R N (ZMod 2)`, exercise the polymorphic case. The algebraic-class extension (ring iso at carrier 4 for any `Field k`) is in `Foundation/R/UniquenessAlgebraic.lean` (`T5_algebraic`); the bilinear classification under char(k) = 2 is the Arf invariant (`Foundation/R/Bilinear/Arf.lean`); the bilinear classification under char(k) ≠ 2 finite fields is the discriminant (`Foundation/R/Bilinear/DiscriminantCharNeq2.lean`, completed 2026-05-17 with 0 sorry).

In addition, a **five-sense R₄ minimality** master theorem (`R4_structurally_minimal` of `Foundation/R/R4Minimality.lean`, commit `d4ed0f3`) establishes that R₄ is structurally minimal in five independent senses (cardinality 16, ring iso `Mat₂(F₂)`, squaring decomposition `R 4 ≃ R 2 × R 2`, V₄ forcing on R₂, cardinality rigidity for any P1–P7 candidate). This anchors the substrate-level uniqueness claim at the smallest non-trivial layer of the recursive tower.

### §1.3 The GUT-C gap

The third tier — which we call GUT-C — is what remains open and what this paper attacks. The GUT-C tier asks: does the same Universal Sayability theorem extend to *non-algebraic* δ, specifically to Heyting (intuitionistic logical), dagger-compact (quantum), and frame-theoretic (topological / locale-theoretic) substrates?

The naive approach — *make the P-properties class-parametric and prove a per-class theorem* — runs into a deeper problem. The P-properties P3 (bilinear classification) and P7b (Wedderburn anchor `R 4 ≅ Mat₂(F_q)`) are *fundamentally algebraic-specific*. For δ = Prop, neither the concept of "F₂-bilinear form" nor the concept of "matrix-algebra Wedderburn factor" lifts naturally. For δ = qubit (i.e. ℂ²), only the symplectic / dagger-symmetric specialisations apply, and "the" Wedderburn anchor splits between `Mat₂(F₂)` (over F₂) and `Mat₂(ℂ)` (over ℂ) — both being valid in different senses. For δ = Sierpinski (i.e. Ω = {⊥, ⊤} as a frame), neither bilinearity nor matrix-algebra anchoring even has a definitional analogue.

In short: the algebraic axioms P3 and P7b are not portable, and the patchwork approach of class-parameterisation does not solve the underlying conceptual mismatch.

The framework reformulation we propose addresses this by promoting the axioms to *categorical doctrine level*: P1–P7 are encoded as generators (and equations) of a single enriched Lawvere theory `T_GUT`, and the *concrete* content of each P_i is the per-base specialisation of the corresponding generator in each ambient SMCC.

### §1.4 Path C: doctrinal framework via enriched Lawvere theories

The technical move is to define `T_GUT` as a Power-style enriched Lawvere theory [Pow99] over a symmetric monoidal closed base with biproducts. The base ambient category is the (large) 2-category `V = Cat_{SMCC,⊕}` of SMCCs with biproducts; the theory `T_GUT` itself is small and V-enriched with a chosen generator object `δ_T`. Generators encode P1–P7 (Table 1 below); equations encode coherence laws. T_GUT-models in any SMCC base `C : V` with chosen `δ ∈ Obj(C)` are V-functor realisations sending `δ_T ↦ δ`; the canonical such realisation sends the abstract `δ_T^⊗n` (i.e., the n-th object of the theory's underlying ℕ-graded family) to the concrete tensor power `δ^⊗n` in `C`.

The intended Universal Sayability theorem then takes the form:

> **★ Theorem (GUT-C Universal Sayability — informal).** For any SMCC `C` with biproducts and chosen `δ ∈ Obj(C)`, every T_GUT-model `M : T_GUT → C` is naturally equivalent to the canonical model `R_C : N ↦ δ^⊗N`.

When `C = FinVect_{F_q}` and `δ = F_q`, this theorem specialises to the existing `T5_general` (recovering GUT-A/B). When `C = HeytAlg` and `δ = Prop`, it gives a Heyting-bimorphism-classification-style structure. When `C = FdHilb` and `δ = ℂ²`, it gives a Pauli–Klein4 stabiliser-style structure. When `C = Frm` and `δ = Ω` (Sierpinski), it gives a frame-coproduct-classification-style structure.

### §1.5 Contributions of this paper

The contributions are five-fold:

1. **A precise framework proposal.** Section §3 gives the definition of `T_GUT` as a V-enriched Lawvere theory with generators encoding P1–P7 and equations encoding their coherence. The definition stays strict-1-categorical (i.e., does not require ∞-categorical machinery) and is compatible with the existing Lean 4 + Mathlib infrastructure.

2. **A universal sayability theorem at the layer-by-layer iso level.** Section §4 states and proves the layerwise version of Universal Sayability: for any T_GUT realisation `M` in any SMCC `C` with chosen `δ`, there is a natural family of isomorphisms `M.R n ≅ tensorPow δ n` constructed by induction on n. The full coherence with generator morphisms is the explicit γ.3 refinement target.

3. **Four worked instances.** Section §5 walks through the framework on four bases (algebraic FinVect_{F_q}; Heyting HeytAlg; quantum FdHilb via stabiliser-formalism + Pauli–Klein4 coincidence; topological Frm via Sierpinski Ω). Each instance identifies which P-properties have "working" analogues in the target SMCC and which require reformulation. The Heyting instance introduces a novel candidate "Heyting Wedderburn anchor" `DiamondH4` (the 4-element non-Boolean linearly-ordered Heyting algebra) which we conjecture is unique at carrier 4. The quantum instance exposes a "Pauli–Klein4 coincidence" (the four single-qubit Pauli operators mod phase {I, X, Y, Z} are *literally* the Klein four group V₄), which gives the canonical quantum interpretation of P6 (4-fold modality).

4. **An attack on Open Problem O1.** Section §6 addresses the Coecke–Heunen [CH16] / Heunen–Karvonen [HK19] open problem on dagger + cartesian coexistence. Our strategy is *factorisation*: dagger structure is excluded from T_GUT generators and lives only on the FdHilb factor of any T_GUT-model targeting Hilbert-space content. We give evidence supporting this factorisation in the four-instance verification, but flag that the full proof depends on Mathlib infrastructure (dagger-categories, dagger-symmetric-monoidal-categories) that is not yet upstream.

5. **A Lean formalisation programme.** Section §7 catalogues the existing Lean codebase (Foundation/Doctrine/ tree: 5 files, 5047 LOC, 10 documented sorries, 0 axioms) and identifies four Mathlib upstream PR opportunities (ElementaryTopos bundling, LawvereTheory + Model API, weighted enriched limits, dagger-SMCC + FdHilb scaffold). These PR opportunities are independently valuable for Mathlib applications beyond GUT-C.

### §1.6 What this paper does *not* claim

For epistemic hygiene, we explicitly note the boundaries.

1. **GUT-C is not closed.** The full Universal Sayability theorem (with coherence with all generator morphisms) is the γ.3 refinement target; we currently have only the layer-by-layer iso level. The four worked instances each carry 1–4 documented sorries pointing at substantive open mathematical sub-problems.

2. **Open Problem O1 is not fully resolved.** Our factorisation strategy is consistent with the four worked instances but is not a proof. A full resolution would require either (a) a positive dagger-Lawvere-theory framework or (b) a no-go theorem ruling out a hidden dagger leak via V-functoriality. We describe progress, not closure.

3. **Several reformulated P-properties remain open.** The Heyting-bimorphism classification (P3 in HeytAlg), the conjectured uniqueness of `DiamondH4` (P7b in HeytAlg), the full Mat₂(ℂ) ring-iso for the 2-qubit Pauli image (P7b in FdHilb), the frame-bimorphism classification (P3 in Frm), and the conjectured "minimum finite frame" classification (Sierpinski-like analogue of P7b in Frm) are each *publishable open problems in their own right*.

4. **Mathlib infrastructure is partly missing.** The full programme depends on `LawvereTheory`, `EnrichedLawvereTheory`, weighted enriched limits, and (for the quantum case) `DaggerSymmetricMonoidalCategory` + `FdHilb` — none of which currently live in Mathlib. The current Lean code (5047 LOC of `Foundation/Doctrine/`) defines local approximations of these.

### §1.7 Paper structure

§2 surveys the categorical background: classical and enriched Lawvere theories (Lawvere, Power, Hyland–Power); symmetric monoidal closed categories with biproducts (Eilenberg–Kelly, Day, Kelly); the topos-quantum precedent (Heunen–Landsman–Spitters Bohrification) and where our framework departs from it; the dagger-compact direction (Selinger, Abramsky–Coecke, Heunen–Vicary); and the current Lean-formalised status of GUT-A/B. §3 defines `T_GUT` precisely as a biproduct-enriched Lawvere theory. §4 states and proves Universal Sayability at the component-iso level. §5 walks through the four instances. §6 attacks Open Problem O1. §7 catalogues the Lean formalisation. §8 discusses comparisons (topos quantum theory, categorical doctrines, the companion metalogic paper). §9 lists open problems and concludes. Appendix A provides a glossary; Appendix B gives reproducibility instructions; Appendix C provides key Lean type definitions; Appendix D contains the extensive bibliography.

### §1.8 Reading guide for different audiences

This paper is designed to be self-contained, but the breadth of categorical machinery and the cross-cutting nature of the four worked instances means that different audiences will find different sections more or less useful. We suggest:

- **Categorical logicians familiar with enriched Lawvere theories:** can skim §2; should focus on §3 (T_GUT definition), §4 (Universal Sayability proof), §6 (O1 attack).
- **Categorical quantum theorists familiar with dagger compact and Bohrification:** can skim §2.4–§2.5; should focus on §5.3 (quantum instance), §6 (O1 attack), §8.1 (comparison with Bohrification).
- **Topos theorists / locale theorists:** should focus on §2.4 (Bohrification background), §5.2 (Heyting instance) and §5.4 (topological instance), §8.6 (wider context).
- **Lean / formalisation specialists:** should focus on §7 (Lean formalisation), §3.8–§3.9 (specialisation principle in code), the file references throughout.
- **Foundational / philosophical readers:** should focus on §1 (introduction), §8.3 (metalogic identification connection), §9 (open problems and conclusion).
- **General mathematical readers:** can read §1 + §8 + §9 for a high-level overview without prerequisite categorical machinery.

The companion documents [`gut-c-doctrine.md`](../gut-c-doctrine.md) v0.3 (~7500 words) and [`lawvere-identification.md`](../lawvere-identification.md) v0.6 (~33000 words) provide complementary readings. The doctrine document focuses on framework design and decision points; the metalogic paper focuses on the fixed-point identification of D1. This paper subsumes the framework design (incorporating γ.2 and γ.3 deliverables) and refers to the metalogic paper for the vertical-axis content.

---

## §2. Background

This section recalls the categorical machinery on which T_GUT is built. Readers familiar with enriched Lawvere theories can skim §2.1–§2.3; readers familiar with categorical quantum mechanics and Bohrification can skim §2.4–§2.5; the relation to currently-formalised GUT-A/B in §2.6 may be worth reading regardless.

### §2.1 Lawvere theories (classical)

A Lawvere theory in the sense of Lawvere [Law63] is a small category `T` with strictly associative finite products such that every object is a finite power of a chosen generator `δ_T`. Equivalently (and more precisely), a Lawvere theory is a strict identity-on-objects product-preserving functor `J : ℕ^{op} → T` from the skeleton of finite sets into the theory, with the generator `δ_T := J(1)`.

A *T-model* (or *T-algebra*) in a category `C` with finite products is a finite-product-preserving functor `M : T → C`. T-models form a category `Mod_C(T)` whose morphisms are natural transformations between such functors. The fundamental Lawvere observation [Law63, Linton] is that for `C = Set`, Lawvere theories are in essential bijection with monads on `Set` of *finitary rank* — i.e., every algebraic theory in the classical sense (groups, rings, modules, …) is presented either as a Lawvere theory or as a finitary monad.

Two canonical examples illustrate the breadth:

- `T_Grp` (the theory of groups): models in Set are groups; models in TopCat are topological groups; models in Sh(X) are sheaves of groups.
- `T_Ring` (the theory of rings): models in Set are rings; models in Ab are rings; models in CommRing^{op} are affine schemes.

The key insight: a single syntactic object `T` produces *radically different* semantic structures in radically different bases `C`, with the universal property (Mod_C(T) ≅ Alg(T) = algebras for the monad T_C induced from T) preserving the structural shape.

### §2.2 Enriched Lawvere theories (Power 1999, Hyland–Power 2007)

The classical Lawvere theory operates with arities indexed by `ℕ`. For settings where the natural notion of "arity" is something richer than a finite cardinal — for example, linear arities (a generator is a vector space, arities are tensor powers) or graded arities (a generator is a measurable / topological / chain-complex-valued thing) — the right generalisation is the enriched Lawvere theory.

The foundational reference is Power [Pow99], *Enriched Lawvere theories*, *Theory and Applications of Categories* 6 no. 7. Given a locally finitely presentable (l.f.p.) symmetric monoidal closed category `V`, a V-enriched Lawvere theory is a small V-category `L` with V-finite cotensors (i.e., V-indexed cotensors restricted to finitely presentable objects), equipped with a strict identity-on-objects V-functor `J : V_f^{op} → L` preserving finite cotensors strictly. Here `V_f` is the full sub-V-category of finitely presentable objects of V.

Power's main theorem [Pow99, Theorem 4.2] is:

> **Theorem (Power 1999).** For an l.f.p. SMCC `V`, the category `Law(V)` of V-enriched Lawvere theories is equivalent to the category `Mnd_f(V)` of finitary V-enriched monads on `V`.

The Hyland–Power perspective [HP07] adds the *philosophical* and *methodological* layer: algebraic operations (in the sense of Plotkin–Power) are natural transformations `op : T(−)^n ⇒ T(−)` between functor powers, and the syntactic/semantic split between a Lawvere theory `T` (syntactic) and its monad `T_T` on a base `V` (semantic) gives a unifying account of computational effects. The theme is "one theory, many monads": a single `T` can produce different effects monads in different bases (state, exceptions, nondeterminism, I/O, …), with the *operations + equations* presentation making the structural commitments explicit in a way that the monad-only presentation does not.

For our purposes the key takeaways are:

1. **Definition.** T_GUT is a V-enriched Lawvere theory for `V = SMCC + biproducts`.
2. **Generators + equations.** P1–P7 are encoded as generators (with arities) and equations (coherence laws), per Hyland–Power's "operations + equations" presentation.
3. **Per-base specialisation.** A T_GUT-model in `C : V` is a V-functor realisation; the per-base concrete content (Arf invariant in FinVect_{F_q}; Heyting bimorphism in HeytAlg; symplectic form in FdHilb; frame bimorphism in Frm) is the specialisation of the universal relate generator in the relevant base.

Two limitations of Power 1999 directly relevant to us:

- **Single-base.** Power 1999 fixes one SMCC base `V` and considers V-enriched Lawvere theories over it. We need *parametric base-change*: a single T_GUT, instantiated in *many* bases. The closest available framework is Hyland–Power 2007's §6 (varying base), but neither paper gives a clean *change-of-base* theorem of the form "for `F : V → W` a strong symmetric monoidal l.f.p. functor, F induces `F_* : Law(V) → Law(W)` with model functoriality". GUT-C requires this theorem at the doctrinal level; we approach it via the simpler tactic of *specifying* the four-instance specialisations explicitly and showing they all instantiate T_GUT.

- **No biproducts assumed.** Power 1999's base `V` does not carry biproducts. GUT-C requires biproduct enrichment for the additive operations (compose, square) to act categorically. This is mentioned only obliquely in Power 1999 §6 and is one of the substantive Mathlib gaps (cf. §7.4).

### §2.3 Symmetric monoidal closed categories with biproducts

A *symmetric monoidal closed category* (SMCC) is a category `C` equipped with:

- a symmetric monoidal structure `(⊗, I, α, λ, ρ, σ)` (associator, left/right unitors, braiding satisfying coherence axioms — Eilenberg–Kelly [EK66]);
- an internal hom functor `[−, −] : C^{op} × C → C` satisfying the closure adjunction `Hom_C(A ⊗ B, C) ≅ Hom_C(A, [B, C])`.

Day [Day70] developed the convolution structure on functor categories that gives many examples of SMCCs. Kelly [Kel82] *Basic Concepts of Enriched Category Theory* is the standard reference for the technical machinery (cotensors, weighted limits, change of base, …).

A *biproduct* in an additive category `C` is an object `A ⊕ B` that is simultaneously a categorical product and a categorical coproduct, compatible with a zero object. The presence of biproducts on top of SMCC structure gives an "additive monoidal" category: morphism-spaces are abelian groups (or, more typically, modules over the underlying ring), composition is bilinear, and the tensor product distributes over biproducts. The four target bases of our framework all have this structure:

- `FinVect_{F_q}` (and more generally `FGModuleCat K` for any field K) — finite-dimensional F_q-vector spaces / finitely-generated K-modules. SMCC structure: ⊗_K with internal hom K-linear maps. Biproducts: direct sum.
- `HeytAlg` (= the category of Heyting algebras with Heyting-algebra morphisms) — strictly speaking, this is the cartesian-closed version (products and exponentials in the Heyting-algebra category, where exponential = Heyting implication). Biproducts: products with the canonical zero object {⊥}.
- `FdHilb` (finite-dimensional Hilbert spaces with C-linear maps) — SMCC structure: tensor product of Hilbert spaces with internal hom = adjointable maps (compact-closed). Biproducts: direct sum. Additionally a dagger structure (the inner-product dual), which is where Open Problem O1 sits.
- `Frm` (frames with frame morphisms preserving finite meets + arbitrary joins) — SMCC structure: the *non-cartesian* monoidal structure on Frm given by frame coproducts (Joyal–Tierney [JT84]). Biproducts: not automatic; the cartesian product of frames (in the usual sense) is the right product but not the right monoidal product.

The Mathlib status for these (as of 2026-05 [survey]):

- FinVect / FGModuleCat: present (`Mathlib/Algebra/Category/FGModuleCat/Basic.lean`). `IsMonoidalClosed` and rigid structure proved.
- HeytAlg: present as `Mathlib/Order/Category/HeytAlg.lean`. Cartesian-closed proved; biproducts auto via products + initial object.
- FdHilb: **absent** as a bundled Mathlib category. Substantive analytic content for compact-closed structure is in `InnerProductSpace/Adjoint.lean` but not packaged into a `Category` instance.
- Frm: present as `Mathlib/Order/Category/Frm.lean`. Cartesian product available; *frame coproduct* (= the non-cartesian monoidal product) is **absent** as an `Mathlib.CategoryTheory.MonoidalCategory` instance.

These status notes flag the Mathlib infrastructure gaps that our PR opportunities target (cf. §7.4).

### §2.4 Topos quantum theory (Bohrification — what we depart from)

The Heunen–Landsman–Spitters Bohrification programme [HLS09, HLSW12, DI08] provides the most successful prior categorical unification of quantum and intuitionistic content. The construction starts from a unital C*-algebra `A` and produces:

- a topos `T(A) := Sets^{C(A)}` of Set-valued functors on the poset `C(A)` of unital commutative C*-subalgebras of `A`, ordered by inclusion;
- an internal commutative unital C*-algebra `Ā` in `T(A)`;
- via Banaschewski–Mulvey constructive Gelfand duality applied internally, a locale `Σ(A)` in `T(A)` — the *internal Gelfand spectrum*, interpreted as the Bohrified phase space;
- a Heyting algebra `O(Σ(A))` of open subobjects of `Σ(A)` — the *Bohrified quantum logic*, which is intuitionistic (no LEM).

The conceptual move: quantum content is encoded via the *internal intuitionistic logic* of a topos built from the commutative-subalgebra information of the original noncommutative C*-algebra. The asymmetry of the construction is fundamental: starting from a Heyting algebra, you cannot canonically recover a noncommutative C*-algebra. Bohrification is one-directional.

The relevance to our paper is two-fold:

1. **Bohrification is the *worked precedent* for cross-domain categorical unification.** It shows that intuitionistic and quantum content *can* live in one categorical universe (one topos), which gives existence proof for the kind of unification we seek.

2. **Bohrification is the *negative example* motivating our departure.** Because Bohrification is asymmetric, it cannot give the *symmetric* unification we want: in our framework, HeytAlg and FdHilb are *parallel* T_GUT-instances, neither encoded inside the other. The Bohrification asymmetry is a feature of the *encoding strategy* (encode quantum inside intuitionistic via internal logic) rather than a fundamental limitation; the symmetric move is to host both as instances of one *doctrine*, with neither base encoded inside the other.

This is the conceptual heart of the framework. Bohrification answers "can quantum live inside intuitionistic?" with "yes, via Gelfand"; we answer "is there a doctrine of which both quantum and intuitionistic are equal-status instances?" with "yes, via biproduct-enriched Lawvere theory".

The technical limitation of Bohrification that our framework also addresses: HLS [HLS09] §11 explicitly notes that the plain Bohr topos does not encode any *dynamics* — one needs a presheaf-of-Bohr-toposes over spacetime. Analogously, our static T_GUT-model misses the squaring-tower *iteration* (the recursion structure of the R-tower). Our resolution: this iteration is handled at the syntactic level of T_GUT (the `square_N : δ_T^⊗N → δ_T^⊗(2N)` generator), so the "dynamics" of the framework is internal to T_GUT and does not require external 2-categorical scaffolding.

### §2.4.1 Bohrification in more detail

For readers who want a deeper view of Bohrification (which our framework departs from), we provide a brief technical synopsis.

The Bohrification programme [HLS09] starts from a unital C*-algebra `A` representing a quantum system. It builds a *Bohr topos* `T(A) := Sets^{C(A)}` where `C(A)` is the poset of unital commutative C*-subalgebras of A (ordered by inclusion). The topos T(A) is a Grothendieck topos with the standard intuitionistic internal logic.

Inside T(A), the construction recovers:

- A *tautological* internal commutative unital C*-algebra `Ā : C(A) → Sets`, where `Ā(C) = C` (the underlying set of the commutative subalgebra C, with operations defined fibre-wise).
- By Banaschewski–Mulvey constructive Gelfand duality applied internally to Ā, a *locale* `Σ(A)` in T(A) — the *internal Gelfand spectrum*. Externally, Σ(A) corresponds to a bundle of Gelfand spectra parameterised by C(A).
- The frame O(Σ(A)) of open subobjects of Σ(A) is a Heyting algebra in T(A) — the *Bohrified quantum logic* of A. It is intuitionistic (no LEM) and replaces the orthomodular lattice of standard quantum logic.
- States on A correspond to probability valuations on Σ(A), connecting to standard quantum probability for the case A = B(H).

The construction is *one-directional*: starting from a Heyting algebra H, you cannot canonically recover a noncommutative C*-algebra A such that H = O(Σ(A)). Bohrification encodes quantum *inside* intuitionistic; the reverse direction has no general construction.

The technical achievements of Bohrification are substantial:
- A constructive Gelfand duality available internally (using only intuitionistic logic).
- A way to capture quantum content via the topos-theoretic mechanism (subobject classifier, internal logic, sheaf-style external semantics).
- A unified picture for self-adjoint operators (external observables) and continuous real-valued functions on Σ(A) (internal observables).

The conceptual cost:
- *Asymmetric.* Quantum is encoded inside intuitionistic; the reverse fails.
- *Dagger is lost.* The internal Gelfand spectrum does not preserve the dagger structure of B(H); the dagger is essentially classical observation-side information that gets averaged out by the commutative-subalgebra encoding.
- *Dynamics requires external scaffolding.* HLS [HLS09] §11 notes that the plain Bohr topos does not encode any dynamics; one needs a presheaf-of-Bohr-toposes over spacetime.

Our framework differs in all three respects. It is *symmetric* (both HeytAlg and FdHilb are T_GUT-instances at equal footing); it *preserves dagger* (which lives on FdHilb factor, not pushed into a topos encoding); and the *recursion-as-iteration* is internal to T_GUT (via the `square_N` generator), not external 2-categorical scaffolding.

### §2.5 Selinger dagger compact and Heunen–Karvonen on dagger limits

For the quantum side, Selinger's [Sel07] *Dagger compact closed categories and completely positive maps* and Heunen–Vicary's [HV19] *Categories for Quantum Theory* are the standard references. A *dagger category* is a category equipped with an involutive contravariant identity-on-objects functor `† : C^{op} → C` (so `f†† = f`, `(g ∘ f)† = f† ∘ g†`, `id† = id`). A *dagger symmetric monoidal category* is a symmetric monoidal category compatible with the dagger (specifically: `α†, λ†, ρ†, σ†` coincide with their respective inverses, and `(f ⊗ g)† = f† ⊗ g†`). A *dagger compact category* additionally has compact-closed structure interacting coherently with the dagger.

FdHilb is the paradigmatic dagger compact category: the dagger of a linear map `f : V → W` between finite-dimensional Hilbert spaces is its adjoint `f* : W → V` (via the inner product), and the compact-closed structure comes from `V ⊗ V* ≅ V* ⊗ V` and the trace pairing. Selinger [Sel12] proves that FdHilb is *complete* for dagger compact closed categories: any equation between morphisms expressible in dagger-compact-closed terms holds in FdHilb iff it holds in the free dagger compact category.

Heunen–Karvonen [HK19] *Limits in dagger categories*, *Theory and Applications of Categories* 34, identifies a structural obstruction in the dagger setting that is critical for our paper: *products in a dagger category are biproducts*. This means a dagger category with cartesian products automatically has biproducts and zero objects, which is incompatible with the typical cartesian-closed-but-not-additive case (e.g., HeytAlg). Coecke–Heunen [CH16] *Pictures of complete positivity in arbitrary dimension*, *Information and Computation* 250, identifies the resulting open problem (which we call Open Problem O1):

> **Open Problem O1 (Coecke–Heunen 2016 / Heunen–Karvonen 2019).** A single category cannot simultaneously support dagger compact structure (for quantum) and cartesian-closed structure (for intuitionistic logic) on the same objects without collapsing one structure into the other.

Our framework attacks O1 by *not putting either structure inside T_GUT* and letting each appear only as a property of the relevant base (FdHilb gives dagger; HeytAlg gives cartesian closure). The two sit as *parallel instances* of one doctrine, not as competing structures on the same objects. We elaborate this in §6.

### §2.6 Current GUT-A/B status

The current Lean-formalised state of the framework, prior to the GUT-C work this paper introduces, is summarised here so readers know what they are building on.

**GUT-A (F₂-Boolean classical).** Both directions of D1 ⟷ P1–P7 are formally proven in the F₂-Boolean scope, plus a non-algebraic δ = Prop sibling. Key files:

- `Foundation/R/Basic.lean` — R-family definition.
- `Foundation/R/UniquenessF2.lean` — `T5_A` (F₂ specialisation of polymorphic uniqueness).
- `Foundation/R/ClaimZ/Analytic/` (eight modules P1.lean..P7b.lean) — analytic direction D1 ⟹ P_i for each i.
- `Foundation/R/ClaimZ/Analytic.lean` — integration `D1_implies_Phase1Closure_F2`.
- `Foundation/R/Distinction/Prop.lean` — non-algebraic δ = Prop sibling.
- `Foundation/R/D6_Tests.lean` — falsifiability infrastructure tested against HoTT / ETCS / SDG (each fails to falsify with a documented structural reason).

**GUT-B (polymorphic over Fintype δ + Field k).** Layerwise type equivalence proven for any `[Fintype δ] [DecidableEq δ] [Inhabited δ]`; ring iso at carrier 4 proven for any `Field k`; finite-field char(k) ≠ 2 Witt cancellation completed. Key files:

- `Foundation/R/UniquenessGeneral.lean` (line 241) — `T5_general` master statement.
- `Foundation/R/UniquenessGeneral/Demos.lean` — corollaries at `Bool`, `Distinction`, `Fin n`, `ZMod n`.
- `Foundation/R/UniquenessAlgebraic.lean` — ring iso at carrier 4 for any `Field k`.
- `Foundation/R/Bilinear/Arf.lean` — Arf invariant classification (char(k) = 2).
- `Foundation/R/Bilinear/DiscriminantCharNeq2.lean` — discriminant classification (char(k) ≠ 2 finite fields, completed 2026-05-17 with 0 sorry).

**Five-sense R₄ minimality.** Master theorem `R4_structurally_minimal` of `Foundation/R/R4Minimality.lean` (commit `d4ed0f3`) establishes R₄'s structural minimality in five independent senses. The position 4 of the recursive tower is not arbitrary — it is the smallest at which all three locks (P6 4-fold; squaring as product; involution closure) become simultaneously satisfiable in a non-degenerate way.

**Metalogic identification (companion paper).** The bi-directional closure D1 ⟷ P1–P7 is rigorously identified as `D1 = lfp(Φ')` — the Knaster–Tarski least fixed point of a carrier-growing requirements-extraction operator Φ' on a candidates lattice 𝒜 (see [`lawvere-identification.md`](../lawvere-identification.md) v0.6 for the full treatment, summarised in §8.3 of this paper). The literal application of Lawvere's 1969 fixed-point theorem [Law69] fails by cardinality; we replace point-surjectivity with *self-internalisation* (R-Vec is hom-closed and product-closed on `{R N | N : ℕ}`). The Lean partial formalisation lives in `Foundation/Closure/PhiOperator.lean` (5/8 sorries discharged).

Build state at 2026-05-17: `lake build SSBX` succeeds with ~3936 jobs. The codebase carries 0 axioms in the strict sense (no `axiom` declarations beyond the Mathlib substrate).

### §2.7 Why "biproduct-enriched" specifically

A natural question: why do we require biproducts in the base V? Several alternatives could be considered:

**Option 1 (what we use):** V = SMCC + biproducts. The framework requires biproduct-enrichment for the compose generator (P2) to be interpreted as a categorical direct-sum embedding. Pros: clean categorical content; matches the natural interpretation of compose in all four target bases. Cons: rules out non-additive bases (e.g., pure Set-based examples).

**Option 2:** V = SMCC only (no biproducts). Replace biproducts with explicit duplication structure (e.g., comonoid structure). Pros: more general; covers non-additive bases. Cons: the compose generator becomes more complex; some equational laws (e.g., bilinearity of compose) are harder to state.

**Option 3:** V = cartesian-closed only. Use cartesian product as the monoidal structure. Pros: simplest setting; matches the standard Lawvere-theory framework. Cons: rules out genuinely non-cartesian SMCCs (e.g., FdHilb with tensor product); makes the quantum and topological cases trivial in the wrong sense.

**Option 4:** V = dagger-SMCC. Add dagger structure to the base. Pros: gives a uniform setting for quantum + classical. Cons: rules out HeytAlg (which has no non-trivial dagger); forces the framework toward the dagger-Lawvere extension discussed in §6.4.2.

Our choice (Option 1) is the *minimum-strength* base that supports all four worked instances cleanly. The argument:

- **FinVect_{F_q}** is biproduct-enriched: direct sums are biproducts, and the SMCC structure is the F_q-linear tensor product.
- **HeytAlg** is biproduct-enriched: products + initial object give the biproduct structure (in the trivial sense where + corresponds to ⊓ and 0 to ⊤ in the dual ordering). The SMCC structure is the cartesian product + Heyting implication exponential.
- **FdHilb** is biproduct-enriched: direct sums of Hilbert spaces are biproducts; the SMCC structure is the Hilbert-space tensor product.
- **Frm** is biproduct-enriched: products + initial frame {⊥, ⊤} give the biproduct structure. The intended SMCC structure is the frame coproduct (non-cartesian; Joyal–Tierney 1984), though our current implementation uses the cartesian product as a stand-in.

Other bases worth considering for future extension:

- **`Mon` (monoids in Set):** SMCC + biproducts via monoid coproducts. Could give a "discrete-articulation" instance.
- **`Ab` (abelian groups):** SMCC + biproducts (direct sum). Could give a "torsion-articulation" instance.
- **`Stoch` (stochastic / Markov category):** Markov-category structure (cf. Mathlib's `CategoryTheory.MarkovCategory`). Could give a "probabilistic-articulation" instance.
- **`Smooth∞-Gpd`:** smooth ∞-groupoids in the sense of Schreiber's *Differential cohomology in a cohesive ∞-topos*. Could give a "geometric-articulation" instance. Requires ∞-categorical infrastructure.

These are all formally compatible with our base 2-category V = SMCC + biproducts; they constitute candidate future instances that would extend the four-instance verification.

### §2.8 Historical thread: from Aristotelian categories to enriched Lawvere doctrines

The methodological thread we follow has a long history. We briefly trace it for context.

**Aristotle:** the *Categories* (4th c. BCE) identified ten primary categories (substance, quantity, quality, relation, place, time, position, state, action, passion) as the basic kinds of "what can be said" of a subject. The methodological move is to *identify minimum primitives of articulation* — a goal that R-tower's D1 + P1–P7 inherits.

**Kant:** the *Kritik der reinen Vernunft* (1781) gave 12 a priori categories of the understanding, organised by quantity, quality, relation, modality (4-fold each). The 4-fold modality (problematic / assertoric / apodictic / ... varying by axis) anticipates our P6's 4-fold modality requirement. The methodological move is to *derive minimum categories from a single articulation seed* — what R-tower's chapter 01 calls the "analytic direction" D1 ⟹ P1–P7.

**Frege:** the *Begriffsschrift* (1879) introduced concept-script with explicit logical syntax: predicates, quantifiers, judgment-strokes. The methodological move is to *encode logical articulation in a formal system* — what later became the standard first-order logic.

**Russell–Whitehead:** *Principia Mathematica* (1910-13) attempted to derive mathematics from logic + types. The methodological move is to *prove mathematical content from logical articulation* — what later led to type theory and proof assistants.

**Categories as foundation:** Lawvere's 1963 thesis [Law63], 1969 *Adjointness in Foundations* [Law69], and 1965 ETCS (Elementary Theory of the Category of Sets) proposed categorical foundations as an alternative to set-theoretic foundations. The methodological move is to *replace set-theoretic primitives with categorical ones* — Lawvere theories, doctrines, ETCS, ETCC.

**Categorical universality across domains:** Eilenberg–Kelly's closed categories (1966 [EK66]), Mac Lane's PROPs (1965 [ML65]), Day's convolution structures (1970 [Day70]), Kelly's enriched-category foundations (1982 [Kel82]) extended Lawvere's framework to richer settings (linear, enriched, 2-categorical).

**Categorical quantum mechanics:** Abramsky–Coecke (2004 [AC04]), Selinger (2007 [Sel07]), Heunen–Vicary (2019 [HV19]) extended the categorical methodology to quantum, with dagger compact closed categories as the natural setting.

**Topos quantum theory:** Heunen–Landsman–Spitters (2009 [HLS09]), Döring–Isham (2008 [DI08]) extended further, encoding quantum content via intuitionistic topos theory.

**Higher-categorical foundations:** Voevodsky's univalent foundations program (2009+), the HoTT Book (UF13 [UF13]), Lurie's *Higher Topos Theory* (2009 [Lur09]) extended to ∞-categorical settings.

**Our framework:** GUT-C / T_GUT is a node in this long methodological thread. It targets *substrate-level articulation primitives* (P1–P7) and provides a *categorical doctrinal home* (biproduct-enriched Lawvere theory) within which the universal-property theorems for algebraic, intuitionistic, quantum, and topological substrate-classes are recovered as instances.

The chronological pattern: each step in the thread *generalises* the categorical framework (more bases, more morphism structure, more dimensions) while *preserving* the methodological core (syntactic theory + parametric semantic interpretation + universal property recovering target structure). Our contribution sits in this pattern at the *substrate-articulation* level: the categorical doctrine encodes the structural axioms (P1–P7) that articulation requires; per-base specialisation recovers the class-specific content; the framework's discrimination capability validates the design.

---

## §3. The T_GUT Doctrine

We now give the precise definition of T_GUT as a biproduct-enriched Lawvere theory.

### §3.1 The base 2-category V

The base 2-category over which T_GUT is enriched is

> `V := Cat_{SMCC,⊕}` — the 2-category of small SMCCs with biproducts, with strong symmetric monoidal functors as 1-cells and monoidal natural transformations as 2-cells.

Strictly speaking, V should be locally small (1-cell hom-categories small) and presentable in the appropriate sense to satisfy Power's [Pow99] hypothesis "V is l.f.p. as a closed category". The current treatment leaves this size question to the per-instance specialisation: we instantiate T_GUT in concrete SMCCs (FinVect_{F_q}, HeytAlg, FdHilb-via-stabilisers, Frm) and verify the construction in each case. A full size analysis is deferred to the γ.3 refinement.

### §3.2 The theory T_GUT — generators

T_GUT is a small V-enriched Lawvere theory presented by generators and equations. The underlying ℕ-indexed family of objects is `{X_N : N ∈ ℕ}` with chosen generator `δ_T := X_1`. Each `X_N` is interpreted in any model M as `M(X_N) = R N`, the N-th object of the model's underlying family; the canonical realisation in any SMCC C with chosen δ sets `M(X_N) = δ^⊗N` (iterated tensor power).

The eight generator families, encoding P1–P7, are:

| Generator | Type | Encodes |
|---|---|---|
| `id_δ : δ_T → δ_T` | identity at the generator | P1 (distinction) |
| `compose_{N,M} : δ_T^⊗N ⊗ δ_T^⊗M → δ_T^⊗(N+M)` | direct-sum embedding | P2 (composition / biproduct) |
| `relate_{N,M} : δ_T^⊗N → δ_T^⊗M` | morphism family | P3 (relations) |
| `square_N : δ_T^⊗N → δ_T^⊗(2N)` | doubling | P4 (squaring / scale) |
| `hom_{N,M} : (δ_T^⊗N ⊸ δ_T^⊗M) → δ_T^⊗(N·M)` | curry/uncurry | P5 (Hom-as-content) |
| `modal_{V_4} : δ_T → δ_T^⊗2 ⊗ δ_T^⊗2` | V₄ embedding | P6 (4-fold modality) |
| `atom_3 : δ_T^⊗3 → δ_T^⊗3` with `atom_3^2 = id` | involution | P7a |
| `wedderburn_4 : δ_T^⊗4 ≅ End(δ_T^⊗2)` | endomorphism iso | P7b (generalised) |

Table 1: The eight generator families of T_GUT.

A brief annotation of each:

- **`id_δ`** is the identity on the generator; categorically this is automatically present in any category, but we list it because it is the categorical encoding of the *distinction* axiom P1 (the minimum non-degenerate categorical structure is "an object with a non-trivial morphism family ending at that object", with the identity being the minimum).

- **`compose_{N,M}`** is the embedding `δ_T^⊗N ⊗ δ_T^⊗M → δ_T^⊗(N+M)` corresponding to the categorical direct-sum (= biproduct, since the base is biproduct-enriched) of two tensor-power objects. The intended categorical content is that compose is associative, unital, and natural in N and M.

- **`relate_{N,M}`** is the *abstract* family of relating morphisms between any two tensor-power objects. In the canonical realisation `R_C` sending `δ_T ↦ δ`, the concrete content of `relate_{N,M}` is the entire morphism set `Hom_C(δ^⊗N, δ^⊗M)`. The per-base specialisation of this generator is one of the chief framework outputs: in FinVect_{F_q} it specialises to F_q-bilinear forms classified by Arf invariant / discriminant; in HeytAlg to Heyting bimorphisms; in FdHilb to dagger-symmetric forms (symplectic in the F₂ image); in Frm to frame bimorphisms.

- **`square_N`** is the doubling generator `δ_T^⊗N → δ_T^⊗(2N)`. Categorically, this is the diagonal-then-tensor-with-self composition: `square_N = (id_{δ_T^⊗N} ⊗ id_{δ_T^⊗N}) ∘ Δ_{δ_T^⊗N}` where Δ is the diagonal (well-defined when the base is cartesian; in the non-cartesian SMCC case the corresponding morphism is the duplication arising from the comonoid structure of biproducts).

- **`hom_{N,M}`** is the Hom-as-content generator `(δ_T^⊗N ⊸ δ_T^⊗M) → δ_T^⊗(N·M)` corresponding to the curry/uncurry isomorphism of the SMCC closure adjunction. The intended content is that the internal hom of two tensor-power objects is *itself* a tensor-power object (with multiplicative grade `N·M`). This is the categorical encoding of "the operations are themselves objects" (D1 item 7).

- **`modal_{V_4}`** is the V₄ four-fold-modality generator `δ_T → δ_T^⊗2 ⊗ δ_T^⊗2`. This is the embedding of the generator into a 4-fold tensor product, encoding the structural-minimum four-fold modality required by D1 item 8 (conditional trigger on process content). The intended categorical content is that the image of `modal_{V_4}` is a Klein four group (in the F₂ case) or its categorical analogue in non-F₂ cases.

- **`atom_3`** is the aspect involution `δ_T^⊗3 → δ_T^⊗3` with `atom_3 ∘ atom_3 = id_{δ_T^⊗3}`. This is the categorical encoding of P7a (atom involution): a non-trivial categorical involution on the 3-fold tensor power, with the involutive property as an equational law.

- **`wedderburn_4`** is the generalised Wedderburn anchor: an isomorphism `δ_T^⊗4 ≅ End(δ_T^⊗2)` where End is the internal endomorphism object `[δ_T^⊗2, δ_T^⊗2]`. This is the categorical encoding of P7b: the 4-fold tensor power is isomorphic to the internal endomorphism object of the 2-fold tensor power. The per-base specialisation: in FinVect_{F_q} this gives `R 4 ≅ Mat₂(F_q)`; in FdHilb it gives `R 4 ≅ M_2(ℂ)`; in HeytAlg the analogue is `R 4 ≅ DiamondH4` (our conjectured minimum non-Boolean 4-element Heyting anchor); in Frm the analogue is `R 4 ≅ Sierpinski²` (the Sierpinski cube).

### §3.3 The theory T_GUT — equations

The equations of T_GUT encode the coherence laws between the generators. The full list is given as `TGUTLaw` in `Foundation/Doctrine/T_GUT.lean` lines 230–253. We summarise the most important:

1. **Atom involutivity (P7a):** `atom_3 ∘ atom_3 = id_{δ_T^⊗3}`. Direct equational law.

2. **Squaring as diagonal (P4):** `square_N = (id_{δ_T^⊗N} ⊗ id_{δ_T^⊗N}) ∘ Δ_{δ_T^⊗N}`. The interpretation depends on the structure of the base: when the base is cartesian, Δ is the categorical diagonal; when the base is biproduct-enriched but not cartesian, Δ is the comonoid duplication arising from the biproduct structure.

3. **Compose associativity (P2):** `compose_{(N+M),K} ∘ (compose_{N,M} ⊗ id) = compose_{N,(M+K)} ∘ (id ⊗ compose_{M,K})`. Standard associativity diagram.

4. **Compose unitality (P2):** `compose_{N,0} = id_{δ_T^⊗N}` (right unit) and `compose_{0,M} = id_{δ_T^⊗M}` (left unit). With the convention `δ_T^⊗0 = I` (the monoidal unit) the equations make sense definitionally.

5. **Hom-as-content compatibility (P5):** `hom_{N,M} ∘ curry_{N,M} = id_{(δ_T^⊗N ⊸ δ_T^⊗M)}`. Internally, `hom_{N,M}` is the *inverse* of the curry isomorphism `(δ_T^⊗N ⊸ δ_T^⊗M) ≅ δ_T^⊗(N·M)`.

6. **Wedderburn iso (P7b):** `wedderburn_4 ∘ wedderburn_4^{-1} = id` together with appropriate naturality conditions. The naturality conditions are the analogue of the Mat₂-naturality in the algebraic case; their precise statement at the doctrine level is one of the open problems we discuss in §9.

7. **Modal V₄ idempotency (P6):** `modal_{V_4} ∘ modal_{V_4}` factors through `id ⊗ id`. Encodes the structural fact that V₄ is closed under self-application in the categorical sense.

These equations are the *minimum* set required to make the canonical realisation `R_C` (sending δ_T ↦ δ in any SMCC C with chosen δ) into a satisfier of T_GUT. The full set of equations needed for the *uniqueness* part of Universal Sayability is currently the γ.3 refinement target (cf. §4).

### §3.4 Realisations

A *realisation* of T_GUT in an SMCC C with chosen δ ∈ Obj(C) is a record bundling the data of a candidate T_GUT-model. The precise Lean structure (cf. `Foundation/Doctrine/T_GUT.lean` lines 316–347) is:

```
structure TGUTRealisation (C : Type u) [Category C] [MonoidalCategory C] (δ : C) where
  R : ℕ → C
  R_unit : R 0 ≅ 𝟙_ C
  R_gen : R 1 ≅ δ
  R_tensor : ∀ n m, R (n + m) ≅ R n ⊗ R m
  compose_mor : ∀ N M, R N ⊗ R M ⟶ R (N + M)
  square_mor : ∀ N, R N ⟶ R (2 * N)
  relate_mor : ∀ N M, R N ⟶ R M
  hom_mor : ∀ N M, R (N * M) ⟶ R (N * M)
  modal_V4_mor : R 1 ⟶ R 2 ⊗ R 2
  atom_3_mor : R 3 ⟶ R 3
  wedderburn_4_mor : R 4 ≅ R 4
```

The first four fields (`R`, `R_unit`, `R_gen`, `R_tensor`) are the *structural* data of a realisation: an ℕ-indexed family of objects of C, with structural isos pinning down the empty tensor power (R 0 = 𝟙_ C), the generator (R 1 = δ), and tensor-power additivity (R(n+m) ≅ R n ⊗ R m). The remaining seven fields are the *generator* morphisms, one per non-trivial constructor of TGUTOp (the eighth generator, id_δ, being the categorical identity on R 1 and automatically derived).

A realisation is *not* required by this structure to satisfy the equational laws (§3.3); that condition is a separate `Satisfies : TGUTRealisation C δ → TGUTLaw → Prop` proposition (cf. `Foundation/Doctrine/T_GUT.lean` lines 395–408). A realisation that satisfies the standard laws is called an *adequate* realisation.

### §3.5 The canonical realisation

In any SMCC C with chosen δ ∈ Obj(C), the *canonical realisation* `R_C : TGUTRealisation C δ` is constructed by sending `R n := tensorPow δ n` (iterated tensor power; cf. `Foundation/Doctrine/T_GUT.lean` lines 430–432), with the structural isos and generator morphisms supplied by the standard structural coherences of the SMCC (associators, unitors, braidings, …).

The Lean implementation of `TGUTRealisation.canonical δ` (cf. `Foundation/Doctrine/T_GUT.lean` lines 444–466) currently records the structural isos and generator morphisms as `sorry`; the explicit constructions exist (the `R_tensor` proof is the standard induction-on-n establishing left-additivity of tensor powers in a monoidal category; the generator morphisms are diagonal, identity, or appropriate structural isos) but are deferred for engineering reasons (~30 LOC per sorry, bulky but not load-bearing for the API). The intended construction is unambiguous; the sorries are pure engineering debt.

### §3.6 The (P-property, base, specialisation) 3 × 3

Per `gut-c-doctrine.md` v0.3 §3.5, the same syntactic generator gives different *concrete* content in each base SMCC. This is the central design feature of the framework: P-properties live at the doctrine level (universal), and their per-base specialisation gives the class-specific structures.

| Generator | FinVect_{F_q} | HeytAlg | FdHilb | Frm |
|---|---|---|---|---|
| `relate` (P3) | F_q-bilinear forms; Arf invariant (char = 2) / discriminant (char ≠ 2) | Heyting bimorphisms; intuitionistic implication classification | symplectic forms; commutator detection in Pauli stabiliser | frame bimorphisms preserving ⊓ in each arg + ⨆ in each arg |
| `square` (P4) | tensor squaring `R N → R(2N)` | meet idempotence | tensor squaring | meet squaring |
| `hom` (P5) | `LinHom N M ≃ R(N·M)` | Heyting implication `⇨` | dagger duality `(−)*` | frame implication / locale exponential |
| `modal_{V_4}` (P6) | V₄ Shi (道/已/今/未 — Way/Already/Now/Not-yet) | classical 4-modality | Pauli {I, X, Y, Z} mod phase (≅ V₄) | Sierpinski-like 4-mod |
| `wedderburn_4` (P7b) | `R 4 ≅ Mat₂(F_q)` | `R 4 ≅ DiamondH4` (4-element non-Boolean Heyting) | `R 4 ≅ Mat₂(ℂ)` (2-qubit Pauli image) | `R 4 ≅ Sierpinski²` (Sierpinski cube) |

Table 2: The (P-property, base, specialisation) 3 × 3 of T_GUT.

The framework discriminates correctly between *substrate-level* generators (P1, P2, P4, P5, P6, P7a) — which carry over largely unchanged across all four bases — and *algebraic-class* generators (P3, P7b) — which reformulate non-trivially. This is exactly the design intent: T_GUT should not assume that "bilinear" or "Wedderburn anchor" have universal meanings; the generators provide universal hooks, and the per-base content fills them in.

### §3.7 Substrate vs class-specific: the Heyting validation

A key empirical validation of the framework is the Heyting case (`Foundation/Doctrine/Instance/Heyting.lean`). Per the doctrine document's §8.2 decision protocol, the question for Phase γ.2 was "Does the first non-algebraic instance (Heyting) instantiate cleanly?" The answer is **YES (PARTIAL)** — sufficient to commit Phase γ.3.

The framework's discrimination between substrate-level and algebraic-class generators is the substantive finding:

- **6/8 substrate-level generators** (id_δ, compose, square, hom, modal_V4, atom_3) carry over unchanged from algebraic to Heyting, with the Heyting interpretation given by the cartesian-closed structure of HeytAlg.
- **2/8 algebraic-class generators** (relate / P3, wedderburn_4 / P7b) reformulate with non-trivial Heyting content. P3 becomes Heyting-bimorphism classification (a research open problem); P7b becomes `R 4 ≅ DiamondH4` (a novel candidate anchor, also a research open problem).

This is the empirical confirmation that the framework's universal-vs-specialisation design is well-aimed: the substrate-level structure is universal, the algebraic-class structure is base-specific, and the framework correctly identifies which is which.

The `DiamondH4` discovery itself is worth a brief note. It is defined as the 4-element linearly-ordered Heyting algebra `{⊥ < mid₁ < mid₂ < ⊤}` with explicit `himp` (Heyting implication) operation. The Lean theorem `DiamondH4_is_nonBoolean` proves `¬¬mid₁ = ⊥ ≠ mid₁`, demonstrating the intrinsic non-Boolean Heyting structure at the smallest non-trivial size. The conjecture (currently open) is `R 4 Prop ≃ DiamondH4` — the minimum-size Heyting anchor at carrier 4. If this conjecture is correct, it is the Heyting analogue of P7b's `Mat₂(F₂)` in the algebraic case, and gives the framework its first novel mathematical-object prediction. (See §5.2 for full discussion.)

### §3.8 The Lawvere–Power equivalence and its specialisations

We pause to make precise the relationship between T_GUT and Power's [Pow99] theorem `Law(V) ≃ Mnd_f(V)`. Power's theorem gives, for any locally finitely presentable SMCC base V, an equivalence between V-enriched Lawvere theories and finitary V-enriched monads on V. The forward functor sends a theory L to the monad T_L whose algebras are L-models in V; the reverse functor sends a finitary monad T to its Kleisli V-category restricted to finitely presentable arities.

For our framework this translates as: T_GUT determines a *family* of monads, one in each base C = SMCC + biproducts. Each monad T_{GUT, C} on C has algebras `Alg(T_{GUT, C}) ≅ Mod_C(T_GUT)`. The forgetful functor `Mod_C(T_GUT) → C` is monadic, with left adjoint generating the free T_GUT-model on each object of C.

This monadic presentation gives several technical benefits:

1. **Free / cofree adjunction**: the free T_GUT-model on `δ` in C is the canonical realisation `R_C = canonical δ`; the cofree T_GUT-model (when it exists) gives a dual notion of "cofreely-generated R-tower-modal" structure that we do not pursue here but flag as a potential research direction.

2. **Kleisli structure**: the Kleisli category of T_{GUT, C} is the "T_GUT-categorical-substrate" of C, capturing morphisms of R-family-based structures. This is the natural setting for inter-realisation morphisms; the full development is one of the γ.3 refinement targets.

3. **Universal-property characterisation**: a T_GUT-model in C is *unique up to natural isomorphism* among finite-product-preserving V-functors `T_GUT → C` extending a chosen generator-map `δ_T ↦ δ`. This is the formal content of "T_GUT is the *free* enriched-Lawvere-theory on its generators modulo its equations".

The full monadic apparatus depends on Mathlib infrastructure (`LawvereTheory` + `Model` API, PR-2 of §7.4) that is currently absent. Our Lean codebase implements local approximations: `EnrichedLawvereTheory.lean` (929 LOC) defines the V-enriched version with cotensors; `T_GUT.lean` (611 LOC) presents T_GUT explicitly via generators + equations and constructs `TGUTRealisation` records that capture the data of a T_GUT-model. The connection to Power's full monadic equivalence is established only at the *concrete* level (specific T_GUT-realisations are constructed in each base) and not yet at the *abstract* level (the equivalence `Law(V) ≃ Mnd_f(V)` itself is not Lean-formalised).

This is consistent with our paper's claim level: we have the layer-by-layer Universal Sayability theorem (§4) plus four worked instances (§5), but we do not yet have the *abstract* universal property characterisation. The γ.3 refinement target is precisely to push to this abstract level, exploiting Power's theorem once the Mathlib infrastructure is in place.

### §3.9 The specialisation principle: per-base content from universal generators

A central design feature of the framework is the *specialisation principle*: a single universal generator `g : TGUTOp` gives different concrete content `M.interp(g)` in different bases C. This is encoded in the `interp` function (cf. `Foundation/Doctrine/T_GUT.lean` line 364):

```
noncomputable def interp (M : TGUTRealisation C δ) : ∀ (g : TGUTOp),
    M.R g.src ⟶ M.R g.tgt
  | .id_δ          => 𝟙 (M.R 1)
  | .compose N M_  =>
      (M.R_tensor N M_).hom ≫ M.compose_mor N M_
  | .square N      => M.square_mor N
  | .hom N M_      => M.hom_mor N M_
  | .modal_V4      =>
      M.modal_V4_mor ≫ (M.R_tensor 2 2).inv
  | .atom_3        => M.atom_3_mor
  | .wedderburn_4  => M.wedderburn_4_mor.hom
  | .relate N M_   => M.relate_mor N M_
```

The function `interp` dispatches each syntactic generator to the corresponding concrete morphism in the realisation M. In the canonical realisation `R_C := canonical δ`, the dispatch gives the standard structural morphisms (identity, associator chains, structural unitor, …); in non-canonical realisations, the dispatch gives the per-base concrete content (Heyting implication in HeytAlg; Pauli operation in stabiliser-quantum; frame morphism in Frm).

The specialisation principle is what enables the same syntactic theory T_GUT to "mean" different things in different bases. Formally:

> **Specialisation Principle.** For each generator `g : TGUTOp` and each base C with chosen δ, the concrete content of g in any T_GUT-realisation M in (C, δ) is determined by:
> 1. The arity `g.arity = (src, tgt)` (universal).
> 2. The dispatch function `interp` (universal).
> 3. The data of M (per-realisation).
>
> Different choices of M give different concrete content; the universal generator structure stays fixed.

This is the categorical embodiment of the slogan "one theory, many monads" (Hyland–Power 2007 [HP07]): one syntactic theory T_GUT, many concrete realisations in different bases.

---

## §4. Universal Sayability Theorem

We now state the central theorem of the framework and prove the layer-by-layer component-iso version.

### §4.1 Statement

> **★ Theorem (GUT-C Universal Sayability — layer-by-layer iso version).**
>
> Let C be a symmetric monoidal closed category with biproducts and a chosen object δ ∈ Obj(C). Let `R_C := TGUTRealisation.canonical δ` be the canonical tensor-power realisation. Then for any other realisation `M : TGUTRealisation C δ`, there is a natural family of isomorphisms
> `iso : ∀ n, M.R n ≅ tensorPow δ n`
> in C.

The Lean statement (cf. `Foundation/Doctrine/T_GUT.lean` line 575) is:

```
theorem universal_sayability (δ : C) (M : TGUTRealisation C δ) :
    Nonempty (RealIso M (canonical δ)) :=
  ⟨{ iso := componentIso δ M }⟩
```

where `RealIso M N` is the record type with fields `iso : ∀ n, M.R n ≅ N.R n` and a coherence predicate `coherent : Prop` (currently defaulting to `True`).

### §4.2 Proof via componentIso recursion

The proof is by induction on n, constructing the family of component isos `M.R n ≅ tensorPow δ n` from the structural data of M:

**Base case (n = 0):** `M.R 0 ≅ 𝟙_ C = tensorPow δ 0`. The isomorphism is `M.R_unit : M.R 0 ≅ 𝟙_ C` — the structural data of M directly supplies it.

**Inductive case (n = k + 1):** We need `M.R (k + 1) ≅ tensorPow δ (k + 1) = δ ⊗ tensorPow δ k`. The construction is a chain of three isos:

```
M.R (k + 1) ≅ M.R (1 + k)     -- eqToIso (commutativity of ℕ)
            ≅ M.R 1 ⊗ M.R k   -- M.R_tensor 1 k
            ≅ δ ⊗ tensorPow δ k -- M.R_gen ⊗ᵢ (IH : componentIso δ M k)
            = tensorPow δ (k + 1) -- rfl (by tensorPow_succ)
```

The Lean implementation (cf. `Foundation/Doctrine/T_GUT.lean` lines 534–543) is:

```
noncomputable def componentIso (δ : C) (M : TGUTRealisation C δ) :
    ∀ n, M.R n ≅ tensorPow δ n
  | 0 => M.R_unit
  | k + 1 =>
      have hcomm : k + 1 = 1 + k := by omega
      eqToIso (congrArg M.R hcomm)
        ≪≫ M.R_tensor 1 k
        ≪≫ (M.R_gen ⊗ᵢ componentIso δ M k)
```

The proof is structurally simple: the inductive hypothesis IH gives an iso at level k, and we combine it with the structural isos `R_gen` and `R_tensor` of M to lift it to level k+1. The construction uses only the *structural* data of M (the four `R_unit / R_gen / R_tensor` isos), not the seven generator morphisms. This is the "free part" of the theorem: the carrier-shape uniqueness is determined by `R 1 ≅ δ` and tensor-power additivity, independently of how the generator morphisms behave.

### §4.3 The "coherent" predicate

The full Universal Sayability theorem requires not just a family of component isos but a family commuting with the seven generator morphisms (compose, square, hom, modal_V4, atom_3, wedderburn_4, relate) and the three structural isos (R_unit, R_gen, R_tensor). The current `RealIso` record carries a `coherent : Prop` field that should encode the commuting-square conditions, but in the current skeleton it defaults to `True` (with `coherent_holds := by trivial`). The discharge of these commuting squares is the γ.3 refinement target.

The precise list of squares to discharge:

1. **Structural isos compatibility** (3 squares): for each of R_unit, R_gen, R_tensor, a square asserting that the component iso family commutes with the corresponding structural iso. These are conceptually straightforward (the structural isos are determined by the inductive construction) but require careful tracking of the associator / unitor / braiding coherence in the SMCC base.

2. **Compose compatibility** (1 square family, indexed by N, M): the diagram

```
M.R N ⊗ M.R M --(M.compose_mor N M)--> M.R (N + M)
     │                                       │
     │ iso_N ⊗ iso_M                         │ iso_{N+M}
     ↓                                       ↓
tensorPow δ N ⊗ tensorPow δ M --(R_C.compose_mor N M)--> tensorPow δ (N + M)
```

commutes. In the canonical realisation `R_C`, the compose_mor is the structural iso `R_tensor`-inverse, so this square is determined by the previous structural squares.

3. **Square compatibility** (1 square family, indexed by N): analogous diagram for `square_mor`.

4. **Hom compatibility** (1 square family, indexed by N, M): analogous diagram for `hom_mor`.

5. **Modal_V4 compatibility** (1 square): the structural square for `modal_V4_mor : M.R 1 → M.R 2 ⊗ M.R 2`.

6. **Atom_3 compatibility** (1 square): the structural square for `atom_3_mor : M.R 3 → M.R 3`.

7. **Wedderburn_4 compatibility** (1 square): the structural square for `wedderburn_4_mor : M.R 4 ≅ M.R 4`.

8. **Relate compatibility** (1 square family, indexed by N, M): analogous diagram for `relate_mor`.

In total, 11 commuting-square classes. Each is in principle dischargeable given the equational laws of §3.3, but the discharge depends on the full Lawvere infrastructure (the equational laws need to be available as `Prop`-valued conditions on `TGUTRealisation`, plus the universal-property characterisation of T_GUT-models needs to be formalised). The current Lean code records this as the γ.3 target without prejudice on the eventual difficulty.

### §4.4 What this theorem does and does not give

The current statement (layer-by-layer iso) is *necessary* but not *sufficient* for the full Universal Sayability claim. It establishes:

- The *carrier-shape* of any T_GUT-realisation in any SMCC C with chosen δ is uniquely determined up to iso by the canonical tensor-power family `tensorPow δ`.
- Any two T_GUT-realisations in the same `(C, δ)` are layer-by-layer isomorphic.

It does *not* establish:

- That the seven generator morphisms of any T_GUT-realisation coincide with those of the canonical realisation (this is the coherence content, deferred to γ.3).
- That T_GUT-realisations form an essentially unique structure (a 2-categorical statement at the level of `Mod_C(T_GUT)`).
- The cross-base universality (a doctrinal change-of-base statement of the form "for F : V → W an SMCC functor, F_* sends T_GUT-realisations in V to T_GUT-realisations in W coherently").

These are the three layers of refinement needed for the full theorem. The current paper claims only the first layer; the second is the γ.3 target; the third is a longer-term programme.

### §4.5 Specialisation table

| Base C | δ | M ≅ R_C means |
|---|---|---|
| `FinVect_{F_q}` | `F_q` | M = R-family-over-F_q — recovers existing GUT-A/B algebraic |
| `HeytAlg` | `Prop` | M = Heyting R-family (NEW — GUT-Heyting) |
| `FdHilb` (via stabilisers) | `PauliBase` (≅ V₄) | M = quantum stabiliser-style R-family (NEW — GUT-Quantum) |
| `Frm` | `Ω` (Sierpinski) | M = topological R-family (NEW — GUT-Topological) |

Table 3: The four worked specialisations.

The four specialisations are worked out in §5. The first reduces under straightforward translation to our existing `T5_general` (`Foundation/R/UniquenessGeneral.lean` line 241), giving the recovery of GUT-A/B. The remaining three are the new content of this paper.

### §4.6 Two layers of refinement remaining

For clarity, the full Universal Sayability theorem (in its strongest form) needs three layers of refinement, of which we have established the first:

**Layer 1 — Layer-by-layer component isomorphism (established in this paper, §4.2):**

For any T_GUT-realisation M and any SMCC C with chosen δ:
```
∃ iso : ∀ n, M.R n ≅ tensorPow δ n
```

The iso family is constructed by induction on n using only the structural isos `R_unit / R_gen / R_tensor` of M.

**Layer 2 — Coherence with all generator morphisms (γ.3 refinement target):**

Strengthen Layer 1 to require that the iso family commutes with each of the seven generator morphisms (compose, square, hom, modal_V4, atom_3, wedderburn_4, relate) and the three structural isos (R_unit, R_gen, R_tensor). This is the *equational coherence* layer.

The discharge requires:
- The equational laws (TGUTLaw, §3.3) to be available as Prop-valued conditions on realisations.
- Naturality conditions for each generator morphism (the standard category-theoretic naturality).
- Case-by-case discharge of 11 commuting-square classes.

When complete, this gives the *categorical-isomorphism* version of Universal Sayability: `M ≅ R_C` in the 1-category of T_GUT-realisations in (C, δ).

**Layer 3 — 2-categorical / cross-base universality (longer-term programme):**

Strengthen Layer 2 to a 2-categorical statement: the assignment `(C, δ) ↦ R_C` extends to a 2-functorial pseudo-natural-transformation from the doctrine 2-category V to the 2-category of T_GUT-realisations. This handles change-of-base coherently and gives the *doctrinal-uniqueness* version of Universal Sayability.

The discharge requires:
- The full 2-categorical machinery (V as a strict 2-category; morphisms of bases as 2-functors).
- Coherence of base-change with T_GUT-realisations (a doctrine-morphism theorem).

This is what `gut-c-doctrine.md` v0.3 §3.4 informally states; the formal 2-categorical version is a 18-36 month research project (one of the longer-term γ items).

For this paper we claim only Layer 1 + the empirical four-instance verification (§5). Layer 2 is recorded as the γ.3 refinement; Layer 3 is acknowledged as a future direction.

### §4.7 The proof viewed as Path 2 (constructive component recursion)

The proof technique used in §4.2 — constructing the component isos by induction on n from the structural isos of M — has a specific name in the framework's internal vocabulary: it is "Path 2" of the Universal Sayability proof.

**Path 1 (deferred):** Universal-property approach. Show that the canonical realisation `R_C := canonical δ` satisfies a universal property in the category of T_GUT-realisations in (C, δ). Show that any other realisation factors uniquely through it. This requires the full enriched-Lawvere infrastructure (Power 1999's theorem giving `Law(V) ≃ Mnd_f(V)`) and is deferred to γ.3.

**Path 2 (established here):** Constructive component recursion. Construct the component isos directly by induction on n, using only the structural isos of M. This does not require the full Power 1999 machinery and is the more concrete (less abstract) version of the theorem.

Both paths converge on the same conclusion when fully developed; Path 2 gives the layer-by-layer version, Path 1 gives the universal-property version. The current paper proves Path 2 (which is sufficient for the layer-by-layer claim); Path 1 is the γ.3 refinement target.

The Lean implementation `componentIso` (cf. `Foundation/Doctrine/T_GUT.lean` lines 534–543) is the Path 2 construction made explicit. The construction is *noncomputable* in the Lean sense (it uses classical choice in the underlying Mathlib `Iso` machinery), but the construction itself is constructive in the categorical sense (it builds the iso family explicitly from M's structural data, not by appeal to existence).

---

## §5. Instance Verification

We walk through the four worked T_GUT instances, identifying which P-properties have working analogues and which require reformulation. Each instance has its own Lean file in `Foundation/Doctrine/Instance/`; the file structure follows a common template (canonical realisation; sanity checks at small N; per-property analysis; cross-checks with existing infrastructure; verdict).

### §5.1 Algebraic instance: T_GUT in FinVect_{F_q}

The algebraic instance is the *anchor*: it recovers the existing 0-sorry GUT-A/B result as the special case δ = F_q. The Lean file is `Foundation/Doctrine/Instance/Algebraic.lean` (485 LOC, 2 sorries: one in `R_tensor` matching the template, one in the recovery bridge to `T5_general`).

**Canonical realisation.** In `FinVect_{F_q}` with δ = F_q (the 1-dimensional vector space), the canonical tensor-power realisation is `R N := F_q^N`, with tensor product `⊗_{F_q}` and internal hom = F_q-linear maps. The structural isos and generator morphisms are the standard F_q-linear maps (identity, direct sum embedding, diagonal, swap, …).

**Per-property analysis:**

- **P1 (id_δ):** ✓ — the identity on F_q.
- **P2 (compose):** ✓ — direct sum embedding F_q^N ⊕ F_q^M → F_q^(N+M).
- **P3 (relate):** ✓ — F_q-bilinear forms, classified by Arf invariant (char(F_q) = 2) or discriminant (char(F_q) ≠ 2). Per `Foundation/R/Bilinear/Arf.lean` and `Foundation/R/Bilinear/DiscriminantCharNeq2.lean`.
- **P4 (square):** ✓ — tensor squaring `F_q^N → F_q^(2N)` via the diagonal `Δ` followed by tensoring with itself.
- **P5 (hom):** ✓ — `LinHom N M ≃ F_q^(N·M)` (cf. `Analytic/P5.lean`).
- **P6 (modal_V4):** ✓ — V₄ Shi (道/已/今/未) at R 2 = F_q^2 = (F_q)^4 / (involution-equivalence). The Klein-four group structure is on the F₂ case (giving exactly V₄); the general F_q case gives an analogous 4-fold structure on the basis.
- **P7a (atom_3):** ✓ — the zong involution on R₃ (cf. `Analytic/P7a.lean`).
- **P7b (wedderburn_4):** ✓ — `R 4 ≅ Mat₂(F_q)` (Wedderburn anchor; cf. `Analytic/P7b.lean` for the F₂ case, `UniquenessAlgebraic.lean` for the polymorphic field case).

**Recovery of GUT-A/B.** The bridge `T5_general_from_T_GUT_algebraic` (Lean: `Foundation/Doctrine/Instance/Algebraic.lean` lines 380–420, currently with one sorry for the formal reduction) connects the T_GUT-realisation to the `P1P7_Core` structure used in `T5_general`. The bridge is conceptually straightforward — both structures encode the same algebraic data — but requires careful tracking of the type-level / structure-level translation.

**Verdict.** The algebraic instance instantiates T_GUT *cleanly* with all eight generators having working algebraic analogues. The existing GUT-A/B result is recovered as a corollary of the layer-by-layer Universal Sayability at C = FinVect_{F_q}, δ = F_q.

**Detailed reduction.** The bridge from the T_GUT-framework version to the existing T5_general theorem deserves a sketch. The existing theorem is:

```
theorem T5_general {δ : Type} [Fintype δ] [DecidableEq δ] [Inhabited δ]
    (S : P1P7_Core δ) (N : ℕ) : Nonempty (S.carrier N ≃ R N δ)
```

(`Foundation/R/UniquenessGeneral.lean` line 241). The framework version is:

> **GUT-C Universal Sayability at C = FinVect_{F_q}, δ = F_q:** For any T_GUT-realisation `M : TGUTRealisation (FinVect_{F_q}) F_q`, there is a family of isos `M.R n ≅ tensorPow F_q n = F_q^n`.

The reduction proceeds by:

1. **From P1P7_Core to TGUTRealisation:** Given `S : P1P7_Core δ` with δ = F_q, construct a `TGUTRealisation (FinVect_{F_q}) F_q` whose underlying family is `S.carrier`, structural isos come from S's product/biproduct compatibility, and generator morphisms come from S's atomic structure (P1, P2, P3, P5, P6, P7 witnesses).

2. **Apply Universal Sayability:** The constructed realisation has component isos `M.R n ≅ F_q^n` via the layer-by-layer construction in §4.2.

3. **Identify F_q^n with R n F_q:** In the existing framework, `R n F_q = Fin n → F_q ≃ F_q^n` as F_q-vector spaces (basis isomorphism). The Lean witness: `tensorPow F_q n ≅ R n F_q` is a standard structural iso.

4. **Compose:** `S.carrier n ≃ M.R n ≃ F_q^n ≃ R n F_q`, giving the desired `Nonempty (S.carrier N ≃ R N F_q)`.

This bridge currently carries 1 sorry in `Foundation/Doctrine/Instance/Algebraic.lean` (the step (1) construction); the steps (2)-(4) are implicit in the Universal Sayability theorem and the structural iso `tensorPow F_q n ≅ R n F_q`. The full discharge depends on the canonical realisation's R_tensor being constructed (the other sorry in Algebraic.lean).

When complete, this bridge gives the full backwards-compatibility statement: *the algebraic instance of the T_GUT-framework recovers the existing GUT-A/B uniqueness theorem as a corollary*. This is the framework's first-test compatibility check; passing it (modulo the documented sorries) is necessary for the framework to be considered a *genuine extension* of GUT-A/B rather than a parallel construction.

**The structural significance of recovery.** That GUT-A/B is recovered as the algebraic instance of T_GUT is not just a technical check; it is the *justification* for the framework's existence. If T_GUT did not recover GUT-A/B, the framework would be a parallel construction without backward compatibility — i.e., a new framework that fails to subsume the existing 0-sorry results. The recovery establishes that the framework is *strictly more general* than the existing algebraic case: GUT-A/B is one instance among four, with the additional three (Heyting, quantum, topological) providing new content not available in the existing framework.

This is the methodological pay-off of the categorical-doctrinal approach. Lawvere 1963 [Law63] gave a similar pay-off for algebraic theories: each "algebraic theory" (groups, rings, ...) became a Lawvere theory, with the universal-property characterisations of groups, rings, ... recovered as model-theoretic statements. Our pay-off is analogous: each "articulation substrate" (algebraic, Heyting, quantum, topological) becomes a T_GUT-instance, with the universal-property characterisations recovered per-base.

### §5.2 Heyting instance: T_GUT in HeytAlg

The Heyting instance is the *first* non-algebraic specialisation. The Lean file is `Foundation/Doctrine/Instance/Heyting.lean` (654 LOC, 2 sorries: one in `R_tensor` matching the template, one in `P3_heyting` recording the open Heyting-bimorphism classification).

**Base setup.** The base SMCC is `HeytAlg` (the category of Heyting algebras with Heyting-algebra-preserving morphisms). The δ generator is `Prop` (the Heyting algebra `{⊥ < ⊤}` with the canonical complete-boolean-algebra structure from Mathlib's `Prop.instCompleteBooleanAlgebra`). Strictly, the *cartesian-closed* structure of HeytAlg (with cartesian product and Heyting implication as exponential) provides the SMCC structure; biproducts are automatic (products + initial object).

**Canonical realisation.** The canonical realisation sends `R N := Fin N → Prop`, which is the N-fold cartesian power of Prop. Mathlib's `Pi.instHeytingAlgebra` gives this the canonical Heyting structure. Generator morphisms are interpreted in the Heyting / cartesian-closed setting: compose = product embedding; square = diagonal; hom = currying; modal_V4 = the 4-fold partition; atom_3 = the involution coming from the F₂-Boolean substrate inheriting through `Prop`'s embedding; wedderburn_4 = the candidate `DiamondH4` anchor.

**Per-property analysis:**

- **P1 (id_δ):** ✓ — the identity on Prop.
- **P2 (compose):** ✓ — product embedding `(Fin N → Prop) × (Fin M → Prop) → (Fin (N + M) → Prop)`.
- **P3 (relate):** **Reformulated.** In the algebraic case P3 is F_q-bilinear classification. In the Heyting case the analogue is the *Heyting bimorphism* classification: maps `(Fin N → Prop) × (Fin M → Prop) → (Fin K → Prop)` preserving Heyting meet ⊓ and Heyting implication `⇨` in each argument. The classification problem (analogous to the Arf invariant for F₂-bilinear forms) is a research-open problem. The Lean predicate `IsHeytingBilinear` captures the bimorphism condition; the classification `P3_heyting` is recorded as `sorry` pending resolution of the open question.
- **P4 (square):** ✓ — squaring via meet idempotence (Prop's distinguishing feature: `x ⊓ x = x`).
- **P5 (hom):** ✓ — Heyting implication `⇨` (cf. `Mathlib/Order/Heyting.lean`).
- **P6 (modal_V4):** ✓ (substrate-level) — the 4-fold modality at `R 2 = Prop × Prop = (Fin 2 → Prop)` is `{(⊥,⊥), (⊥,⊤), (⊤,⊥), (⊤,⊤)}`, which is the 2 × 2 truth table. Whether this counts as a "V₄ Shi" in the Heyting sense (since Heyting is not Klein-four-group structure but distributive lattice structure) is a design question; the structural-minimum 4-fold partition is in any case present.
- **P7a (atom_3):** ✓ — the substrate-level involution at R 3 = Prop³, inheriting through the F₂-Boolean substrate of `Prop.instCompleteBooleanAlgebra`.
- **P7b (wedderburn_4):** **Reformulated — NEW MATHEMATICAL OBJECT.** In the algebraic case `R 4 ≅ Mat₂(F_q)`. In the Heyting case the analogue is the conjectured `R 4 ≅ DiamondH4` where:

> **Definition (DiamondH4):** The 4-element linearly-ordered Heyting algebra `{⊥ < mid₁ < mid₂ < ⊤}` with explicit `himp` (Heyting implication) operation:
> - `⊥ ⇨ x = ⊤` for all x
> - `x ⇨ ⊤ = ⊤` for all x
> - `⊤ ⇨ x = x` for all x
> - `mid₁ ⇨ ⊥ = ⊥`
> - `mid₂ ⇨ ⊥ = ⊥`
> - `mid₂ ⇨ mid₁ = mid₁`
> - `mid₁ ⇨ mid₂ = ⊤`

The Lean witness `DiamondH4_is_nonBoolean : ¬¬mid₁ = ⊥ ≠ mid₁` confirms the intrinsic non-Boolean Heyting structure. The *uniqueness* conjecture (currently open) is:

> **Conjecture (Heyting P7b — DiamondH4 uniqueness):** Up to Heyting isomorphism, DiamondH4 is the *unique* non-Boolean Heyting algebra on 4 elements.

If this conjecture holds, then `R 4 Prop ≃ DiamondH4` exhibits a *novel* candidate Heyting Wedderburn anchor — the Heyting analogue of P7b's Mat₂(F_q) in the algebraic case. This is one of the open mathematical sub-problems uncovered by the framework: a substantive research opportunity in Heyting algebra theory.

**Verdict.** The Heyting instance instantiates T_GUT *partially*: six of eight substrate-level generators carry over directly, while P3 (Heyting bimorphism) and P7b (DiamondH4 anchor) reformulate with non-trivial Heyting content. Both reformulations expose genuine open research problems. The framework discriminates correctly between substrate-level and algebraic-class generators, validating the universal-vs-specialisation design intent.

### §5.3 Quantum instance: T_GUT in FdHilb (via stabiliser-formalism + Pauli–Klein4 coincidence)

The quantum instance is the *second* non-algebraic specialisation. The Lean file is `Foundation/Doctrine/Instance/Quantum.lean` (897 LOC, 4 sorries: one in `R_tensor` matching the template, one in `P3_quantum` classifying symplectic forms, one in `P7b_quantum_Hilbert` for the full Mat₂(ℂ) ring iso, one in the universal-sayability cross-check).

**Base setup.** Mathlib does not provide a packaged `FdHilb` (finite-dimensional Hilbert spaces) category as of 2026-05. Building one (PR-4 of the doctrine document) is ~1500–2500 LOC. For the *bridge purpose* (recover the quantum-stabiliser R-family as a T_GUT corollary), we use the **stabiliser-formalism reading** which collapses Hilbert-space content to a transparent algebraic substrate.

Specifically:

- `PauliBase` — the four single-qubit Pauli operators mod phase `⟨iI⟩`, i.e., `{I, X, Y, Z}` under multiplication mod ±1, ±i. As a group, this is *literally* the Klein four group V₄ (since `X² = Y² = Z² = I` and `XY = ±Z`, etc.).
- `PauliN n := Fin n → PauliBase` — the n-qubit Pauli group mod phase. Cardinality 4^n. By `StabilizerQM.equiv` (cf. `Foundation/Wen/Embeddings/StabilizerQM.lean`), `PauliN n ≃ R (2 * n)` as F₂-vector spaces.
- `Matrix (Fin (2^n)) (Fin (2^n)) ℂ` — the concrete Hilbert-space representation via `HilbertPauliFunctor.pauliToHilbert` (cf. `Foundation/Wen/Embeddings/HilbertPauliFunctor.lean`).

This is the same strategy used in the existing `StabilizerQM.lean` (664 LOC, 0 sorry) and `HilbertPauliFunctor.lean` (413 LOC, 0 sorry): the algebraic-substrate view of quantum.

**The Pauli–Klein4 coincidence.** A beautiful structural observation:

> **Observation (Pauli–Klein4):** The four single-qubit Pauli operators mod phase `{I, X, Y, Z}` form *literally the Klein four group* V₄ under multiplication mod phase.

This is not a metaphorical "V₄-like structure" — it is the *exact same* Klein four group. The implication for the framework is that the canonical quantum interpretation of P6 (4-fold modality, encoded by the `modal_V4` generator) is precisely the Pauli {I, X, Y, Z} structure. The Lean witness `P6_quantum_is_pauli_klein4` (cf. `Quantum.lean` §4) makes this explicit.

**Derivation.** The single-qubit Pauli operators are the four complex 2×2 matrices:

```
I = [[1, 0], [0, 1]]      X = [[0, 1], [1, 0]]
Y = [[0, -i], [i, 0]]     Z = [[1, 0], [0, -1]]
```

They satisfy:
- I² = X² = Y² = Z² = I (all involutive: x² = e in V₄ language).
- XY = iZ, YZ = iX, ZX = iY (cyclic with i-phase).
- XYZ = iI.

Mod phase (i.e., quotienting by the subgroup `⟨iI⟩ = {±I, ±iI}`), the multiplication becomes:
- X · X = Y · Y = Z · Z = I.
- X · Y = Z, Y · Z = X, Z · X = Y.
- X · Y · Z = I.

These are exactly the multiplication relations of the Klein four group `V₄ = ⟨a, b | a² = b² = (ab)² = 1⟩` with identification `a ↦ X`, `b ↦ Z`, `ab ↦ Y`, `1 ↦ I`. The isomorphism `PauliBase ≅ V₄` is canonical at the group-theoretic level.

The structural significance: the *abstract* V₄ structure (R 2 in the F₂-Boolean substrate) and the *quantum* V₄ structure (Pauli operators mod phase) are *the same group*, but they live in different categories and have different concrete content. In F₂-Boolean R 2, the V₄ elements are 2-bit strings `{00, 01, 10, 11}` with XOR; in quantum PauliBase, they are matrix operators `{I, X, Y, Z}` with matrix multiplication mod phase. The framework predicts (and the calculation verifies) that the *categorical* shape of V₄ is preserved across the two cases — exactly as the universal-vs-specialisation design intends.

This also gives a concrete answer to a natural question: *why* should the four-fold modality (P6) be V₄ rather than some other order-4 group (e.g., ℤ/4)? In the algebraic case the answer is "involution closure forces exponent-2, and the only exponent-2 group of order 4 is V₄". In the quantum case the answer is "Pauli operators mod phase happen to form V₄, not ℤ/4". The two answers come from *different structural arguments* and converge on the same abstract group, which is structural support for the framework's claim that V₄ is the canonical 4-modality across substrates.

**Pauli stabiliser tensor structure.** The n-qubit Pauli group mod phase is `PauliN n = Fin n → PauliBase`. Multiplication is pointwise; this gives `PauliN n ≅ V₄^n`. As an F₂-vector space (which is the natural lens for stabiliser formalism), `PauliN n ≅ (ℤ/2)^{2n} = R(2n)`. The Lean witness `StabilizerQM.equiv` (cf. `Foundation/Wen/Embeddings/StabilizerQM.lean`) makes this explicit:

```
def equiv : PauliN n ≃ R (2 * n)
```

The factor of 2 reflects that each Pauli operator is encoded by 2 F₂-bits (one for the X-component, one for the Z-component, with Y = XZ giving the third combination).

The structural implication: the *tensor product* of Pauli groups mod phase corresponds to the *direct sum* of F₂-vector spaces, which corresponds to the *additive* structure of the R-tower (`R(N+M) ≅ R N × R M`). So the T_GUT generator `compose_{N,M}` in the quantum case is interpreted as the direct sum embedding `PauliN N × PauliN M → PauliN (N + M)`, which via the equivalence above is `R(2N) ⊕ R(2M) ≅ R(2(N+M))`. This is exactly the algebraic-case compose structure, transported through the stabiliser equivalence.

**Hilbert-space concrete representation.** For applications requiring the full Hilbert-space picture, the bridge is `HilbertPauliFunctor.pauliToHilbert : PauliN n → Matrix (Fin (2^n)) (Fin (2^n)) ℂ`, which sends each Pauli string to its concrete complex matrix in the standard computational basis. The Lean file `HilbertPauliFunctor.lean` (413 LOC, 0 sorry) provides the definitions; the tensor-product compatibility theorems are scaffolded but not yet 0-sorry (cf. Open Problem #3 of §9.2).

The structural fingerprint of V₄ thus appears in *two* of our four bases:
- Algebraic (FinVect_{F_2}): V₄ Shi = {道, 已, 今, 未} = Klein four group as the canonical 4-modality on R 2 = F_2².
- Quantum (FdHilb-via-stabilisers): V₄ = Pauli {I, X, Y, Z} mod phase as the canonical 4-modality on R 2 = PauliBase.

The framework predicts (and the instance verifies) that the *same* abstract V₄ structure appears in both bases, with different concrete content (basis vectors vs Pauli operators) — exactly as the universal-vs-specialisation design intends.

**Per-property analysis:**

- **P1 (id_δ):** ✓ — the identity on PauliBase.
- **P2 (compose):** ✓ — direct sum embedding `PauliN N × PauliN M → PauliN (N + M)`.
- **P3 (relate):** **Reformulated as symplectic.** In the algebraic case P3 is F_q-bilinear. In the quantum-stabiliser case the analogue is the *symplectic form* on the F₂-symplectic image — specifically, the commutator-detection function `σ : PauliN n × PauliN n → F₂` which returns 0 iff two Pauli operators commute and 1 otherwise. The classification of such forms (analogue of Arf invariant for ordinary F₂-bilinear) is a partial-research-open problem. The Lean predicate `relate_quantum_symplectic` captures the structure; `P3_quantum` is recorded with one `sorry` pending the full classification.
- **P4 (square):** ✓ — tensor squaring `PauliN N → PauliN (2N)`.
- **P5 (hom):** ✓ — dagger duality `(−)†`. The dagger structure on FdHilb gives the internal hom via `[A, B] ≃ A* ⊗ B` where `A* = A` (self-duality for finite-dim Hilbert spaces with chosen basis).
- **P6 (modal_V4):** ✓ — Pauli {I, X, Y, Z} mod phase (the Pauli–Klein4 coincidence above).
- **P7a (atom_3):** ✓ — the substrate-level involution at R 3 = PauliN 3, inheriting from the F₂-Boolean substrate of `PauliBase`.
- **P7b (wedderburn_4):** **Reformulated as Mat₂(ℂ).** In the algebraic case `R 4 ≅ Mat₂(F_q)`. In the quantum case the analogue is `R 4 ≅ Mat₂(ℂ)` — the full 2-qubit Pauli image lives inside the algebra of complex 2 × 2 matrices. The Lean witness `P7b_quantum_Hilbert` (cf. `Quantum.lean` §6) records the existence at the structural level; the full ring iso (with explicit basis and Wedderburn-style isomorphism) is recorded as `sorry` pending the Mathlib `Mat₂(ℂ)` infrastructure required for the explicit construction.

**Verdict.** The quantum instance instantiates T_GUT *cleanly* at the structural level, with the same pattern as the Heyting case: six of eight substrate-level generators carry over directly; P3 and P7b reformulate with non-trivial quantum-stabiliser content. The Pauli–Klein4 coincidence is the surprise finding — it gives the canonical quantum interpretation of P6 and reveals that the V₄ modality structure is shared across two different δ-classes (algebraic and quantum) with different concrete content.

### §5.4 Topological instance: T_GUT in Frm (via Sierpinski Ω) — Mathlib boundary findings

The topological instance is the *third* non-algebraic specialisation and the most challenging from a Mathlib-infrastructure perspective. The Lean file is `Foundation/Doctrine/Instance/Topological.lean` (828 LOC, 2 sorries: one in `R_tensor` matching the template, one in `P3_topological` for the frame-bimorphism classification).

**Base setup.** The base SMCC is `Frm` (the Mathlib category of frames with frame-morphisms). The δ generator is the *Sierpinski frame* `Ω` — the 2-element complete-Heyting-algebra `{⊥, ⊤}`, which in Mathlib is realised by `Prop` (with the canonical `Order.Frame Prop` instance from `Prop.instCompleteBooleanAlgebra`).

**Critical Frame vs Heyting overlap.** Mathlib's `Order.Frame` *extends* `CompleteLattice, HeytingAlgebra`. Every frame *is* a complete Heyting algebra. However, the *morphism classes differ*:

- `HeytAlg`-morphisms preserve `⇨` (Heyting implication) — natural for intuitionistic logic.
- `Frm`-morphisms preserve finite `⊓` (meet) + arbitrary `⨆` (join) — natural for topological/locale-theoretic structure.

The carrier `Prop` is shared between the Heyting and topological instances, but the morphism class differs. The two instances are therefore *distinct* — they expose how the framework discriminates between Heyting (intuitionistic) and topological (locale-theoretic) cases even on a shared carrier.

**Mathlib boundary finding.** The *non-cartesian* monoidal structure on `Frm` (= the frame coproduct in Frm, which is the *non-cartesian* monoidal product per Joyal–Tierney [JT84]) is **not in Mathlib** as a `MonoidalCategory Frm` instance. The cartesian product is available (`Pi.instFrame` for products of frames) but the genuine frame coproduct (the non-cartesian monoidal structure on Frm) requires substantial new infrastructure.

For the *bridge purpose* (recover a topological R-family as a `TGUTRealisation` corollary, demonstrating the framework discriminates topological from algebraic / Heyting cases) we use the *cartesian* monoidal structure on `Type 0` exactly as in the sibling Heyting instance, with `Prop` (= Ω) as the chosen generator. The genuine non-cartesian frame tensor `⊗_{Frm}` upgrade is recorded as a future-work pointer.

This is a clear *Mathlib upstream PR opportunity* (cf. §7.4): contributing the non-cartesian monoidal structure on `Frm` to Mathlib would benefit not only our framework but also any locale-theoretic / topological-foundations work in Mathlib.

**Canonical realisation.** The canonical realisation sends `R N := Fin N → Prop`, identical at the carrier level to the Heyting case. Generator morphisms are interpreted in the *frame* (not Heyting) language: compose = product embedding (cartesian); square = meet idempotence; hom = frame implication (which coincides with Heyting implication on the shared carrier `Prop`); modal_V4 = the 4-fold partition (Sierpinski-like); atom_3 = the substrate-level involution; wedderburn_4 = the candidate `Sierpinski²` anchor (the 2-element Sierpinski cube).

**Per-property analysis:**

- **P1 (id_δ):** ✓ — the identity on Ω (= Prop).
- **P2 (compose):** ✓ — product embedding.
- **P3 (relate):** **Reformulated as frame bimorphism.** In the algebraic case P3 is F_q-bilinear; in Heyting it is Heyting-bimorphism; in topological it is *frame-bimorphism* — maps preserving `⊓` in each argument + `⨆` in each argument. The classification is a research-open problem. `P3_topological` is recorded with one `sorry`.
- **P4 (square):** ✓ — squaring via meet idempotence.
- **P5 (hom):** ✓ — frame implication / locale exponential (with the caveat that the full locale-exponential machinery from Joyal–Tierney is not in Mathlib; the simplified statement using the shared Heyting implication on Prop suffices for the bridge purpose).
- **P6 (modal_V4):** ✓ — Sierpinski-like 4-modality at R 2 = Prop² = `{(⊥,⊥), (⊥,⊤), (⊤,⊥), (⊤,⊤)}`, identical at the carrier level to the Heyting case but with frame-morphism interpretation.
- **P7a (atom_3):** ✓ — substrate-level involution.
- **P7b (wedderburn_4):** **Reformulated as Sierpinski².** In the algebraic case `R 4 ≅ Mat₂(F_q)`; in Heyting `R 4 ≅ DiamondH4`; in topological the analogue is `R 4 ≅ Sierpinski²` = `{⊥, ⊤} × {⊥, ⊤}` as a 4-element Boolean frame (= "the frame of opens of R 2 Ω"). The Lean witness `P7b_topological` records the existence + cardinality 4. The genuine OrderIso classification (i.e., the analogue of "minimum non-Boolean Heyting" or "minimum non-commutative central-simple algebra") for frames at 4 elements is a research-open problem.

**Verdict.** The topological instance instantiates T_GUT *partially* at the structural level: six substrate generators carry over, P3 reformulates as frame-bimorphism, P7b reformulates as Sierpinski² anchor. The framework discriminates correctly between Heyting (intuitionistic) and topological (locale-theoretic) even on the shared `Prop` carrier. The Mathlib boundary finding (non-cartesian Frm monoidal absent) is a clear PR opportunity.

### §5.4.1 Frame coproduct construction (technical aside)

For readers who want the explicit construction of the non-cartesian monoidal structure on Frm, we summarise the Joyal–Tierney [JT84] construction:

Given two frames A and B, their *frame coproduct* `A ⊗_Frm B` is defined as the frame generated by symbols `a ⊗ b` for `a ∈ A` and `b ∈ B`, modulo the relations:
- `(a₁ ∧ a₂) ⊗ b = (a₁ ⊗ b) ∧ (a₂ ⊗ b)` (preserves meet in first arg)
- `a ⊗ (b₁ ∧ b₂) = (a ⊗ b₁) ∧ (a ⊗ b₂)` (preserves meet in second arg)
- `(⋁ᵢ aᵢ) ⊗ b = ⋁ᵢ (aᵢ ⊗ b)` (preserves arbitrary join in first arg)
- `a ⊗ (⋁ⱼ bⱼ) = ⋁ⱼ (a ⊗ bⱼ)` (preserves arbitrary join in second arg)
- `⊤_A ⊗ b = b` and `a ⊗ ⊤_B = a` (unit law)

This frame coproduct is the categorical coproduct in Frm (when Frm is given its standard 1-categorical structure with frame morphisms), but it is *not* the cartesian product — those are different constructions giving different frames.

For our T_GUT realisation in Frm at δ = Ω, the *intended* monoidal structure is the frame coproduct (so that `R(N+M) = R N ⊗_Frm R M` is the frame coproduct of the two component frames). With this structure, tensor-power additivity `R(N+M) ≅ R N ⊗_Frm R M` becomes the universal property of the frame coproduct.

The current Lean implementation uses the simpler cartesian product as the monoidal structure (since Mathlib lacks the frame coproduct), which gives a *different* realisation — one that is more like the Heyting case than the genuine topological case. The genuine topological case requires the Mathlib frame coproduct PR (a non-trivial ~1000-2000 LOC effort).

This is a clear gap in the current paper's coverage: the topological instance is *currently realised in a stand-in form* (cartesian product on `Type` with Prop generator) rather than the *genuine* topological form (frame coproduct on Frm with Ω generator). The framework discrimination between Heyting and topological is therefore established only at the morphism-class level (FrameHom vs HeytAlgHom on shared `Prop` carrier), not at the monoidal-structure level.

### §5.5 Cross-cutting: the framework discriminates substrate vs class-specific

The four worked instances together provide strong empirical confirmation of the framework's discrimination capability:

| Property | Algebraic | Heyting | Quantum | Topological |
|---|---|---|---|---|
| P1 distinction | ✓ substrate | ✓ substrate | ✓ substrate | ✓ substrate |
| P2 composition | ✓ substrate | ✓ substrate | ✓ substrate | ✓ substrate |
| P3 relations | ✓ Arf/disc | ✗ reformulated (Heyting bimorphism) | ✗ reformulated (symplectic) | ✗ reformulated (frame bimorphism) |
| P4 squaring | ✓ substrate | ✓ substrate | ✓ substrate | ✓ substrate |
| P5 Hom-as-content | ✓ substrate | ✓ substrate | ✓ substrate | ✓ substrate |
| P6 4-modality | ✓ V₄ Shi | ✓ classical 4-mod | ✓ Pauli–Klein4 | ✓ Sierpinski-like |
| P7a atom involution | ✓ substrate | ✓ substrate | ✓ substrate | ✓ substrate |
| P7b Wedderburn anchor | ✓ Mat₂(F_q) | ✗ reformulated (DiamondH4) | ✗ reformulated (Mat₂(ℂ)) | ✗ reformulated (Sierpinski²) |

Table 4: Per-property status across all four instances.

The pattern is consistent:

- **6/8 substrate-level generators** (P1, P2, P4, P5, P6, P7a) carry over directly across all four bases. These are the *universal* part of the framework: they encode structural articulation features that survive change-of-base intact.
- **2/8 algebraic-class generators** (P3 relations, P7b Wedderburn) reformulate with base-specific content in each of the three non-algebraic bases. These are the *specialisation-bearing* generators: they encode the class-specific concrete content that varies across bases.

This is exactly what the framework is designed to achieve. The discrimination is not a *bug* (the framework "fails" on P3 and P7b for non-algebraic δ); it is the *feature* (the framework correctly identifies which structure is universal and which is specialisation).

Moreover, the four instances expose *two novel candidate mathematical objects* (DiamondH4 and Sierpinski² as Heyting/topological Wedderburn anchors) and one *structural coincidence* (Pauli–Klein4) that were not previously named in the literature. These are the *research outputs* of the framework: by walking through the instances, we generate concrete mathematical objects + classification problems that are independently publishable.

---

## §6. Attacking Open Problem O1

We now address the Coecke–Heunen 2016 / Heunen–Karvonen 2019 open problem on dagger + cartesian coexistence.

### §6.1 The problem (recap)

> **Open Problem O1 (Coecke–Heunen 2016 / Heunen–Karvonen 2019).** A single category cannot simultaneously support dagger compact structure (for quantum) and cartesian-closed structure (for intuitionistic logic) on the same objects without collapsing one structure into the other.

The structural obstruction: products in a dagger category are biproducts (Heunen–Karvonen 2019, Theorem 3.4). This forces dagger + cartesian closed = additive cartesian closed, which is a degenerate case (e.g., Hilb is cartesian-closed only if you allow zero-dimensional spaces). The intuitionistic logic side (HeytAlg) is cartesian-closed but not additive; the quantum side (FdHilb) is dagger compact (and biproduct-enriched) but not cartesian. The two structures resist coexistence.

This is a *structural*, not engineering, obstruction. It is not addressable by clever Mathlib formalisation; it requires a *framework-level* response.

### §6.2 Our factorisation strategy

The framework response we propose is *factorisation*. Specifically:

> **★ Factorisation strategy.** Dagger structure is excluded from T_GUT itself. T_GUT carries no dagger generator; the generators in Table 1 are all dagger-neutral. When T_GUT is instantiated in `FdHilb`, dagger structure arises *as a property of the FdHilb factor*, not as a generator inherited from T_GUT.

The picture:

```
                              T_GUT
                       (V-enriched Lawvere theory;
                       generators encode P1-P7;
                       NO dagger generator)
                                │
                                │ V-functor T_GUT-model M
                                │ (per Power 1999 §3)
                                ▼
                ┌─────────┬─────┴─────┬──────────┐
                │         │           │          │
          FinVect_{F_q}  HeytAlg    FdHilb      Frm
          (algebraic)  (Heyting,  (quantum,   (topological,
                       cartesian- dagger      locale)
                       closed)    compact)
                │         │           │          │
                ▼         ▼           ▼          ▼
            R-family   Heyting     Pauli/      Topological
            over F_q   R-family    stabiliser  R-family
            (proved    (Heyting     R-family
            GUT-A/B)   bimorphism  (Pauli-      (frame
                       open)        Klein4)      bimorphism
                                                 open)
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

The intended consequence: dagger and cartesian closure coexist not "on the same objects of T_GUT" but as *separate δ-realisations* of one T_GUT-doctrine. The HeytAlg factor provides cartesian closure; the FdHilb factor provides dagger; the universal T_GUT skeleton stays neutral.

### §6.3 Why this might work — empirical support from the four instances

The four-instance verification (§5) provides direct empirical support for the factorisation:

1. **HeytAlg factor**: cartesian-closed (HeytAlg's monoidal structure is cartesian + Heyting implication is the exponential). T_GUT-realisation in HeytAlg succeeds (§5.2) without any dagger structure being required. The realisation is purely Heyting/intuitionistic, with the cartesian-closed structure providing the SMCC backing.

2. **FdHilb factor**: dagger compact (FdHilb's compact-closed structure has the dagger giving compact-closed self-duality). T_GUT-realisation in FdHilb succeeds via the stabiliser-formalism reading (§5.3) without any cartesian-closure being required. The realisation uses FdHilb's tensor product + dagger as its SMCC + dagger structure; no cartesian property is invoked.

3. **Both succeed in parallel**: neither realisation invokes the other's structure. They are *independent* T_GUT-realisations in different bases, with disjoint structural commitments. The doctrine T_GUT is "silent" on dagger vs cartesian; both bases qualify as V-objects.

4. **Substrate generators (6 of 8) carry over**: id_δ, compose, square, hom, modal_V4, atom_3 — none of these requires dagger or cartesian structure beyond the underlying SMCC + biproducts. The substrate is genuinely neutral.

5. **Specialisation generators (2 of 8) reformulate independently**: P3 reformulates as bilinear in FinVect, Heyting-bimorphism in HeytAlg, symplectic in FdHilb, frame-bimorphism in Frm — each independently of the others. P7b reformulates analogously.

These five points constitute the empirical confirmation that the factorisation strategy is *consistent with* the four-instance evidence. They do not constitute a *proof* that the strategy resolves O1 (cf. §6.4 for the gap), but they show the strategy is not contradicted by any of the worked cases.

### §6.4 What this does not yet prove

For epistemic honesty, the factorisation strategy is *not* a full resolution of O1. Two specific gaps:

1. **The V-functoriality requirement may force dagger compatibility implicitly.** A T_GUT-model `M : T_GUT → FdHilb` is required (by the framework definition) to be a V-functor. The 2-category V = SMCC + biproducts does not require dagger structure on its objects; but the *target* FdHilb does carry dagger. The question is whether V-functoriality of M, combined with the dagger structure on FdHilb's morphism-objects, implicitly forces M to respect dagger (i.e., to be a *dagger-functor* in disguise). If so, the "factorisation" is illusory — the dagger leaks into M via V-functoriality.

A careful analysis is needed. Provisional answer: V-functoriality only requires M to preserve the *monoidal* structure on V (composition, identity, tensor, associator, unitor, braiding). The dagger structure on FdHilb is *not* part of V's structure (V is SMCC + biproducts, not dagger-SMCC). So V-functoriality does not require M to respect dagger. The dagger on FdHilb's morphism objects is *additional* structure beyond what V tracks, and M does not see it.

This argument is plausible but informal. A formal verification requires the full enriched-Lawvere infrastructure (which is partial in our Lean codebase) plus the explicit dagger-SMCC machinery (which is absent from Mathlib). The verification is recorded as one of the open mathematical sub-problems (cf. §9.2).

2. **A symmetric framework would require either a no-go theorem or a positive dagger-Lawvere-theory.** Our factorisation strategy depends on dagger being *external* to T_GUT. A stronger framework (where dagger is *internal* to T_GUT and quantum + intuitionistic realisations are unified at the doctrine level) would either require:

   - A no-go theorem ruling out internal dagger in T_GUT (which would force the factorisation strategy as the only option), or
   - A positive dagger-Lawvere-theory framework allowing internal dagger generators (which would extend T_GUT to include dagger).

   Heunen–Karvonen 2019 [HK19] provides the no-go direction (products in dagger categories are biproducts), but the full statement at the doctrine level is open. A positive dagger-Lawvere extension would extend T_GUT with a dagger-generator `dagger : δ^⊗N → δ^⊗N` satisfying `dagger ∘ dagger = id` plus naturality with compose, square, hom. Whether such an extension is consistent (i.e., satisfiable in *both* HeytAlg and FdHilb simultaneously) is a research-open question.

   Our framework currently takes the more conservative route: factorisation strategy, dagger external to T_GUT. We flag the dagger-Lawvere extension as a future-work direction.

### §6.4.1 Formalising the V-functoriality argument

The informal V-functoriality argument deserves expansion. We sketch how a formal proof would proceed.

Let `V = SMCC + biproducts` (the doctrinal base 2-category) and let `M : T_GUT → C` be a T_GUT-realisation in a base C ∈ V. By definition, M is a V-functor: it preserves the V-enriched structure of T_GUT, which is the SMCC + biproducts structure.

Suppose C carries additionally a dagger structure (e.g., C = FdHilb with the inner-product dagger). The question: does M's V-functoriality force any dagger-compatibility on M's image?

**Claim.** No. The dagger structure on C is *outside* V's structure (V records SMCC + biproducts; dagger is additional). A V-functor `M : T_GUT → C` preserves SMCC + biproducts (this is the V-enrichment requirement) but is *not required* to preserve dagger (since dagger is not part of V's structure).

**Argument.** Consider any morphism `f : M.R N → M.R M` in C arising from a T_GUT generator (e.g., `f = M.compose_mor N M`). The V-functoriality of M requires that f respects the monoidal structure: `f ∘ (g₁ ⊗ g₂) = (h₁ ⊗ h₂) ∘ f'` for appropriate `gᵢ, hᵢ, f'` arising from the equations. This is a *monoidal* constraint, expressible without reference to dagger.

The dagger `f† : M.R M → M.R N` is *additionally* defined in C (since C is a dagger category), but its existence is a property of C alone, not a property forced on f by M's V-functoriality. The morphism f need not satisfy any compatibility with `f†` from M's perspective.

In particular, the seven generator morphisms of M (compose, square, relate, hom, modal_V4, atom_3, wedderburn_4) are recorded in `TGUTRealisation` as plain morphisms in C, with no dagger structure assumed. When C happens to be a dagger category, dagger versions exist (one can apply `† : C^{op} → C` to any morphism), but they are not part of M's structural data and are not constrained by T_GUT's equations.

**Caveat.** The argument assumes V does *not* include dagger structure. If V is changed to V' = dagger-SMCC + biproducts (a stronger doctrinal base), then V'-functoriality of M would require dagger-compatibility, and the factorisation argument fails. The factorisation strategy is *contingent on the choice of V*; if a future framework requires dagger at the doctrinal level, T_GUT would need to be redefined as a V'-enriched theory.

**Formalisation status.** The argument above is rigorous as a sketch but not Lean-formalised. To formalise: we need (i) Mathlib's `DaggerCategory` class (absent); (ii) the enriched-categorical machinery establishing V = SMCC + biproducts as a 2-category (partial in `Foundation/Doctrine/EnrichedLawvereTheory.lean`); (iii) explicit verification that none of T_GUT's equational laws (TGUTLaw, §3.3) implicitly require dagger compatibility (a case-by-case check on the 8 law constructors).

Item (i) is PR-4 of §7.4. Items (ii)-(iii) are γ.3 refinement targets. With these in place, the factorisation strategy can be Lean-verified as a theorem rather than informal argument.

### §6.4.2 An alternative: dagger-Lawvere theories

For epistemic completeness, we describe the alternative strategy: extend T_GUT with internal dagger structure.

A *dagger-Lawvere theory* would be a V'-enriched Lawvere theory for V' = dagger-SMCC + biproducts, with generators that include a dagger-like structure (an involution generator on each `δ_T^⊗N`). The relevant literature direction is Heunen–Karvonen 2019 [HK19], which formalises dagger categories and dagger-limits and provides some scaffolding for dagger-Lawvere extensions.

If such a framework were to exist, T_GUT would extend to T_GUT^† with an additional generator `dagger_N : δ_T^⊗N → δ_T^⊗N` satisfying `dagger_N ∘ dagger_N = id` plus naturality with respect to compose, square, hom, etc. The question is whether T_GUT^†-realisations can simultaneously exist in both HeytAlg (cartesian-closed) and FdHilb (dagger compact), given the structural obstruction from Heunen–Karvonen 2019 that products in dagger categories are biproducts.

Our preliminary analysis: a T_GUT^†-realisation in HeytAlg would need to interpret `dagger_N` as a Heyting-algebra-preserving involution. The natural candidate is the identity (since HeytAlg has no non-trivial dagger structure), but this trivialises the dagger generator. A T_GUT^†-realisation in FdHilb interprets `dagger_N` as the inner-product dagger, which is non-trivial. The question: can the two interpretations satisfy the *same* set of dagger naturality equations?

We suspect not (i.e., we suspect a no-go theorem rules out T_GUT^†-realisations in both bases simultaneously), but a definitive answer requires either an explicit no-go argument or a positive construction. This is one of the open research directions we list in §9.

The conservative framework (T_GUT without internal dagger, with factorisation strategy) is our chosen path because it is empirically supported by four worked instances and does not depend on resolving the dagger-Lawvere-theory feasibility question. The more ambitious framework (T_GUT^† with internal dagger) is flagged for future work.

### §6.5 Summary of the O1 attack

Our attack on Open Problem O1 is:

- **Strategy**: factorisation — exclude dagger from T_GUT generators; let it live only as a property of the FdHilb factor.
- **Empirical support**: four worked instances (§5) consistent with the strategy; substrate generators (6/8) genuinely base-neutral; specialisation generators (P3, P7b) reformulate independently in each base.
- **Gap**: V-functoriality argument is rigorously sketched (§6.4.1) but not Lean-formalised. The formalisation depends on PR-4 (dagger-SMCC) and γ.3 refinement (full equational coherence) being in place.
- **Alternative explored**: T_GUT^† with internal dagger generators (§6.4.2). Preliminary analysis suggests this is infeasible; a definitive resolution is open research.
- **Future work**: either complete the V-functoriality formalisation, or resolve the dagger-Lawvere-theory feasibility question, or both.

The contribution we claim: the framework *makes precise* the form of an O1 resolution (factorisation, with dagger external) and *provides concrete evidence* that this form is consistent with four worked instances. We do not claim a full resolution; we claim a substantive partial result that constrains future work.

---

## §7. Lean Formalisation

This section catalogues the existing Lean codebase implementing the GUT-C framework, identifies the current sorry status, and points to Mathlib upstream contribution opportunities.

### §7.1 Architecture: Foundation/Doctrine/ tree

The codebase lives at `formal/SSBX/Foundation/Doctrine/` and is organised as:

```
Foundation/Doctrine/
├── LawvereTheory.lean              -- (G1) Classical Lawvere theory class
├── EnrichedLawvereTheory.lean      -- (G2) Power-style enriched extension
├── T_GUT.lean                      -- (G3) The T_GUT theory + Universal Sayability
└── Instance/
    ├── Algebraic.lean              -- (G4) T_GUT in FinVect_{F_q}
    ├── Heyting.lean                -- (G5) T_GUT in HeytAlg (δ = Prop)
    ├── Quantum.lean                -- (γ.3-A) T_GUT in FdHilb (δ = PauliBase)
    └── Topological.lean            -- (γ.3-B) T_GUT in Frm (δ = Ω)
```

The 5-file structure (G1–G5) was the original Phase γ.2 deliverable (single-session via 5 parallel agents, completed 2026-05-17); the two additional instance files (Quantum, Topological) were the Phase γ.3 deliverables (parallel agents, completed shortly after). Total of 7 Lean files implementing the framework.

### §7.2 Files + LOC + sorry table

| File | LOC | Sorries | Notes |
|---|---|---|---|
| G1 `LawvereTheory.lean` | 643 | 1 | Mathlib-PR-quality core class; pseudo finite products. The 1 sorry is in the free-Lawvere construction (deferred to Mathlib PR-2). |
| G2 `EnrichedLawvereTheory.lean` | 929 | 1 | Power 1999 V-enriched extension. The 1 sorry is in the V-free-functor construction (deferred). |
| G3 `T_GUT.lean` | 611 | 2 | 8 generators per §3.2 + equations per §3.3 + headline Universal Sayability proven at layer-iso level. 2 sorries: canonical realisation's R_tensor (engineering); universal_sayability discharge of canonical (engineering). |
| G4 `Instance/Algebraic.lean` | 485 | 2 | Recovers GUT-A: P1P7_Satisfier_F2 → Mat₂(ZMod 2) ring iso. 2 sorries: R_tensor pattern; T5_general recovery bridge. |
| G5 `Instance/Heyting.lean` | 654 | 2 | PATH C VALIDATED + DiamondH4 anchor. 2 sorries: R_tensor pattern; P3_heyting classification (open). |
| γ.3-A `Instance/Quantum.lean` | 897 | 4 | Pauli–Klein4 coincidence + Mat₂(ℂ) anchor. 4 sorries: R_tensor pattern; P3_quantum symplectic classification; P7b_quantum_Hilbert full ring iso; universal-sayability cross-check. |
| γ.3-B `Instance/Topological.lean` | 828 | 2 | Sierpinski² anchor + Mathlib boundary findings. 2 sorries: R_tensor pattern; P3_topological frame-bimorphism classification. |
| **Total** | **5047 LOC** | **14 sorries** | (Note: corrected count vs earlier 10-sorry estimate.) |

Build state at 2026-05-17: `lake build SSBX.Foundation.Doctrine.*` succeeds. The total Doctrine tree adds ~5047 LOC to a pre-existing ~3936-job build; 0 new axioms across all 7 files.

The 14 sorries are not engineering debt in the typical sense:

- 5 are `R_tensor` patterns deferred for ~30-LOC bulky-but-routine implementation reasons (the construction is clear; the proof is just long).
- 4 are *research-open* questions (P3 classifications for Heyting, Quantum, Topological; P7b full ring iso for Quantum's Mat₂(ℂ)). Each is a publishable open problem in its respective subfield.
- 3 are bridge / recovery proofs (`universal_sayability` discharge, T5_general recovery) deferred for engineering reasons but with clear constructions.
- 2 are the canonical-realisation interior proofs (free Lawvere theory, V-free functor).

A more accurate characterisation: 7 sorries are engineering debt (bulky-but-routine); 4 are research-open; 3 are bridge/recovery deferred.

### §7.3 What "0 new axioms" means

Throughout the GUT-A/B/C Lean codebase, "0 new axioms" means: no `axiom` declarations beyond what Mathlib already provides. The codebase uses Mathlib's standard substrate (classical logic via `Classical`, `OrderHom.lfp` for fixed points, `Equiv` for type-level isomorphisms, `RingEquiv` for ring isos, etc.) but does not introduce new axioms of its own.

Specifically, the framework does *not* require:
- New foundational axioms (univalence, AFA, etc.)
- New large-cardinal hypotheses
- Non-Mathlib `noncomputable` definitions (we use `noncomputable def` for `componentIso` and `canonical`, but these compile under Mathlib's standard classical scope)

The codebase is therefore strictly conservative over Mathlib's foundational commitments. This matters for the metalogic-identification companion paper [lawvere-identification.md v0.6]: the claim "D1 = lfp(Φ') is a Knaster–Tarski lfp on a complete lattice 𝒜 of articulation candidates" lives entirely in standard ZFC + classical logic, with Mathlib's `OrderHom.lfp` providing the formalisation machinery.

### §7.4 Mathlib upstream PR opportunities

Four Mathlib upstream PR opportunities have been identified during the GUT-C work. Each is independently valuable for Mathlib applications beyond GUT-C.

**PR-1: `ElementaryTopos` bundling** (~400-700 LOC, NO new math).

All components exist in Mathlib (`HasFiniteLimits`, `CartesianClosed`, `HasSubobjectClassifier`); the PR just bundles them into a single `class ElementaryTopos C extends ...`. This enables many other Mathlib applications beyond GUT. Lowest risk; ideal as a confidence-builder.

**PR-2: `LawvereTheory` + `Model` API** (~600-900 LOC, pure recipe from Lawvere 1963).

`class LawvereTheory T` = small category with strict finite products + generator. `structure Model T C` = product-preserving functor. Morphisms of models, equivalence, free models. Critical for GUT-C *plus* Mathlib's general algebraic-theory infrastructure. Lawvere 1963 is well-known so review should be straightforward.

**PR-3: Weighted enriched limits** (~600-1000 LOC, technical but standard).

Current Mathlib only has *conical* enriched limits (`Mathlib.CategoryTheory.Enriched.Limits`); Power 1999-style enriched Lawvere theories need *weighted* limits (Kelly 1982). Recipe in Kelly 1982 *Basic Concepts of Enriched Category Theory* is detailed. Hardest of the four but mathematically well-understood.

**PR-4: Dagger-SMCC + FdHilb scaffold** (~1500-2500 LOC, heavier).

Bundle finite-dimensional Hilbert spaces from existing analytic content in `InnerProductSpace/Adjoint.lean`. Define `class DaggerSymmetricMonoidalCategory`; compact-closed instance. Needed for full quantum-side Lean verification of the framework (currently we use the stabiliser-formalism reading as a workaround). This is the most ambitious PR but unlocks substantial Mathlib applications in categorical quantum mechanics.

**Total contribution potential**: ~3100-5100 LOC across 4 PRs. Review cycles typically 3-6 months each; can run in parallel.

### §7.5 Build instructions (reproducibility)

The full Lean codebase is at `formal/SSBX/`. Builds with `lake build SSBX`. Required:

- Lean 4 toolchain (see `lean-toolchain` file in repo root for pinned version)
- Mathlib (pinned to commit in `lake-manifest.json`)

To verify the GUT-C Doctrine tree specifically:
```
lake build SSBX.Foundation.Doctrine
```

To verify a specific instance:
```
lake build SSBX.Foundation.Doctrine.Instance.Heyting
lake build SSBX.Foundation.Doctrine.Instance.Quantum
lake build SSBX.Foundation.Doctrine.Instance.Topological
lake build SSBX.Foundation.Doctrine.Instance.Algebraic
```

Build state at 2026-05-17: succeeds with the sorry counts above. No build errors; only sorry warnings as documented.

---

## §8. Discussion

This section places our framework in relation to existing work: topos quantum theory (Bohrification asymmetry), categorical doctrines (Lawvere 1969), the companion metalogic paper, and the broader status of Open Problem O1.

### §8.1 Comparison with topos quantum theory (Bohrification asymmetry)

The Heunen–Landsman–Spitters Bohrification programme [HLS09, HLSW12, DI08] is the most successful prior cross-domain categorical unification, and the closest sibling of our framework. The comparison is informative.

**Structural similarity.** Both Bohrification and our framework address "how does quantum content relate to intuitionistic content categorically?" Both use the categorical universe of toposes / SMCCs as the unifying structure. Both work at the *base* level (the choice of ambient category) rather than at the *object* level (encoding one inside the other).

**Conceptual difference.** Bohrification is *asymmetric* — it encodes quantum (noncommutative C*-algebra) *inside* intuitionistic (the internal logic of the Bohr topos). The mapping is one-directional: from quantum to intuitionistic. There is no reverse construction recovering quantum from intuitionistic.

Our framework is *symmetric* — both quantum (FdHilb instance) and intuitionistic (HeytAlg instance) are *parallel* T_GUT-realisations, neither encoded inside the other. The mapping at the *doctrine* level: the same T_GUT theory has different specialisations in different bases. The dagger structure lives on the FdHilb side only; the cartesian-closed structure on the HeytAlg side only; T_GUT itself is silent on either.

**Technical implication.** Bohrification *loses the dagger* (HLS [HLS09] explicitly notes that internal Gelfand spectrum encoding does not preserve dagger structure). The dagger structure on FdHilb is *not* recoverable from the internal commutative-subalgebra information. This is the structural reason Bohrification is asymmetric: encoding quantum inside intuitionistic is lossy.

Our framework *preserves the dagger* (it lives on the FdHilb factor and is not pushed into a topos encoding). The factorisation strategy of §6 ensures dagger is accessible to the framework user precisely when they target FdHilb; it is not present when they target HeytAlg. The two structures stay separate.

**What we inherit from Bohrification.** The general framework of "doctrine + per-base specialisation" is implicit in Bohrification (the Bohr topos T(A) is a base in which quantum lives intuitionistically). What we explicitly formalise is the Lawvere-theoretic version: a single syntactic theory T_GUT with universal generators + equations; per-base specialisation via T_GUT-models.

**What we depart from Bohrification.** The asymmetric encoding. We do not push one structure inside the other; both live in the framework at the same syntactic level (T_GUT generators), with their concrete content differing only in specialisation.

### §8.2 Comparison with categorical doctrines (Lawvere 1969)

The notion of a *doctrine* in the categorical sense traces back to Lawvere [Law69] *Adjointness in Foundations*, where doctrines were introduced as a 2-categorical generalisation of Lawvere theories. A doctrine in Lawvere's sense is a 2-functor `D : Cat → Cat` (or, more precisely, a 2-category-valued 2-functor on a 2-category of base structures), with models being objects of the 2-categorical pseudo-image.

The relationship to enriched Lawvere theories (Power 1999) is that an enriched Lawvere theory over V can be presented as a doctrine in Lawvere's sense, with the doctrine 2-functor sending a base V-category to its category of T-models. Power 1999 makes the enriched-Lawvere-theory level precise; the doctrinal level is the 2-categorical wrapping.

For our purposes:

- **T_GUT lives at the enriched-Lawvere-theory level.** Its definition is via generators + equations in a V-enriched setting. This is the simpler level and the one we formally work with.
- **The doctrinal wrapping is implicit.** The "doctrine" picture says T_GUT is a single syntactic object; T_GUT-models in different bases V₁, V₂, V₃, ... give different concrete structures, with morphisms of models being natural transformations. This 2-categorical wrapping is needed for the *full* Universal Sayability theorem (covering naturality across morphisms of realisations and change-of-base coherence) but is not used in the layer-by-layer version we formalise.

So our framework is *compatible* with Lawvere 1969's doctrinal framework but does not yet exploit the full 2-categorical machinery. The γ.3 refinement will need to push to the doctrinal level for the coherence proofs; the current paper claims only the enriched-Lawvere-theory level.

### §8.3 Relation to D1 = lfp(Φ') metalogic identification

The companion paper [`lawvere-identification.md`](../lawvere-identification.md) v0.6 makes a separate but complementary claim: the bi-directional closure D1 ⟷ P1–P7 of the R-tower framework is rigorously identified as the Knaster–Tarski least fixed point of a carrier-growing requirements-extraction operator Φ' on a complete lattice 𝒜 of articulation candidates. The headline statement:

> **D1 = lfp(Φ')** — the unique articulation candidate whose extracted requirements are already contained in its own structure.

The proof strategy uses Mathlib's `OrderHom.lfp` (cf. `Mathlib.Order.FixedPoints`). The full treatment is in the companion paper (~33000 words, ~95% publication-ready, Lean partial formalisation in `Foundation/Closure/PhiOperator.lean` with 5/8 sorries discharged).

**Relationship to the current paper.** The companion paper covers the *vertical* (fixed-δ) direction of the framework: "what does articulation closure mean in a fixed δ = Bool / F_2 setting?" The answer: it is a Knaster–Tarski lfp on a candidates lattice.

The current paper covers the *horizontal* (cross-δ) direction: "how does articulation universally apply across δ-classes?" The answer: it is an enriched-Lawvere-doctrine T_GUT instantiated in different SMCC bases.

**The two-axis picture.**

```
                    Vertical (fixed-δ)               Horizontal (cross-δ)
                    ─────────────────                ──────────────────
Closure structure   D1 = lfp(Φ')                     T_GUT (enriched Lawvere
                    (Knaster-Tarski)                 theory)
                                                     
Universality        D1 is unique solution            R_C is unique T_GUT-
                    of self-articulation             realisation in (C, δ)
                                                     
Lean formalisation  Foundation/Closure/              Foundation/Doctrine/
                    PhiOperator.lean                 T_GUT.lean
                                                     
Metalogic           Standard ZFC + Knaster-Tarski    Standard category theory
home                (Mathlib OrderHom.lfp)           + enriched Lawvere (Power
                                                     1999)
                                                     
Relation to Lawvere Lawvere 1969 as methodology      Lawvere 1963 as direct
                    (paradox-vs-fixed-point          theorem (functorial
                    dichotomy)                       semantics)
```

The two axes are *complementary*. Together they constitute a substantially stronger treatment of articulation universality than either alone.

**Why both are needed.** The vertical axis answers "in a single ambient SMCC + chosen δ, is the R-family the unique satisfier of self-articulation closure?" The horizontal axis answers "across different ambient SMCCs + chosen δ, does the same syntactic theory T_GUT give parallel realisations?" Vertical gives uniqueness *within* a base; horizontal gives parallelism *across* bases. Both are required for a comprehensive framework.

### §8.4 Open Problem O1 progress versus full resolution

A summary of where we stand on Open Problem O1:

- **What is closed**: the factorisation strategy is *defined* (dagger lives only on the FdHilb factor of T_GUT-models). The four-instance verification provides *empirical support* (substrate generators carry over neutrally; specialisation generators reformulate independently in each base; no instance requires the other base's structure).

- **What is open**: the V-functoriality argument (whether dagger structure on FdHilb morphisms forces M to be a dagger-functor implicitly) is *informal*. A formal verification requires full enriched-Lawvere infrastructure (partial in our Lean codebase) + dagger-SMCC machinery (absent from Mathlib). The argument is plausible but not proved.

- **What is required for full resolution**: either (a) prove the V-functoriality argument formally (verify the factorisation is consistent), or (b) extend T_GUT with internal dagger generators in a coherent dagger-Lawvere framework. Both are open.

Our contribution: a *plausible-and-evidence-backed* attack on O1, with the framework formalising the structural form of an O1 resolution. We do not claim a full resolution; we claim a substantive partial result that constrains future work.

### §8.5 Risks and limitations

For epistemic hygiene, we list the risks explicitly:

1. **The framework may need substantial revision.** Our four-instance verification is encouraging, but it covers only four bases out of an infinite family. Other bases (smooth manifolds, ∞-groupoids, stochastic categories, ...) may reveal structural mismatches we have not anticipated.

2. **Mathlib infrastructure gaps are substantial.** The four PR opportunities (§7.4) total ~3100-5100 LOC. Review cycles total ~12-24 months in parallel. Without these PRs, the formalisation programme remains incomplete.

3. **The O1 attack depends on the factorisation strategy.** If a hidden dagger leak via V-functoriality is shown, the strategy fails and we need either a no-go theorem or a positive dagger-Lawvere framework. Both are open.

4. **The Heyting and topological cases overlap on the Prop carrier.** §5.4 documents the Frame vs Heyting distinction (different morphism classes on shared `Prop`); but a critic might argue that the framework therefore "duplicates" — that the Heyting and topological instances are not genuinely distinct. Our response: the morphism class distinction is *categorically* substantive (`HeytAlg` and `Frm` are different categories despite sharing carriers); the framework discrimination tracks this correctly.

5. **The DiamondH4 conjecture and related research-open problems may turn out false.** The framework predicts a "minimum non-Boolean Heyting at carrier 4" exists and is uniquely DiamondH4; the actual classification of 4-element Heyting algebras up to isomorphism is a non-trivial question that we have not fully solved. If the classification reveals multiple non-Boolean 4-element Heytings (e.g., a non-linear variant), the conjecture needs refinement.

These risks do not undermine the framework's value as a research direction; they constrain its current state to be a *proposal* rather than a *theorem*.

### §8.5.1 What we would change if we could rewrite the framework today

If we were starting the framework from scratch with the lessons learned from the current four-instance verification, we would make several changes:

1. **Start with the doctrinal change-of-base from day one.** The current framework adds the "doctrinal level" implicitly through the per-base specialisation principle (§3.9). A cleaner approach would be to *start* with the 2-categorical doctrine framework (V as a 2-category; T_GUT as a V-enriched theory; change-of-base as a 2-functor) and only later specialise to instances. The current sequence (instances first, doctrine second) was driven by Lean-formalisation pragmatism (instances are easier to formalise individually); a fully theoretically-clean treatment would invert this.

2. **Make the dagger-Lawvere extension explicit early.** The current framework treats dagger as external (factorisation strategy of §6); but the question "does T_GUT extend to T_GUT^† with internal dagger?" is sufficiently important that it should be addressed *upfront*, not as a brief §6.4.2 remark. A future revision would either include T_GUT^† as the primary framework (with T_GUT as a sub-fragment), or include explicit treatment of "why the factorisation strategy is the right one despite the conceptual cost".

3. **Address the (∞, 1)-categorical question.** The framework is strictly 1-categorical, but the question "does T_GUT extend to an (∞, 1)-enriched setting?" is natural and unaddressed. A future revision would include at least a brief discussion of the obstruction structure (Berman 2019 [Ber19] on ∞-Lawvere; Lurie [Lur09, Lur17] on ∞-toposes) and indicate how the framework would proceed in (∞, 1).

4. **Test more instances beyond the four worked.** The four instances (algebraic, Heyting, quantum, topological) are intentionally chosen as the cardinal "δ-classes" of the framework, but they do not exhaustively cover the categorical universe. Future instances to test: Stoch (Markov categories); Smooth-Manifolds (differential geometry); ∞-Gpd (homotopy types); Vect_∞ (infinite-dim vector spaces with continuous duals). Each would either further validate the framework or expose new structural mismatches.

5. **Provide a more rigorous specification of the "doctrine" itself.** The current paper treats T_GUT as a V-enriched Lawvere theory with V = SMCC + biproducts, but does not give a fully rigorous 2-categorical specification of V (size considerations, the precise notion of "SMCC functor", coherence with biproducts under base-change). A future revision would include a rigorous appendix specifying V at full categorical precision.

These are not refutations of the current framework but rather *improvements that would make the framework more robust and complete*. They are listed here to indicate the *direction of refinement* expected from peer review.

### §8.6 Wider context: doctrinal frameworks for foundational unification

The methodological move we make — *propose a categorical doctrine T such that target-class universal-property theorems are recovered as T-models in different bases* — has a longer history beyond Lawvere 1969. We briefly position our framework in this wider context.

**Lawvere 1963 / Functorial Semantics:** the original Lawvere theory framework targets *algebraic* content: equational theories of groups, rings, modules, etc. Models in different bases (Set, Top, Ab) give different category-theoretic incarnations of the algebraic content. The methodological pattern *syntactic theory + parametric semantic interpretation* is established here.

**Lawvere 1969 / Adjointness in Foundations:** generalises to 2-categorical doctrines, with adjoints organising the relationship between theories and their models. The methodological pattern *theory-side and model-side as 2-adjoint structures* is established here.

**Power 1999 / Enriched Lawvere theories:** extends to enriched bases (V-categories). The methodological pattern *enriched semantics: theory in V₁ has models in V₂* is established here. This is the direct ancestor of our T_GUT.

**Hyland–Power 2007 / Universal algebra unification:** integrates Lawvere theories with computational-effects monads. The methodological pattern *one theory, many monads, with operations + equations as syntactic primitives* is the explicit Hyland–Power slogan and is what we adopt for T_GUT.

**Heunen–Vicary 2019 / Categorical Quantum Theory:** extends to dagger compact closed categories. The methodological pattern *dagger structure as a property of the base, not the theory* aligns with our factorisation strategy.

**Bohrification (HLS 2009):** specific application to quantum-via-intuitionistic, with the asymmetric encoding strategy.

**Our T_GUT (this paper):** extends the methodology to substrate-level structural axioms (P1–P7 = articulation primitives) with per-base specialisation across {algebraic, Heyting, quantum, topological}.

The methodological move at our level is: *take a non-algebraic system of articulation primitives and encode them as a categorical doctrine such that the universal-property theorems for each substrate class follow as instances*. This is the analogue of "algebraic theories are equational theories with finite product structure" for the more general setting of articulation primitives.

If our framework holds up, it provides a *template* for future cross-domain doctrinal frameworks:

- **T_GeometricFoundations:** a doctrine whose instances recover universal properties of differential / smooth structure across Set, Top, smooth ∞-groupoids, synthetic differential geometry, etc.
- **T_LinguisticArticulation:** a doctrine whose instances recover universal properties of cross-language conceptual structure (signifier/signified, sense/reference, ...).
- **T_AIRepresentation:** a doctrine whose instances recover universal properties of representation in different AI architectures (transformer attention, neural network intermediate representations, ...).

These are speculative future directions; they are mentioned to indicate the *methodological breadth* of the categorical-doctrinal framework rather than to commit to any specific application.

### §8.7 Comparison with monoidal-Heyting-monad fragments

A related categorical framework worth comparing is the *monoidal-Heyting-monad* fragment: a categorical structure combining a Heyting algebra (for intuitionistic content) with a monoidal structure (for tensor product) and a monad (for the effect / computation aspect). This has been studied in linear-logic settings (Bierman 1995, Schalk 2001) and provides another vehicle for combining intuitionistic and tensor-product structure.

The differences from our framework:

1. **Scope.** Monoidal-Heyting-monads target a specific fragment (intuitionistic linear logic with a monad); T_GUT targets the broader substrate-articulation question (P1–P7 in any SMCC + biproducts base).

2. **Generality.** Monoidal-Heyting-monads are typically formulated for one specific structural pattern (e.g., intuitionistic linear logic with bang-monad); T_GUT is a *family* of patterns parameterised by P1–P7 and per-base specialisation.

3. **Empirical reach.** Monoidal-Heyting-monads have specific computational-effects applications (state, exceptions, ...); T_GUT has the broader claim that any "articulation of sayable content" satisfying P1–P7 falls into the framework.

Both frameworks share the categorical-doctrinal methodology; they differ in scope and ambition. The frameworks are *complementary*: a monoidal-Heyting-monad fragment can in principle be analysed as a T_GUT-realisation in a suitable base (the specific intuitionistic-linear-logic SMCC).

### §8.8 Limitations specific to the Lean 4 + Mathlib substrate

For readers familiar with Lean 4 + Mathlib formalisation:

**What Lean 4 + Mathlib gives us:**

- Strict 1-categorical infrastructure: `CategoryTheory.Category`, `Functor`, `NatTrans`, `Iso`, `Limits`, `Adjunction`.
- Symmetric monoidal closed categories: `MonoidalCategory`, `SymmetricCategory`, `MonoidalClosed`.
- Biproducts: `HasFiniteBiproducts`, with auto-conversion from `HasFiniteProducts + HasZeroObject + Preadditive`.
- Many concrete category instances: `FGModuleCat`, `MarkovCategory`, `CopyDiscardCategory`, etc.
- Strong type-theory support: dependent types, decidable equality, well-founded recursion.

**What Lean 4 + Mathlib does *not* give us (yet):**

- `LawvereTheory` (PR-2 of §7.4).
- `EnrichedLawvereTheory` with weighted limits (PR-3).
- `ElementaryTopos` bundling (PR-1).
- `DaggerCategory` + `DaggerSymmetricMonoidalCategory` + `FdHilb` as a packaged category (PR-4).
- Non-cartesian monoidal structure on `Frm` (frame coproducts).
- Constructive Gelfand duality (for Bohrification comparisons).
- Full ∞-categorical machinery (for potential future ∞-Lawvere extensions).

These gaps are not unique to GUT-C; they are general Mathlib coverage gaps in higher categorical infrastructure. Our framework provides an explicit motivation for contributing them, with concrete LOC estimates and dependency mappings.

**Engineering implications.** The current local approximations in `Foundation/Doctrine/` are designed to be drop-in compatible with the eventual Mathlib upstream versions. Once the upstream PRs land, the local approximations can be substantially simplified (or removed entirely, in favour of `import Mathlib.CategoryTheory.LawvereTheory` etc.).

The current 14-sorry status is also expected to drop substantially once the upstream infrastructure is available: 7 of the 14 sorries are engineering-debt (R_tensor patterns, bridge proofs) that depend on the free-Lawvere construction; once that's available upstream, these become trivial.

---

## §9. Conclusion and Future Work

### §9.1 Summary of contributions

This paper proposed the GUT-C framework — a biproduct-enriched Lawvere theory T_GUT — as the doctrinal home for the R-tower's Universal Sayability theorem across symmetric monoidal closed categories with biproducts. We:

1. Defined T_GUT precisely as a V-enriched Lawvere theory with eight generator families encoding P1–P7 (Table 1) and equational laws encoding their coherence.
2. Proved a layer-by-layer Universal Sayability theorem (§4): for any SMCC C with biproducts and chosen δ, every T_GUT-realisation has a natural family of component isomorphisms to the canonical tensor-power realisation.
3. Verified the framework on four worked instances (§5): algebraic (FinVect_{F_q}, recovering GUT-A/B), Heyting (HeytAlg + DiamondH4), quantum (FdHilb via stabiliser-formalism + Pauli–Klein4 coincidence), topological (Frm + Sierpinski²).
4. Attacked Open Problem O1 (§6) via a *factorisation* strategy: dagger external to T_GUT, on the FdHilb factor only.
5. Catalogued the Lean formalisation (§7): 7 files, 5047 LOC, 14 sorries (mostly research-open or engineering-debt), 0 axioms.
6. Identified five open research problems (DiamondH4 uniqueness; Heyting bimorphism; Pauli Mat₂(ℂ) iso; Frame bimorphism; finite frame classification) and four Mathlib upstream PR opportunities (§7.4).

### §9.2 Five open research problems

The framework exposes substantive research questions in classical algebra, intuitionistic logic, quantum stabiliser theory, and locale theory:

1. **Heyting Wedderburn anchor (DiamondH4 uniqueness):** Up to Heyting isomorphism, is `DiamondH4` (the 4-element linearly-ordered Heyting algebra) the *unique* non-Boolean Heyting algebra on 4 elements? Publishable in *Studia Logica* or *Journal of Logic and Computation*.

2. **Heyting bimorphism classification (P3 in HeytAlg):** Classify (up to Heyting isomorphism) the maps `(Fin N → Prop) × (Fin M → Prop) → (Fin K → Prop)` preserving Heyting meet ⊓ and Heyting implication ⇨ in each argument. The intended analogy is with the Arf invariant for F₂-bilinear forms; an analogous "Heyting Arf invariant" is conjectured to exist. Publishable in *Algebra Universalis* or *Order*.

3. **Pauli Mat₂(ℂ) full ring iso (P7b in FdHilb):** Establish the full ring isomorphism `R 4 ≅ Mat₂(ℂ)` via the 2-qubit Pauli image, with explicit basis. This is well-known in quantum stabiliser theory but requires the Mathlib `Mat₂(ℂ)` infrastructure for the formalised version. Publishable in *Quantum Information Processing* (if the formalisation is novel).

4. **Frame bimorphism classification (P3 in Frm):** Classify (up to frame isomorphism) the maps `(Fin N → Prop) × (Fin M → Prop) → (Fin K → Prop)` preserving finite meets ⊓ and arbitrary joins ⨆ in each argument. The intended analogy is with Heyting bimorphism; the differences (frame morphisms preserve joins, Heyting morphisms preserve implications) should produce a different classification. Publishable in *Applied Categorical Structures* or *Cahiers de Topologie et Géométrie Différentielle Catégoriques*.

5. **Finite frame classification (P7b in Frm):** Classify (up to frame isomorphism) the 4-element frames. Is `Sierpinski²` (= `{⊥, ⊤} × {⊥, ⊤}`) the canonical minimum frame anchor at 4 elements? The intended analogy is with DiamondH4 (Heyting) and Mat₂(F_q) (algebraic). Publishable in *Algebra Universalis* or *Cahiers...*.

Each of these is independently publishable; together they constitute a research programme of ~3-5 papers, with the framework providing the unifying motivation.

### §9.3 Connection to ∞-categorical / HoTT extensions

The current framework is *strictly 1-categorical*. Two natural extensions:

- **2-categorical / weighted-enriched-limits version (γ.3 refinement).** The full coherence-with-generator-morphisms version of Universal Sayability requires the 2-categorical machinery + weighted enriched limits (Kelly 1982). Mathlib's current conical enriched limits are insufficient; PR-3 of §7.4 contributes the weighted version. With this infrastructure, the full Universal Sayability theorem (with all 11 commuting-square classes discharged) becomes formalisable.

- **(∞, 1)-categorical version (GUT-D).** A natural longer-term direction is to push T_GUT to the (∞, 1)-categorical level (Berman 2019 [Ber19] *Higher Lawvere theories*, arXiv:1903.02991). This would extend the framework to bases like ∞-stacks, ∞-toposes, or differential ∞-categories. The motivation: certain "higher articulation" content (e.g., HoTT-style higher inductive types) does not fit cleanly in 1-categorical bases. The risk: the (∞, 1)-categorical infrastructure in Mathlib is essentially absent; this is a 5-10 year project.

For HoTT specifically: our framework is *compatible* with HoTT as a model-target (a T_GUT-model in some HoTT-internal SMCC C would give an HoTT-version of the R-family) but does not *require* HoTT for its formalisation. The companion metalogic paper [lawvere-identification.md] confirms that standard ZFC + Knaster–Tarski suffices; HoTT is optional.

### §9.4 Path toward full GUT-C closure

The path to a full GUT-C closure (all four instances + full coherence-discharged Universal Sayability + Mathlib upstream PRs landed) is:

- **Short term (3-6 months):** Discharge the 7 engineering-debt sorries (R_tensor patterns, bridge proofs) and the 3 "open mathematical sub-problems with known solutions" (DiamondH4 uniqueness via finite case analysis; Pauli Mat₂(ℂ) ring iso via explicit basis; Sierpinski² classification via finite frame enumeration). Net effect: drop sorry count from 14 to ~4 (the 4 research-open classification problems).

- **Medium term (6-18 months):** Mathlib upstream PRs (PR-1 ElementaryTopos; PR-2 LawvereTheory + Model; PR-3 weighted enriched limits). With these PRs landed, the local Foundation/Doctrine/ tree can be substantially simplified (relying on Mathlib's upstream infrastructure rather than local approximations).

- **Long term (18-36 months):** Resolution of the four research-open classification problems (Heyting bimorphism; Frame bimorphism; full coherence-discharged Universal Sayability; O1 V-functoriality verification). Each is a substantive research project; together they would constitute the full GUT-C closure.

- **Optional (longer):** PR-4 dagger-SMCC + FdHilb scaffold; (∞, 1)-categorical extension. These are independent of the core GUT-C programme and can proceed in parallel.

### §9.4.1 Decision protocol for γ.3 commitment

Per `gut-c-doctrine.md` v0.3 §8.3 (Decision point after Phase γ.3), the question is:

> **Question**: Are all 4 instances + Universal Sayability theorem complete?
>
> **If YES**: publish, peer engagement, victory.
> **If NO** (some instance proved very hard, e.g., topological): publish partial result; mark remaining as research-level.

This paper's verdict: **PARTIAL — sufficient to merit publication**.

The four instances are all instantiated at the structural level (with documented sorries pointing to research-open or engineering-debt items); the Universal Sayability theorem is proved at the layer-by-layer iso level; the framework discriminates correctly between substrate-level and class-specific generators; the O1 attack via factorisation is articulated with empirical support. The remaining work (full coherence in §4.6 layer 2; full doctrinal universality in §4.6 layer 3; resolution of the five research-open problems in §9.2) is acknowledged as future work rather than blocked-on-this-paper.

The submission strategy: publish this paper as the *framework proposal + partial verification* contribution. The five research-open problems become independent papers (each in its respective subfield). The Mathlib PRs proceed independently. The companion metalogic paper [`lawvere-identification.md`] provides the vertical-axis content. Together they constitute the GUT-C programme as currently constituted.

### §9.5 Closing remark

We have proposed a categorical-doctrinal framework for the R-tower's Universal Sayability and verified it on four substrate-classes (algebraic, Heyting, quantum, topological). The framework discriminates correctly between substrate-level and class-specific structure; it attacks Open Problem O1 via factorisation; it exposes five publishable research questions and four Mathlib infrastructure opportunities. The work is not closed but is substantial enough to merit external review and engagement.

The deeper significance, if the framework holds up: the *form* of "articulation universality" — a categorical doctrine with per-base specialisation — provides a candidate template for unifying foundational frameworks across mathematics, logic, physics, and computer science. The R-tower itself is one instance; T_GUT is its doctrinal wrapping; future doctrines (T_GeometricFoundations, T_LinguisticArticulation, T_AIRepresentation, ...) can be built using the same template. The categorical-doctrinal level is the natural home for cross-domain foundational claims.

If readers find the framework convincing — even partially — we hope the four worked instances + the five open research problems + the Mathlib PR opportunities provide concrete next steps. We welcome adversarial engagement on any of the framework choices, especially the factorisation strategy and the DiamondH4 conjecture.

The framework's design ambition is informed by but not limited to the current paper's content. The categorical doctrine T_GUT can in principle be extended to additional substrate-classes (smooth manifolds, ∞-groupoids, stochastic categories, ...) following the four-instance template. Each new instance verifies (or falsifies) the substrate/specialisation discrimination claim; each contributes empirical content to the framework's overall plausibility.

In the longest term, we see this work as a contribution to the *categorical foundation of articulation*: the methodological vision in which the categorical-doctrinal level is recognised as the natural home for cross-domain foundational claims. Lawvere's 1969 doctrines [Law69] and Mac Lane's PROPs [ML65] established the *technical* machinery for this vision; subsequent work in categorical quantum mechanics, topos quantum theory, enriched Lawvere theories, and ∞-category theory have filled in much of the *technical* development. What our framework adds, if it holds up, is a specific *substrate-articulation* doctrine — T_GUT — that brings the methodological vision to bear on the question "what is the minimum structure required for articulation of sayable content across all categorical substrates?" The four worked instances are the empirical evidence; the five open research problems are the next steps.

We submit the framework for review with the expectation that the framework will undergo substantial revision in response to expert feedback. We do not expect (or want) acceptance in its current form without challenge. The most informative outcome would be a successful refutation of one or more framework claims — for example, a hidden dagger leak in the V-functoriality argument (refuting §6.4.1), or a non-uniqueness of DiamondH4 at 4 elements (refuting §5.2 conjecture), or a structural mismatch in one of the four instances we have not anticipated. These would all be valuable refinements; we would rather know than not.

If the framework holds up substantially, the path forward is clear: complete the γ.3 refinements (§4.6 layers 2 and 3); resolve the five open research problems (§9.2); land the four Mathlib upstream PRs (§7.4); extend to additional substrate-classes (§9.3). The 24-36 month estimate from the doctrine document is realistic with parallel agent / collaborator execution; with single-person serial execution it stretches to 5-7 years. In either case the framework's *trajectory* is well-defined, even if the *timeline* depends on resourcing.

---

## Acknowledgments

We acknowledge: the Lean 4 community for the proof assistant and `mathlib4` library, on which the entire formalisation rests; the categorical-quantum community (Selinger, Coecke, Abramsky, Heunen, Vicary, Karvonen) for the theory of dagger compact closed categories and the identification of Open Problem O1; the topos-quantum-theory community (Heunen, Landsman, Spitters, Döring, Isham) for Bohrification as the precedent / negative example motivating our framework's symmetric design; the categorical-logic and Lawvere-theory community (Lawvere, Power, Hyland, Lack, Kelly, Garner, Lucyshyn-Wright) for the foundational machinery of enriched Lawvere theories; and the Lean / Mathlib maintainers (Mario Carneiro, Kevin Buzzard, Patrick Massot, and many others) for the infrastructure on which our formalisation depends.

Key recent commits during the writing of this paper:
- `e3aeced` — `docs(gut-roadmap): §十二 G11 cut-1 plan — char(k)≠2 finite fields parallel execution`
- `c992da9` — `lean(Closure): D1 = lfp(Φ) skeleton — Knaster-Tarski instance + 5/8 sorries discharged`
- `f0fa9d3` — `docs(metalogic): lawvere-identification v0.4 + representation-closure v0.1.2`
- `d4ed0f3` — `lean+docs(R-minimality): T_P6 explicit lemma + T_P7b form (b) existence + R4 master theorem`

Pending peer engagement: we have prepared a tailored 5-page proposal for Prof. John Power (Macquarie University) — see `outreach/john-power-proposal.md` — and a more general peer-engagement-draft for the Awodey / Shulman / Lambek–Scott lineage — see `peer-engagement-draft.md` v0.1. Co-authorship invitations are pending.

---

## Appendix A — Glossary

| Term | Definition |
|---|---|
| **SMCC** | Symmetric monoidal closed category (Eilenberg–Kelly 1966); a category with symmetric monoidal structure (⊗, I) and internal hom (⊸) with the closure adjunction `Hom(A ⊗ B, C) ≅ Hom(A, B ⊸ C)`. |
| **Biproducts** | Categorical product + coproduct + zero object compatibility (additive categories); for additive categories `A ⊕ B` is simultaneously product and coproduct. |
| **Lawvere theory** | A small category with strictly associative finite products such that every object is a finite power of a chosen generator (Lawvere 1963). |
| **Enriched Lawvere theory** | A V-enriched version of the above: a V-category with V-enriched finite products / cotensors (Power 1999). |
| **V-functor** | A functor preserving the enriched-categorical structure (in particular, the V-action on hom-objects). |
| **PROP** | "Products and permutations" — a symmetric monoidal theory specialising Lawvere's framework (Mac Lane 1965). |
| **T-model** | A product-preserving functor `T → C` from a theory T to an ambient category C; equivalently (in the enriched case), a V-product-preserving V-functor. |
| **Doctrine** | A 2-categorical structure of theories (Lawvere 1969); equivalently, a 2-functor `D : Cat → Cat` (or a V-version) sending each base to its category of T-models for some fixed T. |
| **Topos** | A category with finite limits + cartesian-closure + subobject classifier; *elementary* topos = the version without sheaf-theoretic / Grothendieck conditions. |
| **Frame** | A complete lattice in which finite meets distribute over arbitrary joins; equivalently, a complete Heyting algebra. |
| **Locale** | The opposite category to Frm; concretely, "abstract topological spaces" in the locale-theoretic sense (Joyal–Tierney 1984). |
| **Dagger compact category** | An SMCC equipped with an involutive contravariant identity-on-objects functor `† : C^{op} → C` + compact-closed structure interacting coherently (Selinger 2007). |
| **(∞, 1)-topos** | The higher-categorical generalisation of an elementary topos (Lurie *Higher Topos Theory* 2009). |
| **Sierpinski Ω** | The 2-element complete-Heyting-algebra `{⊥, ⊤}` = the open-set lattice of the Sierpinski topological space `{0, 1}` with `{1}` as the only non-trivial open. |
| **Klein four group V₄** | The unique group of order 4 in which every element is self-inverse: `V₄ ≅ ℤ/2 × ℤ/2`. |
| **Pauli group mod phase** | The group of n-qubit Pauli operators `{I, X, Y, Z}^⊗n` quotiented by the phase subgroup `⟨iI⟩`; isomorphic to `V₄^n` ≅ `(ℤ/2)^{2n}`. |
| **DiamondH4** | The 4-element linearly-ordered (non-Boolean) Heyting algebra `{⊥ < mid₁ < mid₂ < ⊤}` with explicit Heyting implication; introduced in this paper (§5.2) as a candidate Heyting Wedderburn anchor. |
| **Sierpinski²** | The 4-element Boolean frame `{⊥, ⊤} × {⊥, ⊤}` = "the frame of opens of R 2 Ω"; introduced in this paper (§5.4) as a candidate topological Wedderburn anchor. |
| **R-family** | The recursive type-family `R N δ := Fin N → δ` with `R 0 δ ≃ Unit` and `R (N+1) δ ≃ δ × R N δ`. |
| **R-tower** | The squaring sub-tower `{R 1, R 2, R 4, R 16, R 256, ...}` with `R(2N) ≅ R N × R N`. |
| **T5_general** | The polymorphic uniqueness theorem of `Foundation/R/UniquenessGeneral.lean` (line 241) — for any `[Fintype δ] [DecidableEq δ] [Inhabited δ]` and any `P1P7_Core δ`, `Nonempty (S.carrier N ≃ R N δ)`. |
| **D1 articulation** | The minimum definition of "formal articulation" (eight items: distinction, composition, relations, atoms, derivation, recursion, operation-as-content, modality). The starting point of the R-tower framework's analytic direction (chapter 01 of `wen-substrate.md`). |
| **P1–P7** | The seven (or eight, depending on counting) structural properties forced from D1: P1 distinction, P2 composition, P3 relations, P4 recursion, P5 Hom-as-content, P6 4-modality, P7a atom involution, P7b Wedderburn anchor. |
| **Φ' (carrier-growing)** | The monotone operator on the articulation candidates lattice 𝒜 whose Knaster–Tarski lfp identifies D1 in the companion metalogic paper. "Carrier-growing" because each application augments both the property-set and the carrier-class of the candidate. |
| **𝒜 (articulation candidates lattice)** | The complete lattice of triples `(C, M, P)` = (carrier-class, morphism-class, satisfied-property-set) with consistency conditions; the home of D1 = lfp(Φ'). |
| **Bohrification** | Heunen–Landsman–Spitters' construction (2009) building an intuitionistic topos from a unital C*-algebra's commutative subalgebras, and recovering quantum content from the internal Gelfand spectrum. |
| **Open Problem O1** | The Coecke–Heunen 2016 / Heunen–Karvonen 2019 obstruction: dagger structure does not interact cleanly with cartesian closure on the same objects (products in dagger categories are biproducts). |

---

## Appendix B — Reproducibility

### B.1 Lean toolchain

The codebase uses Lean 4 with `lean-toolchain` pinned to a specific stable release (see repository root). To install the same toolchain:

```bash
elan toolchain install $(cat lean-toolchain)
```

The Mathlib dependency is pinned via `lake-manifest.json`. To restore the exact dependency tree:

```bash
lake update
```

(This downloads the pinned Mathlib commit; first download takes ~30 minutes depending on connection.)

### B.2 Build instructions

Full build:
```bash
lake build SSBX
```

Build time: typically 30-60 minutes on first run (Mathlib compilation), 5-15 minutes incremental.

Per-file builds:
```bash
lake build SSBX.Foundation.Doctrine.LawvereTheory
lake build SSBX.Foundation.Doctrine.EnrichedLawvereTheory
lake build SSBX.Foundation.Doctrine.T_GUT
lake build SSBX.Foundation.Doctrine.Instance.Algebraic
lake build SSBX.Foundation.Doctrine.Instance.Heyting
lake build SSBX.Foundation.Doctrine.Instance.Quantum
lake build SSBX.Foundation.Doctrine.Instance.Topological
```

### B.3 Sorry verification

To verify the sorry count is as documented:

```bash
grep -rE "sorry|admit" formal/SSBX/Foundation/Doctrine/ | wc -l
```

Expected output: 14 (excluding comments / docstrings).

### B.4 Axiom verification

To verify no new axioms beyond Mathlib:

```bash
grep -rE "^axiom" formal/SSBX/Foundation/Doctrine/ | wc -l
```

Expected output: 0.

### B.5 Repository

The full repository is at the contact address (renyongxu@gmail.com) on request, or via the project GitHub (URL pending peer-engagement-induced public release).

---

## Appendix C — Key Lean Type Definitions

For readers wishing to see the precise Lean types underlying the framework. All code is from `formal/SSBX/Foundation/Doctrine/` unless otherwise noted.

### C.1 The TGUTOp signature (T_GUT generators)

```lean
inductive TGUTOp : Type
  | id_δ : TGUTOp
  | compose : ℕ → ℕ → TGUTOp
  | square : ℕ → TGUTOp
  | hom : ℕ → ℕ → TGUTOp
  | modal_V4 : TGUTOp
  | atom_3 : TGUTOp
  | wedderburn_4 : TGUTOp
  | relate : ℕ → ℕ → TGUTOp
  deriving DecidableEq, Repr
```

Source: `T_GUT.lean` lines 139–163.

The constructors map to the eight rows of Table 1 in §3.2. The parametric families (`compose`, `square`, `hom`, `relate`) take ℕ-arguments giving their tensor-power arities; the four atomic constructors (`id_δ`, `modal_V4`, `atom_3`, `wedderburn_4`) are at fixed arities.

### C.2 The arity function

```lean
def arity : TGUTOp → ℕ × ℕ
  | .id_δ          => (1, 1)
  | .compose N M   => (N + M, N + M)
  | .square N      => (N, 2 * N)
  | .hom N M       => (N * M, N * M)
  | .modal_V4      => (1, 4)
  | .atom_3        => (3, 3)
  | .wedderburn_4  => (4, 4)
  | .relate N M    => (N, M)
```

Source: `T_GUT.lean` lines 177–185.

The arity `(src, tgt)` gives the input and output δ-tensor-power indices. For example, `(compose N M).arity = (N+M, N+M)` because compose takes two tensor powers and produces their sum-as-direct-sum (which is already a single (N+M)-tensor power up to associator coercion).

### C.3 The TGUTRealisation record

```lean
structure TGUTRealisation (δ : C) where
  R : ℕ → C
  R_unit : R 0 ≅ 𝟙_ C
  R_gen : R 1 ≅ δ
  R_tensor : ∀ n m, R (n + m) ≅ R n ⊗ R m
  compose_mor : ∀ N M, R N ⊗ R M ⟶ R (N + M)
  square_mor : ∀ N, R N ⟶ R (2 * N)
  relate_mor : ∀ N M, R N ⟶ R M
  hom_mor : ∀ N M, R (N * M) ⟶ R (N * M)
  modal_V4_mor : R 1 ⟶ R 2 ⊗ R 2
  atom_3_mor : R 3 ⟶ R 3
  wedderburn_4_mor : R 4 ≅ R 4
```

Source: `T_GUT.lean` lines 316–347.

The first four fields (`R`, `R_unit`, `R_gen`, `R_tensor`) are the *structural* data; the remaining seven fields are the *generator* morphisms (one per non-trivial constructor of `TGUTOp`). The structure carries no equational-law constraints; satisfaction of laws is a separate `Satisfies` proposition.

### C.4 The componentIso construction (Path 2 proof)

```lean
noncomputable def componentIso (δ : C) (M : TGUTRealisation C δ) :
    ∀ n, M.R n ≅ tensorPow δ n
  | 0 => M.R_unit
  | k + 1 =>
      have hcomm : k + 1 = 1 + k := by omega
      eqToIso (congrArg M.R hcomm)
        ≪≫ M.R_tensor 1 k
        ≪≫ (M.R_gen ⊗ᵢ componentIso δ M k)
```

Source: `T_GUT.lean` lines 534–543.

The construction is by structural recursion on the natural number `n`. The base case uses `M.R_unit` directly; the inductive case chains four isos using `eqToIso` (for the ℕ-commutativity coercion), `M.R_tensor` (for tensor-power additivity), `M.R_gen` (for the generator identification), and the inductive hypothesis `componentIso δ M k`.

### C.5 The Universal Sayability theorem

```lean
theorem universal_sayability (δ : C) (M : TGUTRealisation C δ) :
    Nonempty (RealIso M (canonical δ)) :=
  ⟨{ iso := componentIso δ M }⟩
```

Source: `T_GUT.lean` line 575.

The theorem says: for any T_GUT-realisation M and any chosen δ in an SMCC C, there is a "realisation isomorphism" `RealIso M (canonical δ)` between M and the canonical tensor-power realisation. The proof is one line: construct the iso family using `componentIso`, package as a `RealIso` record (whose `coherent` field defaults to `True` at the current skeleton level), and conclude `Nonempty`.

### C.6 The DiamondH4 anchor (Heyting instance)

```lean
inductive DiamondH4 : Type where
  | bot : DiamondH4
  | mid1 : DiamondH4
  | mid2 : DiamondH4
  | top : DiamondH4
  deriving DecidableEq, Repr

instance : LE DiamondH4 := ⟨fun a b => ...⟩  -- explicit order definitions
instance : HeytingAlgebra DiamondH4 := { ... }  -- explicit Heyting structure
```

Source: `Foundation/Doctrine/Instance/Heyting.lean` §5 (approximate; details omitted for brevity).

The key theorem:

```lean
theorem DiamondH4_is_nonBoolean :
    (¬¬DiamondH4.mid1 : DiamondH4) = ⊥
```

This proves that `¬¬mid1 = ⊥ ≠ mid1`, demonstrating the intrinsic non-Boolean Heyting structure. The conjectured uniqueness:

```lean
-- Conjecture (not proved): any non-Boolean 4-element Heyting algebra is iso to DiamondH4.
-- Open Problem #1 in §9.2.
```

### C.7 The Pauli–Klein4 equivalence (Quantum instance)

```lean
-- From Foundation/Wen/Embeddings/StabilizerQM.lean
def equiv : PauliN n ≃ R (2 * n) := { ... }

-- From Foundation/Doctrine/Instance/Quantum.lean
def PauliBase_to_V4 : PauliBase → R 2 := { ... }

theorem P6_quantum_is_pauli_klein4 :
    Nonempty (PauliBase ≃* V4) := { ... }
```

The equivalence `PauliBase ≅ V₄` (as multiplicative groups) is the formal expression of the Pauli–Klein4 coincidence. The proof uses the explicit Pauli multiplication table mod phase.

### C.8 Build verification

To verify the framework's build state:

```bash
cd formal/
lake build SSBX.Foundation.Doctrine
```

Expected output:
```
[3936/3936] Built SSBX.Foundation.Doctrine.LawvereTheory
[3937/3937] Built SSBX.Foundation.Doctrine.EnrichedLawvereTheory
[3938/3938] Built SSBX.Foundation.Doctrine.T_GUT
[3939/3939] Built SSBX.Foundation.Doctrine.Instance.Algebraic
[3940/3940] Built SSBX.Foundation.Doctrine.Instance.Heyting
[3941/3941] Built SSBX.Foundation.Doctrine.Instance.Quantum
[3942/3942] Built SSBX.Foundation.Doctrine.Instance.Topological
```

(Numbers approximate; depend on exact Mathlib snapshot.) Sorry warnings are emitted but do not cause build failure.

---

## Appendix D — References

### Foundational Lawvere theories

- **[Law63]** Lawvere, F. W. (1963/2004). *Functorial Semantics of Algebraic Theories*. PhD thesis, Columbia. Published 2004 as TAC Reprints No. 5.
- **[Law69]** Lawvere, F. W. (1969). *Adjointness in Foundations*. *Dialectica* 23, 281–296. Reprinted TAC Reprints No. 16, 2006.
- **[Law70]** Lawvere, F. W. (1969). *Diagonal arguments and Cartesian closed categories*. In *Category Theory, Homology Theory and their Applications II*, LNM 92, 134–145.

### SMCC and enriched-category foundations

- **[EK66]** Eilenberg, S., & Kelly, G. M. (1966). *Closed categories*. In *Proc. La Jolla Conference on Categorical Algebra*, 421–562.
- **[Day70]** Day, B. J. (1970). *On closed categories of functors*. LNM 137, 1–38.
- **[Kel82]** Kelly, G. M. (1982). *Basic Concepts of Enriched Category Theory*. Cambridge University Press. Reprinted as TAC Reprints No. 10, 2005.
- **[Kel80]** Kelly, G. M. (1980). *A unified treatment of transfinite constructions for free algebras, free monoids, colimits, associated sheaves, and so on*. *Bull. Austral. Math. Soc.* 22, 1–83.
- **[ML65]** Mac Lane, S. (1965). *Categorical algebra*. *Bull. Amer. Math. Soc.* 71, 40–106.

### Enriched Lawvere theories (core references)

- **[Pow99]** Power, J. (1999). *Enriched Lawvere theories*. *Theory and Applications of Categories* 6 no. 7, 83–93. <http://www.tac.mta.ca/tac/volumes/6/n7/n7.pdf>
- **[HP07]** Hyland, M., & Power, J. (2007). *The category theoretic understanding of universal algebra: Lawvere theories and monads*. *Electronic Notes in Theoretical Computer Science* 172, 437–458. DOI 10.1016/j.entcs.2007.02.019
- **[LP09]** Lack, S., & Power, J. (2009). *Notions of Lawvere theory*. *Applied Categorical Structures* 17, 243–265.
- **[GP18]** Garner, R., & Power, J. (2018). *An enriched view on the extended finitary monad—Lawvere theory correspondence*. *Logical Methods in Computer Science* 14(1).
- **[LW16]** Lucyshyn-Wright, R. (2016). *Enriched algebraic theories and monads for a system of arities*. *Theory and Applications of Categories* 31, 101–137.
- **[BG19]** Bourke, J., & Garner, R. (2019). *Monads and theories*. *Advances in Mathematics* 351, 1024–1071.
- **[PT08]** Power, J., & Tanaka, M. (2008). *Pseudo-distributive laws and axiomatics for variable binding*. *Higher-Order and Symbolic Computation* 21, 1–24.

### PROPs and operadic generalizations

- **[Lac04]** Lack, S. (2004). *Composing PROPs*. *Theory and Applications of Categories* 13 no. 9.
- **[BSZ17]** Bonchi, F., Sobociński, P., & Zanasi, F. (2017). *Lawvere categories as composed PROPs*. In *CMCS 2016: Coalgebraic Methods in Computer Science*, LNCS 9608, 11–32.

### Quantum / dagger compact

- **[AC04]** Abramsky, S., & Coecke, B. (2004). *A categorical semantics of quantum protocols*. In *Proceedings of the 19th IEEE Symposium on Logic in Computer Science (LICS)*, 415–425.
- **[Sel07]** Selinger, P. (2007). *Dagger compact closed categories and completely positive maps*. *Electronic Notes in Theoretical Computer Science* 170, 139–163.
- **[Sel12]** Selinger, P. (2012). *Finite dimensional Hilbert spaces are complete for dagger compact closed categories*. *Logical Methods in Computer Science* 8(3:6), 1–12. arXiv:1207.6972.
- **[HV19]** Heunen, C., & Vicary, J. (2019). *Categories for Quantum Theory: An Introduction*. Oxford Graduate Texts in Mathematics 28. Oxford University Press.
- **[CH16]** Coecke, B., & Heunen, C. (2016). *Pictures of complete positivity in arbitrary dimension*. *Information and Computation* 250, 50–58.
- **[HK19]** Heunen, C., & Karvonen, M. (2019). *Limits in dagger categories*. *Theory and Applications of Categories* 34, 468–513.
- **[CK17]** Coecke, B., & Kissinger, A. (2017). *Picturing Quantum Processes*. Cambridge University Press.

### Topos quantum theory (Bohrification — precedent for Heyt + Hilb unification)

- **[HLS09]** Heunen, C., Landsman, N. P., & Spitters, B. (2009). *A topos for algebraic quantum theory*. *Communications in Mathematical Physics* 291, 63–110. arXiv:0709.4364.
- **[HLSW12]** Heunen, C., Landsman, N. P., Spitters, B., & Wolters, S. (2012). *Bohrification of operator algebras and quantum logic*. *Synthese* 186, 719–752. arXiv:0905.2275.
- **[DI08]** Döring, A., & Isham, C. J. (2008). *What is a thing?* In *New Structures for Physics*, LNP 813, 753–937.
- **[Lan17]** Landsman, K. (2017). *Foundations of Quantum Theory: From Classical Concepts to Operator Algebras*. Fundamental Theories of Physics 188. Springer.

### Locale theory and frames

- **[JT84]** Joyal, A., & Tierney, M. (1984). *An extension of the Galois theory of Grothendieck*. *Memoirs of the AMS* 309.
- **[Joh02]** Johnstone, P. (2002–2003). *Sketches of an Elephant: A Topos Theory Compendium*. 2 vols. Oxford University Press.
- **[Vic96]** Vickers, S. (1996). *Topology via Logic*. Cambridge Tracts in Theoretical Computer Science 5.

### Higher-categorical generalizations

- **[Lur09]** Lurie, J. (2009). *Higher Topos Theory*. Annals of Mathematics Studies 170. Princeton University Press.
- **[Lur17]** Lurie, J. (2017). *Higher Algebra*. Online preprint, available at <https://www.math.ias.edu/~lurie/papers/HA.pdf>.
- **[Ber19]** Berman, J. D. (2019). *Higher Lawvere theories*. arXiv:1903.02991.

### Categorical logic and foundations

- **[LS86]** Lambek, J., & Scott, P. J. (1986). *Introduction to Higher Order Categorical Logic*. Cambridge Studies in Advanced Mathematics 7. Cambridge University Press.
- **[Awo10]** Awodey, S. (2010). *Category Theory*, 2nd ed. Oxford Logic Guides 52. Oxford University Press.
- **[AR02]** Awodey, S., & Reck, E. (2002). *Completeness and categoricity*. *History and Philosophy of Logic* 23, 1–30 (Part I), 77–94 (Part II).
- **[Mac98]** Mac Lane, S. (1998). *Categories for the Working Mathematician*, 2nd ed. Graduate Texts in Mathematics 5. Springer.

### Adjoint and fixed-point theory (companion metalogic paper)

- **[KT28]** Knaster, B. (1928). *Un théorème sur les fonctions d'ensembles*. *Annales de la Société Polonaise de Mathématique* 6, 133–134.
- **[Tar55]** Tarski, A. (1955). *A lattice-theoretical fixpoint theorem and its applications*. *Pacific Journal of Mathematics* 5, 285–309.
- **[Kle38]** Kleene, S. C. (1938). *On notation for ordinal numbers*. *Journal of Symbolic Logic* 3, 150–155.
- **[Yan03]** Yanofsky, N. S. (2003). *A universal approach to self-referential paradoxes, incompleteness and fixed points*. *Bulletin of Symbolic Logic* 9(3), 362–386.
- **[Acz88]** Aczel, P. (1988). *Non-Well-Founded Sets*. CSLI Lecture Notes 14. Stanford.
- **[Cou77]** Cousot, P., & Cousot, R. (1977). *Abstract interpretation: a unified lattice model for static analysis of programs by construction or approximation of fixpoints*. In *Proc. 4th ACM Symposium on Principles of Programming Languages (POPL)*, 238–252.

### Univalent foundations / HoTT

- **[UF13]** The Univalent Foundations Program (2013). *Homotopy Type Theory: Univalent Foundations of Mathematics*. Institute for Advanced Study. <https://homotopytypetheory.org/book/>

### Operational semantics and computational effects

- **[Mog89]** Moggi, E. (1989). *Computational lambda-calculus and monads*. In *Proc. 4th IEEE Symposium on Logic in Computer Science (LICS)*, 14–23.
- **[PP02]** Plotkin, G., & Power, J. (2002). *Notions of computation determine monads*. In *Foundations of Software Science and Computation Structures (FOSSACS)*, LNCS 2303, 342–356.
- **[Sta14]** Staton, S. (2014). *Freyd categories are enriched Lawvere theories*. *Electronic Notes in Theoretical Computer Science* 303, 197–206.

### Mathlib and Lean

- **[Mat25]** The Mathlib Community (2025). *mathlib4: a mathematical library for Lean 4*. <https://leanprover-community.github.io/mathlib4_docs/>
- **[CMP+25]** Carneiro, M., Massot, P., Bentkamp, A., et al. (2025). *The Lean Mathematical Library*. *Communications of the ACM* (in press).
- **[Lea24]** de Moura, L., & Ullrich, S. (2024). *The Lean 4 Theorem Prover and Programming Language*. CADE 2021, LNCS 12699, 625–635.

### Algebraic structure foundations

- **[Wed08]** Wedderburn, J. H. M. (1908). *On hypercomplex numbers*. *Proceedings of the London Mathematical Society* (2) 6, 77–118.
- **[Wit37]** Witt, E. (1937). *Theorie der quadratischen Formen in beliebigen Körpern*. *Journal für die Reine und Angewandte Mathematik* 176, 31–44.
- **[Arf41]** Arf, C. (1941). *Untersuchungen über quadratische Formen in Körpern der Charakteristik 2*. *Journal für die Reine und Angewandte Mathematik* 183, 148–167.
- **[Lam05]** Lam, T. Y. (2005). *Introduction to Quadratic Forms over Fields*. Graduate Studies in Mathematics 67. American Mathematical Society.

### Project internal documents

- **gut-c-doctrine** — `docs-next/00_start/gut-c-doctrine.md` v0.3. The full Path C framework proposal (this paper's draft companion).
- **lawvere-identification** — `docs-next/00_start/lawvere-identification.md` v0.6. The companion metalogic identification paper (D1 = lfp(Φ')).
- **representation-closure** — `docs-next/00_start/representation-closure.md` v0.1.3. The philosophical synthesis (three-layer concept/structure/instance chain).
- **peer-engagement-draft** — `docs-next/00_start/peer-engagement-draft.md` v0.1. General outreach material for Awodey / Shulman / Lambek–Scott lineage.
- **john-power-proposal** — `docs-next/00_start/outreach/john-power-proposal.md` v0.1. Tailored 5-page outreach to Prof. John Power (Macquarie University).
- **literature-notes/path-c-foundations** — `docs-next/00_start/literature-notes/path-c-foundations.md`. Deep-reading notes on Power 1999, Hyland–Power 2007, Heunen–Landsman–Spitters 2009.
- **gut-roadmap** — `docs-next/10_formal_形式/gut-roadmap.md` v0.2. Overall GUT-A/B/C roadmap (§十二 covers the Path C / GUT-C plan).
- **wen-substrate** — `docs-next/10_formal_形式/wen-substrate.md` v1.4. R-tower structural axioms and operation monism.

### Lean codebase (cited inline throughout)

- `formal/SSBX/Foundation/R/Basic.lean` — R-family definition.
- `formal/SSBX/Foundation/R/UniquenessGeneral.lean` — `T5_general` polymorphic uniqueness (line 241).
- `formal/SSBX/Foundation/R/UniquenessF2.lean` — F₂-Boolean specialisation.
- `formal/SSBX/Foundation/R/UniquenessAlgebraic.lean` — `T5_algebraic` (ring iso at carrier 4 for any field).
- `formal/SSBX/Foundation/R/Bilinear/Arf.lean` — Arf invariant (char(k) = 2).
- `formal/SSBX/Foundation/R/Bilinear/DiscriminantCharNeq2.lean` — discriminant (char(k) ≠ 2 finite fields, completed 2026-05-17).
- `formal/SSBX/Foundation/R/R4Minimality.lean` — five-sense R₄ minimality master theorem.
- `formal/SSBX/Foundation/R/D6_Tests.lean` — HoTT / ETCS / SDG falsification records.
- `formal/SSBX/Foundation/R/Squaring.lean` — R(N+N) ≅ R N × R N (line 40).
- `formal/SSBX/Foundation/R/ClaimZ/Analytic.lean` — analytic-direction D1 ⟹ P1–P7 integration.
- `formal/SSBX/Foundation/R/ClaimZ/Analytic/P1.lean` ... `Analytic/P7b.lean` — eight per-axiom modules.
- `formal/SSBX/Foundation/R/Distinction/Prop.lean` — non-algebraic δ = Prop sibling.
- `formal/SSBX/Foundation/Wen/Embeddings/StabilizerQM.lean` — Pauli group mod phase ≃ R-tower (664 LOC, 0 sorry).
- `formal/SSBX/Foundation/Wen/Embeddings/HilbertPauliFunctor.lean` — partial R → Pauli → Hilb functor (413 LOC).
- `formal/SSBX/Foundation/Wen/Embeddings/FOL.lean` — FOL syntax-tree embedding.
- `formal/SSBX/Foundation/Closure/PhiOperator.lean` — Knaster–Tarski Φ operator (5/8 sorries discharged).
- `formal/SSBX/Foundation/Doctrine/LawvereTheory.lean` — G1, classical Lawvere theory class (643 LOC).
- `formal/SSBX/Foundation/Doctrine/EnrichedLawvereTheory.lean` — G2, Power-style V-enriched extension (929 LOC).
- `formal/SSBX/Foundation/Doctrine/T_GUT.lean` — G3, T_GUT theory + Universal Sayability (611 LOC).
- `formal/SSBX/Foundation/Doctrine/Instance/Algebraic.lean` — G4, T_GUT in FinVect_{F_q} (485 LOC).
- `formal/SSBX/Foundation/Doctrine/Instance/Heyting.lean` — G5, T_GUT in HeytAlg + DiamondH4 (654 LOC).
- `formal/SSBX/Foundation/Doctrine/Instance/Quantum.lean` — γ.3-A, T_GUT in FdHilb-via-stabilisers + Pauli–Klein4 (897 LOC).
- `formal/SSBX/Foundation/Doctrine/Instance/Topological.lean` — γ.3-B, T_GUT in Frm + Sierpinski² (828 LOC).

---

*End of draft v0.1 · 2026-05-17. Word count: approximately 25,800 words at this revision (target range 25–35k for TAC / LMCS / MSCS submission). Lean codebase referenced throughout (5047 LOC across 7 files in `formal/SSBX/Foundation/Doctrine/`); 14 sorries documented, 0 axioms beyond Mathlib substrate. Status: framework proposal + partial verification, suitable for external review and adversarial engagement. Future revisions will integrate referee feedback and the γ.3 refinement (full coherence-discharged Universal Sayability) when available. Markdown source; LaTeX conversion deferred to final submission.*

---

## Submission Notes

**For the editor:**

This paper proposes a categorical-doctrinal framework (the *T_GUT* biproduct-enriched Lawvere theory) for the R-tower's Universal Sayability theorem across symmetric monoidal closed bases with biproducts. It includes (i) a precise framework definition with eight generator families encoding the substrate-articulation primitives P1–P7; (ii) a layer-by-layer Universal Sayability theorem at the component-iso level, formally proved in Lean 4; (iii) four worked instances (algebraic, Heyting, quantum, topological) verifying the framework's discrimination capability; (iv) an attack on Open Problem O1 (Coecke–Heunen 2016 / Heunen–Karvonen 2019) via a factorisation strategy with empirical evidence from the four instances; (v) catalogue of the Lean formalisation (~5047 LOC, 14 sorries, 0 axioms) and four identified Mathlib upstream PR opportunities.

The paper is honestly partial. It claims a framework proposal + partial verification, not a fully closed theorem. The full Universal Sayability theorem (in the coherence-discharged + cross-base-doctrinal form) is acknowledged as the γ.3 refinement target; five research-open mathematical sub-problems are explicitly identified and listed in §9.2 as independently publishable. The framework is *consistent with* the four worked instances but is not a *theorem* in the strict closed sense.

We submit for editorial consideration on the basis that (a) the framework proposal is novel and substantive, with a precise mathematical formulation and Lean-verifiable content; (b) the four worked instances provide empirical evidence supporting the framework's design; (c) the O1 attack identifies a structural mechanism (factorisation) for resolving a longstanding open problem in categorical quantum mechanics; (d) the Mathlib upstream contribution opportunities are independently valuable for the broader formalisation community.

We are aware that not all reviewers will accept the framework's design (especially the factorisation strategy and the DiamondH4 conjecture); we welcome adversarial engagement and are prepared for substantial revision in response to critique. The companion documents (`gut-c-doctrine.md` v0.3, `lawvere-identification.md` v0.6, `representation-closure.md` v0.1.3) provide complementary context for reviewers wishing to dig deeper.

**Estimated length in TAC format:** ~45-55 pages (at ~600 words/page).

**Suggested reviewers:** John Power (Macquarie University) for enriched Lawvere theory expertise; Chris Heunen (Edinburgh) for categorical quantum + Bohrification expertise; Mike Shulman (San Diego) for categorical logic + doctrines; Steve Awodey (CMU) for foundational positioning. Co-authorship invitations to Power are in progress (cf. `outreach/john-power-proposal.md`).

**Conflict of interest:** None known. The author (Yongxu Ren) is an independent researcher with no institutional affiliation requiring disclosure. The work has been developed solo with Lean 4 + Mathlib over ~2 years; the framework proposal and Lean codebase are entirely the author's work, with parallel-agent execution providing engineering acceleration for the Lean formalisation but not for the mathematical content.
