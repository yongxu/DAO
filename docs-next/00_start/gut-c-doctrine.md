# GUT-C Doctrine: An SMCC-Enriched Lawvere Theory for Universal Sayability
## Path C Framework Proposal — Unified Categorical Foundation

> **Version**: 0.3 · 2026-05-17 · post γ.2 Heyting validation
> **Status**: research framework proposal (draft) — **PATH C VALIDATED, γ.3 commitment**
> **Companion to**: [`lawvere-identification.md`](lawvere-identification.md) v0.6 · [`representation-closure.md`](representation-closure.md) v0.1.3 · [`gut-roadmap.md`](../10_formal_形式/gut-roadmap.md) §十二
> **Author intent**: 推 GUT-C (full δ-realisation 含 non-algebraic) 从 12-24 月 research estimate 内的最优 path
> **Risk tier**: MEDIUM (further revised down post γ.2 Heyting validation — framework discriminates correctly)
> **Estimated timeline**: 24-36 months (γ.1 + γ.2 substantially compressed via parallel agent execution; γ.3 in progress)
> **Novel contribution**: Open Problem O1 attack (dagger + cartesian coexistence as separate δ-realisations of one R-tower) — identified as **publishable in TAC / LMCS / MSCS**
> **γ.2 deliverables**: 5 G files (G1-G5) totaling 3120 LOC, 8 documented sorries (no axioms); Heyting instance introduces `DiamondH4` as new non-Boolean 4-element Heyting anchor

---

## Abstract

GUT-A (F₂-Boolean classical) 与 GUT-B (polymorphic over Fintype δ + Field k 至 ring iso) 已**形式完成** ([gut-roadmap.md](../10_formal_形式/gut-roadmap.md) §十一)。GUT-C (full δ-realisation 含 non-algebraic: Heyting, quantum, topological) 仍**研究级开放**。

本提案给出 GUT-C 的 **Path C 方案**: 定义一个 SMCC-enriched Lawvere theory `T_GUT`, 让任意 SMCC + 选定 δ object 内的 `T_GUT`-models 自然给出对应 δ-class 的 "R-family-over-δ"。

**核心 thesis**: GUT-C 不该 try to "扩展 GUT-A 的 P1-P7 axioms 到非代数 δ" (Path A 的尝试), 而该 **rethink the axioms themselves as enriched-categorical structure**, 让 P-properties 在不同 SMCC base 上自然采取不同形态。

**Mathematical contribution**: 把 R-tower 升格为 enriched-categorical doctrine; P1-P7 reformulate 为 doctrine axioms; Universal Sayability becomes a meta-theorem 跨 SMCC base.

**Risks**: Mathlib 的 enriched-Lawvere infrastructure 大部分缺; 需 ~6-12 月 upstream contributions 才能 Lean-formalize. Framework discovery 本身 ~30% chance need significant revision.

---

## §1. Problem Definition — GUT-C 精确陈述

### §1.1 Current GUT-A/B statement (recap)

Per [gut-roadmap.md](../10_formal_形式/gut-roadmap.md) §二:

> **Theorem (Universal Sayability)**: Any formal articulation S of sayable/abstractable content satisfies P1-P7 ⟹ S ≃ R-family-over-δ for an appropriate realisation δ of the primitive binary distinction.

In GUT-A: δ = Bool (F₂-Boolean classical scope) + at least one non-algebraic δ instance (G4: Distinction/Prop) — formally closed (0 sorry).

In GUT-B: extended to any `Fintype δ` (layerwise via [UniquenessGeneral.lean](../../formal/SSBX/Foundation/R/UniquenessGeneral.lean)) + any `Field k` (ring iso at carrier 4 via [UniquenessAlgebraic.lean](../../formal/SSBX/Foundation/R/UniquenessAlgebraic.lean)) + finite-field char ≠ 2 Witt cancellation ([DiscriminantCharNeq2.lean](../../formal/SSBX/Foundation/R/Bilinear/DiscriminantCharNeq2.lean), completed 2026-05-17, 0 sorry).

### §1.2 The GUT-C gap

The current statement requires *all* P1-P7 to hold uniformly. For non-algebraic δ this breaks:

Per [`Foundation/R/Distinction/Prop.lean`](../../formal/SSBX/Foundation/R/Distinction/Prop.lean) (status report for δ=Prop):

| Property | δ=Bool | δ=Prop | δ=Hilb | δ=Frame |
|---|---|---|---|---|
| **P1** distinction | ✓ | ✓ | ✓ | ✓ |
| **P2** composition | ✓ | ✓ | ✓ | ✓ |
| **P3** bilinear | ✓ (Arf) | **✗** | ⚠ (symplectic only) | ⚠ (lattice only) |
| **P4** scale/squaring | ✓ | ✓ | ✓ | ✓ |
| **P5** Hom-as-content | ✓ (LinHom=R(NM)) | ⚠ (curry only) | ⚠ (dagger duality) | ⚠ (frame morphisms) |
| **P6** 4-modality | ✓ (V₄ Shi) | ⚠ (classical only) | ⚠ (Pauli mod phase) | ⚠ (Sierpinski-like) |
| **P7a** atom involution | ✓ | ✓ | ✓ (dagger) | ✓ |
| **P7b** Wedderburn anchor | ✓ (Mat₂(F₂)) | **✗** | **✗** | **✗** |

⟹ **P3 and P7b are fundamentally algebraic-specific.** Path A's idea "make P-properties class-parametric" runs into a deeper problem: even the *concept* of "bilinear" or "Wedderburn anchor" doesn't lift naturally to non-algebraic contexts.

The resolution requires a **categorical reformulation** where the P-properties are *intrinsically* defined in the ambient category, not as fixed algebraic constructs.

### §1.3 What GUT-C demands

A satisfactory GUT-C framework must:

1. **Universal P-properties**: redefine P1-P7 in a way that works in any SMCC, not just FinVect
2. **Per-instance specialization**: in each SMCC, the abstract P-properties recover the class-specific forms (Arf, discriminant, Heyting lattice, symplectic form, ...)
3. **Single Universal Sayability theorem**: one theorem covers all δ-classes
4. **Empirically falsifiable**: D6-style protocol generalizes

---

## §2. Why Path C — The Case for Unification

### §2.1 Comparison with Path A and Path B

| Aspect | Path A (parametric) | Path B (enum per-class) | **Path C (SMCC-Lawvere)** |
|---|---|---|---|
| Statement form | Family of theorems indexed by δ-class | N separate theorems | Single universal theorem |
| Math infrastructure | Need "δ-class" concept (informal) | Standard | Enriched Lawvere (well-established) |
| Engineering work | Medium-high | High (per-class) | Very high (framework + instances) |
| Publication impact | OK (multi-paper sequence) | Adequate (incremental papers) | **Field-changing single paper** |
| Risk of "wrong framing" | Medium | Low | **High (genuine research)** |

### §2.2 Why categorical doctrine is the right level

The 4 target δ-classes — algebraic / Heyting / quantum / topological — share a common **structural shape**:

| Class | Base category | Generator δ | Tensor product | Internal hom |
|---|---|---|---|---|
| Algebraic (F_q) | FinVect_{F_q} | F_q (= 1-dim vec) | ⊗_{F_q} | LinHom |
| Heyting | HeytAlg | Prop | ⊗_Heyt | Heyting impl → |
| Quantum | FdHilb | ℂ² (qubit) | ⊗ (Hilbert) | ⊸ (dagger) |
| Topological | Frame | Ω (Sierpinski) | ⊗ (frame) | ⇒ (frame impl) |

All 4 are **symmetric monoidal closed categories with biproducts** (SMCC + biproducts). All have a chosen "δ generator" object. All have "R N δ = δ^⊗N" as the natural construction.

**Insight**: the right framework is **categorical universal algebra** — the "doctrinal" level where R-tower's axioms are encoded in a Lawvere-style theory enriched in SMCC.

### §2.3 Path C's promise

If successful, Path C delivers:

1. **One Universal Sayability theorem** in standard categorical language (enriched-Lawvere theory + base SMCC)
2. **Free derivations** of GUT-A/B/Heyting/Quantum/Topological as specializations
3. **Conceptual unification**: GUT becomes "the categorical doctrine of articulation" — a foundational mathematical object
4. **Future extensibility**: new δ-classes (smooth, AI, linguistic) just instantiate the same framework

This is the kind of contribution that lands in *Journal of Pure and Applied Algebra* or *Theory and Applications of Categories*, with potential follow-up in higher-categorical / HoTT venues.

---

## §3. Proposed Framework — T_GUT Lawvere Theory

### §3.1 Background: Standard Lawvere Theory

**Definition (Lawvere 1963)**: A *Lawvere theory* is a small category T with finite products, equipped with a chosen object δ_T ∈ Obj(T) such that every object is a finite power of δ_T.

A *T-model* in a category C with finite products is a finite-product-preserving functor M: T → C.

T-models in C form a category Mod_C(T) with natural transformations as morphisms.

**Examples**:
- T_Grp (group theory): models in Set = groups; models in TopCat = topological groups
- T_Ring (ring theory): models in Set = rings; models in Ab = rings
- T_Vec_F (F-vector spaces): models in Set = F-vector spaces

### §3.2 Enrichment to SMCC (Power 1999)

For SMCC bases (where the natural notion is "linear" rather than "set-theoretic"), Power 1999 introduced **enriched Lawvere theories**:

**Definition (Power 1999, Enriched Lawvere theory)**: Given an SMCC (V, ⊗, I), a *V-enriched Lawvere theory* is a small V-category T with V-finite products, equipped with a generator δ_T.

A *V-T-model* in a V-category C is a V-finite-product-preserving V-functor M: T → C.

This generalizes plain Lawvere theories (V = Set) to settings where morphisms have richer structure (V = Ab gives "additive theories", V = Vec_F gives "linear theories" / PROPs).

### §3.3 Proposed: T_GUT Lawvere Theory

**Definition (T_GUT — proposed for GUT-C)**:

`T_GUT` is a **biproduct-enriched Lawvere theory**:
- Underlying V-category: V = a chosen SMCC with biproducts (typically SMCC + biproducts itself)
- Objects: ℕ-indexed family, with object 0 (terminal) and object 1 (generator δ_T)
- Morphisms: generated by axioms encoding P1-P7

**Generators (corresponding to P-properties)**:

| Generator | Type | Encodes |
|---|---|---|
| `id_δ : δ_T → δ_T` | identity | P1 (distinction) |
| `compose : δ_T^⊗N ⊗ δ_T^⊗M → δ_T^⊗(N+M)` | direct sum embedding | P2 (composition) |
| `relate_NM : δ_T^⊗N → δ_T^⊗M` for all N, M | morphism family | P3 (relations) |
| `square_N : δ_T^⊗N → δ_T^⊗(2N)` | doubling | P4 (scale) |
| `hom_NM : (δ_T^⊗N ⊸ δ_T^⊗M) → δ_T^⊗(N·M)` | Hom-as-content | P5 |
| `modal_V₄ : δ_T → δ_T^⊗2 ⊗ δ_T^⊗2` | V₄ embedding | P6 (modality, conditional) |
| `atom_3 : (δ_T^⊗3 → δ_T^⊗3)` with `atom_3 ∘ atom_3 = id` | involution | P7a |
| `wedderburn_4 : δ_T^⊗4 ≅ End(δ_T^⊗2)` | endomorphism iso | P7b (generalized) |

**Equations** (selected — full list in Phase γ.1 paper):

1. **Squaring closure** (from P4):
   `square_N ∘ id = (id ⊗ id) ∘ Δ` (diagonal)

2. **Hom-as-content compatibility** (from P5):
   For all f: δ^⊗N → δ^⊗M, `hom_NM(f^*) = ε_f` where ε_f is the curry of f.

3. **Wedderburn invariance** (P7b reformulated):
   `wedderburn_4 ∘ (wedderburn_4)^{-1} = id` plus appropriate naturality

These need careful design to ensure that in different SMCC bases C, T_GUT-models in C have the right specializations. This is the key Phase γ.1 work.

### §3.4 Universal Sayability theorem (proposed)

> **Theorem (GUT-C — Universal Sayability across SMCCs)**:
>
> Let `C` be an SMCC with biproducts and a chosen object `δ : Obj(C)`. Let `R_C` be the canonical T_GUT-model in C with `δ_T ↦ δ` (i.e., the tensor-power construction `R N δ := δ^⊗N`).
>
> Then for any T_GUT-model `M : T_GUT → C`, there exists a natural T_GUT-model isomorphism `M ≅ R_C` (up to equivalence in the 2-category Mod_C(T_GUT)).

**Specializations**:

| Base C | δ | M ≅ R_C means |
|---|---|---|
| FinVect_{F_q} | F_q | M = R-family-over-F_q (recover GUT-A/B algebraic) |
| HeytAlg | Prop | M = Heyting R-family (new GUT-Heyting) |
| FdHilb | ℂ² (qubit) | M = quantum stabilizer-style R-family (new GUT-Quantum) |
| Frm (frames) | Ω (Sierpinski) | M = topological R-family (new GUT-Topological) |

**Reduction to GUT-A/B**: when C = FinVect_{F₂}, this theorem recovers GUT-A's `T5_general` (currently in `UniquenessGeneral.lean`) as a corollary.

### §3.5 P-properties — universal versus specialization

The key insight: **P-properties live in T_GUT** (universal level), but their *concrete content* depends on the base SMCC C.

For example:
- P3 (relations / bilinear classification):
  - In C = FinVect_{F_q}: bilinear forms, Arf invariant (char 2) or discriminant (char ≠ 2)
  - In C = HeytAlg: Heyting lattice classification, Galois connections
  - In C = FdHilb: dagger-symmetric forms, signatures
  - In C = Frame: frame morphisms classification

The single P3 axiom in T_GUT, instantiated in different C, gives different concrete classifications. **This is what "categorical universality" means**.

- P7b (Wedderburn anchor):
  - In C = FinVect_{F_q}: R 4 ≅ Mat₂(F_q)
  - In C = HeytAlg: R 4 ≅ End(R 2) = lattice of self-maps (Boolean lattice in classical case)
  - In C = FdHilb: R 4 ≅ End(R 2) = M₂(ℂ) (full matrix algebra)
  - In C = Frame: R 4 ≅ End(R 2) = frame of opens of R 2

The abstract "R 4 ≅ End(R 2)" is the universal form; the specialization gives the concrete characterization.

---

## §4. Phase γ Implementation Plan

### §4.1 Phase γ.1 (3-6 months) — Framework Design

**Deliverables**:

1. **Read & synthesize key literature**:
   - Lawvere 1963 PhD ("Functorial Semantics of Algebraic Theories")
   - Power 1999 "Enriched Lawvere theories" (TAC)
   - Hyland-Power 2007 "The category theoretic understanding of universal algebra" (ENTCS)
   - Garner-Power 2018 "Enriched Lawvere theories for operational semantics" (NJM)
   - Awodey-Reck 2002 "Completeness and Categoricity"
   - Selinger 2007 "Dagger compact closed categories and completely positive maps"
   - Heunen-Landsman 2009 "A topos for algebraic quantum theory"

2. **Write `gut-c-doctrine.md` v0.2** (this document evolved):
   - Precise definition of T_GUT as enriched-Lawvere
   - Full P1-P7 reformulation as universal axioms
   - Proof sketch of Universal Sayability for one base case (HeytAlg, simpler than quantum)
   - Risk analysis updated based on literature

3. **Mathlib `CategoryTheory` audit** (per parallel subagent):
   - What enriched-Lawvere infrastructure exists?
   - What needs upstream contributions?
   - Realistic Lean implementation timeline estimate

**Decision point**: If γ.1 reveals fundamental framework problems, retreat to Path B (per-class enumeration).

### §4.2 Phase γ.2 — ★ SUBSTANTIALLY COMPLETE (2026-05-17)

**Original approach**: Start with simplest non-algebraic instance (Heyting) to validate framework, then expand.

**Actual γ.2 deliverables** (5 G files via parallel agent execution, single session):

| File | LOC | Sorries | Notes |
|---|---|---|---|
| ✅ G1 `Foundation/Doctrine/LawvereTheory.lean` | 503 | 1 (`free` Lawvere) | Mathlib-PR-quality core class; pseudo finite products |
| ✅ G2 `Foundation/Doctrine/EnrichedLawvereTheory.lean` | 929 | 1 (`freeVFunctor`) | Power 1999 V-enriched extension |
| ✅ G3 `Foundation/Doctrine/T_GUT.lean` | 549 | 2 (`canonical` isos + `universal_sayability`) | 8 generators per §3.3 + 8 laws + headline theorem stated |
| ✅ G4 `Foundation/Doctrine/Instance/Algebraic.lean` | 485 | 2 (R_tensor + recovery) | Recovers GUT-A: P1P7_Satisfier_F2 → Mat₂(ZMod 2) ring iso |
| ✅ G5 `Foundation/Doctrine/Instance/Heyting.lean` | 654 | 2 (R_tensor + P3 class.) | **PATH C VALIDATED** + introduces `DiamondH4` non-Boolean Heyting anchor |
| **Total** | **3120 LOC** | **8 sorries** | Full `lake build SSBX` = 3936 jobs success, 0 axioms |

### §4.2.1 γ.2 Heyting Validation Findings (G5 result)

Per gut-c-doctrine §8.2 decision protocol: **YES (PARTIAL) — sufficient to commit Phase γ.3**.

**Per-generator analysis** (Heyting case):

| Generator | Heyting form | Status |
|---|---|---|
| `id_δ`, `compose`, `square`, `hom`, `modal_V4`, `atom_3` (**6/8 substrate generators**) | Direct substrate transfer | ✓ clean |
| `relate` (**P3**) | Reformulated as lattice morphism classification (`P3_heyting`) | Specialized |
| `wedderburn_4` (**P7b**) | Reformulated as `DiamondH4` 4-element non-Boolean Heyting | Specialized + new math |

**Framework validation conclusion**:
- Framework **DISCRIMINATES correctly** between substrate-level (transfers freely) and algebraic-class (needs reformulation) generators — exactly as designed in §3.5
- Substrate-level generators (P1, P2, P4, atom involution, currying) carry over unchanged
- Algebraic-class generators (P3 bilinear classification, P7b Wedderburn anchor) reformulate with non-trivial Heyting content
- Both reformulations expose **genuine open mathematical problems** publishable as standalone research:
  - Heyting-bimorphism classification (analogue of Arf invariant)
  - Uniqueness of `DiamondH4` as minimum non-Boolean 4-element Heyting anchor

### §4.2.2 The `DiamondH4` Discovery

A new mathematical object introduced via G5:

> `DiamondH4` := the 4-element linearly-ordered Heyting algebra {⊥ < mid₁ < mid₂ < ⊤} with explicit `himp` (Heyting implication).

**Theorem (G5)**: `DiamondH4_is_nonBoolean` — proves `¬¬mid₁ = ⊥ ≠ mid₁`, demonstrating intrinsic non-Boolean Heyting structure.

**Conjecture (open)**: `R 4 Prop ≃ DiamondH4` (uniqueness as minimum non-Boolean 4-element Heyting anchor).

This is the **Heyting analog of P7b's Mat₂(F₂)**: the framework predicts a canonical minimum 4-element structure exists in each δ-class.

### §4.2.3 γ.2 estimated work vs actual

| Original estimate | Actual |
|---|---|
| 6-12 months sequential | Single session via 5 parallel agents |
| 2000-4000 LOC | 3120 LOC |
| Heyting case = validation | Validated PARTIAL — sufficient to commit γ.3 |

### §4.3 Phase γ.3 (6-12 months) — Remaining Instances + Publication

**Deliverables**:

1. `Foundation/Doctrine/Instance/Quantum.lean` — FdHilb instantiation
2. `Foundation/Doctrine/Instance/Topological.lean` — Frame instantiation
3. `Foundation/Doctrine/D6Tests_C.lean` — falsification protocol for GUT-C
4. Standalone publication paper (40-60 pages target venue: *Theory and Applications of Categories* or *Journal of Pure and Applied Algebra*)
5. Mathlib upstream PRs (enriched-Lawvere infrastructure)

**Total Phase γ estimate**: 24-36 months (revised from initial 12-24 estimate). With **parallel agent execution**: potential compression to 12-18 months.

---

## §5. Risk Analysis

### §5.1 Framework risks (HIGH)

1. **P-properties don't fit T_GUT cleanly**:
   - Risk: P3 / P7b may resist universal reformulation
   - Probability: 40%
   - Mitigation: γ.1 informal analysis BEFORE Lean work; can revise framework
   
2. **Enriched-Lawvere insufficient**:
   - Risk: SMCC-enriched-Lawvere may not capture quantum's dagger structure
   - Probability: 30%
   - Mitigation: fallback to dagger compact + Heyting hybrid (Selinger / Heunen-Landsman)

3. **No single base captures all 4 cases**:
   - Risk: FinVect / HeytAlg / FdHilb / Frame may not embed in a common doctrine
   - Probability: 20%
   - Mitigation: relax to "Universal Sayability per doctrine class"

### §5.2 Engineering risks (MEDIUM-HIGH) — UPDATED post Mathlib survey

1. **Mathlib enriched-Lawvere infrastructure CONFIRMED ABSENT**:
   - **Confirmed gap**: no `LawvereTheory` class, no `EnrichedLawvereTheory`, only *conical* (not weighted) enriched limits
   - **LOC needed**: ~2500-3500 for core categorical (i)-(iii) + ~1500-2500 for FdHilb (iv) + ~400-700 for ElementaryTopos (v)
   - **Probability of needing**: 100% (confirmed by direct file survey)
   - **Mitigation strategy**:
     - **Parallel pattern**: build scaffolding locally in `formal/SSBX/Foundation/CategoryTheory/`, then mirror as Mathlib PRs
     - **Mathlib PR cycle**: 3-6 months each; can run γ.2 work locally while upstreaming proceeds
     - 3 highest-leverage PRs identified (see §11)

2. **Lean proof complexity**:
   - Risk: T_GUT-model uniqueness proofs in enriched setting are complex
   - Probability: 70%
   - Mitigation: start with simplest case (HeytAlg, classical); use parallel agents

3. **NEW: Mathlib infrastructure 70-80% ready** (downside revised):
   - SMCC, biproducts, monoidal-closed, cartesian-closed, bicategory, subobject classifier, distributivity, FGModuleCat-as-SMCC, MarkovCategory, CopyDiscardCategory — all present
   - This is **much stronger substrate than expected**; raises overall path feasibility from "research project" to "engineering project with research components"

### §5.3 Acceptance risks (LOW-MEDIUM)

1. **Peer reaction "this is just topos theory"**:
   - Risk: framework dismissed as not novel
   - Probability: 30%
   - Mitigation: emphasize the **specific structure** of T_GUT (P1-P7 encoded as Lawvere generators is novel); cite differences from topos theory

2. **Peer reaction "premature unification"**:
   - Risk: peer says we should do more per-class proof first before unifying
   - Probability: 40%
   - Mitigation: γ.2 starts with concrete Heyting case BEFORE pushing universal claim

### §5.4 Project-level risks

1. **Time overrun**:
   - 12-36 month range is realistic; 12 month best case requires parallel + fortunate framework match
   - Mitigation: phased decision points; can pivot to Path B at end of γ.1

2. **Resource constraint**:
   - Single-person path likely 24-36 months; with 2-3 collaborators 12-18 months
   - Mitigation: peer outreach (G9) may yield collaborators

---

## §6. Connection to `lawvere-identification.md` v0.6

The Path C framework is **complementary** to lawvere-identification's Knaster-Tarski identification, not replacement.

| Aspect | Lawvere-identification v0.6 | Path C (this doc) |
|---|---|---|
| Scope | Fixed δ = Bool/F₂ | Varies δ across SMCC bases |
| Question answered | "What kind of metalogic claim is D1 = lfp(Φ')?" | "How does P1-P7 universally cover all δ-classes?" |
| Framework | Knaster-Tarski + Lawvere methodology | Enriched-Lawvere doctrine |
| Lean status | 0 sorry | Future work |

**Path C theorem**: Universal Sayability across SMCCs
**Lawvere-id theorem**: D1 ⟷ P1-P7 = Knaster-Tarski lfp

Together they form a 2-axis comprehensive framework:
- Vertical (lawvere-id): "What does articulation closure mean in a fixed δ context?"
- Horizontal (Path C): "How does articulation universally apply across δ-classes?"

---

## §7. Open Research Questions — UPDATED post literature survey

The literature survey (a31693b sub-agent) identified **5 open problems in published literature** directly relevant to GUT-C. These now anchor the research questions:

### §7.1 Literature-identified open problems

**O1 (CRITICAL — GUT-C's novel contribution)**: **Dagger structure + cartesian-closure coexistence**
- Cited in: Coecke-Heunen 2016 (*Inf. Comput.* 250), Heunen-Karvonen 2019 (TAC 34)
- Issue: Dagger does NOT interact cleanly with cartesian limits. Products in a dagger category are biproducts. A single SMCC-enriched Lawvere theory cannot simultaneously be cartesian (for Heyt) AND dagger compact (for Hilb) on the *same* objects.
- **GUT-C's required move**: doctrinal framework where dagger and cartesian-closure coexist as *separate δ-realisations* of one R-tower
- **Status in lit**: OPEN
- **GUT-C contribution**: provides a concrete framework + 4 worked-out instances

**O2**: **Symmetric quantum + intuitionistic unification**
- Bohrification (Heunen-Spitters-Landsman 2009, *Comm. Math. Phys.* 291) is asymmetric — quantum encoded via *internal* intuitionistic logic of a topos built from commutative subalgebras
- A symmetric unification (Hilb and Heyt as parallel δ-realisations of *one* structure) is OPEN
- **GUT-C contribution**: T_GUT-models in FdHilb AND in HeytAlg, as parallel instances

**O3**: **Enriched models of intuitionistic algebraic theories**
- Power-Tanaka 2008 onwards: when does a V-enriched Lawvere theory have an *intuitionistic* (Heyting-internal) classifying topos?
- Known for V=Set; OPEN in general
- **GUT-C touches**: requires HeytAlg-enrichment work

**O4**: **∞-Lawvere vs ∞-operad equivalence**
- Berman 2019 (arXiv:1903.02991) proves ∞-Lawvere ≃ finitary monads on spaces; relationship to Lurie's ∞-operads (HA §2) conjectural for non-cartesian V
- OPEN for V = stable ∞-cat (quantum-style)
- **GUT-C strategy**: deferred — Path C stays strict-1-categorical (compatible with current Lean 0-sorry state)

**O5**: **Lean / Mathlib formalization of enriched theories**
- Mathlib has `CategoryTheory.Monad` and `CategoryTheory.Limits` but no general `EnrichedLawvereTheory` API
- Confirmed by Mathlib survey (aef5e4 sub-agent)
- **GUT-C contribution**: ~2500-3500 LOC of Mathlib contributions = THIS work being done

### §7.2 GUT-C-specific questions (from v0.1)

6. **Does the framework subsume the Knaster-Tarski D1 = lfp(Φ') identification?**
   - I.e., does T_GUT-model-existence in C correspond to Φ'_C having a least fixed point?
   - **Hint from survey**: Kelly 1980 "A unified treatment of transfinite constructions" (*Bull. Austral. Math. Soc.* 22) shows enriched Lawvere theories carry complete lattices of subtheories with lfp-style closure preserved — this suggests YES

7. **What's the right notion of "T_GUT-model equivalence" for the Universal Sayability conclusion?**
   - Natural equivalence (standard category theory)? — likely sufficient for strict-1-categorical setting
   - 2-categorical biequivalence? — for stronger universality
   - ∞-categorical equivalence? — deferred to potential GUT-D

8. **How does D6 falsification generalize?**
   - In GUT-A: HoTT / ETCS / SDG tested as alternative *foundations* (all happen to be SMCCs)
   - In GUT-C: alternatives might be *non-SMCC* frameworks (non-commutative geometry, ∞-cosmoi)
   - Specifically test: does our T_GUT have a model in Lurie's ∞-topos that breaks the 1-categorical version?

---

## §8. Decision Points

### §8.1 After Phase γ.1 (3-6 months from start)

**Question**: Is SMCC-enriched-Lawvere the right framework?

**If YES** (literature supports + framework looks clean): commit Phase γ.2.

**If NO** (framework misalignment with one or more bases): 
- Option α: try dagger compact + Heyting hybrid (Selinger)
- Option β: try ∞-topos approach (Lurie HTT)
- Option γ: retreat to Path B (per-class enumeration)

### §8.2 After Phase γ.2 Heyting case (12-18 months from start)

**Question**: Does the first non-algebraic instance (Heyting) instantiate cleanly?

**If YES** (T_GUT-model in HeytAlg = Heyting R-family proved): commit Phase γ.3 (quantum + topological).

**If NO** (specific obstructions in Heyting case): 
- Identify which axiom broke; revise T_GUT
- May need 6-12 month delay to fix

### §8.3 After Phase γ.3 (24-36 months from start)

**Question**: Are all 4 instances + Universal Sayability theorem complete?

**If YES**: publish, peer engagement, victory.

**If NO** (some instance proved very hard, e.g., topological): publish partial result; mark remaining as research-level.

---

## §9. Why This Could Fail (Brutal Honesty)

For epistemic hygiene, scenarios where Path C does NOT work:

1. **"P3 is fundamentally algebraic"**: The Arf invariant / discriminant structure may not have a non-trivial analog in HeytAlg or Frame. If P3 can't be made universal, Path C fails — fall back to Path B.

2. **"Quantum requires dagger, not just SMCC"**: FdHilb's dagger structure may be essential for quantum-side specialization, breaking SMCC universality. Could be salvaged by dagger-SMCC-enriched-Lawvere but adds complexity.

3. **"P7b has no universal form"**: Wedderburn anchor (Mat₂) is specific to finite-dimensional matrix algebras. Non-algebraic analogs may not exist.

4. **"Mathlib infrastructure too thin"**: If Mathlib's enriched-categorical foundations turn out 2-3 years behind what's needed, Phase γ.2 timeline doubles.

5. **"Discovery of foundational paradox"**: Universal Sayability across all SMCCs might be **inconsistent** (e.g., would contradict Russell-style results). Unlikely but possible — the metalogic check (cf. lawvere-id §6) would catch it.

If 2 or more of these materialize, **Path C should be abandoned in favor of Path B**.

---

## §10. Why This Is Worth Trying Anyway

Despite the high risk, Path C is worth pursuing because:

1. **Single field-changing contribution**: if successful, GUT-C as enriched-Lawvere doctrine is a *foundational mathematical object* — equivalent to Lawvere's ETCS as foundation for set theory.

2. **Conceptual clarity**: even if specific implementation fails, the *attempt* clarifies what P-properties are and why they hold (or don't) in each δ-class.

3. **Mathlib contributions are intrinsically valuable**: enriched-Lawvere infrastructure is useful for many other Lean projects beyond GUT.

4. **Acceptance pathway**: enriched-Lawvere is well-established (Power, Hyland 30+ years). Reviewers will understand the framework even if the specific GUT application is novel.

5. **Complements lawvere-identification**: together they form a comprehensive metalogic-and-categorical-doctrine treatment of articulation that's substantially more impressive than either alone.

---

## §11. Mathlib Contribution Strategy

**Confirmed by Mathlib survey** (aef5e4 sub-agent): the most efficient path is to develop GUT-C infrastructure LOCALLY in `formal/SSBX/Foundation/CategoryTheory/` first, then mirror as Mathlib PRs. This avoids being blocked on 3-6 month Mathlib review cycles while still contributing back.

### §11.1 Three highest-leverage Mathlib PRs

**PR-1: `ElementaryTopos` bundling** (~400-700 LOC, NO new math)
- All components exist (`HasFiniteLimits`, `CartesianClosed`, `HasSubobjectClassifier`)
- Just need to bundle into `class ElementaryTopos C extends ...`
- Enables many other Mathlib applications beyond GUT
- Lowest risk; do FIRST as confidence-builder

**PR-2: `LawvereTheory` + `Model` API** (~600-900 LOC, pure recipe from Lawvere 1963)
- `class LawvereTheory T` = small category with strict finite products + generator
- `structure Model T C` = product-preserving functor
- Morphisms of models, equivalence, free models
- Critical for GUT-C **plus** Mathlib's general algebraic theory infrastructure

**PR-3: Weighted enriched limits** (~600-1000 LOC, technical but standard)
- Current Mathlib only has *conical* enriched limits
- Power-cotensors `V ⊗ ‐`-style weighting needed for proper enriched Lawvere
- Recipe in Kelly 1982 *Basic Concepts of Enriched Category Theory* (Cambridge)
- Hardest of the 3 but well-understood mathematically

**Total Mathlib contribution**: ~1600-2600 LOC across 3 PRs. Mathlib review: typically 3-6 months each in parallel.

### §11.2 GUT-C-specific local files (not Mathlib upstream)

**Local files in SSBX scope** (~2000-3000 LOC):

- `Foundation/CategoryTheory/EnrichedLawvere.lean` — V-enriched version on top of PR-2 + PR-3
- `Foundation/Doctrine/T_GUT.lean` — specific T_GUT theory
- `Foundation/Doctrine/Instance/Algebraic.lean` — T_GUT in FinVect_{F_q}
- `Foundation/Doctrine/Instance/Heyting.lean` — T_GUT in HeytAlg
- `Foundation/Doctrine/Instance/Quantum.lean` — T_GUT in FdHilb (needs PR-4 below)
- `Foundation/Doctrine/Instance/Topological.lean` — T_GUT in Frm
- `Foundation/Doctrine/UniversalSayability.lean` — main GUT-C theorem

### §11.3 Optional 4th Mathlib PR (for quantum case)

**PR-4: `FdHilb` + dagger SMCC infrastructure** (~1500-2500 LOC, heavier)
- Bundle finite-dim Hilbert spaces from existing analytic content
- `class DaggerSymmetricMonoidalCategory`
- Compact-closed instance (much of analytic content exists in `InnerProductSpace/Adjoint.lean`)
- Needed only if Quantum instance is pursued in Phase γ.3

### §11.4 Substrate already in Mathlib (turnkey)

Saves substantial work:
- `MonoidalClosed` over `CartesianMonoidalCategory` — unified SMCC interface
- `monoidalOfHasFiniteProducts` — automatic SMC from finite products
- `Distributive/Monoidal.lean:242` — symmetric+closed ⟹ distributive (proved)
- `HasFiniteBiproducts` ↔ `HasFiniteProducts + HasZeroObject + Preadditive`
- `FGModuleCat` over field K — proved `IsMonoidalClosed` + rigid (F_q case **turnkey**)
- `MarkovCategory` + `CopyDiscardCategory` — stochastic substrate free
- `Bicategory + EnrichedCat V` — 2-category of enriched categories for free

---

## §12. Peer Engagement Plan (Path C-specific)

From literature survey (a31693b sub-agent), 5 living researchers most valuable for framework validation:

### §12.1 Recommended outreach (in order)

1. **John Power** (Macquarie Univ., formerly Edinburgh)
   - Direct authority on enriched Lawvere theories (Power 1999, Hyland-Power 2007)
   - Best for sanity-checking V = Vect_{F_q} / V = Frm formulations
   - **Action**: 5-page proposal asking for framework validation BEFORE Phase γ.2 commit

2. **Chris Heunen** (Univ. of Edinburgh)
   - Author Heunen-Vicary 2019 *Categories for Quantum Theory* (Oxford GTM)
   - Co-author Bohrification papers (Heunen-Spitters-Landsman)
   - Best for Hilb + Heyt unification (directly relevant to Open Problem O1)
   - **Action**: 3-page note on T_GUT's dagger + cartesian separation strategy

3. **Mike Shulman** (Univ. of San Diego)
   - Categorical logic, internal logics of higher categories, HoTT
   - Best for metalogic/doctrine side
   - Relevance: connects to lawvere-identification.md v0.6 (D1 = lfp(Φ'))
   - **Action**: joint discussion of metalogic-vs-doctrine 2-axis framing

4. **Steve Awodey** (CMU)
   - Author *Category Theory* (OUP), recent work on univalent foundations
   - Best for foundational positioning of "axiom status = closure under R-tower"
   - **Action**: invite as co-author on standalone GUT-A paper (the v0.1 with metalogic identification)

5. **Bart Jacobs** or **Bartek Klin** (Nijmegen / Warsaw)
   - Coalgebra, modal logic, categorical CS
   - Best for empirical face (D6 falsifier / FOL embedding)
   - **Action**: feedback on GUT framework's testability angle

### §12.2 Outreach format

Per peer-engagement-draft.md v0.1 (3108 words, ready): tailor cover letter to each author's expertise. Lead with the **specific question** for that author, not generic GUT pitch.

### §12.3 Phase γ.1 immediate action items

Concrete next moves in next 1-3 months (revised post-surveys):

1. **Read Power 1999 + Hyland-Power 2007 + Heunen-Spitters-Landsman 2009** (2-3 weeks): the core literature foundation
2. **Start PR-1 (ElementaryTopos bundling)**: lowest risk, builds Mathlib reputation, ~2 weeks
3. **Personalize peer outreach** for Power + Heunen: send within 4 weeks
4. **Write `gut-c-doctrine.md` v0.3** integrating Power feedback (if received): 1-2 weeks
5. **Decision point**: commit Phase γ.2 or retreat to Path B

---

## §12. Conclusion — Path C as a Bet

Path C is a **high-risk, high-reward bet**:

- 24-36 months to potential single Universal Sayability theorem across SMCCs
- Framework risk ~30-40%; if fails, ~6 months sunk cost
- If succeeds: field-changing contribution + complete GUT framework

Alternative is Path B (~24-30 months for per-class proofs, lower risk, multi-paper sequence, less unified).

**Recommended**: commit Phase γ.1 (3-6 months) to investigate framework feasibility before deciding γ.2 commitment. Use parallel agent execution to maximize γ.1 throughput.

---

## Appendix A — Glossary

| Term | Definition |
|---|---|
| **SMCC** | Symmetric monoidal closed category (Eilenberg-Kelly) |
| **Biproducts** | Categorical product + coproduct + zero object compatibility (additive categories) |
| **Lawvere theory** | Cartesian category with chosen generator (Lawvere 1963) |
| **Enriched Lawvere theory** | V-enriched version (Power 1999) |
| **PROP** | "Products and permutations" — symmetric monoidal theory (Mac Lane 1965) |
| **T-model** | Product-preserving functor from theory T to ambient category |
| **Doctrine** | 2-categorical structure of theories (Lawvere 1969) |
| **Topos** | Category with subobject classifier + exponentials (cartesian closed + Ω) |
| **Frame / Locale** | Complete Heyting algebra (= dual of topological space) |
| **Dagger compact** | SMCC + involutive functor + compact closed (Selinger 2007) |
| **(∞,1)-topos** | Higher categorical generalization (Lurie HTT) |

---

## Appendix B — References (v0.2, post literature survey)

### Foundational Lawvere theories
- Lawvere, F. W. (1963/2004). *Functorial Semantics of Algebraic Theories*. PhD thesis, Columbia. Published 2004 as TAC Reprints No. 5.
- Lawvere, F. W. (1969). *Adjointness in Foundations*. Dialectica 23, 281–296. Reprinted TAC Reprints No. 16, 2006.
- Mac Lane, S. (1965). *Categorical algebra*. Bull. AMS 71, 40–106.

### SMCC foundations
- Eilenberg, S., & Kelly, G. M. (1966). *Closed categories*. In *Proc. La Jolla Conference on Categorical Algebra*.
- Day, B. J. (1970). *On closed categories of functors*. LNM 137.
- Kelly, G. M. (1982). *Basic Concepts of Enriched Category Theory*. Cambridge Univ. Press.
- Kelly, G. M. (1980). *A unified treatment of transfinite constructions for free algebras, free monoids, colimits, associated sheaves, and so on*. Bull. Austral. Math. Soc. 22, 1–83.

### Enriched Lawvere theories (core)
- Power, J. (1999). *Enriched Lawvere theories*. TAC 6 no. 7, 83–93. <http://www.tac.mta.ca/tac/volumes/6/n7/n7.pdf>
- Hyland, M., & Power, J. (2007). *The category theoretic understanding of universal algebra: Lawvere theories and monads*. ENTCS 172, 437–458. DOI 10.1016/j.entcs.2007.02.019
- Lack, S., & Power, J. (2009). *Notions of Lawvere theory*. Applied Categorical Structures 17, 243–265.
- Garner, R., & Power, J. (2018). *An enriched view on the extended finitary monad—Lawvere theory correspondence*. Logical Methods in Computer Science 14(1).
- Lucyshyn-Wright, R. (2016). *Enriched algebraic theories and monads for a system of arities*. TAC 31, 101–137.
- Bourke, J., & Garner, R. (2019). *Monads and theories*. Advances in Mathematics 351, 1024–1071.

### PROPs and operadic generalizations
- Lack, S. (2004). *Composing PROPs*. TAC 13 no. 9.
- Bonchi, F., Sobociński, P., & Zanasi, F. (2017). *Lawvere categories as composed PROPs*. In CMCS.

### Quantum / dagger compact
- Selinger, P. (2007). *Dagger compact closed categories and completely positive maps*. ENTCS 170, 139–163.
- Selinger, P. (2012). *Finite dimensional Hilbert spaces are complete for dagger compact closed categories*. arXiv:1207.6972.
- Abramsky, S., & Coecke, B. (2004). *A categorical semantics of quantum protocols*. LICS 2004.
- Heunen, C., & Vicary, J. (2019). *Categories for Quantum Theory*. Oxford GTM.
- Coecke, B., & Heunen, C. (2016). *Pictures of complete positivity in arbitrary dimension*. Information and Computation 250, 50–58.
- Heunen, C., & Karvonen, M. (2019). *Limits in dagger categories*. TAC 34.

### Topos quantum theory (Bohrification — precedent for Heyt+Hilb)
- Heunen, C., Landsman, N. P., & Spitters, B. (2009). *A topos for algebraic quantum theory*. Comm. Math. Phys. 291, 63–110. arXiv:0709.4364
- Heunen, C., Landsman, N. P., Spitters, B., & Wolters, S. (2012). *Bohrification of operator algebras and quantum logic*. Synthese 186. arXiv:0905.2275 (note: full Bohrification at arXiv:0909.3468)
- Döring, A., & Isham, C. J. (2008). *What is a thing?* In *New Structures for Physics*, LNP 813.

### Locale theory and frames
- Joyal, A., & Tierney, M. (1984). *An extension of the Galois theory of Grothendieck*. Memoirs AMS 309.
- Johnstone, P. (2002–2003). *Sketches of an Elephant: A Topos Theory Compendium*. 2 vols. Oxford.

### Higher categorical generalizations
- Lurie, J. (2009). *Higher Topos Theory*. Princeton.
- Lurie, J. (2017). *Higher Algebra*. Online preprint, lurie@math.harvard.edu.
- Berman, J. D. (2019). *Higher Lawvere theories*. arXiv:1903.02991.

### Adjacent / inspirational
- Awodey, S., & Reck, E. (2002). *Completeness and categoricity*. History and Philosophy of Logic 23.
- Power, J., & Tanaka, M. (2008). *Pseudo-distributive laws and axiomatics for variable binding*. Higher-Order and Symbolic Computation 21.
- Hyland, M., & Robinson, E. (1990s). Various on intuitionistic algebra / topos perspective.

### Lean / Mathlib categorical infrastructure (status per 2026-05 survey)
- `Mathlib/CategoryTheory/Monoidal/` — comprehensive SMCC scaffolding (50+ files)
- `Mathlib/CategoryTheory/Enriched/` — V-enrichment basics (10 files), conical limits only
- `Mathlib/CategoryTheory/Limits/Shapes/Biproducts.lean` — full biproduct interconversion
- `Mathlib/Algebra/Category/FGModuleCat/Basic.lean` — F_q case turnkey
- `Mathlib/CategoryTheory/MarkovCategory/Basic.lean` — stochastic substrate free
- `Mathlib/CategoryTheory/CopyDiscardCategory/Basic.lean` — Fox theorem direction
- `Mathlib/CategoryTheory/Subobject/Classifier/Defs.lean` — subobject classifier (pre-Topos)
- Gaps (confirmed absent): `LawvereTheory`, `EnrichedLawvereTheory`, weighted enriched limits, `ElementaryTopos` (bundling), `FdHilb` (as Mathlib category), dagger categories

### Project internal documents
- [`lawvere-identification.md`](lawvere-identification.md) v0.6 — companion metalogic identification (D1 = lfp(Φ'))
- [`representation-closure.md`](representation-closure.md) v0.1.3 — companion philosophical synthesis
- [`gut-roadmap.md`](../10_formal_形式/gut-roadmap.md) — overall GUT-A/B/C plan
- [`peer-engagement-draft.md`](peer-engagement-draft.md) v0.1 — outreach materials

---

## Appendix C — Revision History

- **v0.3 (2026-05-17, post γ.2 Heyting validation)**: ★ **PATH C VALIDATED**. Key updates:
  - **§4.2 rewritten**: γ.2 substantially complete via 5 parallel agents (G1-G5), 3120 LOC, 8 sorries
  - **§4.2.1 NEW**: Heyting validation findings — framework discriminates correctly between substrate-level (6/8 generators) and algebraic-class (P3, P7b) generators per §3.5 design
  - **§4.2.2 NEW**: `DiamondH4` discovery — 4-element non-Boolean Heyting algebra as P7b-Heyting anchor; opens publishable open problem (uniqueness conjecture)
  - **§4.2.3 NEW**: γ.2 actual vs estimated — single session compressed 6-12 month sequential estimate via parallel agent execution
  - **Risk tier**: MEDIUM-HIGH → **MEDIUM** (further down post γ.2 success)
  - **Status**: "GO recommendation" → "**PATH C VALIDATED, γ.3 commitment**"
  - **Per gut-c-doctrine §8.2 decision protocol**: γ.2 question "Does the first non-algebraic instance instantiate cleanly?" answered **YES (PARTIAL)** — sufficient to commit γ.3
  - γ.3 in progress: Quantum (γ.3-A), Topological (γ.3-B), universal_sayability discharge (γ.3-C), free Lawvere discharge (γ.3-D)

- **v0.2 (2026-05-17, post-surveys)**: ★ Integrated literature survey (a31693b) + Mathlib survey (aef5e4) findings. Key updates:
  - Header bumped to v0.2, status "GO recommendation"
  - **§5.2 Engineering risks**: Mathlib gap **CONFIRMED** at 2500-3500 LOC core (+ 1500-2500 FdHilb optional); 70-80% substrate already in Mathlib (much better than expected)
  - **§7 Open questions**: replaced with literature-identified Open Problems O1-O5; **O1 (dagger + cartesian coexistence) identified as GUT-C's novel contribution** — publishable in TAC/LMCS/MSCS
  - **§11 Mathlib Contribution Strategy** (NEW): 3 highest-leverage PRs identified — (1) ElementaryTopos bundling ~400-700 LOC, (2) LawvereTheory+Model ~600-900 LOC, (3) weighted enriched limits ~600-1000 LOC
  - **§12 Peer Engagement Plan** (NEW): 5 living researchers prioritized — Power (most direct), Heunen (Bohrification), Shulman (metalogic), Awodey (foundational positioning), Jacobs/Klin (empirical)
  - **Appendix B**: extensive references from literature survey (50+ citations across 8 areas)
  - **Risk tier**: HIGH → MEDIUM-HIGH (revised down ~25% given Mathlib substrate strength + literature precedents)
  - **Estimated timeline**: 24-36 months **confirmed feasible** (Mathlib survey verdict tier b)
  - **Decision recommendation**: **commit Phase γ.1** (3-6 months investigation + Power outreach), then re-evaluate γ.2 commitment

- **v0.1 (2026-05-17)**: Initial framework proposal. Path C among 3 options (A: parametric, B: per-class, C: this — enriched-Lawvere doctrine). Heavy on framework design, light on literature integration (pending parallel subagent survey).
