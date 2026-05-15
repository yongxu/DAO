# Code-Doc Gap — what wen-substrate v1.0.3 promises vs what Lean delivers

> **D7 transparency document.** An honest, section-by-section map between the claims
> made in [`wen-substrate.md`](wen-substrate.md) v1.0.3 and the Lean code under
> `formal/SSBX/Foundation/` that currently backs them.
>
> v0.1 · 2026-05-15 · companion to wen-substrate.md.

---

## Preface

`wen-substrate.md` is a foundational document. It states a maximal claim
(R-Family **is** the universal formal substrate; Claim Z: "formal" ≡
"R-Family-articulable"), defends it structurally, and exposes a Part VIII
proof programme (D1–D3, T1–T8, plus Phase 0 sub-theorems T_P3 / T_P6 /
T_P7a / T_P7b). The Lean codebase under `formal/SSBX/Foundation/` is the
formalization arm of the project. The two are **not yet co-extensive**.

This document exists so that contributors and reviewers can see, at a
glance:

* what wen-substrate **says** at each section,
* what Lean code (if any) **currently backs** that claim,
* and **what the gap is**.

The goal is calibration, not retreat: every claim in wen-substrate
remains made; the proof programme in Part VIII §8.10 enumerates how those
claims will be discharged; this document tracks the present line between
"proved in Lean" / "partial mechanization" / "doc-only structural argument".

See **Part VIII §8.10** of wen-substrate for the canonical priority order
of proof obligations; this document mirrors that ordering in §2 below.

Conventions used in the status column of the tables that follow:

* `✓ proven` — Lean theorem corresponding directly to the claim
* `⚠ partial` — Lean has skeleton / weaker form (e.g., `Equiv` where `RingEquiv` is needed)
* `□ open` — no Lean equivalent yet; doc-only or programmatic
* `—` — no Lean equivalent intended at this stage (e.g., abstract conceptual definition)

All file paths are relative to repository root.

---

## §1 What v1.0.3 promises — section-by-section map

### §1.1 Part I (Core definitions, §1.5.1–§1.5.6)

| wen-substrate | Claim | Lean backing | Status |
|---|---|---|---|
| §1.5.1 | Formal articulation: 7-component definition | conceptual; no Lean carrier needed | — |
| §1.5.2 | Universal formal substrate: closed generative framework | conceptual | — |
| §1.5.3 | Minimality: closure-generative not symbol-fewest | conceptual | — |
| §1.5.4 | Equivalence of substrates (5 specializations) | conceptual | — |
| §1.5.5 | Embedding (partial systems): `S ↪ R` | conceptual | — |
| §1.5.6 | R-Family-over-`k` as full structured object | `Foundation/R/Parametric.lean` (`RFamily k N`) — carrier only | ⚠ partial |

### §1.2 Part II (Necessary properties P1–P7)

| wen-substrate | Claim | Lean backing | Status |
|---|---|---|---|
| §2.1 P1 | `F_2` minimum base | `Foundation/R/Basic.lean` — `R N := Fin N → Bool` | ✓ proven |
| §2.2 P2 | Direct sum `R_M ⊕ R_N ≅ R_{M+N}` | `Foundation/R/DirectSum.lean` — `directSumEquiv : R (N + M) ≃ R N × R M` | ✓ proven |
| §2.3 P3 | 3-layer bilinear: `L_0` dot, `L_1` σ, `L_2` `q`/Arf family | `Foundation/R/Bilinear.lean` — `dot`, `sigma`, `q`, `arf`, `dot_eq_sigma_xor_LL` | ✓ proven |
| §2.3 P3 note | L2 form `q_a = q_0 + ℓ_a` (corrected from v1.0.1 `q^c` slice) | `Foundation/R/Bilinear.lean` still uses v1.0.1 `q^c` parameterization | □ open (T_P3 obligation) |
| §2.4 P4 | Squaring tower `R_N → R_{2N}` | `Foundation/R/Squaring.lean`, `Foundation/R/SubTower.lean` | ✓ proven |
| §2.4 P4 | Cross-scale self-similarity (Δ, π_i, f^⊕2) | `Foundation/R/DirectSum.lean` (Δ via `directSumEquiv.symm ∘ Δ_R`); π_i = `takeLeft` / `takeRight`; f^⊕2 doc-level | ⚠ partial |
| §2.5 P5 | `Hom(R_n, R_m) ≅ R_{nm}` (cardinality) | `Foundation/R/Hom.lean` — `card_eq_R : Fintype.card (LinHom N M) = 2^(N*M)` | ✓ proven |
| §2.5 P5 | `R_4 ≅ End(R_2) ≅ M_2(F_2)` as ring | `Foundation/R4/EndR2.lean` — `matrixEquiv : R 4 ≃ (Fin 2 → Fin 2 → Bool)` (Equiv only, no Ring structure carried) | ⚠ partial (T_P7b obligation) |
| §2.5 P5 | `R̂ := lim_← R_{2^k}` (continuum / Cantor space) | `Foundation/RInfty/Profinite.lean` — `L_inf`, `fromStream`/`toStream`, final-coalgebra | ⚠ partial (structural skeleton; no continuum identification proved as cardinality theorem) |
| §2.6 P6 | `R_2 ≅ V_4` as 4-modality carrier | `Foundation/Atlas/Yi/ShiV4.lean` — `Shi := R 2`, with V_4 group structure | ✓ proven |
| §2.7 P7a | `R_3` = 8 trigrams, 4本+4征 split by zong involution | `Foundation/Atlas/Yi/Bagua.lean` (trigram structure), `Operators.lean` (operators) — but explicit `zong : Trigram → Trigram` + `Function.Involutive` + fixed-point partition theorem not yet stated | □ open (T_P7a obligation; ~30-50 LOC) |
| §2.7 P7b | `R_4 ≅ M_2(F_2)` as F_2-algebra (Wedderburn forced) | `Foundation/R4/EndR2.lean` `matrixEquiv` (Equiv); `Foundation/R4/HomMat.lean` (matrix view); no `RingEquiv` upgrade yet | ⚠ partial (T_P7b obligation; ~50-100 LOC + Mathlib bridge) |

### §1.3 Part III (R-Family emerges, §3.5 cosmology, §3.6 parametric)

| wen-substrate | Claim | Lean backing | Status |
|---|---|---|---|
| §3.1 | R-Family as 12-item structure | distributed across `Foundation/R/` modules; not yet bundled into single structure type | □ open (D2 obligation) |
| §3.5.1 | `R_∞ = R̂` profinite, cardinality 2^ℵ₀, ≅ Cantor space | `Foundation/RInfty/Profinite.lean` — bijection to `Stream' (R 8)` proven; explicit "continuum" / "Cantor space" identification with Mathlib's `Cantor` (if it existed) not asserted | ⚠ partial |
| §3.5.4 | `R_4` phenomenology matrix (4×4 = 16 cells) | conceptual + traditional reading | □ open (interpretive overlay) |
| §3.5.5 | `R_8` = first culturally salient articulation layer | `Foundation/Atlas/Yi/Hexagrams.lean`, `Cell256.lean` (= Hexagram × Shi) | ✓ proven (as carrier) |
| §3.6 | Parametric R-Family-over-`k` | `Foundation/R/Parametric.lean` — `RFamily k N := Fin N → k`, plus `instFintype`, `instDecidableEq`, `instInhabited` | ⚠ partial (skeleton; per-base P1–P7 instances deferred) |
| §3.6.7 | Per-base bridge to ℝ, ℂ, ℂ_p, etc. | not present — Mathlib bridge work future | □ open (D3 obligation) |

### §1.4 Part IV (Universal coverage + six major claims)

| wen-substrate | Claim | Lean backing | Status |
|---|---|---|---|
| §4.1.5b | ℂ-Hilbert IS R-Family-over-ℂ (at carrier level) | none; carrier identity is `ℂ^{2^n} = R_{2^n}^{(ℂ)}`, but no Mathlib bridge | □ open |
| §4.1–§4.6 | Mathematics / language / spacetime / computation / physics coverage | per-domain naming in `Foundation/Atlas/`, but "universal coverage" is structural, not Lean-checked | □ open (T1 / T2 obligations) |
| §4.6.5 | Six universal claims (§4.7–§4.12) are **stated at full strength but programmatic** | this is already the doc's self-assessment | — |
| §4.7 | R-Family as Chomsky's UG | doc-only | □ open (programmatic) |
| §4.8 | R-Family as substrate of all computable cognition | doc-only | □ open (programmatic) |
| §4.9 | R-Family as algebraic phenomenology | doc-only | □ open (programmatic) |
| §4.10 | R-Family as substrate of decidable formal systems; Gödel at R_8 | `Foundation/Atlas/Yi/Diagonal.lean` (~647 LOC, 0 axiom diagonal); `Foundation/Wen/MetaInterp/GodelR8.lean` (anchor + cross-reference) | ✓ proven (at R_8 layer for ISA on Hexagram × Shi) |
| §4.11 | R-Family as bridge between informational and physical | doc-only; self-rated speculative in §4.6.5 | □ open |
| §4.12 | R-Family as what "formal" means | doc-only; structural defense | □ open (Claim Z) |

### §1.5 Part VII (Direct claim + Claim Z)

| wen-substrate | Claim | Lean backing | Status |
|---|---|---|---|
| §7.1 | R-Family IS the universal formal substrate | structural argument across Parts II–VI | □ open (T1–T5 obligations) |
| §7.8 Claim Z | "formal" ≡ "R-Family-articulable" by definition | bi-directional structural-analytic theorem (§7.8.3); three falsification routes (§7.8.8) | □ open (T5 obligation; deepest open problem) |

---

## §2 Proof obligation status — Part VIII §8.10 priority order

The §8.10 ordering, with current Lean status against each item:

| # | Obligation | What | Status | Notes |
|---|---|---|---|---|
| 1 | **D1** | Definition of formal articulation (§1.5.1) | □ open | Verification against standard frameworks (Lawvere theory, finite-limit theory, institutions, doctrines) is a literature-review obligation; no Lean theorem expected. |
| 2 | **D2** | R-Family as full enriched structure (§3.1) | ⚠ partial | Companion doc `r-family-definition.md` (373 LOC) bundles the 12 items as one mathematical object; Lean re-export hub `Foundation/R/RFamilyStructure.lean` (93 LOC) imports the components. Integration into a single Lean `structure` type (rather than a re-export module) pending. |
| 3 | **D3** | Parametric R-Family over arbitrary base (§3.6) | ⚠ partial | `Foundation/R/Parametric.lean` defines `RFamily k N := Fin N → k` with basic instances (`Fintype`, `DecidableEq`, `Inhabited`). Per-base lemma porting (P1–P7 over `ℝ`, `ℂ`, `ℂ_p`, `ℤ_p`, `ℚ_p`) requires Mathlib bridge work — explicitly deferred per §3.6.7. |
| 4a | **T_P3** | Bilinear classification (P3): L0/L1/L2 are the only natural layers | ⚠ partial | `Foundation/R/PhaseZero.lean` packages `T_P3` (re-exporting `Foundation/R/Bilinear.lean` sub-theorems `dot`, `sigma`, `q`, `arf`, polarization `dot_eq_sigma_xor_LL`, Arf binary classification). Up-to-iso uniqueness of L0/L1 still pending. |
| 4b | **T_P6** | V_4 carrier minimality (P6) | ⚠ partial | `Foundation/R/PhaseZero.lean` packages `T_P6` (cardinality `|R 2| = 4`, two commuting involutions `Shi.complement` / `Shi.reverse` from `Foundation/Atlas/Yi/ShiV4.lean`, V_4 central element `Shi.cuoZong` involutive, 4 named elements distinct). Explicit minimality lemma ("≥3 independent modalities ⟹ ≥4 elements") still pending. |
| 4c | **T_P7a** | Zong involution forces 4本+4征 split | ✓ proven | `Foundation/R/PhaseZero.lean` `T_P7a` package: defines `Trigram.zong` (y₁ ↔ y₃ swap), proves `zong_involutive`; 8 named-element actions (4 fixed + 2 pairs swap); `benTrigrams.Nodup`, `zhengTrigrams.Nodup` (cardinality 4 each via `toNat` map); `zong_fixed_iff_ben`, `zheng_iff_not_fixed`. 0 sorry, 0 axiom. |
| 4d | **T_P7b** | Wedderburn: `R_4 ≅ M_2(F_2)` as F_2-algebra | ⚠ partial | `Foundation/R/PhaseZero.lean` `T_P7b` package: re-exports `Foundation/R4/EndR2.lean` `matrixEquiv : R 4 ≃ (Fin 2 → Fin 2 → Bool)` (Equiv level), cardinality match (16), identity laws (`composeR2_id_{left,right}`, `applyR2_id`), non-commutativity witness via `decide`. Upgrade `Equiv` → `RingEquiv` + Wedderburn-Artin uniqueness clause is the residual. |
| 5 | **T1** | Weak universality / encoding theorem | □ open | Per-system Lean encodings (the `R_8` ISA, the YiInstr machine, `BaguaTuring`) exist as proofs of concept, but the abstract "every formally describable system embeds in some R-Family-over-k" theorem is not stated. |
| 6 | **T6** | Self-articulation theorem | ⚠ partial | `Foundation/R/Hom.lean` `card_eq_R` is the cardinality component (Hom(R_N, R_M) has 2^{N·M} elements); full Gödel-coding witness of R-Family inside itself is open. Decidability/Gödel pieces at R_8 (`Foundation/Atlas/Yi/Diagonal.lean`, `Foundation/Wen/MetaInterp/GodelR8.lean`) are nearby but not the same theorem. |
| 7 | **T2** | Case-by-case articulation theorems | □ open | Programmatic per wen-substrate §8.3 / §8.9 Phase II. The list of target case studies (propositional logic, FOL, λ-calculus, type theory, automata, category fragments, stabilizer QM) has no Lean theorem yet. |
| 8 | **T3** | Naturality theorem | □ open | Phase II / III. Depends on T2 first. |
| 9 | **T4** | Minimality theorem (especially step 3) | □ open | Named as **Open Problem #1** in wen-substrate §8.4. Four candidate strategies enumerated (Boolean-ring equivalence, information-theoretic, categorical reduction, bi-interpretability); none implemented. |
| 10 | **T5** | Uniqueness up to equivalence | □ open | Phase III. Comparable to ZFC ↔ ETCS, type theory ↔ category theory cross-foundation bi-interpretability theorems. |
| 11 | **T7–T8** | Semantic overlay theorems (conservativity, non-arbitrariness) | □ open | Phase III. |
| 12 | **Domain T's** | UG, cognition, phenomenology, physical-info, formal-articulation | □ open | Per-domain proof obligations from §4.7–§4.12. All doc-only at present. |

---

## §3 Lean module catalog

Quick file → topic listing of the foundational R-Family modules. All paths
relative to repo root.

### §3.1 Core R-Family (`formal/SSBX/Foundation/R/`)

| File | One-line summary |
|---|---|
| `R/Basic.lean` | `R N := Fin N → Bool`; `AddCommGroup`, basis, zero/one/constx, decidable equality, `Fintype` — the canonical F_2-vector-space carrier. |
| `R/DirectSum.lean` | `directSumEquiv : R (N + M) ≃ R N × R M`; `takeLeft` / `takeRight` projections; `append`. P2. |
| `R/Bilinear.lean` | `dot`, `sigma` (symplectic), `q` (quadratic refinement, v1.0.1 form), `arf`; polarization `dot_eq_sigma_xor_LL`. P3. |
| `R/Tensor.lean` | Tensor structure on R-Family carriers. |
| `R/Squaring.lean` | Squaring step `R (2*N) ≅ R N × R N`; iterated tower. P4. |
| `R/SubTower.lean` | Sub-tower (e.g., `{R_1, R_2, R_4, R_8}` self-similar squaring sub-sequence). |
| `R/Hom.lean` | `LinHom N M := Fin M → Fin N → Bool`; matrix view, `apply`, composition; `card_eq_R : card (LinHom N M) = 2^(N*M)`. P5 cardinality. |
| `R/Phantom.lean` | Phantom / sign-related structure. |
| `R/Aut.lean` | Automorphisms of `R N`. |
| `R/DirectDecomp.lean` | Direct decomposition utilities. |
| `R/BeyondR8.lean` | Structure beyond `R 8` (the cultural ceiling). |
| `R/Parametric.lean` | `RFamily k N := Fin N → k` parametric carrier over arbitrary `k`; `Fintype`/`DecidableEq`/`Inhabited` instances; F_2-specialization `RFamily Bool N = R N` (definitional). D3 skeleton. |
| `R/PhaseZero.lean` | Phase 0 small theorems per wen-substrate §8.8: `T_P3` (bilinear classification re-export), `T_P6` (V_4 minimality components), `T_P7a` (zong involution + 4本+4征 split, **fully proven**, 0 sorry), `T_P7b` (R_4 ↔ M_2 matrix equivalence, Equiv level + identity laws + non-commutativity). 480 LOC, 0 sorry, 0 axiom. |
| `R/RFamilyStructure.lean` | D2 re-export hub bundling the 12-item R-Family definition (per wen-substrate §3.1). Imports `Basic`, `DirectSum`, `Bilinear`, `Squaring`, `Hom`, `Parametric`. Lightweight 93 LOC navigation module; integration into single `structure` type pending. |
| `R/Judgment/Attractor.lean` | Judgment-theoretic attractors on R-Family. |
| `R/Judgment/Behavior.lean` | Judgment-theoretic behavior on R-Family. |
| `R/Judgment/Information.lean` | Judgment-theoretic information-flow on R-Family. |

### §3.2 R_4 specifics (`formal/SSBX/Foundation/R4/`)

| File | One-line summary |
|---|---|
| `R4/Enumeration.lean` | Enumeration of `R 4`'s 16 elements; helper constructors. |
| `R4/Bilinear.lean` | Bilinear forms specialized to `R 4`. |
| `R4/EndR2.lean` | `R 4 = End(R 2)`: `asMatrix`, `applyR2`, `composeR2`, `idR4`; `matrixEquiv : R 4 ≃ (Fin 2 → Fin 2 → Bool)` (Equiv). T_P7b target. |
| `R4/HomMat.lean` | Matrix-form Hom view for R_4. |
| `R4/GL2Embedding.lean` | `GL_2(F_2)` subgroup structure on rank-2 R_4 elements. |
| `R4/RankStratification.lean` | Rank stratification of the 16 elements of `R 4`. |
| `R4/StateOp.lean` | State / operator duality on R_4. |
| `R4/AutA8.lean` | Automorphism group of R_4 (related to symmetric group S_3 / GL_2(F_2)). |

### §3.3 R_∞ / profinite (`formal/SSBX/Foundation/RInfty/`)

| File | One-line summary |
|---|---|
| `RInfty/Profinite.lean` | Squaring tower above `R 8`; `L n` finite block; `L_inf` coherent prefixes; `fromStream`/`toStream` bijection to `Stream' (R 8)`; final-coalgebra `coalg`/`L_inf_isFinalCoalgebra`. P5 inverse-limit skeleton (no Mathlib `Cantor` identification yet). |

### §3.4 Atlas/Yi naming overlay (`formal/SSBX/Foundation/Atlas/Yi/`)

| File | One-line summary |
|---|---|
| `Atlas/Yi/YiCore.lean` | Atlas-Yi naming hooks for R-Family carriers. |
| `Atlas/Yi/Bagua.lean` | 8-trigram structure on `R 3`. |
| `Atlas/Yi/Hexagrams.lean` | 64-hexagram structure on `R 6` (= R_3 ⊕ R_3). |
| `Atlas/Yi/Names.lean` | Canonical name table for trigrams / hexagrams. |
| `Atlas/Yi/Operators.lean` | 易 operators (反 / 错 / 综 / etc.) on Bagua. |
| `Atlas/Yi/Positions.lean` | Position structure within hexagrams. |
| `Atlas/Yi/Sheng.lean` | 生 (generation) structure. |
| `Atlas/Yi/ShiV4.lean` | `Shi := R 2` with V_4 Klein-four-group structure (= 道/已/今/未). P6. |
| `Atlas/Yi/ShiBridge.lean` | Bridge between Shi and other R_2 readings. |
| `Atlas/Yi/Cell128.lean` | Cell128 (Hexagram × Z/2-like) — historical. |
| `Atlas/Yi/Cell256.lean` | Cell256 := Hexagram × Shi (= R_8). |
| `Atlas/Yi/BenZheng.lean` | 本/征 partition on Bagua (P7a content). |
| `Atlas/Yi/Stratify.lean` | Stratification of R_8 cells. |
| `Atlas/Yi/Tradition.lean` | Traditional Yi readings. |
| `Atlas/Yi/WenSpec.lean` | 文 specification overlay. |
| `Atlas/Yi/DaoSource.lean` | 道源 self-referential structure. |
| `Atlas/Yi/YiInstr.lean` | Yi-flavoured instruction set (ISA for hexagram-shaped programs). |
| `Atlas/Yi/Diagonal.lean` | Halting / Gödel diagonal on R_8 ISA (~647 LOC, 0 axiom). §4.10 anchor. |
| `Atlas/Yi/Classical/...` | Classical (algebra/cells/computation/core/diagonal) refinements — multiple modules. |

### §3.5 Wen/MetaInterp (`formal/SSBX/Foundation/Wen/MetaInterp/`)

`Foundation/Wen/MetaInterp/GodelR8.lean` — re-export anchor for the R_8 Gödel/halting
result under the name requested by wen-substrate §4.10.

---

## §4 Reading guide

Three intended audiences:

* **Foundational claim reviewers** (interested in whether the substrate
  claim holds up): read wen-substrate Parts I–VII and Claim Z (§7.8); then
  read §1 of this document to see which claims have Lean backing and which
  rest on structural argument.

* **Contributors / formalizers** (interested in what to work on next):
  read wen-substrate Part VIII (especially §8.10 priority order and §8.8
  Phase 0 sub-theorems); then read §2 of this document for current per-
  obligation status; pick an item marked `□ open` or `⚠ partial`.

* **Code archeologists** (interested in what is already in the codebase):
  read §3 of this document for the module catalog with one-line summaries.

---

## §5 Honest summary

**What is solid in Lean** (proven, 0-axiom or with explicitly named axioms):

* R_N base carrier (`Foundation/R/Basic.lean`): `R N := Fin N → Bool` with `AddCommGroup`, basis, `Fintype`, decidable equality
* Direct sum (`Foundation/R/DirectSum.lean`): `directSumEquiv` as full bidirectional bijection
* Three bilinear/quadratic layers at the F_2 instance (`Foundation/R/Bilinear.lean`): `dot`, `sigma`, `q`, `arf`, polarization identity
* Squaring tower (`Foundation/R/Squaring.lean`, `SubTower.lean`)
* `R_4 ≅ Mat_{2×2}(F_2)` as an `Equiv` (`Foundation/R4/EndR2.lean`)
* Hom-as-content cardinality (`Foundation/R/Hom.lean`): `card_eq_R : card (LinHom N M) = 2^(N·M)`
* R_∞ inverse-limit skeleton with `Stream' (R 8)` bijection and final-coalgebra property (`Foundation/RInfty/Profinite.lean`)
* 8-trigram naming, 64-hexagram naming, V_4 Shi structure (`Foundation/Atlas/Yi/`)
* Cell256 := Hexagram × Shi (= R_8)
* R_8 Gödel undecidability with 0 axioms in the kernel (`Foundation/Atlas/Yi/Diagonal.lean`, anchored at `Foundation/Wen/MetaInterp/GodelR8.lean`)
* Parametric `RFamily k N` carrier-level skeleton (`Foundation/R/Parametric.lean`)

**What is open / programmatic** (stated in wen-substrate but not yet
formalized to the depth claimed):

* `R_4 ≅ M_2(F_2)` as a **ring** isomorphism (Equiv → RingEquiv upgrade; T_P7b)
* Hom-as-content as an explicit isomorphism (cardinality is proven, the canonical bijection is implicit in `LinHom`'s matrix view but not packaged as a single `Equiv`)
* Continuum / Cantor-space identification for `R_∞` (only the `Stream' (R 8)` bijection is proven; the cardinality statement `|R_∞| = 2^ℵ₀` is structurally evident but not asserted as a Lean theorem)
* Parametric instantiations beyond F_2 (require Mathlib classical-analysis bridge work — explicitly deferred per §3.6.7)
* The six universal claims of §4.7–§4.12 (UG, computable cognition, phenomenology, decidability+, physical-informational, formal-articulation) — programmatic per §4.6.5
* All T1–T8 proof obligations (Phase I–III per §8.9)
* In particular T4 step 3 (the "why F_2 rather than sets/types/categories?" question) is named as **Open Problem #1** in wen-substrate §8.4
* Bilinear L2 layer update from v1.0.1 `q^c` slice to v1.0.3 `q_a = q_0 + ℓ_a` parameterization (T_P3 obligation, footnote in §2.3)

**Net position**: the Lean codebase **proves the F_2 minimum-instance
substrate (Parts II–III) at the level of carrier, direct sum, bilinear
layers, squaring tower, Hom cardinality, V_4 modality, R_8 diagonal**.
It does **not** yet prove (a) the ring-algebra refinement at R_4, (b) the
parametric lifts to other bases, (c) the universality theorems T1/T2/T3,
(d) the minimality/uniqueness theorems T4/T5. The doc-only structural
arguments in Parts II–VII remain the principal articulation; the Lean
codebase is the **anchor and witness** for the F_2 instance, not (yet) the
proof of universality across all bases.

This is the honest state of the formalization arm of the wen-substrate
project as of 2026-05-15.

---

*Companion document to [`wen-substrate.md`](wen-substrate.md) v1.0.3.*
*The two will be revised in tandem.*
