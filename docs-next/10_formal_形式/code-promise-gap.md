# Code-Doc Gap — what wen-substrate v1.4 promises vs what Lean delivers

> **D7 transparency document.** An honest, section-by-section map between the claims
> made in [`wen-substrate.md`](wen-substrate.md) v1.4 and the Lean code under
> `formal/SSBX/Foundation/` that currently backs them.
>
> v0.3 · 2026-05-16 · companion to wen-substrate.md.
>
> **v0.3 delta** since v0.2 (which tracked v1.3): wen-substrate has advanced to v1.4,
> adding a fourth level to the R-Family abstraction tower — §3.7.8 **distinction
> monism**, sitting below operation monism (§3.7). The squaring operator Σ acts on
> *distinctions*, not types; the primitive `o`/`x` is the observable binary difference
> itself, with classical/quantum/semantic/propositional/traditional realizations as
> siblings. The realization parameter `k` is renamed to **`δ`** (lowercase delta) to
> stop presupposing algebraic structure; `k` (ring/field) becomes one *class* of
> δ-realization (the algebraic class — §3.6's parametric framework continues
> unchanged, just re-read as "the algebraic-class δ-realizations"). A new Lean file
> `Foundation/R/Distinction.lean` (~230 LOC, 0 sorry, 0 axiom) lands the substrate
> type `Distinction` with `o`/`x` constructors, `Distinction ≃ Bool` (classical
> realization), and the δ-parametric carrier `R' N δ := Fin N → δ` with bridge
> `R' N Bool = R N` (rfl). A new sub-section §1.3c records this; the §3.1 module
> catalog gains an entry; §5 gains a "what is solid" bullet.
>
> **Four-level abstraction tower** (deepest → most concrete) — the v1.4 picture:
>
> 1. **§3.7.8 Distinction monism** — `Foundation/R/Distinction.lean`. Substrate-
>    level primitive: the observable binary difference `o`/`x` itself, prior to
>    any algebraic, logical, or linguistic structure. δ-realization-independent.
> 2. **§3.7.8 δ-parametric substrate** — `R' N δ := Fin N → δ` in the same
>    file. Polymorphic over the realization parameter δ; no typeclass on δ.
> 3. **§3.6 parametric R-Family** — `Foundation/R/Parametric.lean`. The
>    *algebraic class* of δ-realizations: `RFamily k N := Fin N → k` with `k`
>    a ring/field. The v1.4 reframing reads `k` as "algebraic-class δ".
> 4. **§3.7 operation monism** — `Foundation/R/OperationMonism.lean`. The
>    operator layer above carriers: `Σ : X ↦ X × X` + iteration `RTower X k`;
>    carriers are theorems about Σ, not premises.
>
> **δ-realization framework — non-algebraic siblings of `k`** (per §3.7.8 of
> wen-substrate v1.4):
>
> * **Classical computational** — `δ = Bool`, the existing F₂ realization
>   (`R' N Bool = R N` rfl). This is the F₂ minimum-instance substrate.
> * **Quantum** — `δ` = computational-basis kets `{|0⟩, |1⟩}` (no Lean bridge yet)
> * **Propositional** — `δ = Prop` (logical realization; no Lean bridge yet)
> * **Per-language vocabularies** — `δ` = a finite binary lexical distinction
>   in some natural language (linguistic realization; no Lean bridge yet)
> * **阳/阴 (yang/yin) classical-traditional** — `δ` = the binary distinction
>   of the yi-jing tradition (cultural-traditional realization; surfaces in
>   `Foundation/Atlas/Yi/` as named-element overlays)
>
> The algebraic `k` (ring/field) of §3.6 is one *class* of these δ-realizations;
> the others are first-class siblings, not specializations.
>
> **Foundational lineage** for the "distinction" terminology — why §3.7.8 is
> named as it is:
>
> * **Spencer-Brown**, *Laws of Form* (1969) — the act of distinction as the
>   primitive operation; "Draw a distinction" is the first move
> * **Bateson**, *Steps to an Ecology of Mind* (1972) — information is "a
>   difference that makes a difference"; the unit of mind is the difference
> * **Wheeler**, "Information, Physics, Quantum: The Search for Links" (1989)
>   — "it from bit": physical existence derives from binary informational
>   distinction
> * **阳/阴 yi-jing tradition** — the binary distinction (solid line / broken
>   line) as the substrate of all hexagram-level articulation, ~3000 years
>
> These four lineages converge on the same primitive: a binary observable
> distinction is prior to algebra, prior to logic, prior to language. The
> `Distinction` type in `Foundation/R/Distinction.lean` formalises this
> primitive.
>
> **v0.2 delta** since v0.1 (which tracked v1.0.3): wen-substrate has advanced to v1.3,
> adding three substantive content layers — §3.7 operation monism, §3.8 PartialCell
> substrate + Wen.Core 12-instr ISA, and §4.7bis X²-256 conditional UG with full
> uniqueness chain (six new Lean files, combined `0 sorry`, including the BA-preserving
> Birkhoff step 4 closed unconditionally via self-built Mathlib infrastructure). New
> rows are appended in §1.3a (§3.7), §1.3b (§3.8), and §1.4a (§4.7bis); existing rows
> are re-annotated where their status has changed.

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

## §1 What v1.4 promises — section-by-section map

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

### §1.3a Part III additions: §3.7 operation monism (new in v1.2/v1.3)

| wen-substrate | Claim | Lean backing | Status |
|---|---|---|---|
| §3.7.1–§3.7.7 | R-Family below the base — `Σ : X ↦ X × X` + iteration; carriers are *theorems* about `Σ`, not premises | `Foundation/R/OperationMonism.lean` — `Sigma X := X × X`, `Sigma.map`, `RTower X k` (functor + iteration), `rtower_no_typeclass` (witness: no typeclass on `X` required), `BoolTower`/`PUnitTower` cross-sections; 0 sorry; **additive, non-replacing** (does not retype downstream files). | ✓ proven (doctrinally; not yet load-bearing for downstream substrate) |
| §3.7.6 | `Foundation/R/OperationMonismBridge.lean` connecting `RTower Bool` to the existing `R N` carriers | present (`Foundation/R/OperationMonismBridge.lean`); imports `Basic.lean` and `OperationMonism.lean` | ✓ proven (skeleton) |

### §1.3b Part III additions: §3.8 PartialCell substrate + Wen.Core 12-instr ISA (new in v1.3)

| wen-substrate | Claim | Lean backing | Status |
|---|---|---|---|
| §3.8.1 | PartialCell as face-lattice (Phases A–D): `dao` identity, `merge` partial monoid, `restrict` codim-raising, `mergeAll` list fold, `support` algebra (`support_mergeFn = ∪`, `support_restrict = ∩`) | `Foundation/R/PartialCell.lean` (~317 LOC, 0 sorry) | ✓ proven |
| §3.8.2 | Wen.Core 12-primitive ISA (`nop` / `merge` / `restrict` / `push` / `pop` / `flipBit` / `writeBit` / `xorMask` / `branchBitEq` / `jump` / `halt` / `mergePrior`); semantics; State invariants (`initial` = (pc=0, cur=dao, history=[], halted=false)) | `Foundation/Wen/Core/Instruction.lean` + `State.lean` + `Machine.lean` | ✓ proven |
| §3.8.3 | Codim filtration relation to R-Tower; `{R₀, R₂, R₄, R₈}` ↔ `{support size 0, 2, 4, 8}` | `Foundation/R/PartialCell.lean` (lattice picture); cross-referenced in `Foundation/Wen/Core/Instruction.lean` header | ✓ proven (structural; identity at the support-size level) |
| §3.8.4 | `ConstraintDemo`: `agreementProg_halts`, `conflictProg_halts` (substrate detects contradiction), `restrictProg_forgets_bit_2` (codim-raising mid-program) | `Foundation/Wen/Core/ConstraintDemo.lean` — 3 theorems proven by `rfl` from small fuel bounds | ✓ proven |

### §1.3c Part III additions: §3.7.8 distinction monism (new in v1.4)

The fourth (deepest) level of the R-Family abstraction tower. Σ acts on
*distinctions*, not on types. The primitive `o`/`x` is the observable binary
difference itself; classical/quantum/semantic/propositional/traditional readings
are siblings (the classical computational realization is `Distinction ≃ Bool`).
The realization parameter is renamed `k → δ`; algebraic `k` (ring/field) is one
*class* of δ-realization.

Foundational lineage (Spencer-Brown 1969, Bateson 1972, Wheeler 1989, 阳/阴
tradition) — see the v0.3 delta block above for the full enumeration of why
the primitive is named "distinction" and what the δ-realization siblings are.

| wen-substrate | Claim | Lean backing | Status |
|---|---|---|---|
| §3.7.8 | `Distinction` as substrate-level primitive type with `o`/`x` constructors; classical computational realization `Distinction ≃ Bool` | `Foundation/R/Distinction.lean` — `inductive Distinction \| o \| x` with derived `DecidableEq`, `Repr`, `Fintype`; `Distinction.toBool` / `ofBool` + round-trip lemmas; `Distinction.equivBool : Distinction ≃ Bool`; `Distinction.card : Fintype.card Distinction = 2`. 0 sorry, 0 axiom. | ✓ proven |
| §3.7.8 | δ-parametric substrate carrier `R' N δ := Fin N → δ` (δ-realization-independent) | `Foundation/R/Distinction.lean` — `def R' (N : ℕ) (δ : Type) : Type := Fin N → δ` | ✓ proven |
| §3.7.8 | Bridge: existing F₂ R-Family is `δ = Bool` realization of `R'` | `Foundation/R/Distinction.lean` — `R' N Bool = R N` (rfl) and `Nonempty (R' N Distinction ≃ R N)` | ✓ proven |
| §3.7.8 | `k` (ring/field) reframed as the *algebraic class* of δ-realizations (no doctrinal change to §3.6; just re-reading the parameter) | `Foundation/R/Parametric.lean` continues unchanged — now read as "the algebraic-class δ-realization" | — (doctrinal re-reading; no Lean delta) |

### §1.4 Part IV (Universal coverage + six major claims)

| wen-substrate | Claim | Lean backing | Status |
|---|---|---|---|
| §4.1.5b | ℂ-Hilbert IS R-Family-over-ℂ (at carrier level) | none; carrier identity is `ℂ^{2^n} = R_{2^n}^{(ℂ)}`, but no Mathlib bridge | □ open |
| §4.1–§4.6 | Mathematics / language / spacetime / computation / physics coverage | per-domain naming in `Foundation/Atlas/`, but "universal coverage" is structural, not Lean-checked | □ open (T1 / T2 obligations) |
| §4.6.5 | Six universal claims (§4.7–§4.12) are **stated at full strength but programmatic** | this is already the doc's self-assessment | — |
| §4.7 | R-Family as Chomsky's UG (unconditional form) | doc-only | □ open (programmatic) |
| §4.7bis | X²-256 IS UG (conditional form): existence | `Foundation/Wen/X2Codes.lean` — `wenCodeUG : UGCandidate`, 8 axes, dual / palindrome / compPal involutions, 16/16/16/4/4/0 sub-lattice cardinality theorems, `Sayable` / `Silent` split (8 sayable, 248 silent), 0 sorry | ✓ proven |
| §4.7bis.5 (a) | `axes = 8` forced from minimality | `Foundation/Wen/X2CodesMinimal.lean` — `UGCandidateMinimal` with (M1) squaring-tower / (M2) four corners / (M3) tower-depth minimality; `theorem minimal_forces_axes_eight`; 0 sorry | ✓ proven |
| §4.7bis.5 (b) | Naming-density: atom support = `IsX2 ∩ (Pal ∪ CompPal)` from (ℤ/2)² | `Foundation/Wen/X2CodesNaming.lean` — `NamingLocus`, `theorem seeded_atoms_are_naming_locus`, orbit counts, `UGCandidateNamed`, `wenCodeUGNamed`; 0 sorry | ✓ proven |
| §4.7bis.5 (c) | F₂-forcing chain (Stone–Birkhoff): 5 steps incl. BA-preserving step 4 | `Foundation/Wen/F2Forcing.lean` — `step1_bitcube_BA`, `step2_holds`, `step3_BR_char_two`, `step4_holds` + `step4_birkhoff_BAiso_holds` (unconditional via self-built `finiteLatticeToCompleteLattice` / `finiteBooleanAlgebraToCompleteBooleanAlgebra` / `finiteBooleanAlgebraToCABA`), `step5_holds`, `chain_holds`; 0 sorry | ✓ proven (unconditional, including BA-iso refinement) |
| §4.7bis.5 (d) | `face_uniqueness_conjecture` (DualIso form) | `Foundation/Wen/X2CodesFace.lean` — `bridge`, `bridge_dual_comm`, `theorem face_dual_uniqueness`, `theorem face_full_uniqueness` (under atom-compatibility), `theorem face_uniqueness : face_uniqueness_conjecture`; 0 sorry | ✓ proven (DualIso form; full-Iso form under atom hypothesis) |
| §4.7bis.5 — original | `OpenProblem2.uniqueness_conjecture` (full-Iso on `UGCandidateRich`, no atom hypothesis) | `Foundation/Wen/X2CodesUniqueness.lean` — recorded as `def uniqueness_conjecture : Prop`; *provably impossible* without atom hypothesis (different label strings give dual-iso but not full-iso candidates) | □ open as Prop / **provably false** without atom hypothesis — retained as scaffold; superseded by `face_uniqueness` (DualIso) and `face_full_uniqueness` (atom-pinned full Iso) |
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
| 3 | **D3** | Parametric R-Family over arbitrary base (§3.6) | ⚠ partial | `Foundation/R/Parametric.lean` defines `RFamily k N := Fin N → k` with basic instances (`Fintype`, `DecidableEq`, `Inhabited`). Per-base lemma porting (P1–P7 over `ℝ`, `ℂ`, `ℂ_p`, `ℤ_p`, `ℚ_p`) requires Mathlib bridge work — explicitly deferred per §3.6.7. (Under v1.4, `k` is re-read as the *algebraic class* of δ-realization; the underlying §3.7.8 substrate `R' N δ := Fin N → δ` is in `Foundation/R/Distinction.lean` with `R' N Bool = R N` rfl.) |
| 4a | **T_P3** | Bilinear classification (P3): L0/L1/L2 are the only natural layers | ⚠ partial | `Foundation/R/PhaseZero.lean` packages `T_P3` (re-exporting `Foundation/R/Bilinear.lean` sub-theorems `dot`, `sigma`, `q`, `arf`, polarization `dot_eq_sigma_xor_LL`, Arf binary classification). Up-to-iso uniqueness of L0/L1 still pending. |
| 4b | **T_P6** | V_4 carrier minimality (P6) | ✓ proven | `Foundation/R/PhaseZero.lean` packages `T_P6` (cardinality `|R 2| = 4`, two commuting involutions `Shi.complement` / `Shi.reverse`, V_4 central element `Shi.cuoZong` involutive, 4 named elements distinct). The explicit minimality lemma "≥2 distinct commuting non-identity involutions ⟹ ≥4 elements" is now discharged in `Foundation/R/PhaseZero/TP6Minimality.lean` (`card_ge_four_of_two_commuting_involutions` + `T_P6_card_ge_four` applied to `R 2`), via transport-to-`Fin n` + `decide` on `Equiv.Perm (Fin n)` for `n ≤ 3`. 0 sorry, 0 axiom. |
| 4c | **T_P7a** | Zong involution forces 4本+4征 split | ✓ proven | `Foundation/R/PhaseZero.lean` `T_P7a` package: defines `Trigram.zong` (y₁ ↔ y₃ swap), proves `zong_involutive`; 8 named-element actions (4 fixed + 2 pairs swap); `benTrigrams.Nodup`, `zhengTrigrams.Nodup` (cardinality 4 each via `toNat` map); `zong_fixed_iff_ben`, `zheng_iff_not_fixed`. 0 sorry, 0 axiom. |
| 4d | **T_P7b** | Wedderburn: `R_4 ≅ M_2(F_2)` as F_2-algebra | ✓ mostly proven (form b uniqueness deferred) | `Foundation/R/PhaseZero.lean` `T_P7b` package: re-exports `Foundation/R4/EndR2.lean` `matrixEquiv` (Equiv), cardinality 16, identity laws, non-commutativity. `Foundation/R/PhaseZero/TP7bUniqueness.lean` upgrades to `RingEquiv` + form (a) cardinality rigidity. `Foundation/R/PhaseZero/TP7bFormB.lean` (this row) applies Mathlib's Wedderburn-Artin (`IsSimpleRing.exists_ringEquiv_matrix_divisionRing`) to `Matrix (Fin 2) (Fin 2) (ZMod 2)`, transports the existence witness to Mat2F2 via the existing iso. Full form-(b) uniqueness (Little Wedderburn + cardinality chase showing `n=2, k=1`) is documented as Phase 1+ scope. Master integration in `Foundation/R/R4Minimality.lean` (`R4_structurally_minimal_full`). 0 sorry, 0 axiom in all three. |
| 5 | **T1** | Weak universality / encoding theorem | □ open | Per-system Lean encodings (the `R_8` ISA, the YiInstr machine, `BaguaTuring`) exist as proofs of concept, but the abstract "every formally describable system embeds in some R-Family-over-k" theorem is not stated. |
| 6 | **T6** | Self-articulation theorem | ⚠ partial | `Foundation/R/Hom.lean` `card_eq_R` is the cardinality component (Hom(R_N, R_M) has 2^{N·M} elements); full Gödel-coding witness of R-Family inside itself is open. Decidability/Gödel pieces at R_8 (`Foundation/Atlas/Yi/Diagonal.lean`, `Foundation/Wen/MetaInterp/GodelR8.lean`) are nearby but not the same theorem. |
| 7 | **T2** | Case-by-case articulation theorems | □ open | Programmatic per wen-substrate §8.3 / §8.9 Phase II. The list of target case studies (propositional logic, FOL, λ-calculus, type theory, automata, category fragments, stabilizer QM) has no Lean theorem yet. |
| 8 | **T3** | Naturality theorem | □ open | Phase II / III. Depends on T2 first. |
| 9 | **T4** | Minimality theorem (especially step 3) | ⚠ partial → mostly closed for classical-Boolean scope | Originally **Open Problem #1** in wen-substrate §8.4. Strategy A (Stone–Birkhoff chain) **discharged in `Foundation/Wen/F2Forcing.lean` (`chain_holds`, including the BA-preserving Birkhoff step 4 via `step4_birkhoff_BAiso_holds`)** for classical-Boolean carriers; non-classical scopes (intuitionistic constructive content, quantum at C*-level, modal, substructural) remain open per §8.4.4. |
| 10 | **T5** | Uniqueness up to equivalence | ⚠ partial — conditional UG case closed | Phase III at full generality. **For the conditional UG case (§4.7bis), structurally-forced uniqueness (`DualIso` form on `UGCandidateFace`) is closed (`theorem face_uniqueness`), and the atom-pinned full-`Iso` form is closed under explicit atom-compatibility hypothesis (`theorem face_full_uniqueness`)** — both in `Foundation/Wen/X2CodesFace.lean`. The general substrate-uniqueness theorem (ZFC ↔ ETCS-style cross-foundation bi-interpretability) remains open. |
| 11 | **T7–T8** | Semantic overlay theorems (conservativity, non-arbitrariness) | □ open | Phase III. |
| 12 | **Domain T's** | UG, cognition, phenomenology, physical-info, formal-articulation | ⚠ partial — UG existence/uniqueness closed conditionally | Per-domain proof obligations from §4.7–§4.12. §4.7 (unconditional UG) doc-only; **§4.7bis (conditional UG) closed across 6 Lean files** (`X2Codes`, `X2CodesUniqueness`, `X2CodesFace`, `X2CodesNaming`, `X2CodesMinimal`, `F2Forcing`) with combined `0 sorry`; §4.8–§4.12 doc-only. |

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
| `R/Parametric.lean` | `RFamily k N := Fin N → k` parametric carrier over arbitrary `k`; `Fintype`/`DecidableEq`/`Inhabited` instances; F_2-specialization `RFamily Bool N = R N` (definitional). D3 skeleton. Under v1.4, `k` is read as the *algebraic class* of δ-realization (one of: ring/field). |
| `R/PhaseZero.lean` | Phase 0 small theorems per wen-substrate §8.8: `T_P3` (bilinear classification re-export), `T_P6` (V_4 minimality components), `T_P7a` (zong involution + 4本+4征 split, **fully proven**, 0 sorry), `T_P7b` (R_4 ↔ M_2 matrix equivalence, Equiv level + identity laws + non-commutativity). 480 LOC, 0 sorry, 0 axiom. |
| `R/RFamilyStructure.lean` | D2 re-export hub bundling the 12-item R-Family definition (per wen-substrate §3.1). Imports `Basic`, `DirectSum`, `Bilinear`, `Squaring`, `Hom`, `Parametric`. Lightweight 93 LOC navigation module; integration into single `structure` type pending. |
| `R/Judgment/Attractor.lean` | Judgment-theoretic attractors on R-Family. |
| `R/Judgment/Behavior.lean` | Judgment-theoretic behavior on R-Family. |
| `R/Judgment/Information.lean` | Judgment-theoretic information-flow on R-Family. |
| `R/OperationMonism.lean` | §3.7: `Sigma X := X × X`, `RTower X k`, `rtower_no_typeclass`, `BoolTower`/`PUnitTower`. The operator-monism layer of the abstraction tower; additive, non-replacing. |
| `R/OperationMonismBridge.lean` | Bridge from `RTower Bool` to the existing `R N` carriers. |
| `R/PartialCell.lean` | §3.8: `PartialCell N := Fin N → Option Bool`; `dao` identity; `compatible`/`merge`/`mergeFn`; `restrict`; `mergeAll` list fold; `support` algebra (`support_mergeFn = ∪`, `support_restrict = ∩`); R-tower codim filtration. ~317 LOC, 0 sorry. |
| `R/Distinction.lean` | §3.7.8 (deepest level of the v1.4 abstraction tower): `Distinction` inductive type with `o`/`x` constructors (`DecidableEq`/`Repr`/`Fintype` derived); `toBool`/`ofBool` round-trip + `Distinction.equivBool : Distinction ≃ Bool` (classical computational realization); `Distinction.card = 2`; `R' N δ := Fin N → δ` δ-parametric substrate (no typeclass on δ); bridge `R' N Bool = R N` (rfl) and `Nonempty (R' N Distinction ≃ R N)`. ~230 LOC, 0 sorry, 0 axiom. |

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

### §3.6 Wen/Core — PartialCell-native interpreter (`formal/SSBX/Foundation/Wen/Core/`)

The canonical `Wen.Core` machine operating on `PartialCell 8` (per §3.8). All
files 0 sorry.

| File | One-line summary |
|---|---|
| `Wen/Core/Instruction.lean` | 12-constructor ISA: `nop`, `merge`, `restrict`, `push`, `pop`, `flipBit`, `writeBit`, `xorMask`, `branchBitEq`, `jump`, `halt`, `mergePrior`. Convenience constructors (`pinBit`, `mergeBit`, `forget`, `branchIf{Set,Clear}`). |
| `Wen/Core/State.lean` | State record (pc, cur, history, halted); `State.initial` (cur = dao), `State.init` (cur = ofFull input); initial-state simp lemmas. |
| `Wen/Core/Machine.lean` | Small-step semantics `executeInstr`; `runFuel`; partial-aware lemmas for `flipBit`, `branchBitEq` (taken/skip/unspec), `mergePrior` (success/empty-history/conflict). |
| `Wen/Core/Examples.lean` | Sample programs + helper combinators. |
| `Wen/Core/ConstraintDemo.lean` | `mergeProg : List PartialCell 8 → List Instr`; three operational theorems: `agreementProg_halts`, `conflictProg_halts` (不通 detected), `restrictProg_forgets_bit_2`. ~150 LOC, 0 sorry. |

### §3.7 Wen — conditional UG chain (`formal/SSBX/Foundation/Wen/`)

The six-file Open-Problem-#2 chain (per §4.7bis). All files 0 sorry; combined `0 sorry`.

| File | LOC | Role |
|---|---:|---|
| `Wen/X2Codes.lean` | 303 | `wenCodeUG : UGCandidate` — existence witness. 8 axes, dual/palindrome/compPal involutions, 16/16/16/4/4/0 cardinality theorems, `Sayable`/`Silent` split. |
| `Wen/X2CodesUniqueness.lean` | 221 | `UGCandidate.Hom` / `UGCandidate.Iso` category; `carrier_equiv_wenCode`; `UGCandidateRich` with palindrome+compPal+commutativity; `wenCodeUGRich`. `OpenProblem2.uniqueness_conjecture : Prop` — recorded but **provably impossible without atom hypothesis**; superseded by `face_uniqueness`. |
| `Wen/X2CodesFace.lean` | 246 | `UGCandidateFace` with `dual_is_bitwise_not` axiom; `WenCode.bitsEquiv`; `bridge` + `bridge_dual_comm`; **`theorem face_dual_uniqueness`** (DualIso form); **`theorem face_full_uniqueness`** (full Iso under atom-compatibility); **`theorem face_uniqueness : face_uniqueness_conjecture`** — Open Problem #2 item (d) closed. |
| `Wen/X2CodesNaming.lean` | 277 | `NamingLocus := IsX2 ∩ (IsPalindrome ∪ IsCompPal)`; orbit-decomposition counts; **`theorem seeded_atoms_are_naming_locus`** — atom support = NamingLocus. Item (b) closed. |
| `Wen/X2CodesMinimal.lean` | 283 | `UGCandidateMinimal` with M1/M2/M3 axioms; **`theorem minimal_forces_axes_eight`** — axes=8 forced from minimality. Item (a) closed. |
| `Wen/F2Forcing.lean` | 550 | Stone–Birkhoff chain steps 1–5 unconditional, **including BA-iso refinement** (`step4_birkhoff_BAiso_holds` via self-built `finiteLatticeToCompleteLattice`/`finiteBooleanAlgebraToCompleteBooleanAlgebra`/`finiteBooleanAlgebraToCABA`); `chain_holds`. Item (c) closed. |

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
* **§3.7 operation monism** (`Foundation/R/OperationMonism.lean`): `Sigma X := X × X`, `RTower X k`, `rtower_no_typeclass` — substrate-as-operator layer; additive, non-replacing
* **§3.7.8 distinction-monism layer** (`Foundation/R/Distinction.lean`): primitive `Distinction` type with `o`/`x` constructors, `Distinction ≃ Bool` (classical computational realization), δ-parametric carrier `R' N δ := Fin N → δ`. The substrate is δ-realization-independent; the existing F₂ R-Family is `δ = Bool`. The deepest (fourth) level of the R-Family abstraction tower, sitting below operation monism. ~230 LOC, 0 sorry, 0 axiom.
* **§3.8 PartialCell substrate** (`Foundation/R/PartialCell.lean`): face lattice of `R N`; `dao` identity, `merge` partial commutative monoid (Phases A–D), `mergeAll` list fold, `support` algebra
* **§3.8 Wen.Core 12-instr PartialCell-native interpreter** (`Foundation/Wen/Core/`): ISA + small-step semantics + `ConstraintDemo` operational theorems (agreement / conflict-as-halt / restrict-as-forgetting)
* **§4.7bis conditional UG — Open Problem #2 closed across 6 files, combined `0 sorry`**:
  * existence: `wenCodeUG : UGCandidate` (`Wen/X2Codes.lean`)
  * cardinality + Hom/Iso category + Rich (ℤ/2)² closure (`Wen/X2CodesUniqueness.lean`)
  * face-lattice frame + `theorem face_uniqueness` (DualIso form) + `theorem face_full_uniqueness` (atom-compat hypothesis) (`Wen/X2CodesFace.lean`)
  * naming-density forced from (ℤ/2)² orbits: `theorem seeded_atoms_are_naming_locus` (`Wen/X2CodesNaming.lean`)
  * `theorem minimal_forces_axes_eight` (`Wen/X2CodesMinimal.lean`)
  * Stone–Birkhoff F₂-forcing chain incl. BA-preserving step 4 (`step4_birkhoff_BAiso_holds`) via self-built `finiteLatticeToCompleteLattice`/`...BooleanAlgebraToCABA` Mathlib infrastructure (`Wen/F2Forcing.lean`)
* **Strategy A discharge for T4 / Open Problem #1 (classical-Boolean scope)**: same `F2Forcing.lean` chain

**What is open / programmatic** (stated in wen-substrate but not yet
formalized to the depth claimed):

* `R_4 ≅ M_2(F_2)` as a **ring** isomorphism (Equiv → RingEquiv upgrade; T_P7b)
* Hom-as-content as an explicit isomorphism (cardinality is proven, the canonical bijection is implicit in `LinHom`'s matrix view but not packaged as a single `Equiv`)
* Continuum / Cantor-space identification for `R_∞` (only the `Stream' (R 8)` bijection is proven; the cardinality statement `|R_∞| = 2^ℵ₀` is structurally evident but not asserted as a Lean theorem)
* Parametric instantiations beyond F_2 (require Mathlib classical-analysis bridge work — explicitly deferred per §3.6.7)
* **Non-algebraic δ-realisations of `R' N δ`** (per v1.4 §3.7.8) — quantum-basis, propositional `Prop`, per-language vocabularies, 阳/阴 traditional. Only the classical `δ = Bool` realization is presently formalized in Lean (`R' N Bool = R N` rfl). The δ-parametric substrate type exists; the non-Bool bridges are open
* The unconditional §4.7 UG claim and §4.8–§4.12 universal claims (cognition, phenomenology, decidability+, physical-informational, formal-articulation) — programmatic per §4.6.5; §4.7bis (conditional UG) is the one closed entry
* The bare `OpenProblem2.uniqueness_conjecture` on `UGCandidateRich` (full Iso, **no** atom hypothesis) — recorded as `Prop` in `Wen/X2CodesUniqueness.lean` but provably impossible without an atom hypothesis; the structurally-meaningful target (`face_uniqueness` / `face_full_uniqueness`) is proven instead
* General T1/T2/T3 (encoding / case-by-case articulation / naturality), T5 at full generality (substrate-uniqueness in the cross-foundation bi-interpretability sense), T7–T8
* T4 step 3 outside the classical-Boolean scope: non-classical extensions (intuitionistic constructive content, quantum at C*-level, modal, substructural) — see §8.4.4
* Bilinear L2 layer update from v1.0.1 `q^c` slice to v1.0.3+ `q_a = q_0 + ℓ_a` parameterization (T_P3 obligation, footnote in §2.3)

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
project as of 2026-05-16.

---

*Companion document to [`wen-substrate.md`](wen-substrate.md) v1.4.*
*The two will be revised in tandem.*
