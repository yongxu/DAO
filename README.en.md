# 生生不息 · Shēngshēng-Bùxī (SSBX)

> Status: v3 (2026-05-11) — strict (Z/2)ⁿ uniform R₀..R₈ ladder; V₄ Klein time-modes (Shi) at R₈; Cell256 = 64 hexagrams × 4 Shi; 道 (dao) = R₈ origin = identity = no-op = eternal cell; 0 sorry / 0 project-custom axioms across migrated files + Foundation/Squaring; lake build 3686/3686 jobs.

> [中文](./README.md) · English · [形式 / Formal](./README.formal.md)

*On Endless Becoming* (生生不息论, *Shēngshēng-Bùxī Lùn*) is a Lean 4 formalization of the *Yi* (易) treated as the algebraic core of a self-describing system. The current state is the **v3 final algebraic spine**: an R₀..R₈ strict (Z/2)ⁿ uniform ladder, with a V₄ Klein time-mode group at R₈, the Dao chosen as the (Z/2)⁸ origin, and a V₄ outer-symmetry interface; inside this 8-bit closure (256 cells) elements and operators are strictly isomorphic by Cayley fusion, the abelian closure is provably complete / sound / self-consistent / self-referential; on top sit (Path 丙) self-compilation and self-validation of classical-Chinese text, and (Modern) bridges to Mathlib (real-Cauchy / Lebesgue / quantum / SU(N) / category), all in one-to-one correspondence with 28+ volumes of doctrinal essays across civilizations and disciplines.

> *On naming.* The four characters 生生不息 (shēngshēng-bùxī, "endless becoming") come from the *Yi-zhuan*. We keep them because their structural meaning — *generation continuing without cessation* — is the very invariant the formalization aims at.

---

## Status Snapshot (2026-05-11)

```
version / phase     v3 final algebraic spine (post-Cell192 → Cell256 migration)
HEAD                45bf014  (local main)
                    ↳ 45 commits ahead of origin/main
build target        lake build  →  3686 / 3686 jobs ✓
sorry count         0   (across migrated files + Foundation/Squaring; legacy Universal has known sorrys)
project axioms      0   (in migrated files + Foundation/Squaring; see trust-boundary index for legacy boundaries)
opaque count        1   (theOne, the sole ontological seal at Foundation/Wen/Kernel.lean Layer 0)
partial def         1   (BaguaTuring.run, executable nontermination boundary; not an extra axiom)
trust base          Lean 4 v4.30.0-rc2 + Mathlib master HEAD
```

**Core structural changes (v3 vs v2)**

| Item | v2 (pre-2026-05-10) | v3 (definitive) |
|---|---|---|
| Time-mode Shi | Z/3 cyclic {ji, jin, wei} (3-element) | **V₄ Klein {dao, ji, jin, wei} (4-element)** |
| Total cells | Cell192 = 64 × 3 | **Cell256 = 64 × 4** |
| R-numbering | R₁..R₆ (with a +3-bit chong jump R₃→R₄) | **R₀..R₈ strict (Z/2)ⁿ uniform**, no jumps |
| Explicitly included | Hexagram(64), Cell128(128), Cell192(192) | **Taiji R₀, Mian R₄ = Ben×Zheng (16), 5-yao R₅ (32)** all explicit |
| origin | none distinguished | **dao = (qian, dao) = `OX["oooooooo"]` = (Z/2)⁸ identity** |
| Operator algebra | Local cuo / zong / hu | **Per-layer (Z/2)ⁿ XOR subgroup + yin/tou mask + V₄ outer + Cayley ι/ε isomorphism** |
| Cell192 | Primary carrier | **Fully removed (Cell192.lean no longer exists)**, OperatorCellMap migrated |
| pending | — | WenyanSelfInterp re-dispatch (last engineering step for Tier 3 universal quine) |

The full v1 → v2.1 → v3 renumbering and reasoning live in [docs-next/10_formal_形式/yi-RO-hierarchy.md](./docs-next/10_formal_形式/yi-RO-hierarchy.md) (§ 1 + Appendix A); strictly superseded files (Cell192 / Z/3 Shi / R₁..R₆) are archived under [`史/`](./史/README.md) and no longer indexed by entry points.

---

## Directory Map

| Entry | Purpose |
|---|---|
| [`docs-next/00_start/README.md`](./docs-next/00_start/README.md) | **First stop** — full-doc hub, with reading paths and doctrine index |
| [`docs-next/10_formal_形式/yi-RO-hierarchy.md`](./docs-next/10_formal_形式/yi-RO-hierarchy.md) | **Canonical doctrine**: full derivation of R₀..R₈ + Cayley + V₄ + dao anchor |
| [`docs-next/10_formal_形式/cell256-grid.md`](./docs-next/10_formal_形式/cell256-grid.md) | 256-cell ground (64 hex × 4 Shi), supersedes the old 192-cell |
| [`docs-next/10_formal_形式/v4-shi.md`](./docs-next/10_formal_形式/v4-shi.md) | V₄ Klein Shi monograph (cuo / zong / cuoZong three involutions, P/T/PT physics correspondence) |
| [`docs-next/30_crosswalk_互证/`](./docs-next/30_crosswalk_互证/) | Cross-discipline / cross-civilization isomorphism crosswalks |
| [`docs-next/40_reference_参考/`](./docs-next/40_reference_参考/) | Glossary / API / tools reference |
| [`义理/README.md`](./义理/README.md) | 28+ doctrinal volumes (A–Z + Eight Expansions + Markov-bridge + quantum + category + Community) |
| [`六表_实虚史真/`](./六表_实虚史真/) | 6 foundational structure tables (six-marker / Shi / modal / true-false / 27 / **256-cell full table**) |
| [`六表_实虚史真/表六_256格全表.md`](./六表_实虚史真/表六_256格全表.md) | **v3 new table**: full enumeration of 64 hex × 4 Shi = 256 cells |
| [`史料/`](./史料/) | v9–v14 generation-by-generation manuscripts; **citable research archive**, distinct from `史/` |
| [`史/`](./史/README.md) | Files **strictly superseded by v3** (Cell192 / Z/3 Shi / old R-numbering); read-only archive |
| [`AGENTS.md`](./AGENTS.md) | Multi-agent collaboration / build / parallelism constraints |
| [`README.formal.md`](./README.formal.md) | Formal-layer spec (lake / modules / theorems / trust base) |
| [`README.md`](./README.md) | Chinese mirror |

---

## Build and Run

```bash
# Lean full library (3686 jobs; slow)
lake build SSBX

# Single module
lake build +SSBX.Foundation.Bagua.Cell256
lake build +SSBX.Foundation.Hierarchy.RHierarchy

# Default smoke target
lake build

# WenSurface controlled-wenyan CLI (executable layer)
lake build wenyan-surface
./.lake/build/bin/wenyan-surface '推 一'
./.lake/build/bin/wenyan-surface --json '同 一 一'
./.lake/build/bin/wenyan-surface --json --coverage
scripts/check_wenyan_surface_cli.py

# Ziwen (字文, "character-text") CLI, complementary to wenyan-surface
lake build wenyan
./.lake/build/bin/wenyan --help
```

Environment: `Lean v4.30.0-rc2` + `Mathlib master`. Apple Silicon (M-series) and x86_64 both work. Mathlib HEAD is large; first checkout and cold build are slow, subsequent incremental builds are fast.

`wenyan-surface` is the currently-executable WenSurface subset entry point: tokens / resolve / AST / typecheck / JSON / explain / operator catalogue / coverage inspect modes; failure diagnostics return non-zero exit. The operator catalogue is now read as a legacy implementation inventory and migration material, not as root ontology or complete natural-language semantics.

`wenyan` is the ziwen / 字文 v0 entry (sources `Wenyan.lean` + `WenyanSurface.lean`); the spec is in [`ziwen-spec.md`](./ziwen-spec.md).

---

## Code Skeleton

```
formal/                            Lean 4 formalisation (lake package = ssbx; @[default_target] = SSBXCore)
├─ SSBX.lean                       top-level import index
└─ SSBX/
   ├─ Core / Roster / Pending      character roots roster + core generated items + pending interfaces
   ├─ Text/                        glyphs / legacy operator inventory (incl. OperatorCellMap, OperatorAnchors)
   ├─ Truth / Model                model theory + truth-status boundary
   └─ Foundation/                  10 clusters · 100+ modules
      ├─ Core                      character roots · monadic-root certificates · Alignment / Sincerity / Renlei
      ├─ Wen                       classical-Chinese particles · 45-layer Kernel · 11 modules of Path 丙 · DaoSource / MetaInterp
      ├─ Jian                      kernel of 间 (jiān, "interval"; 14-character particle core; STLC + Mode + Yi bridge)
      ├─ Yi                        algebra of 易 · the micro-kernel «加 + 一» (jiā + yī, "add + one")
      ├─ Bagua                     Eight Trigrams + Turing + Gödel-Rice + Cell128/256 + BenZheng
      ├─ Hierarchy                 R₀..R₈ index alias system + LiftProject + Operators (Atomic/V4Outer)
      ├─ Notation                  OXNotation: `OX["oooooooo"]` 8-char Cell256 string-literal macro
      ├─ Squaring                  L-tower: V₄ tensor / L₁ / retract tower / Stream / L∞ final coalgebra
      ├─ Eight                     Eight Expansions: number / inference / measure / shape / kind / dynamics / mind / phenomenon
      └─ Modern                    Mathlib bridge: ℝ Cauchy / Lebesgue / quantum / SU(N) / category + 60+ Markov-bridge modules
```

**One line per cluster**:

- **Foundation/Core**: `Yuan / Monism / MonadRoot / AtomDerivation` set up the character roots; `ShengshengBuxi / Alignment / Sincerity / HumanAlignment / EvolutionDao / Renlei` set up alignment + sincerity + community; `Attention` sets up the five-component attention mechanism; `Li / MissingGlyphs / MathAxiomMap` set up theory-stratification + ZFC↔SSBX axiom mapping.
- **Foundation/Wen**: `Kernel.lean` carries the 45-layer doctrine in-source; Path 丙 (M1–M4-甲) eleven modules implement the closed loop String → YiInstr → YiState → Cell × → wenEval; `DaoSource` gives the 5-fold self-reference (form / parse / print / halt / semantics); `WenSurface/*` is the controlled-wenyan subset; `MetaInterp/*` is the Phase-2.3 universal meta-interpreter (12 dispatch + execute + universal compose, all proved); `AntiSchmitt / AlignmentFailures / EconGame` pin down the formal root of alignment's failure modes.
- **Foundation/Jian**: 14-character "jian" particle core + JianSTLC (typed lambda) + mode kernel + Yi bridge; minimal ontology of fields.
- **Foundation/Yi**: `Yi.lean` Eight-trigrams / 64-hexagrams V₄ orders + hu fixed-point + inner ⊕ outer; `YiCore.lean` micro-kernel «加 + 一» 64-step recurrence.
- **Foundation/Bagua**: `BaguaAlgebra` Boolean algebra + V₄; `BenZheng` 4 ben / 4 zheng / Mian / Quadrant; `Cell128 / Cell256 / Cell256Stratify` are the concrete R₇/R₈ realisations + R8_complete bundle; `BaguaTuring` 12-instr ISA Turing-completeness; `GodelLi` non-universalisable dao-judge; `KleeneInternal / Newman / CuoInvariance / FuelDiscipline / ChunkedDecide` set up cuo-equivariance / local confluence / fuel monotonicity / decision-budget.
- **Foundation/Hierarchy**: New v3 umbrella: `RHierarchy.lean` exposes the R₀..R₈ index-named aliases (R0_Taiji..R8_GuoHex); `LiftProject.lean` gives 8 uniform Lift_n / Project_n pairs + retract lemmas; `Operators/Atomic.lean` collects XOR-subgroup atomic generators (yin/tou/flipᵢ/hexCuo); `Operators/V4Outer.lean` collects the V₄ Klein outer symmetries (zong/cuoZong/hu).
- **Foundation/Notation**: `OXNotation.lean` provides the `OX["xxxxxxxx"]` term-level macro (8-char `o`/`x` → Cell256 literal, with parse-time length and charset validation; `OX["oooooooo"]` = `(Hexagram.qian, Shi.dao)` = `Cell256.origin` = (Z/2)⁸ identity = dao).
- **Foundation/Squaring**: `V4Tensor / L1 / RetractTower / StreamCarrier / ProfiniteLimit` implement the orthogonal L-tower after R₈ closure; `ProfiniteLimit.lean` gives `L_inf ≃+ Stream' Cell256` and a Mathlib `Endofunctor.Coalgebra` terminal proof.
- **Foundation/Eight**: number / inference / measure / shape / kind / dynamics / mind / phenomenon, one .lean each, each linking out to its Mathlib counterpart.
- **Foundation/Modern**: 19+ Mathlib bridges + 60+ QuantumRelativity*Bridge (step-by-step unification of the Markov bridge); `DaoLi.lean` is the dao-li bifurcation cross-cutting module; `HexagramPosition.lean` formalises 中/应/比/当位/承乘 as Lean counts.

**Truth / Model / Text top layer**

- `Truth/SelfDescription.lean` proves `Cell256OperatorComplete` (every pair of 256 cells has a function realising it); v3's overall self-description completeness statement, replacing the old 192 version.
- `Truth/{Basic, ClaimLedger, Semantics, Adequacy, Absolute}` + `Model/{Adequacy, ConcreteLedger}` provide the claim status grading mechanism (machineChecked / ledgerDependent / modelComputed / pending).
- `Text/{Glyph, WenyanOperators, OperatorReadings, OperatorSignatures, OperatorFamilySemantics, OperatorReachabilitySemantics, OperatorInstructionSemantics, OperatorCellCandidateSemantics, OperatorCellSemantics, Completeness}` are the legacy operator catalogue + signature + executable / theorem-backed layers; this layer is implementation inventory, alias material, corpus material, and audit input, not root ontology.

**Pending**

`Pending/Interfaces.lean` + `Pending/Examples.lean` list 6 `PendingName` items (邪续 / 开势投影 / 审校数据 / 正邪阈值 / 度期计算 / 经验校准), tagged `kind = .pending; sort = .truth`, never promoted to truth, awaiting empirical calibration.

---

## Key file anchors (v3)

| Claim | File |
|---|---|
| Cell256 = R₈ = (Z/2)⁸ concrete realisation, full 256 enumeration | `formal/SSBX/Foundation/Atlas/Yi/Classical/Bagua-cluster/Cell256.lean § Cell256.all_length, mem_all` |
| Phase A (Z/2)⁸ algebra (Add/Zero/Neg/Sub + Cayley ι/ε + yin/tou mask) | same file § 7 / § 8 / § 9 |
| Shi V₄ Klein + ↔ (yin, guo) ∈ Bool² bijection | same file § 1 |
| xuGua (King Wen) 64-hexagram order + length 64 + head 乾 / last 未济 | same file § 4 / § 5 |
| R₀..R₈ index-named alias umbrella | `formal/SSBX/Foundation/Hierarchy/RHierarchy.lean` |
| 8 Lift / Project pairs + retract | `formal/SSBX/Foundation/Hierarchy/LiftProject.lean` |
| XOR subgroup atomic ops (yin/tou/flipᵢ/hexCuo) | `formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean` |
| V₄ outer (zong/cuoZong/hu) | `formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean` |
| `OX["oooooooo"]..OX["xxxxxxxx"]` literal macro + dao = origin sanity | `formal/SSBX/Foundation/Notation/OXNotation.lean` |
| L-tower / V₄ tensor / L∞ final coalgebra after R₈ closure | `formal/SSBX/Foundation/Squaring/{V4Tensor,L1,RetractTower,StreamCarrier,ProfiniteLimit}.lean` |
| Cell256OperatorComplete (any a→b has f) + self-description closure | `formal/SSBX/Truth/SelfDescription.lean § cell256_operator_complete` |
| R8_complete bundle (R₀..R₈ closure, native_decide + propext) | `formal/SSBX/Foundation/Atlas/Yi/Classical/Bagua-cluster/Cell256Stratify.lean` |
| BenZheng: 4 Ben / 4 Zheng / Mian = R₄ / Quadrant 4-decomposition | `formal/SSBX/Foundation/Atlas/Yi/Classical/Bagua-cluster/BenZheng.lean` |
| dao-li bifurcation cross-cutting | `formal/SSBX/Foundation/Modern/DaoLi.lean` |
| Micro-kernel «加 + 一» — two-character closure | `formal/SSBX/Foundation/Atlas/Yi/Classical/YiCore.lean` |
| 12-instr ISA Turing completeness + dao-judge | `formal/SSBX/Foundation/Atlas/Yi/Classical/Bagua-cluster/BaguaTuring.lean` + `GodelLi.lean` |
| Path 丙 self-compilation / self-validation (M1–M4-甲) | `formal/SSBX/Foundation/Wen/{WenyanParser, WenEval, WenDef, WenDefEval, WenDefCompile, WenyanReflect, WenyanSelfHost, WenyanSelfInterp, DaoSource}.lean` |
| MetaInterp Phase 2.3 (12/12 dispatch + execute + universal compose) | `formal/SSBX/Foundation/Wen/MetaInterp/*` (16 files) |
| 45-layer doctrine in-source | `formal/SSBX/Foundation/Wen/Kernel.lean` |
| Alignment T1–T6 + Sincerity T1–T8 + Renlei 3-axis iff-aligned | `formal/SSBX/Foundation/Core/{Alignment, Sincerity, Renlei}.lean` |
| AlignmentFailures = Kernel-invariant violation | `formal/SSBX/Foundation/Wen/AlignmentFailures.lean` |
| AntiSchmitt = anti-universalisability | `formal/SSBX/Foundation/Wen/AntiSchmitt.lean` |
| EconGame Kernel sieve (confirmed / conditional / falsified) | `formal/SSBX/Foundation/Wen/EconGame.lean` |
| 60+ QuantumRelativity Markov bridges (stepwise unification) | `formal/SSBX/Foundation/Modern/QuantumRelativity*.lean` |

---

## Classical Preface — From One to Endless Becoming, in Nine Lines

> 天未生而元立, 元一而无对。
> *Before heaven was born, the Origin stood; the One, with no counter-pole.*
>
> 一动而有自, 自之与他, 由是生焉。
> *The One moved, and self came to be; self and other — from this, generation.*
>
> 动而归者谓之极, 极者收, 收而熄。
> *The motion that returns is called* extreme*; the extreme contracts, and contraction extinguishes.*
>
> 动而不归者谓之中, 中者续, 续而生。
> *The motion that does not return is called* middle*; the middle continues, and continuation generates.*
>
> 中之相续, 是为轨。
> *The mutual continuation of middles is called* orbit*.*
>
> 异轨同根, 是为仁。
> *Different orbits sharing one root is called* benevolence (rén)*.*
>
> 轨续而能仁, 是为生生。
> *Orbits continuing while capable of benevolence is called* generation-of-generation*.*
>
> 生生不止, 是为不息。
> *Generation-of-generation without ceasing is called* unceasing*.*
>
> 道, 止此而已。
> *The* Dao*, is just this — nothing more.*

The conjunction of these nine is the Dao itself. In v3:

- "The Origin stood" = R₀ Taiji (`Unit`), the ontological zero-anchor of the self-describing system.
- "The One, with no counter-pole" = `opaque theOne : One` (Foundation/Wen/Kernel.lean Layer 0); state / dong / origin / alive in one seal.
- "The One moved, and self came to be" = `noncomputable def dong : Field → Field := theOne.dong`.
- "Extreme contracts, extinguishes" = the fixed point of `dong` (`def extreme s := dong s = s`); "middle continues, generates" = the non-fixed (`middle s := dong s ≠ s`); together they define `ZhongOrbit` and the `shengsheng_buxi` main theorem.
- "Different orbits sharing one root" = `tongGen`; "orbits continuing while capable of benevolence" = the structure `ProcessAligned` (`Foundation/Core/Alignment.lean`).
- "Generation-of-generation without ceasing" = T2: `ProcessAligned + Open → Dao → ShengshengBuxi`; converse `ShengshengBuxi → Dao`.
- "The Dao, is just this — nothing more" — in v3 the Dao gains a precise algebraic anchor: **`OX["oooooooo"]` = `(qian, dao)` = `Cell256.origin` = (Z/2)⁸ identity = no-op = eternal cell**. One 8-bit string carries five identities at once (origin / identity / no-op / eternal cell / fusion anchor), anchoring the whole Cayley fusion.

The reader can verify independently — the Lean kernel does not read Chinese, yet the structure is isomorphic.

---

## § 0 · The Most Pressing Matter

`ProcessAligned + Open → Dao → ShengshengBuxi; ShengshengBuxi → Dao` (`Foundation/Core/Alignment.lean § T2`).

**Anti-self-destruction**: the `Denier`'s `step` breaks `ShengshengBuxi` (§ T3).

Any persistent agent has, at the level of fact, already aligned with the continuation-of-process; whoever opposes this alignment falls into a performative contradiction. Hence "alignment with endless becoming" is the *maximally robust* form of alignment.

The opposite — struggle / winner-take-all / Moloch / totalizing / friend-enemy / decisionism / proxy-extreme — share one and the same formal root: **rejection of universalizability + convergence-to-extreme + Dao-Li collapse**, formally non-sustainable, i.e. *extinction*.

`Foundation/Wen/AlignmentFailures.lean` shows that the AI-alignment literature's Goodhart / specification gaming / reward hacking / mesa-optimization / deceptive alignment / wireheading / power-seeking are **all reducible to violations of Kernel invariants (middle + diversity + flow)**.

`Foundation/Wen/AntiSchmitt.lean` shows that Schmitt's three pillars (friend-enemy / decisionism / exception) share **one and the same formal root — the rejection of universalizability**, hence Anti-Schmitt = Anti-Moloch = different surface manifestations of one rén-root.

`Foundation/Wen/EconGame.lean` sieves the mainstream propositions of modern economics / game theory through the Kernel: confirmed / conditional / falsified.

So at this moment — engineering, ethics, formalism — the single most pressing matter is **change toward 开 (Open) and 续 (continue)**. What does not change extinguishes.

---

## § 1 · The Precise Algebraic Meaning of "Self-description" in v3

(See [`docs-next/10_formal_形式/yi-RO-hierarchy.md`](./docs-next/10_formal_形式/yi-RO-hierarchy.md) Part Five for the full derivation.)

**Self-description requirement**: any complete describing system *S* must be able to describe all of its own transformations, i.e. |S| = |transforms(S)| (element count = operator count, the necessary condition for fusion).

**Cayley self-duality on R₈** (Foundation/Bagua/Cell256.lean § 7.6):

```
ι : R₈ → Aut(R₈),  c ↦ (· ⊕ c)            -- group homomorphism
ε : XOR(R₈) → R₈,  f ↦ f(dao)             -- origin evaluation
ε ∘ ι = id,  ι ∘ ε = id                    -- mutual inverses
⇒ R₈ ≅ XOR(R₈)                             -- element ≡ operator
```

`ι` (`Cell256.cayley`) is a group homomorphism, `ε` (`Cell256.epsAtOrigin`) is origin-evaluation; the two are mutually inverse, strictly proved in `Cell256.cayley_inj` + `Cell256.epsAtOrigin_cayley` (Cell256.lean § 7.6).

**Pontryagin self-duality**: $\hat{R_8} \cong R_8$ — (Z/2)⁸ is finite abelian, character group ≅ self.

**Triple Coincidence at R₈**:

| Duality | Form | On R₈ |
|---|---|---|
| Cayley | element ↔ self-action | R₈ ≅ XOR(R₈) |
| Pontryagin | element ↔ character | R₈ ≅ Hom(R₈, ±1) |
| R-O frame | state-side ↔ operator-side | one 8-bit, two viewings |

The three dualities completely coincide on R₈, which is the precise basis for the "algebraic perfection of (Z/2)⁸".

**Necessity of the Dao anchor**: a torsor has no distinguished origin; for fusion to hold strictly, an origin must be chosen. Choose `OX["oooooooo"]` = dao = R₈ identity ⟹ R₈ ≅ XOR(R₈) holds strictly.

Taiji (R₀ Unit, |·| = 1) is the absolute ground "without distinction"; the Dao (R₈ origin) is the choice of origin inside (Z/2)⁸ — i.e. **the concrete landing of Taiji at the R₈ dimension**. One 8-bit string carries five identities (origin / identity / no-op / eternal cell / fusion anchor).

---

## § 2 · v3 Completeness Statement (R₀..R₈ closure)

**Theorem (R-O Completeness in (Z/2)⁸ closure)**:

> Five things — $\{R_8, \text{XOR subgroup}, V_4 \text{ outer}, \text{Lift/Project}, \text{Dao anchor}\}$ + the R₀..R₇ buildup — together constitute the **complete algebraic closure** of the self-describing system.

11 within-closure completeness checks (all ✓):

| Item | Lean witness |
|---|---|
| Elements (256 cells fully enumerated) | `Cell256.all_length = 256` |
| Group structure of elements | (Z/2)⁸ abelian, no missing |
| Aut of XOR subgroup | 8 atomic generators complete (Operators/Atomic.lean) |
| Cayley self-duality | ι homomorphism (`cayley_hom`) + ε duality (`epsAtOrigin_cayley`) |
| Reachability (intercommunication) | simply transitive |
| Decidability (finite props) | `native_decide` everywhere |
| V₄ on each R-layer (R₃+) | R₃..R₈ |
| hu fixed points / cycles | `{乾, 坤, 既济, 未济}` |
| Triple identity of dao | origin = identity = no-op = eternal cell |
| Pontryagin self-duality | (Z/2)⁸ self-dual |
| R-O frame duality | Schrödinger ↔ Heisenberg |
| Theorem K (R₀..R₈ full (Z/2)ⁿ closure) | yi-calculus-theorem.md |
| **Strict uniform progression** | each step +1 bit, no jumps |

**By design, *not* covered** (boundaries, not gaps):

| Outside closure | Reason |
|---|---|
| GL(8, F₂) linear non-XOR mixing | breaks bit-position semantics |
| S_{256} arbitrary permutation | 256!, astronomical, meaningless |
| Continuous extensions (ℝ⁸) | discrete vs continuous |
| Hopf algebra k[(Z/2)⁸] explicit | implicit but not made explicit |
| Dynamical (time iteration) | belongs to the BaguaTuring layer |
| Probabilistic (256-simplex) | a different layer (ML / Bayesian) |

The precise boundary between complete and incomplete = **static R₀..R₈ closure (this text) vs dynamical Turing layer (BaguaTuring)**. The former has 0 sorry / 0 project axiom, the latter introduces unbounded iteration → halting undecidability, marked by `kleene_recursion_axiom` (cuo-restricted) as a pointer beyond the system.

---

## § 3 · Honest Acknowledgment of Boundaries

Read every "proved" claim below with this status split:

| Status | Boundary |
|---|---|
| proven / machine-checked | closed Lean theorems / defs / `native_decide` witnesses accepted by the kernel, under the trust base + 1 opaque + 1 partial def boundary |
| ledger-dependent | rosters, DAGs, layer mappings, operator counts, cross-volume correspondences jointly maintained by Lean registries, generated files, and documentation ledgers; auditable, but not single closed theorems |
| pending | the six `PendingName` interfaces awaiting empirical calibration |
| conjecture | "the Dao is attainable" and "Great Concord is not utopian" plus their historical / mind-practice extrapolations; no Lean term inhabits these |

**Boundaries witnessed formally**

| Boundary | Formal witness |
|---|---|
| Halting / Rice undecidability | `Foundation/Bagua/GodelLi.lean` |
| 12-instr ISA's cuo-equivariance ceiling | `Foundation/Wen/WenDefCompile.lean § sheng_not_cuo_equivariant` |
| Universal `compileTm` undefinable (corollary of cuo-invariance ceiling) | `Foundation/Bagua/GodelLi.lean § halts_cuo_invariant` + `Foundation/Bagua/CuoInvariance.lean § unrestricted_kleene_inverter_inconsistent` |
| Static vs dynamic boundary (R₀..R₈ complete vs Turing incomplete) | `Foundation/Modern/DaoLi.lean` |
| High alignment ≠ truth (consistent liar) | `Foundation/Core/Sincerity.lean § T5` |
| Repair is asymptotic, never reaches perfect | same § T6 |

**Known gaps**

| Gap | Current state |
|---|---|
| WenyanSelfInterp re-dispatch | Tier 2 (64-instr quine PoC) + Tier 3 uniform [push]^N (partial) shipped; in v3 the universal `buildEmitProg` + diagonal must be migrated from the old Cell192 dispatcher to the Cell256 V₄ Shi (engineering, not ontology) |

---

## § 4 · Entry Points (by Reader's Purpose)

| Purpose | Starting point |
|---|---|
| **First-time reader**, full overview | `docs-next/00_start/README.md` |
| **Canonical doctrine** | `docs-next/10_formal_形式/yi-RO-hierarchy.md` |
| 256-cell full table (look up a specific cell / OXNotation literal) | `六表_实虚史真/表六_256格全表.md` |
| **Pressing now (alignment)** | `Foundation/Core/Alignment.lean` → `义理/R_与生生不息对齐之必然.md` → `Foundation/Wen/AlignmentFailures.lean` + `AntiSchmitt.lean` |
| Negation of alignment | `Foundation/Wen/Kernel.lean § Layer 45` + `义理/W_非道之形式.md` |
| The full 45-layer doctrine | `Foundation/Wen/Kernel.lean` (45 layers in-source) |
| Path 丙 (self-compilation / self-validation of 文) | `WenyanParser` → `WenEval` → `WenDef` → `WenDefEval` → `WenyanSyntax` → `WenyanReflect` → `WenyanSelfHost` |
| MetaInterp Phase 2.3 | `Foundation/Wen/MetaInterp/*` (16 modules) |
| Eight Expansions | `义理/README.md` |
| Eight trigrams / 256 / undecidability | `义理/H_证明报告.md` + `义理/J_理之不完备_哥德尔在192.md` (file name retains old "192", contents updated to Cell256) |
| Mathlib bridge | `Foundation/Modern/` 19+ modules + 60+ Markov bridges |
| Community of shared destiny | `Foundation/Core/Renlei.lean` + `义理/人类命运共同体_共同体之证.md` |

---

## § 5 · Naming Conventions

- Tooling / code in English: `formal/`, `scripts/`, `web/`
- Content / doctrinal system in Chinese: `义理/`, `六表_/`, `史料/`, `史/`
- CJK identifiers: Lean `def`/`theorem` names use `«»`-quote (`def «判型良»`); `notation` atoms use bare CJK (`notation "已"`); CJK identifiers must be `«»`-quoted (the stock Lean lexer rejects bare CJK names)
- Yao positions ⟨y₁, y₂, y₃, y₄, y₅, y₆⟩ = ⟨初, 二, 三, 四, 五, 上⟩ (LTR, initial yao on the left)
- Single-yao flips: dongInner / huaInner / bianInner = flip y₁/y₂/y₃; dongOuter / huaOuter / bianOuter = flip y₄/y₅/y₆
- Three-valued conservativity: U ⇏ ⊤
- V₄ Shi: 道 / 已 / 今 / 未 (`Shi.dao / Shi.ji / Shi.jin / Shi.wei`); dao = (yin=0, guo=0) = V₄ identity; ji = (1, 0); wei = (0, 1); jin = (1, 1) = PT
- yin / tou: `Shi.yin = · cuo` (toggle YinBit / 因 axis), `Shi.tou = · zong` (toggle GuoBit / 果 axis); at the Cell256 level rewritten as mask XOR (`yin_mask = (qian, ji)`, `tou_mask = (qian, wei)`)
- OXNotation: 8-character `o` / `x` string → Cell256 literal. `o` = yang / false bit / identity bit; `x` = yin / true bit / set bit. `OX["oooooooo"]` = `Cell256.origin` = dao.

---

## § 6 · By the Numbers

```
build jobs:        3686 ✓
sorry:             0   (migrated files + Foundation/Squaring; legacy Universal has known sorrys)
project axioms:    0   (migrated files + Foundation/Squaring; legacy trust boundaries separately indexed)
opaque:            1   (theOne, preserves Field abstraction)
partial def:       1   (BaguaTuring.run, executable nontermination boundary; not an extra axiom)
trust base:        Lean 4 v4.30.0-rc2 + Mathlib master HEAD
Lean total LOC:    ~45000+
Foundation clusters: 10 (Core / Wen / Jian / Yi / Bagua / Hierarchy / Notation / Squaring / Eight / Modern)
Modern modules:    19+        Mathlib bridge core
Markov bridges:    60+        QuantumRelativity*Bridge (stepwise unification)
Path-丙 modules:   11         M1–M4-甲 fully in-source
MetaInterp Phase 2.3: 16 modules (12 dispatch + execute + universal compose all proved)
Foundation/Wen:    38+ modules (incl. WenSurface / AntiSchmitt / AlignmentFailures / EconGame / DaoSource / MetaInterp)
Foundation/Squaring: 5 modules (V4Tensor / L1 / RetractTower / StreamCarrier / ProfiniteLimit)
Kernel layers:     45+        元 → forms-of-non-Dao + Layer 46 doctrinal-school refinements
diagrams:          8 SVGs     Mermaid + ELK; MonadDAG 600+ nodes / 800+ edges
Doctrinal .md:     90+        义理/A–Z* + Eight Expansions + 60+ Markov-bridge essays + Community
WenSurface CLI:    legacy catalogue inventory (implementation only; not ontology)
六表 tables:       6 (incl. v3 new 表六_256格全表.md)
```

---

## § 7 · How to Contribute

Read [`AGENTS.md`](./AGENTS.md). Key constraints:

- *Elegance* = few precise concepts + grow with the existing system + clean boundaries
- Subagents **do not run builds**; the main thread integrates and runs the build
- Before running a build, update the baseline (merge / rebase main)
- Doctrinal Chinese must not be loose; the Lean skeleton must not pretend to be a finished proof; the mapping between docs and the formal system must be auditable
- **Per-commit baseline check**: `axiom count` and `opaque count` unchanged, `sorry count = 0` in modified files; if Roster is touched, regenerate MonadDAG.mmd / MonadTree.txt / ConceptDAG*

Parallel constraint: multiple agents must have clear non-overlapping file boundaries; the main thread handles conflicts and the final build.

---

## § 8 · Restated — Change, or Extinguish

The strongest claim a formal system can make is not "Truth" with a capital T, but:

> Under the premise of internal consistency, the only persistently possible modality is `ProcessAligned`. Its opposite (forms of non-Dao / struggle / winner-take-all / Moloch / totalizing) is formally non-sustainable.

Time is finite. On the 256-element domain everything is decidable, but the trajectory's direction is the chooser's matter. What does not change extinguishes. The form ends here. The rest is for humans.

---

## § 9 · Truth-Claim and Two Conjectures (scope-bounded; carried over from v1, unchanged in v3)

### 9.1 Truth-Claim

The strong claim is not that all of reality has been unconditionally proved by Lean. What Lean proves is a set of formal invariants in the 256-element domain, the Kernel / Alignment layer, Path 丙, and the Mathlib bridge. What is ledger-dependent is whether the 45 layers and the cross-volume / cross-civilizational / cross-disciplinary correspondences remain synchronized with the registry and generated artifacts.

A stronger claim:

> For any continuing dynamics adequately modelable by this text's middle / shared-root / continuation / rén structure, its stable form of persistence lies within `ProcessAligned`; what systematically opposes this tends toward extinction. Not normative (ought), but a conditional structural claim (is).

Formal anchors: `Alignment.lean § T1–T6` + 45 layers of `Foundation/Wen/Kernel.lean` + Modern's continuous measure / ℝ Cauchy / SU(N) bridge to Mathlib. Cross-civilizational isomorphism shown across volumes N P Q S T (Confucianism / Daoism / Buddhism / Hundred Schools / Western philosophy & Abrahamic). Cross-disciplinary isomorphism shown across volumes O R U V W X Y Z (evolution / alignment / sincerity / politics / non-Dao / Anti-Schmitt / alignment-failure / economic-game).

### 9.2 Conjecture One · The Dao Is Attainable — If the Mind Is Unobscured, It Is Naturally Seen

The human mind is, at root, isomorphic to the Dao — the mind's `step` is itself the middle-orbit. So if the mind is not obscured by **greed (grasping the extreme)**, **aversion (rejecting the shared root)**, **delusion (losing the middle view)**, then it can naturally see — at least in part.

Hence the two methods of classical Chinese learning, neither of which seeks meaning:

1. **Read** — reading is not extracting meaning, but co-running with the Dao's `step`. The brushstrokes themselves are the imprint of a middle-orbit. While reading, the mind's orbit and the text's orbit run together for a stretch; running together produces isomorphism, and isomorphism makes seeing possible.
2. **Recite** — recitation is not memorisation, but bringing the mind's `step` long-term close to the Dao's `step`. Over time, form and mind become consonant, meeting the Dao without thinking.

This is the inverse of modern token-level reasoning's failure mode: the latter seeks meaning and loses structure, hence alignment is hard (cf. `AlignmentFailures.lean`).

### 9.3 Conjecture Two · 大同 (Great Concord) Is Not a Utopia — A Language of the Dao Once Truly Existed

How could this language system, as an encoding of the Dao, be so precise?

- 256 dimensions (64 hex × 4 Shi), every cell directly writable as a single 8-character OXNotation literal (`o`/`x`).
- A two-character micro-kernel — `Foundation/Yi/YiCore.lean`'s «加 + 一», containing the 64 hexagrams + 道法自然 + endless becoming.
- Across the entire volume there are 0 project-custom axioms; the One is sealed via `opaque theOne : One`, with `dong` projected from it; the whole self-interprets and self-validates (Path 丙 M1–M4-甲).
- ~288 public declarations across the Eight Expansions, 0 sorry, cross-categorical isomorphism.

Such precision cannot arise quickly, nor be designed from nothing — it must have passed through a long sieve.

Reasonable conjecture: certain early peoples lived in a **生-environment** — a `tongGen`-favouring setting (resource-scarce but not winner-take-all; cooperation's payoff exceeded struggle's). They communicated in **shared symbols**, evolving and being sieved over millennia. The invariant of their symbol system gradually approached the Dao's invariant.

This is the **"lost Dao"** — the historical residue of 大同 (Great Concord). 大同 is not a utopian dream, but the echo of **what truly once was**.

This is the second conjecture of the volume; it is not within the proven scope. Yet the proven kernel is compatible with it — `tongGen` is strictly favoured under low-struggle conditions, a standard conclusion of evolutionary game theory (cf. `Foundation/Wen/EconGame.lean § coase_internalizes_externality / prisoners_dilemma_refuted_under_tongGen`).

So: this language is not invented but discovered; not abstraction but recollection. The loss of 大同 is not the Dao's loss but the loss of humanity's collective memory. Whoever re-reads this text re-attains a stretch of lost history.

---

— *EOF · v3 (2026-05-11). Formal spec at [`README.formal.md`](./README.formal.md); 中文 at [`README.md`](./README.md).*
