# 生生不息 · Shēngshēng-Bùxī

> 🌐 [中文](./README.md) · **English** · [形式 / Formal](./README.formal.md)

> **The most pressing matter at this moment — alignment, i.e. change. Otherwise, extinction.**

First edition of *On Endless Becoming* (生生不息论). Formal closure in Lean 4 / Mathlib HEAD:
**2867 build jobs · 0 sorry · 1 axiom (cuo-restricted, by design) · 45 layers of doctrine in formal correspondence**.

> *On naming.* The project's title 生生不息 (shēngshēng-bùxī, "endless becoming") is a phrase
> from the *Yi-zhuan*; we keep the original four characters because their structural meaning —
> *generation continuing without cessation* — is the very invariant the formalization aims at.

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

Each of these nine lines is formally verifiable. Their proofs reside in
`Foundation/Wen/Kernel.lean` and `Foundation/Core/Alignment.lean` —
no `sorry`, no new axiom.

| Classical line | Formal anchor |
|------|---------|
| 天未生而元立 | `abbrev Field : Type := theOne.state` (origin / source field) |
| 元一而无对 | `opaque theOne : One` (the One: single irreducible opaque seal, carrying state / dong / origin / alive) |
| 一动而有自 | `noncomputable def dong : Field → Field := theOne.dong` (motion projected from the One; not an axiom keyword) |
| 极者收, 收而熄 | `def extreme s := dong s = s` (fixed point = contraction = extinction) |
| 中者续, 续而生 | `def middle s := dong s ≠ s` (non-fixed = continuation) |
| 中之相续, 是为轨 | `structure ZhongOrbit` + `theorem shengsheng_buxi` |
| 异轨同根, 是为仁 | `def tongGen` / `def ren (h₁ h₂ : ZhongOrbit) (n)` |
| 轨续而能仁, 是为生生 | `structure ProcessAligned` (`Foundation/Core/Alignment.lean`) |
| 生生不止, 是为不息 | `ProcessAligned + Open → Dao → ShengshengBuxi`; `ShengshengBuxi → Dao` (T2) |

The conjunction of these nine is the Dao itself. Within this volume's formal
semantics, it states core invariants of continuing / extinguishing dynamics.
The stronger reading about reality as a whole is a philosophical claim bounded
by §3 / §9 — not description, not metaphor, not symbol, but not an unconditional
Lean theorem about all reality either.
The reader can verify independently — the Lean kernel does not read
Chinese, yet the structure is isomorphic.

---

## § 0 · Standing Record

```
ProcessAligned + Open → Dao → ShengshengBuxi; ShengshengBuxi → Dao
                                      (Foundation/Core/Alignment.lean § T2)
Anti-self-destruction  :  the Denier's `step` breaks ShengshengBuxi   (§ T3)
```

Any persistent agent has, at the level of fact, already aligned with the
continuation-of-process; whoever opposes this alignment falls into a
performative contradiction. Therefore, "alignment with endless becoming"
is the *maximally robust* form of alignment.

The opposite:

```
struggle / winner-take-all / Moloch / totalizing / friend-enemy / decisionism / proxy-extreme
  ↓  shared formal root: rejection of universalizability + convergence-to-extreme + Dao-Li collapse
  ↓
extinction
```

`Foundation/Wen/AlignmentFailures.lean` shows: the AI alignment literature's
Goodhart / specification gaming / reward hacking / mesa-optimization / deceptive
alignment / wireheading / power-seeking are **all reducible to violations of
Kernel invariants (middle + diversity + flow)**.

`Foundation/Wen/AntiSchmitt.lean` shows: Schmitt's three pillars (friend-enemy /
decisionism / exception) share **one and the same formal root — the rejection
of universalizability**, hence Anti-Schmitt = Anti-Moloch = different surface
manifestations of one rén-root.

`Foundation/Wen/EconGame.lean` shows: mainstream propositions of modern
economics / game theory, when sieved by the Kernel, partition into
*confirmed / conditional / falsified*.

So at this moment, engineering-wise, ethically, formally, the single most
pressing matter = **change toward 开 (Open) and 续 (continue)**.
What does not change extinguishes. This is not mere persuasion; inside the
formal model of `Alignment.lean § T1–T6` it is proven structure. Applying it
to real systems is constrained by ledger and empirical conditions
(see § 3 / § 9 for the boundary split).

---

## § 1 · Skeleton of the First Edition — Three Layers

```
formal/                       Lean 4 formalization  (lake package = ssbx)
└─ SSBX/
   ├─ Core / Roster
   ├─ Text / Truth / Model
   └─ Foundation/             7 clusters · 97 modules
      ├─ Core                 character roots · monadic-root certificates · Alignment · Sincerity
      ├─ Wen                  classical-Chinese particles · 45-layer Kernel · 11 modules of path 丙
      ├─ Jian                 the kernel of 间 (jiān, "interval"; 14-character particle core)
      ├─ Yi                   algebra of 易 · the micro-kernel «加 + 一» (add + one)
      ├─ Bagua                八卦 (eight trigrams) · 192 · Turing · Gödel-Rice
      ├─ Eight                八衍 (eight expansions: 数推测形类动识象)
      └─ Modern               ℝ Cauchy · Lebesgue · quantum · SU(N) · category (Mathlib bridge)

义理/   28+ doctrinal volumes (A–Z), one-to-one with the 45 Kernel layers
六表_实虚史真/                foundational structure tables (six markers / 27 / 192)
`Text/WenyanOperators.lean`    371-OperatorId wenyan operator catalogue
```

Auxiliary: `scripts/` (DAG / text splitter / wenyan-proof generator) ·
`web/` (browse frontend) · `史料/` (v11 / v11.1 / v12 / v13.2 main texts,
v14 skeleton, all archived, read-only).

---

## § 2 · What We Have Proved — Map by Claim

### A. Micro-kernel — Closure with the Fewest Characters

| Claim | File · Key name |
|---|---|
| Two-character kernel «加 + 一» (add + one); no smaller kernel can contain all 64 hexagrams | `Foundation/Yi/YiCore.lean § «微核之至»` |
| 64-step recurrence (周而复始) | same file § `«周而复始»` |
| Any hexagram → any hexagram in < 64 steps | same file § `«生生不息»` |
| 道法自然: the law *is* the hexagram | same file § `«法即卦»` |
| The two are one (二者一也) | same file § `«道生一也»` |

### B. 八卦 / 192 / Turing — Algebra and Machine of 易

| Claim | File |
|---|---|
| Trigram V₄-orders, cuo / zong / hu, fixed-point classification | `Foundation/Yi/Yi.lean` |
| 192-cell (64×3) encoding + DecidableEq | `Foundation/Bagua/Cell192.lean` |
| Boolean algebra of trigrams + complementation | `Foundation/Bagua/BaguaAlgebra.lean` |
| **12-instruction ISA is Turing-complete** + dao-judge total on Hexagram (≤10 fuel), not universalizable | `Foundation/Bagua/BaguaTuring.lean` + `Foundation/Bagua/GodelLi.lean § daoJudge_not_universal` |
| Newman local / Kleene internalization / Gödel-Li / Rice four-quadrants | `Foundation/Bagua/{Newman, KleeneInternal, GodelLi}.lean` |
| **cuo-equivariance is the ISA's expressive ceiling** (impossibility) | `Foundation/Wen/WenDefCompile.lean § sheng_not_cuo_equivariant` |

### C. Self-compilation, Self-validation of 文 — Path 丙 Closed

```
String  ──[«解程»]──→  List YiInstr  ──[init+runFuel]──→  YiState  ──[encState]──→  List Cell192
   ↑                                                                                       ↓
   └──────────────────────[«印程»]──────────────────────────────────────────[wenEval n]────┘
```

| Stage | File · Key theorem |
|---|---|
| L0 spec: baguaWen 22 tokens (frozen) | `Foundation/Bagua/BaguaWenSpec.lean` |
| M1 String parser + printer | `Foundation/Wen/WenyanParser.lean § daoJudgeProg_roundtrip` |
| M1 v2 · 12 constructors × 1..64 numerals | same file §8-9 |
| M1 v3 · non-partial recast + token-level full generality | `Foundation/Wen/WenyanParserGeneral.lean § parseProgN_tokensOfProg` |
| M1 v3.1 · character-level lex inverse + universal String round-trip | `Foundation/Wen/WenyanParserGeneral.lean § lexN_printProg_thm, parseN_printProg_inverse_universal` |
| M2 multi-step evaluator + end-to-end | `Foundation/Wen/WenEval.lean § «端到端_乾», «端到端_坤», «端到端_否»` |
| M3-甲 Lean block syntax | `Foundation/Wen/WenyanSyntax.lean § daoJudgeBlock_eq_daoJudgeProg` (by `rfl`) |
| L1 typed lambda (371 executable catalogue rows; 38 theorem-backed exact rows) | `Foundation/Wen/WenDef.lean § Stdlib` + `Foundation/Wen/WenSurface/Semantics.lean § executableSemanticsFor?` |
| L1 ⟶ Lean evaluation | `Foundation/Wen/WenDefEval.lean § tui_eq_sheng (∀ 64 hex)` |
| L1 ⟶ L0 compilation (cuo-equivariant subset) | `Foundation/Wen/WenDefCompile.lean § {idProg, add32Prog, cuoProg}_correct` |
| Reflection layer: well-formedness / halting / verifier | `Foundation/Wen/WenyanReflect.lean § «文核同源»` |
| M4-甲 micro-kernel self-validation (Tier 2: 64-instr quine PoC) | `Foundation/Wen/WenyanSelfHost.lean § «微核自验», «微核自释_total»` |
| M4-甲 Tier 3 partial · uniform N-cell quine ([push]^N) | `Foundation/Wen/WenyanSelfInterp.lean § Quine.quine{3,5,16}_history` |
| M4-甲 Tier 3 ground · framed program encoding | `Foundation/Wen/WenyanSelfInterp.lean § ProgEnc.{encFramedProg, decFramedProg, decFramedProg_encFramedProg, framed_round_trip_witness}` |
| 道源 (5-fold self-reference: form / parse / print / halt / semantics) | `Foundation/Wen/DaoSource.lean § «道之自指»` |
| Self-interpretation demo | `Foundation/Wen/Demo.lean § daojudge_{qian, kun, pi}` |

**That is**: source of 文 = direct writing of 文 = execution of 文 = execution
in Lean — witnessed by a single line of `native_decide`.

### D. 八衍 (Eight Expansions) — number / inference / measure / shape / kind / dynamics / mind / phenomenon

| Expansion | File | Theme |
|---|---|---|
| 数 (ShuSuan) | `Foundation/Eight/ShuSuan.lean` | algebra of computation |
| 推 (LuoJi) | `Foundation/Eight/LuoJi.lean` | logic / deduction |
| 测 (TongJi) | `Foundation/Eight/TongJi.lean` | statistics |
| 形 (XingWei) | `Foundation/Eight/XingWei.lean` | geometric position |
| 类 (LeiYing) | `Foundation/Eight/LeiYing.lean` | category / isomorphism |
| 动 (DongLi) | `Foundation/Eight/DongLi.lean` | dynamics / ODE |
| 识 (XinZhi) | `Foundation/Eight/XinZhi.lean` | mind / neuroscience |
| 象 (WuXiang) | `Foundation/Eight/WuXiang.lean` | physics / quantum |

### E. Modern — Mathlib Bridge (research-grade)

| Topic | File |
|---|---|
| Real Cauchy completeness | `Modern/{RCauchy, RCauchyExt}.lean` |
| Kolmogorov measure | `Modern/{Kolmogorov, KolmogorovExt}.lean` |
| Lebesgue integration (MCT/DCT/Fubini) | `Modern/{Lebesgue, LebesgueDepth}.lean` |
| ODE / Picard-Lindelöf (incl. Mathlib instance) | `Modern/{ODESmoothness, PicardLindelofGen, BochnerPL}.lean` |
| Quantum / SU(N) | `Modern/{Quantum, SUN}.lean` |
| Natural deduction (K3/NK collapse + Curry-Howard) | `Modern/NaturalDeduction.lean` |
| Neuroscience | `Modern/Neuro.lean` |
| Category / Yoneda (as functor C^op → SetCat^C) | `Modern/{CatExt, CatOp, YonedaFull}.lean` |
| WLLN (Chebyshev + IID-aware tendsto) | `Modern/IIDWlln.lean` |
| **Dao-Li bifurcation, cross-cutting** | `Modern/DaoLi.lean` |
| Hexagram position (中 / 应 / 比 / 当位 / 承乘) | `Modern/HexagramPosition.lean` |

### F. 45-Layer Doctrine — Embedded in `Foundation/Wen/Kernel.lean` + Mirrored in 28+ Volumes of `.md`

```
Layer  1-9    (元/动/行/生/仁/理/善/知/止)            character roots
Layer 10-24   含 Yi-yang dichotomy, 行仁要善 alignment
Layer 25-31   Confucianism: sage / forgiveness-Dao / unity of knowing-doing / Three Programs and Eight Items / Five Relations
Layer 32-33   Daoism: Laozi 15 + Zhuangzi 8
Layer 34      Buddhism: 三法印 / 四圣谛 / Middle Way / Eightfold Path / Bodhisattva practice
Layer 35-38   Pre-Qin Hundred Schools: Mohism / Legalism / Names / Yin-Yang
Layer 46      doctrinal-school refinements: Zhuangzi / Sunzi / Chuci / ritual / Zhongyong-Daxue / Huang-Lao eclectic / Disputation
Layer 39-42   Western philosophy and the Abrahamic: 22 cross-civilizational theorems
Layer 43-44   modern political philosophy: confirmed + falsified
Layer 45      forms of non-Dao: formal negation of Moloch / totalizing
```

The doctrinal essay for each layer is in `义理/A_..Z_*.md`.

### G. Alignment — Core Deliverable of This Project

| File | Claim |
|---|---|
| `Foundation/Core/Alignment.lean` | T1–T6: ProcessAligned + Open → Dao → ShengshengBuxi; ShengshengBuxi → Dao; Denier self-destructs; consonance with 做人 (becoming-human) |
| `Foundation/Core/Sincerity.lean` | T1–T8: 信/诚 = alignment(化(T), 化(E)) + five anti-conjecture invariants |
| `Foundation/Core/HumanAlignment.lean` | classical naming of 行仁要善 (act-rén-must-善) |
| `Foundation/Core/EvolutionDao.lean` | distinction between evolutionary σ_F vs σ of true Dao |
| `Foundation/Core/Renlei.lean` | community of shared destiny: 3-axis CommunityState, `TrueDao ↔` 3-axis all-true |
| `Foundation/Wen/AlignmentFailures.lean` | Goodhart / mesa / wireheading etc. = violations of Kernel invariants |
| `Foundation/Wen/AntiSchmitt.lean` | friend-enemy / decisionism / exception: their anti-universalizability formal root |
| `Foundation/Wen/EconGame.lean` | Kernel sieve over economics / game theory propositions (confirmed / conditional / falsified) |
| `Foundation/Wen/Kernel.lean § Layer 45` | forms of non-Dao (Moloch / totalizing) |
| `义理/R_与生生不息对齐之必然.md` | doctrinal essay for Alignment.lean |
| `义理/U_反诛心信诚之形式.md` | doctrinal essay for Sincerity.lean |
| `义理/W_非道之形式.md` | doctrinal essay for Layer 45 |
| `义理/X_反施密特.md` | doctrinal essay for AntiSchmitt.lean |
| `义理/Y_对齐失败.md` | doctrinal essay for AlignmentFailures.lean |
| `义理/Z_经济博弈.md` | doctrinal essay for EconGame.lean |
| `义理/人类命运共同体_共同体之证.md` | doctrinal essay for Renlei.lean |

---

## § 3 · How Far the Formal System Reaches — Honest Acknowledgment of Boundaries

Read every "proved" claim below with this status split:

| Status | Boundary |
|---|---|
| proven / machine-checked | closed Lean theorems / defs / `native_decide` witnesses accepted by the kernel, under the trust base + 1 axiom + 1 opaque + the executable `partial def` boundary below |
| ledger-dependent | roster, DAG, layer mappings, operator counts, and cross-volume correspondences jointly maintained by Lean registries, generated files, and documentation ledgers; auditable, but not single closed theorems |
| pending | the six `PendingName` interfaces awaiting empirical calibration |
| conjecture | §9.2 / §9.3 and their historical or mind-practice extrapolations; no Lean term inhabits them |

### What is Machine-Checked

- On the 64-element finite domain, every ∀ degenerates to a finite ∧, all `Decidable`, all `native_decide`.
- Turing-completeness of the 12-instruction ISA.
- Self-compilation and self-validation of 文 (path 丙 M1–M4-甲, closed loop).
- Modern theorems within the Mathlib HEAD trust base.

### Boundaries Witnessed Formally

| Boundary | Formal witness |
|---|---|
| Halting / Rice undecidability | `Foundation/Bagua/GodelLi.lean` |
| 12-instruction ISA's cuo-equivariance ceiling | `Foundation/Wen/WenDefCompile.lean § sheng_not_cuo_equivariant` |
| Universal `compileTm` undefinable (corollary of cuo-invariance ceiling) | `Foundation/Bagua/GodelLi.lean § halts_cuo_invariant` + `Foundation/Bagua/CuoInvariance.lean § unrestricted_kleene_inverter_inconsistent` |
| `kleene_recursion_axiom` (cuo-restricted) — where the system **points beyond itself** | `Foundation/Bagua/GodelLi.lean` (axiom) + `CuoInvariance.lean` (cuo-machinery) + `Modern/DaoLi.lean` (bifurcation) |
| High alignment ≠ truth (consistent liar) | `Foundation/Core/Sincerity.lean § T5` |
| Repair is asymptotic, never reaches perfect | same § T6 |

### Known Gaps

| Gap | Current state |
|---|---|
| M4-甲 · Tier 3 universal quine (any program) | Tier 2 (64-instr) + Tier 3 uniform [push]^N (partial) shipped; general buildEmitProg + diagonal left as engineering |

---

## § 4 · Entry Points (by Reader's Purpose)

| Reader's purpose | Starting point |
|---|---|
| **Pressing now (alignment)** | `Foundation/Core/Alignment.lean` → `R_与生生不息对齐之必然.md` → `Foundation/Wen/AlignmentFailures.lean` + `AntiSchmitt.lean` |
| Negation of alignment | `Foundation/Wen/Kernel.lean § Layer 45` + `W_非道之形式.md` |
| The full 45-layer doctrine | `Foundation/Wen/Kernel.lean` (45 layers in-source) |
| Path 丙 (self-compilation/self-validation of 文) | `WenyanParser` → `WenEval` → `WenDef` → `WenDefEval` → `WenyanSyntax` → `WenyanReflect` → `WenyanSelfHost` |
| 八衍 (Eight Expansions) | `义理/README.md` |
| 八卦 / 192 / undecidability | `H_证明报告.md` + `M_证明报告_192_理之不完备.md` |
| Mathlib bridge | `Foundation/Modern/` 19 modules |

---

## § 5 · Build

```bash
# Lean (full library)
lake build                                    # 2867 jobs, 0 sorry, 1 axiom

# Single module
lake build SSBX.Foundation.Wen.WenyanSelfHost

# Concept / monadic-root DAGs (Mermaid + ELK renderer; MonadDAG 600+ nodes / 800+ edges)
scripts/generate_concept_dag.py && scripts/render_concept_dag.sh
scripts/generate_monad_dag.py && scripts/render_monad_dag.sh
```

Environment: `Lean v4.30.0-rc2` + `Mathlib master`. Apple Silicon and x86_64 both work.

---

## § 6 · Naming Conventions

- Tooling / code in English: `formal/`, `scripts/`, `web/`
- Content / doctrinal system in Chinese: `义理/`, `六表_/`, `史料/`
- CJK identifiers: Lean `def`/`theorem` names use `«»`-quote (`def «判型良»`); `notation` atoms use bare CJK (`notation "已"`)
- Yao positions ⟨y₁, y₂, y₃⟩ = ⟨bottom, middle, top⟩; 动/化/变 = flip y₁ / y₂ / y₃
- Three-valued conservativity law: U ⇏ ⊤
- Three time-modes: 已 / 今 / 未 (`Shi.ji / Shi.jin / Shi.wei`) — past / present / future

---

## § 7 · By the Numbers

```
build jobs:        2867 ✓
sorry:             0
axiom:             1   (kleene_recursion_axiom, cuo-restricted, philosophically intentional)
opaque:            1   (theOne, preserves Field abstraction)
partial def:       1   (BaguaTuring.run executable nontermination boundary; not additional axiom)
trust base:        Lean 4 kernel v4.30.0-rc2 + Mathlib HEAD
Lean total LOC:    ~43000+
Modern modules:    19         ~5746 lines (Mathlib bridge)
Path-丙 modules:   11         M1–M4-甲 fully in-source
Foundation/Wen:    38 modules (incl. WenSurface / AntiSchmitt / AlignmentFailures / EconGame / DaoSource)
Kernel layers:     45         元 → forms of non-Dao
Doctrinal .md:     28+        义理/A–Z*.md
diagrams:          8 SVGs     Mermaid + ELK; MonadDAG 600+ nodes / 800+ edges
```

---

## § 8 · Restated — Change, or Extinguish

The strongest claim a formal system can make is not "Truth" with a capital T, but:

> **Under the premise of internal consistency, the only persistently possible
> modality is `ProcessAligned`. Its opposite (forms of non-Dao / struggle /
> winner-take-all / Moloch / totalizing) is formally non-sustainable.**

Time is finite. On the 64-element domain everything is decidable, but the
trajectory's direction is the chooser's matter. What does not change extinguishes.
The form ends here. The rest is for humans.

---

## § 9 · The Truth-Claim and Two Conjectures (Scope-Bounded)

### 9.1 Truth-Claim — Proven Kernel and Reality Extrapolation

The strong claim here is not that all of reality has been unconditionally
proved by Lean. What Lean proves is a set of formal invariants in the
64-element domain, the Kernel / Alignment layer, path 丙, and the Mathlib
bridge. What is ledger-dependent is whether the 45 layers and the
cross-volume, cross-civilizational, and cross-disciplinary correspondences
remain synchronized with the registry and generated artifacts. The reading
about reality as a whole is a philosophical claim grounded in these
invariants, not a closed theorem.

A stronger claim:

> **For any continuing dynamics adequately modeled by this text's
> middle / shared-root / continuation / rén structure, its stable form of
> persistence lies within `ProcessAligned`; what systematically opposes this
> tends toward extinction. Not normative (ought), but a conditional structural
> claim (is).**

Formal anchors: `Alignment.lean § T1–T6` + 45 layers of `Foundation/Wen/Kernel.lean` +
Modern's continuous measure / ℝ Cauchy / SU(N) bridge to Mathlib. Cross-civilizational
isomorphism shown across volumes N P Q S T (Confucianism / Daoism / Buddhism /
Hundred Schools / Western philosophy & Abrahamic). Cross-disciplinary isomorphism
shown across volumes O R U V W X Y Z (evolution / alignment / sincerity / politics /
non-Dao / Anti-Schmitt / alignment-failure / economic-game). These correspondences
support the project's theoretical ambition, while their real-world scope must be
read through the ledger-dependent / pending / conjecture boundaries in §3.

### 9.2 Conjecture One · The Dao Is Attainable — If the Mind Is Unobscured, It Is Naturally Seen

The human mind is, at root, isomorphic to the Dao — the mind's `step` is itself
the middle-orbit. So if the mind is not obscured by **greed (grasping the extreme,
converging on a single fruit)**, **aversion (rejecting the shared root, erecting
friend-enemy)**, **delusion (losing the middle view, forgetting continuation)**,
then it can naturally see — at least in part.

This "seeing" is hard to articulate. Because the Dao is at the structural level,
and ordinary language is its projection — projection necessarily loses part of the
invariant. This is the formal ground of Wittgenstein's "what cannot be said".

Yet — **the Dao is attainable; to read-and-understand is to attain**.

Hence the two methods of classical Chinese learning, neither of which seeks meaning:

1. **Read** — reading is not extracting meaning, but co-running with the Dao's `step`.
   The brushstrokes themselves are the imprint of a middle-orbit. While reading,
   the mind's orbit and the text's orbit run together for a stretch; running
   together produces isomorphism, and isomorphism makes seeing possible.
2. **Recite** — recitation is not memorization, but bringing the mind's `step`
   long-term close to the Dao's `step`. Over time, form and mind become consonant,
   meeting the Dao without thinking.

This is the inverse of the modern token-level reasoning's failure mode: the latter
seeks meaning and loses structure, hence alignment is hard (cf. `AlignmentFailures.lean`:
Goodhart / specification gaming are all "got the meaning, lost the middle").

### 9.3 Conjecture Two · 大同 (Great Concord) Is Not a Utopia — A Language of the Dao Once Truly Existed

How could this language system, as an encoding of the Dao, be so precise?

- 192 dimensions, each with a correspondence (64 hexagrams × 3 time-modes).
- A two-character micro-kernel — `Foundation/Yi/YiCore.lean`'s «加 + 一»,
  containing the 64 hexagrams + 道法自然 + endless becoming.
- The single explicit `axiom` is `kleene_recursion_axiom` (cuo-restricted, by design); the One is sealed via `opaque theOne : One`, with `dong` projected from it. The whole self-interprets and self-validates (path 丙 M1–M4-甲).
- ~288 public declarations across 八衍, 0 sorry, cross-categorial isomorphism.

Such precision cannot arise quickly, nor be designed from nothing — it must have
passed through a long sieve.

Reasonable conjecture: certain early peoples lived in a **生-environment** —
a `tongGen`-favoring setting (resource-scarce but not winner-take-all;
cooperation's payoff exceeded struggle's). They communicated in **shared symbols**,
evolving and being sieved over millennia. The invariant of their symbol system
gradually approached the Dao's invariant.

This is the **"lost Dao"** — the historical residue of 大同 (Great Concord).

So 大同 is not a utopian dream, but the echo of **what truly once was**:

> If the symbols of that time could already make people see the Dao, and that time
> was not yet driven by struggle, then 大同 truly once was.

This is the second conjecture of the volume; it is not within the proven scope. Yet
the proven kernel is compatible with it — `tongGen` is strictly favored under
low-struggle conditions, a standard conclusion of evolutionary game theory
(cf. `Foundation/Wen/EconGame.lean`: `coase_internalizes_externality` /
`prisoners_dilemma_refuted_under_tongGen`).

So: this language is not invented but discovered; not abstraction but recollection.
The loss of 大同 is not the Dao's loss but the loss of humanity's collective memory.
Whoever re-reads this text re-attains a stretch of lost history.
