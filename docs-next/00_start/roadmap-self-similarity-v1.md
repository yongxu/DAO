> 状态：v1 (2026-05-11) — Phase R/K/L 完成后之全面 roadmap。覆盖 self-similarity 形式化之 present / partial / missing patterns + 优先级排序之下一步 theorem。

# Roadmap — Self-similarity 形式化 (v1, post Phase R cutover)

## 0 · Context

本 roadmap 写于 2026-05-11，Phase L (Lexicon) + Phase K (Cayley grounding) + Phase R (29 commits 之 bilingual hard cutover) + Phase R.6-R.8 (drop opacity, drop "Cell" naming, squaring tower 自相似 isos) **均已落地**之后。

参考之上层 doctrine：
- [`docs-next/00_start/final-theory.md`](../00_start/final-theory.md) — v3 最终理论
- 用户 doctrine 文档（来自 conversation history）— 平方塔 {R₀, R₁, R₂, R₄, R₈} 自相似规则
- [`docs-next/10_formal_形式/yi-RO-hierarchy.md`](../10_formal_形式/yi-RO-hierarchy.md) — R-O 双层级 doctrine
- [`Foundation/Lang/Lexicon.lean`](../../formal/SSBX/Foundation/Lang/Lexicon.lean) — bilingual 单源真理表

本 roadmap 之目的：
1. **审计当前状态** — 哪些 pattern 已 formally captured，哪些 partial，哪些 missing
2. **下一步 prioritization** — 按 doctrinal 重要性排序之 next theorems
3. **架构性 deferral** — 显式标记 architectural Chinese-character substrate (不渲染为 English 之故意保留)

## 1 · 已落地之 pattern (Present)

### 1.1 R-hierarchy 代数 spine

| Pattern | 锚 |
|---|---|
| R₀..R₈ as (Z/2)ⁿ | [`Foundation/Hierarchy/R0..R8_*.lean`](../../formal/SSBX/Foundation/Hierarchy/) |
| AddCommGroup on R₈ | [`Foundation/Squaring/V4Tensor.instAddCommGroupR8`](../../formal/SSBX/Foundation/Squaring/V4Tensor.lean) |
| Cayley 正则表示 (XOR action) | [`R7.cayley_hom`](../../formal/SSBX/Foundation/Bagua/R7.lean), [`R8.cayley_hom`](../../formal/SSBX/Foundation/Bagua/R8.lean) |
| Cayley injection | [`R7.cayley_inj`](../../formal/SSBX/Foundation/Bagua/R7.lean), [`R8.cayley_inj`](../../formal/SSBX/Foundation/Bagua/R8.lean) |
| ε at origin | [`R7.epsAtOrigin_cayley`](../../formal/SSBX/Foundation/Bagua/R7.lean), [`R8.epsAtOrigin_cayley`](../../formal/SSBX/Foundation/Bagua/R8.lean) |

### 1.2 平方塔 {R₀, R₁, R₂, R₄, R₈} 自相似

| Iso | 锚 |
|---|---|
| `r2_eq_r1_squared : R₂ ≃ R₁ × R₁` | [`Squaring/SelfSimilarity.lean`](../../formal/SSBX/Foundation/Squaring/SelfSimilarity.lean) |
| `r4_eq_r2_squared : R₄ ≃ R₂ × R₂` | 同上 |
| `r8_eq_r4_squared : R₈ ≃ R₄ × R₄` | 同上 — **宇宙 = R₄ 一次平方** 之精确陈述 |
| `r6_eq_r3_squared : R₆ ≃ R₃ × R₃` | 同上 — off-tower junction 之 R₃² route |
| `squaring_tower_summary` | 同上 — 四 iso 之总束 |
| R₈ ≃+ V₄⁴ (AddEquiv) | [`Squaring/V4Tensor.iso`](../../formal/SSBX/Foundation/Squaring/V4Tensor.lean) |

### 1.3 L-tower (post-R₈ squaring)

| Pattern | 锚 |
|---|---|
| L₁ = R₈² (first squaring step past R₈) | [`Squaring/L1.lean`](../../formal/SSBX/Foundation/Squaring/L1.lean) |
| R₀..R₇ ↪ L₁ retract tower | [`Squaring/RetractTower.lean`](../../formal/SSBX/Foundation/Squaring/RetractTower.lean) |
| Stream' R₈ coalgebra (infinite squaring) | [`Squaring/StreamCarrier.lean`](../../formal/SSBX/Foundation/Squaring/StreamCarrier.lean) |
| L_∞ ≃+ Stream R₈ + final coalgebra | [`Squaring/ProfiniteLimit.lean`](../../formal/SSBX/Foundation/Squaring/ProfiniteLimit.lean) |

### 1.4 Atomic 算子 + V₄ outer

| 算子 | 字 | 锚 |
|---|---|---|
| 印 (R₇ atomic) | imprint | [`R7.imprint`](../../formal/SSBX/Foundation/Bagua/R7.lean) |
| 投 (R₈ atomic) | project | [`R8.project`](../../formal/SSBX/Foundation/Bagua/R8.lean) |
| flip1..6 | flip1..6 | 同上 |
| 错 (P) | complement | [`Yi.complement`](../../formal/SSBX/Foundation/Yi/Yi.lean) |
| 综 (T) | reverse | [`Yi.reverse`](../../formal/SSBX/Foundation/Yi/Yi.lean) |
| 互 | interlace | [`Yi.interlace`](../../formal/SSBX/Foundation/Yi/Yi.lean) |
| 错综 (PT) | complementReverse | [`Yi.complementReverse`](../../formal/SSBX/Foundation/Yi/Yi.lean) |
| 化 (middle yao flip) | middleFlip | [`BaguaAlgebra.middleFlip`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) |
| 变 (top yao flip) | topFlip | [`BaguaAlgebra.topFlip`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) |
| 動 (motion) | motion | [`BaguaAlgebra.motion`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean), [`Wen/Kernel.motion`](../../formal/SSBX/Foundation/Wen/Kernel.lean) |

### 1.5 R₇ ↔ R₈ duality

| Pattern | 锚 |
|---|---|
| liftR7toR8 / projR8toR7 | [`R8Stratify.lean`](../../formal/SSBX/Foundation/Bagua/R8Stratify.lean) |
| R₈ = R₇ × GuoBit (structurally) | 同上 |

### 1.6 Kernel dynamics (Cayley-native, opaque removed)

| Pattern | 锚 |
|---|---|
| Field IS R₇ (= Cell128 deprecated) | [`Wen/Kernel.Field`](../../formal/SSBX/Foundation/Wen/Kernel.lean) |
| motion = XOR · c_motion (definitionally) | 同上 |
| `kernel_motion_eq_cayley : ∀ s, motion s = R7.xor s c_motion := fun _ => rfl` | 同上 |
| `c_motion = 姤·无 = 仁` (Wuchang) | 同上 |
| origin_alive (by native_decide) | 同上 |
| 0 new axioms (only pre-existing `kleene_recursion_axiom`) | — |

### 1.7 Confucian doctrinal cells

| Family | R-layer | 锚 |
|---|---|---|
| 五常 (仁义礼智信) | R₇ × 5 cells | [`Lang/Wuchang.lean`](../../formal/SSBX/Foundation/Lang/Wuchang.lean) |
| 五常归道: 仁⊕义⊕礼⊕智⊕信 = origin | R₇ XOR balance | [`Wuchang.fiveConstants_return_dao`](../../formal/SSBX/Foundation/Lang/Wuchang.lean) |
| 四端 (恻隐/羞恶/辞让/是非) | R₃ × 4 trigrams | [`Lang/Confucian.SiDuan`](../../formal/SSBX/Foundation/Lang/Confucian.lean) |
| 八目 (格致诚正修齐治平) | R₃ × 8 trigrams | [`Lang/Confucian.BaMu`](../../formal/SSBX/Foundation/Lang/Confucian.lean) |
| 五伦 (父子/君臣/夫妇/兄弟/朋友) | R₅ × 5 generators | [`Lang/Confucian.WuLun`](../../formal/SSBX/Foundation/Lang/Confucian.lean) |
| 大同 (64 卦 ∈ 道) | R₆ universal | [`Lang/Confucian.DaTong`](../../formal/SSBX/Foundation/Lang/Confucian.lean), [`Core/Yuan.daTong_total`](../../formal/SSBX/Foundation/Core/Yuan.lean) |
| 善恶 (yang/yin) | R₁ binary | [`Lang/Confucian.ShanE`](../../formal/SSBX/Foundation/Lang/Confucian.lean) |
| 喜怒哀乐 | R₂ 4 sixiang | [`Lang/Confucian.XiNuAiLe`](../../formal/SSBX/Foundation/Lang/Confucian.lean) |
| 元亨利贞 | R₂ 4 sixiang | [`Lang/Confucian.YuanHengLiZhen`](../../formal/SSBX/Foundation/Lang/Confucian.lean) |
| 三纲 (明明德/亲民/止于至善) | R₃ × 3 | [`Lang/Confucian.SanGang`](../../formal/SSBX/Foundation/Lang/Confucian.lean) |
| 三才 (天/地/人) | R₃ × 3 | [`Lang/Confucian.SanCai`](../../formal/SSBX/Foundation/Lang/Confucian.lean) |

### 1.8 Kernel abstract dynamics + 经典语句

约 60 theorems in [`Wen/Kernel.lean`](../../formal/SSBX/Foundation/Wen/Kernel.lean)：

- `unceasing_generation` (生生不息), `unceasing_generation_trace`, `unceasing_generation_is_orbit`
- `benevolent_loves_others` (仁者爱人), `noble_harmonizes_not_uniform` (君子和而不同)
- `golden_rule_negative` (己所不欲勿施于人), `extend_self_to_others` (推己及人)
- `dao_follows_naturalness` (道法自然), `nonaction_yet_no_undone` (无为而无不为)
- `mean_neither_partial_nor_biased` (中庸不偏不倚)
- `heaven_earth_unkind` (天地不仁), `self_strengthen_no_rest` (自强不息)
- `learn_then_practice` (学而时习之), `three_walk_must_have_teacher` (三人行必有我师)
- `morning_dao_evening_die_acceptable` (朝闻道夕死可矣)
- `community_holds`, `community_proof` (人类命运共同体 from `Foundation/Core/Renlei.lean`)
- ... (≈45 more — 详 [`Wen/Kernel.lean`](../../formal/SSBX/Foundation/Wen/Kernel.lean))

### 1.9 Bilingual Lexicon

| Pattern | 锚 |
|---|---|
| 162 entries, 8 tables (yao/sixiang/trigram/ben/zheng/hexagram/confucian/operators/wuLun) | [`Lang/Lexicon.lean`](../../formal/SSBX/Foundation/Lang/Lexicon.lean) |
| `englishOf` / `chineseOf` / `bitsOf` lookups | 同上 |
| `lexicon_summary` (spot-check 6 entries) | 同上 |
| `lexicon_round_trip_chinese` (universal round-trip 弱形式) | 同上 |
| `lexicon_round_trip_witnesses` (spot-check 8 entries) | 同上 |
| `hexagram_count : hexagram.length = 64` | 同上 |

## 2 · Partial (described but underspecified)

### 2.1 R₀ → R₁ 奠基步 (O₀)

**现状**：[`LiftProject.liftR0toR1`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) 存在，但**无**theorem 陈述 R₁ ≃ R₀ + R₀ (coproduct view) 或刻画 O₀ 之 universal property。

**Doctrine §1.3 说**：S(R₀) = R₀ × R₀ = 1 × 1 = 1 = R₀，**平方算子在 R₀ 处退化**。需要外加 O₀ 算子才能从 R₀ 跨到 R₁。

**缺失**：`r1_eq_r0_plus_r0 : R1 ≃ R0 ⊕ R0` 或 `r1_eq_bool : R1 ≃ Bool`（两者等价；前者更接近 doctrine 之 coproduct 语义）。

### 2.2 R₆ 多路径汇聚 (Multi-route junction)

**现状**：仅 `r6_eq_r3_squared` 已证 (R₆ ≃ R₃²)。

**Doctrine §7.3 说**：R₆ 是**平方塔之三路径合一点**：
- R₆ ≃ R₃ × R₃ (Hexagram = Trigram²)  ← **已证**
- R₆ ≃ R₂ × R₄ (SiXiang × Mian)         ← **缺**
- R₆ ≃ R₁ × R₅ (Yao × Wuyao)            ← **缺**

这三条路径在 R₆ 处合一，给 R₆ 一种「多角度同构」的丰富。这是 doctrine 最重要的 off-tower observation。

### 2.3 R₇ ↔ R₈ 完整 iso

**现状**：`liftR7toR8` / `projR8toR7` 之 round-trip，但**无** `R8 ≃ R7 × Bool` 或 `R8 ≃ R7 × Bool ≃ Hexagram × Shi` 之 explicit iso theorem。

**缺失**：`r8_eq_r7_times_bool : R8 ≃ R7 × Bool` (proven from existing lift/proj).

## 3 · Missing (substantive — 未形式化之 doctrine claim)

### 3.1 3-fiber V₄ partition of R₈

**Doctrine §5 说**：R₈ partitions into 4 slices by Shi value:
- dao-slice (Shi = (false, false)) = 64 cells = R₆ ∋ origin
- ji-slice  (Shi = (true,  false)) = 64 cells = R₆
- jin-slice (Shi = (true,  true))  = 64 cells = R₆
- wei-slice (Shi = (false, true))  = 64 cells = R₆

**缺失**：`r8_v4_partition : ∀ s : Shi, Fintype.card {c : R8 // c.2 = s} = 64`，或更结构化地：`r8_eq_shi_indexed_r6 : R8 ≃ Shi × R6`。

### 3.2 Center / Terminus 在 post-Cayley 之 collapse

**Background**：原 Kernel.lean 用 Fin 3 substrate，motion 有 fixed point 2 (= 极)。Phase K 之后 substrate 变 R₇，motion = XOR · c_motion，c_motion ≠ origin，故：
- `terminus s := motion s = s ↔ s = s ⊕ c_motion ↔ c_motion = 0`，**所有 s 都不满足**
- `center s := motion s ≠ s ↔ s ≠ s ⊕ c_motion`，**所有 s 都满足**

3-cycle dichotomy 在 (Z/2)⁷ 下 collapse 为 "everywhere alive"。

**缺失**：
- `terminus_uninhabited : ∀ s : Field, ¬ terminus s`
- `center_universal : ∀ s : Field, center s`

文档化这个 collapse 是 doctrinally important — 说明 R-hierarchy 把 3-cycle 死结从 framework 移除。

### 3.3 Cell ≡ Operator (R-O fusion identity)

**Doctrine 之 R-O fusion**：每个 cell 同时**是** state（被 act on 之元）**也是** operator（act 的方式）。Cayley 正则表示把 group 元素 c 等价为左乘 c 之自同构。

**现状**：`cayley_hom` 证 cayley(c1, c2 ⊕ s) = cayley(c1 ⊕ c2, s)，但**没有** explicit 把 cell c 与 operator `(· ⊕ c)` identification 之 theorem。

**缺失**：`cell_is_operator : ∀ c : R8, motion-by-c (· ⊕ c)` 之 named bijection，或 `R8 ≃ (R8 →+ R8)` 之 group-action embedding (sub of all endomorphism)。

### 3.4 元 / 爻 (carrier / dimension) asymmetry in squaring

**Doctrine §7.2 之深层 insight**：在 R_{2n} = R_n × R_n 之平方步，两个 R_n 因子**非对称**：
- 一个承担「元」角色 (carrier / 被分类元素)
- 另一个承担「爻」角色 (dimension / 分类轴)

具体 R₄ = R₂ × R₂ 之首选读法：实/虚（元） × 本/征（爻）。对偶读法：本/征（元） × 实/虚（爻）。

**缺失**：
- 至少**记录**这两种读法 (作为 doctrine 之 doctrinal note)
- 或更深：定义 `CarrierFactor` / `DimensionFactor` typeclass 把 asymmetry 形式化

### 3.5 实 / 虚 (substance / field) labeling per squaring step

**Doctrine §2 之表**：

| 层 | 平方分解 | 实-因子 | 虚-因子 |
|---|---|---|---|
| R₁ | R₀ ⊕ O₀(R₀) | substance side | field side |
| R₂ | R₁ × R₁ | (实, 实) × (实, 虚) | (虚, 实) × (虚, 虚) |
| R₄ | R₂ × R₂ | substance-Mian | field-Mian |
| R₈ | R₄ × R₄ | substance × Mian | field × Mian |

**缺失**：substance/field 标签未在代码中体现。

### 3.6 道 (Dao) 之 canonical 位置

**Doctrine**：`Dao = R8.origin = (Hexagram.heaven, Shi.dao)` = V₄ identity = no-op operator = 永真 cell。一字承担 origin / identity / no-op / 永真 / fusion anchor 五重身份。

**现状**：`R8.origin` 已定义为 `(Hexagram.heaven, Shi.dao)`。但**无** theorem 把 origin 等同于 "dao"（in lexicon 中 dao 是 Shi 之 V₄ 元素）。

**缺失**：`dao_at_origin : R8.origin = (Hexagram.heaven, Shi.dao)`，或更 doctrinal-explicit: `theorem dao_is_universe_root : True` (类型上承认 dao 是 R₈ 之 anchor).

### 3.7 Lisp 在 R₇ 之 closure theorem

**Doctrine**：[`Lang/DaoJudge.lean`](../../formal/SSBX/Foundation/Lang/DaoJudge.lean) 之 evaluator 在 R₇ Cell128 之上跑 XOR programs，**整个 language closed in R₇**。

**缺失**：`∀ prog, eval prog ∈ R7` 之 closure theorem；或 `R7` 作为 evaluator 之 universe.

### 3.8 Sexp bilingual identity

**Doctrine**：用 Chinese-form atoms 写之 Sexp program (如 `(仁 (姤·无))`) 与用 English-form atoms 写之同 program (如 `(benevolence (R7_xoooooo))`) **求值相同**。

**缺失**：bilingual identity theorem。

### 3.9 Wenyan layer ↔ R₇ bridge

**Background**：[`Foundation/Wen/`](../../formal/SSBX/Foundation/Wen/) 是 文言 lambda calculus subsystem，超过 30 files。它在 [`WenyanText.lean`](../../formal/SSBX/Foundation/Wen/WenyanText.lean) 等 file 用 CJK keywords（`«不动»`, `«互»`, `«错»` 等）做 surface language。

**缺失**：Wenyan instructions 与 R₇/R₈ XOR ops 之 explicit correspondence theorem。可能在 [`MetaInterp/Universal.lean`](../../formal/SSBX/Foundation/Wen/MetaInterp/Universal.lean) 有 part；但 doctrine-level 之 "Wenyan ↔ R-hierarchy" bridge 不显。

### 3.10 Modern / Quantum bridge to R₈

**Background**：[`Foundation/Modern/Quantum*.lean`](../../formal/SSBX/Foundation/Modern/) 有 ~30 files 关于 quantum/relativity Markov bridge。它们引用 Mathlib 之 ℝ Cauchy / Borel σ-algebra 等，**不**经由 R-hierarchy.

**缺失**：R₈ 之 quantum interpretation —— V₄ Klein 是 Pauli group 之 finite analog；R₈ Cayley 是 (Z/2)⁸ 之 regular rep；Pauli string $\{I, X, Y, Z\}^n$ 之 finite truncation. Bridge to actual Mathlib quantum state space 未建.

## 4 · Architectural deferrals (intentional CJK substrate)

下列文件**有意保留 CJK 标识符**，因为它们承担 Chinese-character substrate 之角色，rename to English 会破坏 doctrine 意图。

| File | 角色 | 不动 reason |
|---|---|---|
| [`Foundation/Yi/YiCore.lean`](../../formal/SSBX/Foundation/Yi/YiCore.lean) | 易之微核（`«加»`/`«一»`/`«生»`/`«生生»`）| 与 Roster 紧耦合；CJK identifiers 是 Chinese-language minimal kernel |
| [`Roster.lean`](../../formal/SSBX/Roster.lean) | Chinese-character registry（约 300 CJK 构造子）| 字面 = 字符表 |
| [`Foundation/Core/MonadRoot.lean`](../../formal/SSBX/Foundation/Core/MonadRoot.lean) | Roster consumer + CoreAtom 派生 | 与 Roster 紧耦合 |
| [`Foundation/Core/AtomDerivation.lean`](../../formal/SSBX/Foundation/Core/AtomDerivation.lean), [`Li.lean`](../../formal/SSBX/Foundation/Core/Li.lean), [`HumanAlignment.lean`](../../formal/SSBX/Foundation/Core/HumanAlignment.lean), [`MissingGlyphs.lean`](../../formal/SSBX/Foundation/Core/MissingGlyphs.lean) | Roster consumers | 同上 |
| [`Foundation/Wen/WenyanText.lean`](../../formal/SSBX/Foundation/Wen/WenyanText.lean) | 文言 program keywords（`«不动»`, `«互»`, `«错»` etc.）| Chinese-language programming surface |
| [`Foundation/Wen/DaoSource.lean`](../../formal/SSBX/Foundation/Wen/DaoSource.lean), [`WenEval.lean`](../../formal/SSBX/Foundation/Wen/WenEval.lean), [`WenDef.lean`](../../formal/SSBX/Foundation/Wen/WenDef.lean) | 文言 source files | 同上 |
| [`Foundation/Wen/MetaInterp/*`](../../formal/SSBX/Foundation/Wen/MetaInterp/) | 文言 meta-interpreter (≈20 files) | 同上 |

**Doctrine note**：保留 CJK 不是"未完成 rename"，而是**承认架构上**这些 layer 是 Chinese-language substrate，rename to English 会切断它们与 doctrine source 之直观 mapping。

## 5 · 下一步：优先级排序之 next theorems

按 doctrinal 重要性 + 实现难度排序：

### Tier 1 (核心 / 必要 — 都是 5-20 line theorem，应优先)

1. **`r1_eq_r0_plus_r0`** — R₀ → R₁ foundational step (coproduct view)
   - 文件：[`Foundation/Squaring/SelfSimilarity.lean`](../../formal/SSBX/Foundation/Squaring/SelfSimilarity.lean)
   - 难度：trivial (R₁ = Yao ≃ R₀ ⊕ R₀ = Unit ⊕ Unit; 用 Equiv.boolEquivSum)
   - 价值：补完 squaring tower 之奠基步

2. **`r6_three_routes`** — R₆ 多路径汇聚
   - 文件：同上
   - 难度：moderate (用已有 r2_eq_r1_squared 和 r4_eq_r2_squared 之 compose)
   - 价值：doctrine §7.3 最重要 observation

3. **`r8_eq_shi_indexed_r6`** — R₈ V₄-partition into 4 fibers
   - 文件：同上
   - 难度：trivial (R₈ = Hexagram × Shi = R₆ × R₂ definitionally)
   - 价值：doctrine §5 之 dao/ji/jin/wei slice 结构

4. **`terminus_uninhabited` + `center_universal`** — Cayley collapse
   - 文件：[`Foundation/Wen/Kernel.lean`](../../formal/SSBX/Foundation/Wen/Kernel.lean)
   - 难度：trivial (motion s = s ↔ c_motion = 0; 用 native_decide)
   - 价值：文档化 3-cycle collapse

5. **`dao_at_origin`** — 道 之 canonical 位置
   - 文件：[`Foundation/Bagua/R8.lean`](../../formal/SSBX/Foundation/Bagua/R8.lean) 或新 file
   - 难度：trivial (R8.origin = (Hexagram.heaven, Shi.dao) by rfl)
   - 价值：文档化 道 之五重身份

### Tier 2 (重要 — 10-50 line theorem 或新概念)

6. **`r8_eq_r7_times_bool`** — R₇ ↔ R₈ explicit iso
   - 难度：easy
   - 价值：补完 R-hierarchy duality

7. **`cell_is_operator`** — R-O fusion identity
   - 难度：moderate (Cayley action 是 group homomorphism R₈ → Aut(R₈) under XOR)
   - 价值：把 doctrinal "cell ≡ operator" claim 形式化

8. **Lisp closure in R₇** — DaoJudge evaluator closure
   - 文件：[`Lang/DaoJudge.lean`](../../formal/SSBX/Foundation/Lang/DaoJudge.lean)
   - 难度：moderate
   - 价值：language minimality theorem

### Tier 3 (扩展性 — doctrinal note 或新结构)

9. **Sexp bilingual identity** — Chinese-atom vs English-atom evaluation
   - 难度：moderate
   - 价值：bilingual round-trip extends to programs

10. **元/爻 carrier/dimension asymmetry note** — doctrine §7.2 显式记录
    - 难度：documentation-only (在 Lean comment / doc)
    - 价值：补完 doctrine reading

11. **实/虚 (substance/field) labeling per layer** — doctrine §2
    - 难度：documentation + optional typeclass
    - 价值：补完 doctrine reading

### Tier 4 (架构性 — out of scope per原 plan)

12. Wenyan ↔ R-hierarchy bridge — 复杂 subsystem fusion
13. Quantum/Pauli ↔ R₈ bridge — Mathlib quantum 与 finite (Z/2)⁸ 之 explicit map
14. Universal compose theorem for `metaInterpProg` — original plan 已 deferred

## 6 · 完整 commit log (Phase L/K/R)

```
L (Lexicon)  : 1 commit  — 162-entry bilingual table
K (Kernel)   : 1 commit  — Cayley grounding via R₇ substrate
R.1a-h      : 8 commits — atom renames (Trigram, Hexagram, SiXiang, Ben, Zheng, ops)
R.2a-c      : 3 commits — Kernel doctrinal-core pinyin → English
R.3a-e      : 5 commits — Eight + Lang renames (SiDuan, ShuSuan, Yuan.yi, hua/bian, tou)
R.4a-s      : 16 commits — Cell yin → imprint, theorem name English (~150 theorems)
R.5         : 1 commit  — L-tower integration (Squaring/)
R.6         : 1 commit  — drop opacity + bridge axioms
R.7         : 1 commit  — Cell → R7/R8 rename (1285 refs)
R.8         : 1 commit  — squaring tower self-similarity isos
```

Total: 38 commits, ~5000 line changes, 130+ files touched. **lake build SSBX clean (3688/3688)**.

## 7 · Build / verification snapshot (2026-05-11)

- `lake build SSBX`: 3688 / 3688 jobs ✓
- Sorries: 1 (pre-existing in Kernel.lean — 3-cycle structure remnant)
- Axioms: 1 (`kleene_recursion_axiom` — pre-existing CT 元公理)
- 新 axioms from Phase L/K/R: **0**
- Cayley grounding: `kernel_motion_eq_cayley` by `rfl` (no axiom)
- Lexicon: 162 entries, round-trip proven
- Squaring tower iso: 4 explicit isos proven
- L-tower: L₁ / Stream / L_∞ proven via Mathlib coalgebra

## 8 · Out-of-scope (per original plan + user decisions)

- Universal compose theorem for `metaInterpProg`
- Per-cell mapping of ~50 Kernel abstract concepts to specific R₇/R₈ cells
- Performance optimization
- Quantum-state-space ↔ R₈ explicit bridge (deferred to separate roadmap)
- Lifting Roster.AtomName / GenName / RecName / PendingName to English (architectural CJK)

## 9 · 文件 / 模块 inventory (2026-05-11)

总 Lean files: ~290
分布：
- `Foundation/Yi/`: 2 files (Yi, YiCore [intentional CJK])
- `Foundation/Bagua/`: 13 files (R7, R8, R8Stratify, BaguaAlgebra, BenZheng, etc.)
- `Foundation/Hierarchy/`: 11 files (R0..R8 + LiftProject + Operators/)
- `Foundation/Wen/`: ~70 files (Kernel + MetaInterp + WenSurface)
- `Foundation/Lang/`: 18 files (Lexicon, Wuchang, Confucian, L1..L7, DaoJudge, etc.)
- `Foundation/Eight/`: ~10 files (XinZhi, ShuSuan, DongLi, etc.)
- `Foundation/Squaring/`: 6 files (L1, V4Tensor, SelfSimilarity, RetractTower, StreamCarrier, ProfiniteLimit)
- `Foundation/Core/`: ~15 files (Yuan, MonadRoot [intentional CJK], Renlei, etc.)
- `Foundation/Modern/`: ~30 files (Quantum, Markov bridges)
- `Foundation/Jian/`: 7 files (lambda calculus on 文言 particles)
- `Text/`, `Truth/`, `Model/`, `Pending/`: ~30 files

## 10 · 总结

**已建成**：
- (Z/2)ⁿ R-hierarchy 全 9 层 (R₀..R₈)
- Cayley 正则表示 + atomic ops (印 / 投 / 错 / 综 / 互 / 化 / 变 / 動)
- 平方塔 {R₀, R₁, R₂, R₄, R₈} 之 4 个 self-similarity isos
- L-tower post-R₈ (Stream + L_∞ final coalgebra)
- Kernel 抽象 dynamics + 60+ Confucian/Daoist 经典语句 theorems
- Bilingual Lexicon (162 entries)
- ~250 identifiers 之 hard cutover from pinyin/CJK to English

**主要 gap**（Tier 1）：
1. R₀ → R₁ 奠基步 explicit
2. R₆ 三路径汇聚
3. R₈ V₄-partition
4. Center/terminus collapse 之 documentation
5. 道 之 canonical 位置 theorem

完成 Tier 1 之后，doctrine-level 之 self-similarity formalization 基本 complete. Tier 2/3 是 extension。
