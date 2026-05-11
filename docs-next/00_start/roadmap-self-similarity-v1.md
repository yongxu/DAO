> 状态：v1.3 (2026-05-11) — Phase R/K/L 后之 self-similarity roadmap 已完成一轮形式补齐；F.7c.2 闭合 zero-step/prologue compose，并把 Strategy-B fixed-parameter boundary machineChecked；full arbitrary-program universal compose 仍 pending。

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

v1.1 本轮完成项：
- `SelfSimilarity.lean` 补齐 R₁ 奠基步、R₆ 三路汇聚、R₈ ≃ R₇ × Bool。
- `V4Tensor.lean` 补齐 R₈ = R₆ × trace bit × projection bit、temporal-state-indexed R₆ slices、每个 temporal-state fiber = 64、Way (道) origin/no-op、cell-as-operator。
- `Kernel.lean` / `DaoJudge.lean` 补齐 post-Cayley collapse、R₇ Lisp closure、concrete bilingual identity。
- 新增 `ClassicalTextRHierarchyBridge.lean` 与 `QuantumR8Bridge.lean`，只证明 direct typed skeleton；Quantum 桥已含有限函数空间 `R8 → ℂ` 与 faithful regular translation，但不宣称 physical Pauli-string / unitary semantics 已完成。
- `MetaInterp/Assembly.lean` 已有 base-256 concrete dispatch/assembly structural summary；`MetaInterp/Universal.lean` 已证明 embedded prologue U.0a、zero-step/prologue compose，并把 U.0 改成 exact-fuel no-sorry composition from explicit loop/padding semantic obligations。
- `MetaInterp/Universal.lean` 新增 `SemanticLoopObligations`、`semantic_loop_obligation_frontier_summary`、`metaInterpProg_meta_halted_padding`、`StrategyBCompatibleProgram` 与 `universal_compose_current_boundary_summary`；`Fetch.lean` 新增 pc=0 scaffold 的 exact dispatch route theorem；`FetchProg.lean` 暴露 halted/running peel-witness route 的 exact-fuel theorem。这只是 F.7c.4 incremental frontier，不宣称 concrete U.1/U.2/U.3 witnesses 或 full arbitrary-program simulation 已完成。

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
| `r1_eq_r0_plus_r0 : R₁ ≃ R₀ ⊕ R₀` | 同上 — O₀ foundational split |
| `r4_eq_r2_squared : R₄ ≃ R₂ × R₂` | 同上 |
| `r8_eq_r4_squared : R₈ ≃ R₄ × R₄` | 同上 — **宇宙 = R₄ 一次平方** 之精确陈述 |
| `r6_eq_r3_squared : R₆ ≃ R₃ × R₃` | 同上 — off-tower junction 之 R₃² route |
| `r6_eq_r2_times_r4 : R₆ ≃ R₂ × R₄` | 同上 — off-tower junction 之 R₂×R₄ route |
| `r6_eq_r1_times_r5 : R₆ ≃ R₁ × R₅` | 同上 — off-tower junction 之 R₁×R₅ route |
| `r8_eq_r7_times_bool : R₈ ≃ R₇ × Bool` | 同上 — R₇/R₈ explicit split |
| `squaring_tower_summary` | 同上 — 四 iso 之总束 |
| `self_similarity_gap_summary` | 同上 — v1 §2 gap bundle |
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
| R₈ = R₇ × projection bit (explicit iso) | [`SelfSimilarity.r8_eq_r7_times_bool`](../../formal/SSBX/Foundation/Squaring/SelfSimilarity.lean) |

### 1.6 Kernel dynamics (Cayley-native, opaque removed)

| Pattern | 锚 |
|---|---|
| Field IS R₇ (= Cell128 deprecated) | [`Wen/Kernel.Field`](../../formal/SSBX/Foundation/Wen/Kernel.lean) |
| motion = XOR · c_motion (definitionally) | 同上 |
| `kernel_motion_eq_cayley : ∀ s, motion s = R7.xor s c_motion := fun _ => rfl` | 同上 |
| `terminus_uninhabited` / `center_universal` | 同上 — post-Cayley fixed-point collapse |
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

## 2 · Former partials — v1.1 已补齐

### 2.1 R₀ → R₁ 奠基步 (O₀)

**状态**：closed in [`SelfSimilarity.lean`](../../formal/SSBX/Foundation/Squaring/SelfSimilarity.lean).

| 新锚 | 读法 |
|---|---|
| `r1_eq_bool : R1 ≃ Bool` | R₁ 是第一个二值 distinction |
| `r1_eq_r0_plus_r0 : R1 ≃ R0 ⊕ R0` | R₀ 之 Unit root 经 O₀ split 成两仪 |

### 2.2 R₆ 多路径汇聚 (Multi-route junction)

**状态**：closed in [`SelfSimilarity.lean`](../../formal/SSBX/Foundation/Squaring/SelfSimilarity.lean).

| Route | Lean anchor |
|---|---|
| R₆ ≃ R₃ × R₃ | `r6_eq_r3_squared` |
| R₆ ≃ R₂ × R₄ | `r6_eq_r2_times_r4` |
| R₆ ≃ R₁ × R₅ | `r6_eq_r1_times_r5` |

这三条路径在 R₆ 处合一，给 R₆ 一种「多角度同构」的丰富。v1.1 选择显式 bit 拆装证明，避免把解释性「路径」误写成额外结构。

### 2.3 R₇ ↔ R₈ 完整 iso

**状态**：closed in [`SelfSimilarity.lean`](../../formal/SSBX/Foundation/Squaring/SelfSimilarity.lean).

| 新锚 | 读法 |
|---|---|
| `r8_eq_r7_times_bool : R8 ≃ R7 × Bool` | R₈ = R₇ 加 projection bit；temporal state = trace bit × projection bit |
| `self_similarity_gap_summary` | v1 §2 三项 partial gap bundle |

## 3 · Substantive claims — v1.1 收口状态

### 3.1 4-fiber V₄ partition of R₈

**状态**：closed in [`V4Tensor.lean`](../../formal/SSBX/Foundation/Squaring/V4Tensor.lean).

| 新锚 | 读法 |
|---|---|
| `V4Tensor.r8_eq_temporal_state_indexed_r6` | R₈ 是 4 个 temporal-state-indexed R₆ slices |
| `V4Tensor.r8_eq_r6_times_trace_projection` | R₈ 是 R₆ 加 trace bit 与 projection bit |
| `V4Tensor.r8_temporal_coordinate_summary` | temporal coordinate 的 trace/projection 读法 bundle |
| `V4Tensor.temporalStateFiberEquiv` | 每个 temporal-state fiber 等价于 R₆ |
| `V4Tensor.r8_temporal_state_fiber_card_eq_64` | 道/已/今/未 每片各 64 cells |

### 3.2 Center / Terminus 在 post-Cayley 之 collapse

**状态**：closed in [`Kernel.lean`](../../formal/SSBX/Foundation/Wen/Kernel.lean).

| 新锚 | 读法 |
|---|---|
| `c_motion_ne_origin` | primer motion cell 非 origin |
| `terminus_uninhabited : ∀ s : Field, ¬ terminus s` | post-Cayley R₇ motion 无 fixed point |
| `center_universal : ∀ s : Field, center s` | 所有 R₇ Field state 都在 center |
| `kernel_post_cayley_collapse_summary` | collapse bundle |

这里证明的只是 `(Z/2)^7` 上非零 XOR translation 的代数事实；义理上可读作 3-cycle 死结被移除，但不要读成更强的形上结论。

### 3.3 Cell ≡ Operator (R-O fusion identity)

**状态**：closed as thin Cayley embedding in [`V4Tensor.lean`](../../formal/SSBX/Foundation/Squaring/V4Tensor.lean).

| 新锚 | 读法 |
|---|---|
| `cellOperator (c : R8) : R8 → R8` | cell c 作为 operator，作用为 `fun s => R8.xor s c` |
| `cell_operator_eq_cayley` | 右 XOR translation 与既有 Cayley 左 translation 相同（R₈ abelian） |
| `cell_is_operator : Function.Injective cellOperator` | 不同 cell 给出不同 translation operator |
| `V4Tensor.way_noop_operator` | Way (道) / origin 是 no-op operator |

### 3.4 元 / 爻 (carrier / dimension) asymmetry in squaring

**状态**：documentation-only. 本轮不引入 `CarrierFactor` / `DimensionFactor` typeclass。

原因：`r4_eq_r2_squared` / `r8_eq_r4_squared` 给出的是类型等价；「哪个因子读作元、哪个因子读作爻」是 doctrine orientation，不是现有群结构中的额外可计算数据。v1.1 的处理原则是：在文档中承认首选读法与对偶读法，暂不把解释方向硬编码成 typeclass。

### 3.5 实 / 虚 (substance / field) labeling per squaring step

**状态**：documentation-only. 本轮不在 Lean 中加入 substance/field 标签。

原因：这些标签目前没有稳定的计算行为；强行 Lean 化会过早固定解释层命名。它们应继续挂在 `yi-RO-hierarchy.md` 的 doctrine 表中，等下游有可执行判准时再提升为结构。

### 3.6 Way (道) 之 canonical 位置

**状态**：closed in [`V4Tensor.lean`](../../formal/SSBX/Foundation/Squaring/V4Tensor.lean).

| 新锚 | 读法 |
|---|---|
| `V4Tensor.way_at_origin` | 道 = R₈ origin |
| `V4Tensor.way_noop_operator` | 道作为 cell/operator 是 no-op |
| `V4Tensor.way_origin_operator_summary` | origin / no-op / V₄⁴ zero bundle |

### 3.7 Lisp 在 R₇ 之 closure theorem

**状态**：closed as typed closure in [`DaoJudge.lean`](../../formal/SSBX/Foundation/Lang/DaoJudge.lean).

| 新锚 | 读法 |
|---|---|
| `eval_closed_in_r7` | `eval : Sexp → Option R7` 的成功结果必在 R₇ enumeration 中 |
| `DaoJudge.way_judge_closure_bilingual_summary` | closure + bilingual examples bundle |

### 3.8 Sexp bilingual identity

**状态**：closed for concrete parser identities in [`DaoJudge.lean`](../../formal/SSBX/Foundation/Lang/DaoJudge.lean).

| 新锚 | 读法 |
|---|---|
| `DaoJudge.eval_chinese_earth_eq_ascii_earth` | `坤·有` 与 ASCII spelling 求值相同 |
| `DaoJudge.judge_bilingual_same_earth_self` | concrete judge verdict identity |

注意：这里没有把整个 Lexicon table 提升成任意 program 的 bilingual theorem；本轮只补 WayJudge (`DaoJudge.lean`) parser 层的 concrete identity。

### 3.9 Classical-language layer ↔ R-hierarchy bridge

**状态**：typed skeleton in [`ClassicalTextRHierarchyBridge.lean`](../../formal/SSBX/Foundation/Wen/ClassicalTextRHierarchyBridge.lean).

| 新锚 | 读法 |
|---|---|
| `classical_text_instruction_aliases_are_yiinstr` | CJK surface aliases definitionally equal to `YiInstr` constructors |
| `classical_text_surface_ops_match_r8_ops` | `«互»/«错»/«综»/«设时»` execution matches R₈ operator semantics |
| `classical_text_way_judge_rhierarchy_bridge_summary` | `«道判之程»` 与 `daoJudgeProg` / `daoJudge_correct` 对齐 |
| `classical_text_rhierarchy_scope_boundary` | 明确不宣称 full `MetaInterp.Universal` |

### 3.10 Modern / Quantum bridge to R₈

**状态**：typed skeleton in [`QuantumR8Bridge.lean`](../../formal/SSBX/Foundation/Modern/QuantumR8Bridge.lean).

| 新锚 | 读法 |
|---|---|
| `pauliX_matches_r1_xor` | Pauli X on one-qubit basis matches the R₁ line negation |
| `trigram_pauli_basis_matches_r3_xor` | R₃ 三个位 flip 对齐 `Fin 8` basis bit operations |
| `R8Hilbert`, `r8RegularTranslate` | R₈ finite function-space carrier `R8 → ℂ` 与 regular translation action |
| `r8_regular_translate_involutive`, `r8RegularTranslateEquiv` | 每个 R₈ regular translation 是有限函数空间上的 involutive permutation |
| `r8_regular_translate_faithful` | R₈ cell 对有限函数空间之 regular action faithful |
| `r8_regular_representation_quantum_bridge_summary` | R₈ ≃+ V₄⁴ + Cayley injection + finite function-space regular representation |
| `quantum_r8_bridge_scope_boundary` | physical Pauli-string / analytic unitarity semantics 未在本文件构造 |

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

## 5 · 本轮完成记录与剩余边界

原 v1 Tier 1–2 theorem 已在本轮完成：

| 原优先项 | v1.1 状态 |
|---|---|
| `r1_eq_r0_plus_r0` | closed in `SelfSimilarity.lean` |
| R₆ 三路汇聚 | closed via `r6_eq_r3_squared` / `r6_eq_r2_times_r4` / `r6_eq_r1_times_r5` |
| `V4Tensor.r8_eq_r6_times_trace_projection` / `V4Tensor.r8_temporal_state_fiber_card_eq_64` | closed in `V4Tensor.lean` |
| `terminus_uninhabited` + `center_universal` | closed in `Kernel.lean` |
| `V4Tensor.way_at_origin` | closed in `V4Tensor.lean` |
| `r8_eq_r7_times_bool` | closed in `SelfSimilarity.lean` |
| `cell_is_operator` | closed as injective `cellOperator` in `V4Tensor.lean` |
| Lisp closure in R₇ | closed as `eval_closed_in_r7` in `DaoJudge.lean` |
| Sexp bilingual identity | closed for concrete WayJudge (`DaoJudge.lean`) parser identities |

本轮没有强行 Lean 化的两项 doctrine reading：
- **元/爻 carrier/dimension asymmetry**：documentation-only；属于同构分解之解释方向。
- **实/虚 labeling per squaring step**：documentation-only；待有稳定计算行为后再考虑结构化。

仍然 deferred 的架构性边界：
- **Full arbitrary-program universal compose theorem for `metaInterpProg`**：`MetaInterp/Assembly.lean` 已有 base-256 structural summary；`MetaInterp/Universal.lean` 已有 zero-step/prologue compose、exact-fuel composition frontier、U.1/U.2/U.3 obligation interface 与 Strategy-B fixed-parameter boundary；`Fetch.lean` 已有 pc=0 scaffold exact dispatch route；`FetchProg.lean` 已有 peel-witness exact-fuel route wrappers。剩余是从 concrete fetch peel/decode、hard-block semantic effects、parameterized sub-dispatch 构造 `SemanticLoopObligations`。
- **Physical Pauli-string / analytic unitarity bridge**：`QuantumR8Bridge.lean` 已给 finite basis + `R8 → ℂ` regular function-space semantics；未宣称物理 Pauli-string 或 inner-product unitary 结构。

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

Baseline before v1.1：`lake build SSBX` 曾在 Phase L/K/R cutover 后 clean。v1.1 本轮没有重跑全量 build；本仓库 build 很慢，按 AGENTS.md 原则只跑必要检查。

本轮主线程验证：
- `lake env lean`：`SelfSimilarity.lean`, `V4Tensor.lean`, `Kernel.lean`, `DaoJudge.lean`, `ClassicalTextRHierarchyBridge.lean`, `QuantumR8Bridge.lean`
- `lake env lean formal/SSBX/Foundation/Wen/MetaInterp/Universal.lean`
- `lake build SSBX.Foundation.Wen.ClassicalTextRHierarchyBridge SSBX.Foundation.Modern.QuantumR8Bridge`
- `lake env lean formal/SSBX.lean`
- `git diff --check` on touched docs + Lean files

形式边界：
- 新 axioms from v1.1: **0**
- `Kernel.lean` 的既有 trust boundary 不在本轮扩大
- `ClassicalTextRHierarchyBridge.lean`、`MetaInterp/Assembly.lean`、`MetaInterp/Universal.lean`、`MetaInterp/Fetch.lean`、`MetaInterp/FetchProg.lean` 已给 classical-language direct bridge + base-256 structural assembly + zero-step/prologue compose + exact-fuel semantic frontier + U.1/U.2/U.3 obligation interface + pc=0 fetch route + peel-witness exact-fuel route wrappers；不宣称 full universality
- `QuantumR8Bridge.lean` 是 typed skeleton，不宣称 physical Pauli-string semantics

## 8 · Out-of-scope (per original plan + user decisions)

- Full arbitrary-program / parameterized universal compose theorem for `metaInterpProg`
- Per-cell mapping of ~50 Kernel abstract concepts to specific R₇/R₈ cells
- Performance optimization
- Physical Pauli-string / analytic unitarity semantics (finite `R8 → ℂ` function-space bridge 已落，完整物理桥 deferred)
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
- 平方塔 {R₀, R₁, R₂, R₄, R₈} 之 self-similarity isos + R₆ 三路 junction + R₈/R₇ split
- L-tower post-R₈ (Stream + L_∞ final coalgebra)
- Kernel 抽象 dynamics + 60+ Confucian/Daoist 经典语句 theorems
- Bilingual Lexicon (162 entries)
- ~250 identifiers 之 hard cutover from pinyin/CJK to English

**v1 Tier 1–2 gap 已闭合**：
1. R₀ → R₁ 奠基步 explicit：`r1_eq_r0_plus_r0`
2. R₆ 三路径汇聚：`r6_eq_r3_squared`, `r6_eq_r2_times_r4`, `r6_eq_r1_times_r5`
3. R₈ V₄ partition：`V4Tensor.r8_eq_r6_times_trace_projection`, `V4Tensor.r8_temporal_state_fiber_card_eq_64`
4. Center/terminus collapse：`Kernel.kernel_post_cayley_collapse_summary`
5. Way (道) 之 canonical 位置：`V4Tensor.way_origin_operator_summary`
6. Cell-as-operator：`cellOperator`, `cell_is_operator`
7. R₇ evaluator closure + concrete bilingual identity：`DaoJudge.way_judge_closure_bilingual_summary`

剩余边界不属于 self-similarity v1 核心：constructing `SemanticLoopObligations` for `metaInterpProg` from concrete fetch peel/decode and hard-block semantic effects、parameterized sub-dispatch arbitrary-program simulation、physical Pauli-string / analytic unitarity semantics。
