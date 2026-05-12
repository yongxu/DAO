> 状态：v3 (2026-05-11) — 从 Lean 事实回读义理的口径页。已更新到 Cell256 + V₄ Klein Shi + R₀..R₈ + Hierarchy umbrella。

# Lean → 义理 回读

本页说明从 Lean 事实读回义理文本的口径。Lean 是机器检查层；义理页是解释层。二者可以互证，但不能互相替代。

## 读取顺序

1. 先以本页的 R₀..R₈ 主轴回读，确认 Lean 事实落在哪一层。
2. 再查 `../_generated/lean-index.md`，确认模块、文件与声明所在 cluster。
3. 再查 `../_generated/claim-index.md`，确认相关 claim 是 machineChecked、modelComputed 还是 ledgerDependent。
4. 若涉及信任边界，先读 `../_generated/trust-boundary.md` 与 `../10_formal_形式/trust-boundaries.md`。
5. 最后回到 `../20_theory_义理/`，只把已确认的形式事实映射为解释语言。

## R₀..R₈ 主轴回读

| R 层 | 基数 | Lean anchor | 可读作 | 不可读作 |
|---|---:|---|---|---|
| R₀ | 1 | `Foundation/Hierarchy/R0_Taiji.lean`; `Unit` | one-point root; absolute origin layer | value theory or generated ontology already closed |
| R₁ | 2 | `Foundation/Hierarchy/R1_Yao.lean`; `Yao` | binary line distinction; first split | all ethics, language, or alignment semantics |
| R₂ | 4 | `Foundation/Hierarchy/R2_SiXiang.lean`; `SiXiang` | four-state image layer; two-bit square | all V₄ or fourfold structures exhausted |
| R₃ | 8 | `Foundation/Hierarchy/R3_Trigram.lean`; `Trigram` | trigram layer; three-bit position space | full hexagram structure or R₈ closure |
| R₄ | 16 | `Foundation/Hierarchy/R4_Mian.lean`; `Mian = Ben × Zheng` | 16-state face layer; base × orientation | hierarchy terminus or complete semantic surface |
| R₅ | 32 | `Foundation/Hierarchy/R5_Wuyao.lean`; `Wuyao` | explicit 32-state intermediate layer | settled traditional canon anchor |
| R₆ | 64 | `Foundation/Hierarchy/R6_Hexagram.lean`; `Hexagram` | hexagram layer; classical 64-state carrier | Cell256, Way origin, or temporal closure |
| R₇ | 128 | `Foundation/Hierarchy/R7_YinHex.lean`; `Cell128` | Cell128; hexagram × trace bit | final R₈ closure or projection-bit completion |
| R₈ | 256 | `Foundation/Hierarchy/R8_GuoHex.lean`; `Cell256`; `Cell256Stratify` | Cell256; R₆ × trace bit × projection bit; Way origin | continuous, probabilistic, physical, or semantic universal-compose claims already proved |

## 跨层模块读法

- `Foundation/Core`、`Foundation/Wen`、`Foundation/Modern`、`Text`、`Truth` 是支撑、解释、桥接或登记层，不构成 R 层级主轴。
- `Foundation/Hierarchy/Operators` 与 `Foundation/Notation/OXNotation` 是 R-axis 周边结构，不读成与 R₀..R₈ 并列的本体层。

## v3 之 「signature」结果（machineChecked，可作锚点）

| 主张 | Lean 锚 | 强度 |
|---|---|---|
| `Cell256.all.length = 256` 且 `Cell256.all.Nodup` | `Cell256.lean § 2` | machineChecked (`native_decide`) |
| Cell256 是 (Z/2)⁸ Abelian 群（XOR + origin） | `Cell256.lean § 7` `cell256_phaseA_summary` | machineChecked |
| Cayley fusion 严格成立：`ε ∘ ι = id`，`ι` 单射 | `Cell256.lean § 7.6` `epsAtOrigin_cayley`, `cayley_inj` | machineChecked |
| 印 / 投 是 XOR-with-mask involution，且交换 | `Cell256.lean § 8` `yin_yin / tou_tou / yin_tou_comm` | machineChecked |
| Cell128 是 (Z/2)⁷ Abelian 群 + Cayley | `Cell128.lean § 6` `cell128_phaseA_summary` | machineChecked |
| R₀..R₈ 8 对 lift/project 全 retract（`proj ∘ lift = id`） | `LiftProject.lean § 9` `liftProject_summary` | machineChecked |
| R₁ 奠基 split、R₆ 三路汇聚、R₈ ≃ R₇×Bool | `SelfSimilarity.lean` `self_similarity_gap_summary` | machineChecked |
| R₈ = R₆ × trace bit × projection bit；4 个 temporal-state-indexed R₆ slices 每片 64 cells | `V4Tensor.lean` `V4Tensor.r8_eq_r6_times_trace_projection`, `V4Tensor.r8_temporal_coordinate_summary`, `V4Tensor.r8_temporal_state_fiber_card_eq_64` | machineChecked |
| Way (道) = R₈ origin = no-op operator；cell-as-operator 单射 | `V4Tensor.lean` `V4Tensor.way_origin_operator_summary`, `cell_is_operator` | machineChecked |
| Atomic XOR 算子皆 involution（10 件） | `Operators/Atomic.lean § 5` `atomic_all_involutive` | machineChecked |
| `{id, cuo, zong, cuoZong}` Hexagram 上构成 V₄ Klein 群 | `Operators/V4Outer.lean § 7` `v4_outer_summary` | machineChecked |
| `R8_complete` 收口（基数 + R-hierarchy + P/T/Y closure + 群作用 simply-transitive + BenZheng 投影 + 位置-算子树 + xuGua256） | `Cell256Stratify.lean § 7` `R8_complete` | machineChecked，依赖仅 `propext + native_decide` |
| Kernel post-Cayley terminus empty / center universal | `Kernel.lean` `kernel_post_cayley_collapse_summary` | machineChecked |
| WayJudge R₇ closure + concrete bilingual parser identities | `DaoJudge.lean` `DaoJudge.eval_chinese_earth_eq_ascii_earth`, `DaoJudge.judge_bilingual_same_earth_self`, `DaoJudge.way_judge_closure_bilingual_summary` | machineChecked |
| Classical-language surface aliases / R₈ execution / WayJudge direct bridge | `ClassicalTextRHierarchyBridge.lean` `classical_text_way_judge_rhierarchy_bridge_summary` | machineChecked typed skeleton |
| Base-256 self-interpreter structural assembly | `MetaInterp/Assembly.lean` `metaInterpProg_base256_structural_summary` | machineChecked typed skeleton |
| Exact-fuel semantic-compose frontier | `MetaInterp/Universal.lean` `metaStart_runFuel_five_eq_postPrologue`, `semantic_compose_frontier_summary` | machineChecked conditional theorem; U.1/U.2/U.3 remain pending |
| Quantum one-bit / R₃ basis / R₈ finite function-space regular representation bridge | `QuantumR8Bridge.lean` `r8_regular_representation_quantum_bridge_summary`, `r8_regular_translate_involutive`, `r8_regular_translate_faithful` | machineChecked typed skeleton |

## 强度词

写义理说明时应保留 Lean 强度：

| Lean/索引状态 | 义理写法 |
|---|---|
| theorem / proved / machineChecked | 「Lean 已检查」「形式层已闭合」 |
| modelComputed | 「模型给出计算结果」「案例层可复现」 |
| registry | 「登记完备」「名册完备」 |
| axiomBacked | 「依赖明示公理或 ledger」 |
| ledgerDependent | 「由账本承接，非机器闭合证明」 |
| pending | 「接口待落地」「经验或协议层未闭合」 |

## 引用格式

人工文档优先引用生成索引，而不是复制 Lean 统计：

- 模块位置：`../_generated/lean-index.md`
- claim 状态：`../_generated/claim-index.md`
- 信任边界：`../_generated/trust-boundary.md`
- 图文件：`../_generated/diagram-index.md`
- 字元和 pending：`../_generated/registry-index.md`

若需要解释某个 theorem 的含义，可以提 Lean 文件路径，但不要在 docs-next 中重写证明。证明变化由 Lean 和生成索引反映。

## 边界

- `kleene_recursion_axiom` 下的结论必须写成「在此 axiom 下」。
- `opaque theOne` 是抽象 witness，不是新增 axiom。
- `YiState.run` 是执行边界；证明路径应引用 fuel 版本或有限见证。
- `R8_complete` 之依赖只含 `propext + native_decide`（项目无新公理）；这是 v3 之主基线。
- Classical-language self-interpreter 已有 base-256 structural assembly 与 exact-fuel semantic-compose frontier；U.1/U.2/U.3 full semantic obligations 仍 pending（详 `../30_crosswalk_互证/claim-status.md`）。
- pending interface 不得被义理页写成已证明命题。

## v2 → v3 阅读迁移

| 旧 Lean 锚 | v3 替代 | 备注 |
|---|---|---|
| `Cell192.lean` (已删) | `Cell256.lean` | V₄ Klein 取代 Z/3 cyclic |
| `Cell192.Shi` (Z/3) | `Cell256.Shi` (V₄) | ctor: `dao / ji / jin / wei` |
| `Cell192Stratify.lean` (已删) | `Cell256Stratify.lean` | `R6_complete → R8_complete` |
| 旧 `R6_complete` | `R8_complete` (重号 +2) | 仍是 closure summary |

## 维护入口

- 旧术语迁移：[`old-to-new.md`](old-to-new.md)
- 详细迁移操作（带代码 diff）：[`cell192-to-cell256-migration.md`](cell192-to-cell256-migration.md)
- claim 状态：[`claim-status.md`](claim-status.md)

## 形式锚

- [`formal/SSBX/Foundation/Hierarchy/RHierarchy.lean`](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean)
- [`formal/SSBX/Foundation/Hierarchy/LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean)
- [`formal/SSBX/Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean)
- [`formal/SSBX/Foundation/Bagua/Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean)
- [`formal/SSBX/Foundation/Bagua/Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean)
- [`formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean)
- [`formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean)
- [`formal/SSBX/Foundation/Notation/OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean)
- [`formal/SSBX/Foundation/Squaring/SelfSimilarity.lean`](../../formal/SSBX/Foundation/Squaring/SelfSimilarity.lean)
- [`formal/SSBX/Foundation/Squaring/V4Tensor.lean`](../../formal/SSBX/Foundation/Squaring/V4Tensor.lean)
- [`formal/SSBX/Foundation/Wen/ClassicalTextRHierarchyBridge.lean`](../../formal/SSBX/Foundation/Wen/ClassicalTextRHierarchyBridge.lean)
- [`formal/SSBX/Foundation/Wen/MetaInterp/Assembly.lean`](../../formal/SSBX/Foundation/Wen/MetaInterp/Assembly.lean)
- [`formal/SSBX/Foundation/Wen/MetaInterp/Universal.lean`](../../formal/SSBX/Foundation/Wen/MetaInterp/Universal.lean)
- [`formal/SSBX/Foundation/Modern/QuantumR8Bridge.lean`](../../formal/SSBX/Foundation/Modern/QuantumR8Bridge.lean)
