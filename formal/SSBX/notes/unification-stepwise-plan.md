# 大统一逐步验证路线

目标：把 Markov-因果桥从最小 typed skeleton 推进为逐步增强的验证程序。本文只规划“逐渐完善，直至更统一的形式接口”，不声称已经完成物理大统一、量子引力、Born rule、度规恢复或经验闭合。

依据文档：

| 文件 | 作用 |
|---|---|
| `formal/SSBX/notes/markov-causal-bridge-verification-plan.md` | 当前已验证锚点、最低验证门槛、边界审计与失败模板 |
| `义理/Markov因果桥 · 大统一最小验证构造.md` | Markov-因果桥的义理边界、Lean theorem 锚点与未纳入范围 |

## 总原则

逐步路线只允许按以下顺序加厚：

```text
有限过程双读
-> 具体实例
-> 有限概率核接口
-> 路径组合与因果约束
-> 经典 Markov / 量子 amplitude 分层
-> 干涉与测量律候选
-> 几何候选接口
-> 经验 pending ledger
-> 统一摘要 theorem
```

每一阶段必须同时满足三件事：

| 要求 | 说明 |
|---|---|
| Lean 出口 | 新增或更新明确 theorem / example / structure，并能由目标 `lake build` 检查 |
| 失败记录 | 失败不能删除，必须写入本文件或 `markov-causal-bridge-verification-plan.md` 的失败记录格式 |
| 边界降级 | 若 Lean 出口没有关闭，则义理文档只能写 `未纳入本轮`、`pending` 或 `candidate`，不能写成已证明 |

默认验证命令沿用：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityWenBoundary
lake build SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
lake build SSBX.Foundation.Modern.QuantumRelativityConcreteBridge
lake build SSBX.Foundation.Modern.OperatorCellGridMarkovBridge
lake build SSBX.Foundation.Modern.QuantumRelativityFiniteProbabilityBridge
lake build SSBX.Foundation.Modern.QuantumRelativityPathCausalBridge
lake build SSBX.Foundation.Modern.QuantumRelativityAmplitudeChannelBridge
lake build SSBX.Foundation.Modern.QuantumRelativityInterferenceBridge
lake build SSBX
git diff --check -- formal/SSBX/Foundation/Modern/QuantumRelativityConcreteBridge.lean formal/SSBX/Foundation/Modern/OperatorCellGridMarkovBridge.lean formal/SSBX/Foundation/Modern/QuantumRelativityFiniteProbabilityBridge.lean formal/SSBX/Foundation/Modern/QuantumRelativityPathCausalBridge.lean formal/SSBX/Foundation/Modern/QuantumRelativityAmplitudeChannelBridge.lean formal/SSBX/Foundation/Modern/QuantumRelativityInterferenceBridge.lean formal/SSBX.lean formal/SSBX/notes/unification-stepwise-plan.md formal/SSBX/notes/markov-causal-bridge-verification-plan.md '义理/Markov因果桥 · 大统一最小验证构造.md' '义理/有限概率核接口 · Markov桥S2.md' '义理/路径组合与因果约束 · Markov桥S3.md' '义理/经典Markov与量子振幅分层 · Markov桥S4.md' '义理/干涉与测量律候选 · Markov桥S5.md'
```

## S0 · 基线重审

目标：确认现有 Markov-因果桥只关闭最小骨架，不把最小骨架误读为物理统一。

| 项 | 内容 |
|---|---|
| Lean 出口 | 保持 `markov_causal_bridge_summary`、`measurement_event_alignment`、`markov_bridge_not_direct_language_addition` 为 `machineChecked` |
| 文档出口 | 本文件与验证计划明确列出未关闭项：sum-one 概率律、Born rule 从桥的推导、真实 quantum channel law、干涉、因果偏序、度规恢复、经验闭合 |
| 失败记录 | 若发现文档中有“已完成大统一”“已证明量子引力”等强 claim，记录为 `conceptual overclaim`，并降级 |
| 不可声称 | 不能说 Markov-因果桥已经等于物理大统一；只能说它是最小可验证中介构造 |

通过判准：

```text
现有 Lean 锚点仍可构建；
所有公开句子都把当前结果限制在 finite typed skeleton。
```

## S1 · 非空有限实例

目标：从“结构可定义”推进到“至少有一个具体有限过程实例可通过双读”。

| 项 | 内容 |
|---|---|
| Lean 出口 | `concrete_bridge_summary` 关闭三状态实例；`operator_cell_grid_markov_causal_bridge_summary` 关闭 `71232` grid 实例 |
| 最低 theorem 形态 | 已有命名 theorem：`concrete_bridge_summary`、`operator_cell_grid_markov_causal_bridge_summary` |
| 失败记录 | 若实例卡在有限编码、终端状态或路径构造，记录为 `Lean proof failure`，保留未关闭字段 |
| 文档更新 | 义理文档只能写“存在一个 toy finite bridge instance”，不能写“物理模型存在” |
| 不可声称 | 不能从 toy instance 推出真实测量过程、真实概率或实验预言 |

通过判准：

```text
Lean 能检查一个具体实例；
该实例只作为 consistency witness，不作为物理模型。
```

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `concrete_bridge_summary` | `QuantumRelativityConcreteBridge.lean` | 三状态 toy witness：`prepared → evolved → measured` |
| `operator_cell_grid_markov_causal_bridge_summary` | `OperatorCellGridMarkovBridge.lean` | `371 × 192 = 71232` operator-cell grid 可作为 finite bridge process |

## S2 · 有限概率核接口

目标：把 `Nat` 权重升级为有限概率核接口，先关闭有限行分母与权重上界，而不是 Born rule 或 sum-one 概率律。

| 项 | 内容 |
|---|---|
| Lean 出口 | `finite_probability_bridge_summary` |
| 最低 theorem 形态 | `FiniteProbabilityKernelSkeleton`、`RowNormalizable`、`finiteMassCandidate_denominator_positive_if_not_terminal` |
| 失败记录 | 若无法证明行分母非零或权重上界，记录失败的状态空间、rowTotal 定义和阻塞 theorem |
| 文档更新 | 通过后可写“有限概率核接口已形式化”；仍需保留“sum-one 概率律 / Born rule 未纳入本轮” |
| 不可声称 | 不能说 Born rule、真实归一化概率律或量子测量律已推出 |

通过判准：

```text
每个非终端状态有可检查的非零行分母；
每个一步权重有可检查的分母上界；
Markov 权重与一步转移的支持关系仍保留。
```

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `finite_probability_bridge_summary` | `QuantumRelativityFiniteProbabilityBridge.lean` | concrete 与 `71232` grid bridge 都有有限概率核接口 |
| `finiteMassCandidate_denominator_positive_if_not_terminal` | `QuantumRelativityFiniteProbabilityBridge.lean` | 非终端行的有限质量候选分母非零 |
| `operatorCellGrid_nonterminal_row_normalizable` | `QuantumRelativityFiniteProbabilityBridge.lean` | `371 × 192` grid 的非终端行可规格化为有限分母候选 |

## S3 · 路径组合与局部因果约束

目标：让路径权重和因果读法不只是接口占位，而有一个可组合或可约束的 theorem。

| 项 | 内容 |
|---|---|
| Lean 出口 | `path_causal_bridge_summary` |
| 最低 theorem 形态 | `ComposableProcessPaths`、`composed_path_reachable`、`composed_path_causal_before`、`code_monotone_step_no_self_loop` |
| 失败记录 | 若组合律与现有 `ProcessPath` 不匹配，记录为 structure mismatch，不重写历史结论 |
| 文档更新 | 只说明新增 path witness composition 与 code-successor/no-self-loop 约束；未证明的因果集公理继续列为未纳入 |
| 不可声称 | 不能说已恢复 spacetime、light cone、Lorentzian metric 或完整 causal set theory |

通过判准：

```text
至少一个路径或因果性质成为 machine-checked theorem；
未关闭性质保留在 pending 表。
```

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `path_causal_bridge_summary` | `QuantumRelativityPathCausalBridge.lean` | S3 关闭路径 witness 组合、组合后可达/因果读法、concrete/grid code-successor 与 no-self-loop |
| `composed_path_reachable` | `QuantumRelativityPathCausalBridge.lean` | 两段有效 path witness 可组合成外端点可达 |
| `composed_path_causal_before` | `QuantumRelativityPathCausalBridge.lean` | 组合 path witness 可读成外端点 `causalBefore` |
| `code_monotone_step_no_self_loop` | `QuantumRelativityPathCausalBridge.lean` | code-monotone 一步转移排除自环 |

## S4 · 经典 Markov 与量子 amplitude 分层

目标：引入 quantum channel / amplitude skeleton 时，显式区分经典概率核与量子振幅结构，避免把 Markov 权重偷换为 Born rule。

| 项 | 内容 |
|---|---|
| Lean 出口 | `amplitude_channel_bridge_summary` |
| 最低 theorem 形态 | `QuantumAmplitudeSkeleton`、`QuantumChannelSkeleton`、`amplitude_layer_is_not_markov_kernel`、`channel_layer_is_not_markov_kernel`、`channel_projection_keeps_markov_boundary` |
| 失败记录 | 若复数、范数、unitarity 或 channel law 依赖不足，记录为 `conceptual / library gap` |
| 文档更新 | 可写“量子振幅 / 通道候选接口已开口，且与经典 Markov 层分开”；不能写“量子理论已恢复” |
| 不可声称 | 不能说已经推出干涉、Born rule、unitary evolution 或真实 quantum channel |

通过判准：

```text
Lean 中有独立的 amplitude / channel 层；
旧 Markov 层和新量子候选层的边界有 theorem 标记。
```

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `amplitude_channel_bridge_summary` | `QuantumRelativityAmplitudeChannelBridge.lean` | concrete 与 `71232` grid bridge 同时承载 classical finite-probability boundary、quantum amplitude candidate 与 channel candidate |
| `amplitude_layer_is_not_markov_kernel` | `QuantumRelativityAmplitudeChannelBridge.lean` | quantum amplitude layer 不等同 classical Markov kernel layer |
| `channel_layer_is_not_markov_kernel` | `QuantumRelativityAmplitudeChannelBridge.lean` | quantum channel layer 不等同 classical Markov kernel layer |
| `channel_projection_keeps_markov_boundary` | `QuantumRelativityAmplitudeChannelBridge.lean` | channel candidate 保留并投影回 S2 finite probability-kernel boundary |
| `channel_amplitude_support_implies_step` | `QuantumRelativityAmplitudeChannelBridge.lean` | 非零振幅支持仍尊重 `FiniteProcess.step` |

## S5 · 干涉与测量律候选

目标：只有在 amplitude 层存在之后，才尝试表达相位、路径相消或测量律候选。

| 项 | 内容 |
|---|---|
| Lean 出口 | `interference_bridge_summary` |
| 最低 theorem 形态 | `amplitude_path_composition`、`interference_candidate`、`born_rule_candidate_boundary` |
| 失败记录 | 若只能写候选接口而无法证明数值律，记录为 `candidate only`，并保留 theorem 名称空缺 |
| 文档更新 | 只能写“Born-rule-shaped candidate”，不能写“Born rule 已证” |
| 不可声称 | 不能把候选测量律当成经验证实的量子概率律 |

通过判准：

```text
候选测量律有明确输入、输出和未关闭条件；
所有未证明条件保留为 pending ledger 条目。
```

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `interference_bridge_summary` | `QuantumRelativityInterferenceBridge.lean` | concrete 与 `71232` grid bridge 承载 path amplitude candidate、interference witness 与 Born-shaped boundary |
| `amplitude_path_composition` | `QuantumRelativityInterferenceBridge.lean` | 显式 composable path witness 上的 path-amplitude candidate 组合等式 |
| `interference_candidate` | `QuantumRelativityInterferenceBridge.lean` | `1 + (-1) = 0` 的 destructive-interference typed witness |
| `born_rule_candidate_boundary` | `QuantumRelativityInterferenceBridge.lean` | 单一复幅候选权重等于 `ampProb` |
| `born_rule_candidate_nonnegative` | `QuantumRelativityInterferenceBridge.lean` | Born-shaped candidate weight 非负 |

## S6 · 几何与度规候选接口

目标：从因果事件网络推进到几何候选接口，但只在有 theorem 时声称具体结构。

| 项 | 内容 |
|---|---|
| Lean 出口 | 新增粗粒化事件、邻域、距离候选、拓扑候选或 metric recovery boundary theorem |
| 最低 theorem 形态 | `coarse_event_neighborhood`、`metric_recovery_candidate_boundary` 或同类命名 |
| 失败记录 | 若无法从因果结构恢复几何，记录为 `conceptual gap`，不要补写强 claim |
| 文档更新 | 可写“几何恢复接口 pending”；通过后也只能写“候选接口关闭” |
| 不可声称 | 不能说已恢复 Lorentzian geometry、Einstein equation、曲率动力学或广义相对论 |

通过判准：

```text
Lean 只关闭一个几何候选接口；
度规和动力学仍需单独 theorem。
```

## S7 · 经验 pending ledger

目标：把候选可测差异写成 ledger，而不是直接宣称实验闭合。

| 项 | 内容 |
|---|---|
| Lean 出口 | 新增 `ObservableCandidate`、`PredictionBoundary` 或 pending ledger structure |
| 最低 theorem 形态 | `observable_candidate_has_boundary`、`prediction_requires_external_data` |
| 失败记录 | 若没有数据接口或观测量定义，记录为 `empirical interface pending` |
| 文档更新 | 只列出待验证差异、所需数据、判准和失败条件 |
| 不可声称 | 不能说已有经验预言、实验验证或 phenomenology 闭合 |

通过判准：

```text
每个经验候选都有状态、所需数据、判准和失败路径；
没有数据时保持 pending。
```

## S8 · 统一摘要 theorem

目标：只有当前面阶段的 Lean 出口逐步关闭后，才写更强的统一摘要 theorem。该 theorem 仍然应命名为“stepwise”或“candidate”，避免冒充最终物理统一。

| 项 | 内容 |
|---|---|
| Lean 出口 | 新增聚合 theorem，合取已关闭的实例、概率核、路径/因果、量子候选、几何候选和经验 ledger 边界 |
| 最低 theorem 形态 | `stepwise_unification_candidate_summary` |
| 失败记录 | 若任何子阶段未关闭，摘要 theorem 必须缺席或只合取已关闭部分 |
| 文档更新 | 说明“统一”在本文件中只表示形式接口逐渐汇聚，不表示物理统一已经完成 |
| 不可声称 | 不能说 final theory、theory of everything、quantum gravity solved 或 empirical closure complete |

通过判准：

```text
摘要 theorem 只合取已经 machine-checked 的阶段；
未关闭阶段在 theorem 外作为 pending ledger 保留。
```

## 失败记录追加区

失败记录格式沿用验证计划，并允许追加在此区：

```text
日期：
阶段：
目标：
命令 / theorem：
失败类型：Lean proof failure / build failure / infra failure / conceptual overclaim / empirical interface pending
失败原因：
保留结论：
下一步：
```

当前记录：

| 日期 | 阶段 | 结果 | 说明 |
|---|---|---|---|
| 2026-05-08 | S0 | plan | 本文件新增逐步验证路线；不新增物理 claim |
| 2026-05-08 | S1 | success | 新增 concrete 三状态 witness 与 `71232` operator-cell grid bridge；仍不证明 sum-one 概率律、Born rule、几何恢复或经验闭合 |
| 2026-05-08 | S2 | success | 新增 finite probability-kernel denominator interface；关闭非终端行分母非零与权重上界，仍不证明 sum-one 概率律、Born rule、真实 quantum channel law 或经验闭合 |
| 2026-05-08 | S3 | success | 新增 path composition and local causal constraints；关闭组合 path witness 的可达/因果读法与 concrete/grid no-self-loop，仍不证明完整偏序、局部有限 causal set、light cone 或 metric recovery |
| 2026-05-08 | S4 | success | 新增 classical Markov / quantum amplitude-channel 分层接口；关闭 layer separation、channel candidate 到 S2 边界的投影与非零振幅支持精化，仍不证明干涉、Born rule 推导、unitary/CPTP channel law 或经验闭合 |
| 2026-05-08 | S5 | success | 新增 path amplitude / interference / Born-shaped candidate interface；关闭候选组合等式、相消 witness 与 `ampProb` boundary，仍不证明真实干涉律、Born rule 推导、unitary/CPTP channel law 或经验闭合 |

## 统一用语边界

本文中的“统一”只允许有三种弱读法：

| 词 | 允许含义 | 禁止含义 |
|---|---|---|
| 逐步统一 | 多个形式接口逐步合取到同一个候选 bridge summary | 物理大统一已完成 |
| 候选统一 | Lean 中有更强的 typed skeleton 和 pending ledger | 已推出真实世界理论 |
| 最小统一摘要 | 已关闭 theorem 的保守合取 | 量子引力、Born rule、度规和实验全部闭合 |

推荐边界句：

```text
本路线追求的是逐步增强的形式统一候选；
每一步必须有 Lean 出口和失败记录；
在概率律、真实 quantum channel law、几何恢复与经验 ledger 关闭前，
不得宣称物理大统一已经完成。
```
