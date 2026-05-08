# 大统一逐步验证路线

目标：把 Markov-因果桥从最小 typed skeleton 推进为逐步增强的验证程序。本文把“统一”限定为已经关闭或计划关闭的形式接口；量子引力、Born rule、度规恢复和经验闭合分别作为后续结构单独推进。

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
-> 非零路径振幅候选
-> 双路径相消候选
-> 离散相位标记候选
-> 离散作用量相位候选
-> 有限路径族求和候选
-> 有限路径族求和代数候选
-> 端点索引路径族候选
-> 端点支撑规范化候选
-> 双路径枚举候选
-> 路径身份键候选
-> 有限键商候选
-> 几何候选接口
-> 经验 pending ledger
-> 统一摘要 theorem
```

每一阶段必须同时满足三件事：

| 要求 | 说明 |
|---|---|
| Lean 出口 | 新增或更新明确 theorem / example / structure，并能由目标 `lake build` 检查 |
| 失败记录 | 失败不能删除，必须写入本文件或 `markov-causal-bridge-verification-plan.md` 的失败记录格式 |
| 边界正名 | Lean 出口关闭到哪一层，义理文档就按哪一层命名；未关闭项写入 `未纳入本轮`、`pending` 或 `candidate` |

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
lake build SSBX.Foundation.Modern.QuantumRelativityNonzeroPathAmplitudeBridge
lake build SSBX.Foundation.Modern.QuantumRelativityTwoPathInterferenceBridge
lake build SSBX.Foundation.Modern.QuantumRelativityDiscretePhaseBridge
lake build SSBX.Foundation.Modern.QuantumRelativityDiscreteActionBridge
lake build SSBX.Foundation.Modern.QuantumRelativityFinitePathSumBridge
lake build SSBX.Foundation.Modern.QuantumRelativityFinitePathSumAlgebraBridge
lake build SSBX.Foundation.Modern.QuantumRelativityEndpointIndexedPathFamilyBridge
lake build SSBX.Foundation.Modern.QuantumRelativityEndpointSupportNormalizationBridge
lake build SSBX.Foundation.Modern.QuantumRelativityTwoRouteEnumerationBridge
lake build SSBX.Foundation.Modern.QuantumRelativityPathIdentityBridge
lake build SSBX.Foundation.Modern.QuantumRelativityFiniteKeyQuotientBridge
lake build SSBX
git diff --check -- formal/SSBX/Foundation/Modern/QuantumRelativityConcreteBridge.lean formal/SSBX/Foundation/Modern/OperatorCellGridMarkovBridge.lean formal/SSBX/Foundation/Modern/QuantumRelativityFiniteProbabilityBridge.lean formal/SSBX/Foundation/Modern/QuantumRelativityPathCausalBridge.lean formal/SSBX/Foundation/Modern/QuantumRelativityAmplitudeChannelBridge.lean formal/SSBX/Foundation/Modern/QuantumRelativityInterferenceBridge.lean formal/SSBX/Foundation/Modern/QuantumRelativityNonzeroPathAmplitudeBridge.lean formal/SSBX/Foundation/Modern/QuantumRelativityTwoPathInterferenceBridge.lean formal/SSBX/Foundation/Modern/QuantumRelativityDiscretePhaseBridge.lean formal/SSBX/Foundation/Modern/QuantumRelativityDiscreteActionBridge.lean formal/SSBX/Foundation/Modern/QuantumRelativityFinitePathSumBridge.lean formal/SSBX/Foundation/Modern/QuantumRelativityFinitePathSumAlgebraBridge.lean formal/SSBX/Foundation/Modern/QuantumRelativityEndpointIndexedPathFamilyBridge.lean formal/SSBX/Foundation/Modern/QuantumRelativityEndpointSupportNormalizationBridge.lean formal/SSBX/Foundation/Modern/QuantumRelativityTwoRouteEnumerationBridge.lean formal/SSBX/Foundation/Modern/QuantumRelativityPathIdentityBridge.lean formal/SSBX/Foundation/Modern/QuantumRelativityFiniteKeyQuotientBridge.lean formal/SSBX.lean formal/SSBX/notes/unification-stepwise-plan.md formal/SSBX/notes/markov-causal-bridge-verification-plan.md '义理/Markov因果桥 · 大统一最小验证构造.md' '义理/有限概率核接口 · Markov桥S2.md' '义理/路径组合与因果约束 · Markov桥S3.md' '义理/经典Markov与量子振幅分层 · Markov桥S4.md' '义理/干涉与测量律候选 · Markov桥S5.md' '义理/非零路径振幅候选 · Markov桥S5b.md' '义理/双路径相消候选 · Markov桥S5c.md' '义理/离散相位标记候选 · Markov桥S5d.md' '义理/离散作用量相位候选 · Markov桥S5e.md' '义理/有限路径族求和候选 · Markov桥S5f.md' '义理/有限路径族求和代数候选 · Markov桥S5g.md' '义理/端点索引路径族候选 · Markov桥S5h.md' '义理/端点支撑规范化候选 · Markov桥S5i.md' '义理/双路径枚举候选 · Markov桥S5j.md' '义理/路径身份键候选 · Markov桥S5k.md' '义理/有限键商候选 · Markov桥S5l.md'
```

## S0 · 基线重审

目标：确认现有 Markov-因果桥只关闭最小骨架，不把最小骨架误读为物理统一。

| 项 | 内容 |
|---|---|
| Lean 出口 | 保持 `markov_causal_bridge_summary`、`measurement_event_alignment`、`markov_bridge_not_direct_language_addition` 为 `machineChecked` |
| 文档出口 | 本文件与验证计划明确列出未关闭项：sum-one 概率律、Born rule 从桥的推导、真实 quantum channel law、干涉、因果偏序、度规恢复、经验闭合 |
| 失败记录 | 若发现文档中有强于 theorem 的终局统一或量子引力完成等 claim，记录为 `conceptual mismatch`，并改回对应结构层级 |
| 当前正名 | Markov-因果桥当前是最小可验证中介构造；更强的物理大统一读法需要后续 theorem 合取后再命名 |

通过判准：

```text
现有 Lean 锚点仍可构建；
所有公开句子都按 finite typed skeleton 命名当前结果。
```

## S1 · 非空有限实例

目标：从“结构可定义”推进到“至少有一个具体有限过程实例可通过双读”。

| 项 | 内容 |
|---|---|
| Lean 出口 | `concrete_bridge_summary` 关闭三状态实例；`operator_cell_grid_markov_causal_bridge_summary` 关闭 `71232` grid 实例 |
| 最低 theorem 形态 | 已有命名 theorem：`concrete_bridge_summary`、`operator_cell_grid_markov_causal_bridge_summary` |
| 失败记录 | 若实例卡在有限编码、终端状态或路径构造，记录为 `Lean proof failure`，保留未关闭字段 |
| 文档更新 | 义理文档写“存在一个 toy finite bridge instance”；若要写“物理模型存在”，需另有模型与数据判准 |
| 后续结构 | 从 toy instance 推进到真实测量过程、真实概率或实验预言，需要新增物理模型、观测量和数据接口 |

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
| 文档更新 | 通过后可写“有限概率核接口已形式化”；sum-one 概率律 / Born rule 继续作为后续结构 |
| 后续结构 | Born rule、真实归一化概率律或量子测量律需要额外 theorem 推出 |

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
| 文档更新 | 说明新增 path witness composition 与 code-successor/no-self-loop 约束；未证明的因果集公理继续列为未纳入 |
| 后续结构 | spacetime、light cone、Lorentzian metric 或完整 causal set theory 需要额外结构与 theorem |

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
| 文档更新 | 可写“量子振幅 / 通道候选接口已开口，且与经典 Markov 层分开”；量子理论恢复需另有动力学与经验接口 |
| 后续结构 | 干涉、Born rule、unitary evolution 或真实 quantum channel 需要额外 theorem |

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
| 文档更新 | 写“Born-rule-shaped candidate”；Born rule 完成需要从候选接口推出概率律 |
| 后续结构 | 候选测量律要成为经验证实的量子概率律，需要观测 ledger、数据判准和经验验证接口 |

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

## S5b · 非零路径振幅候选

目标：在不引入真实相位动力学的情况下，先摆脱全零 placeholder，并证明非零 path amplitude 不跑出 path / causal boundary。

| 项 | 内容 |
|---|---|
| Lean 出口 | `nonzero_path_amplitude_bridge_summary` |
| 最低 theorem 形态 | `nonzero_path_amplitude_implies_valid`、`nonzero_path_amplitude_implies_reachable`、`nonzero_path_amplitude_implies_causal_before`、`concrete_prepared_measured_path_nonzero_amplitude` |
| 失败记录 | 若非零 witness 只依赖任意有效性假设，记录为 `candidate only`；物理动力学由后续 phase/action law 承接 |
| 文档读法 | 正面写明已证 nonzero path-amplitude candidate witness；真实干涉律仍需 phase law、path integral、Born-rule derivation、unitary/CPTP law 或 empirical prediction |
| 边界保留 | S5b 的 Lean 出口扩展了非零振幅边界，但尚未闭合真实物理干涉 |

通过判准：

```text
Lean 中存在一个非零候选 path amplitude witness；
该 witness 可以投影到 valid path、Reachable 和 causalBefore；
S5c 已关闭最小 two-path finite cancellation；真实干涉律仍在 theorem 外。
```

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `nonzero_path_amplitude_bridge_summary` | `QuantumRelativityNonzeroPathAmplitudeBridge.lean` | 非零 path amplitude 推出 valid / Reachable / causalBefore，并给 concrete path 一个非零 candidate witness |
| `validPathIndicatorPathAmplitudeSkeleton` | `QuantumRelativityNonzeroPathAmplitudeBridge.lean` | 有效 path 给 `1`，无效 path 给 `0` 的最小候选骨架 |
| `concrete_prepared_measured_path_nonzero_amplitude` | `QuantumRelativityNonzeroPathAmplitudeBridge.lean` | concrete `prepared -> measured` composed path 的候选振幅非零 |

## S5c · 双路径相消候选

目标：先不引入一般 path integral，只证明两条同端点、不同中间态的有限 candidate paths 可携带相反候选振幅并相消。

| 项 | 内容 |
|---|---|
| Lean 出口 | `two_path_interference_bridge_summary` |
| 最低 theorem 形态 | `TwoStepPathWitness`、`SameEndpointTwoStepPair`、`two_route_upper_amplitude`、`two_route_lower_amplitude`、`two_route_pair_amplitude_cancels`、`two_route_cancelled_born_weight_zero` |
| 失败记录 | 若无法保留 middle identity，记录为 `structure mismatch`，不要把 endpoint-only `ProcessPath` 冒充为双路径身份 |
| 文档读法 | 正面写明已证 two-path finite cancellation candidate；真实干涉律仍需 path integral、phase/action law、Born-rule derivation、unitary/CPTP law、decoherence 或 empirical prediction |
| 边界保留 | S5c 的 Lean 出口已经把相消接到同端点、不同中间态路径；它尚未闭合物理相位动力学 |

通过判准：

```text
Lean 中存在一个 same-endpoint / different-middle two-step pair；
两条路径的候选振幅分别为 1 与 -1；
有限两路径和为 0，并能接回 Born-shaped zero boundary；
一般路径积分、相位动力学与可测干涉仍在 theorem 外。
```

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `two_path_interference_bridge_summary` | `QuantumRelativityTwoPathInterferenceBridge.lean` | two-route toy process 承载 finite probability / channel / path-amplitude / two-step amplitude candidate，并关闭两路径相消 |
| `two_route_paths_same_endpoints` | `QuantumRelativityTwoPathInterferenceBridge.lean` | upper/lower two-step paths 同起点、同终点 |
| `two_route_paths_distinct_middle` | `QuantumRelativityTwoPathInterferenceBridge.lean` | upper/lower two-step paths 的中间态不同 |
| `two_route_pair_amplitude_cancels` | `QuantumRelativityTwoPathInterferenceBridge.lean` | `1 + (-1) = 0` 接到 same-endpoint two-step pair |
| `two_route_cancelled_born_weight_zero` | `QuantumRelativityTwoPathInterferenceBridge.lean` | 相消后的 Born-shaped candidate weight 为 `0` |

## S5d · 离散相位标记候选

目标：把 S5c 中裸露的 `1/-1` 候选振幅改写为由离散 phase label 导出的候选振幅，但仍不引入连续相位群、Hamiltonian 或作用量动力学。

| 项 | 内容 |
|---|---|
| Lean 出口 | `discrete_phase_bridge_summary` |
| 最低 theorem 形态 | `DiscretePhase`、`discretePhaseAmplitude`、`discrete_phase_amplitudes_cancel`、`TwoStepPhaseCandidate`、`two_route_upper_phase`、`two_route_lower_phase`、`two_route_phase_pair_amplitude_cancels` |
| 失败记录 | 若暂时只能直接给 `1/-1`，记录为 `candidate only`；相位动力学由后续 continuous phase / action law 承接 |
| 文档读法 | 正面写明已证 discrete phase-label candidate；physical phase law 仍需 Hamiltonian、action functional、continuous phase group、unitary/CPTP dynamics、path integral 或 empirical prediction |
| 边界保留 | S5d 的 Lean 出口已经把 `1/-1` 解释为 `zero/pi` 标签导出；它尚未闭合连续相位或作用量动力学 |

通过判准：

```text
Lean 中有 finite phase labels；
zero/pi 标签分别导出 1/-1；
upper/lower two-step paths 分别携带 zero/pi；
phase-induced finite two-path amplitude cancels；
连续相位、作用量动力学与 path integral 仍在 theorem 外。
```

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `discrete_phase_bridge_summary` | `QuantumRelativityDiscretePhaseBridge.lean` | two-route cancellation 可由离散 phase labels 导出 |
| `discrete_phase_amplitudes_cancel` | `QuantumRelativityDiscretePhaseBridge.lean` | `phaseAmplitude zero + phaseAmplitude pi = 0` |
| `two_route_upper_phase`、`two_route_lower_phase` | `QuantumRelativityDiscretePhaseBridge.lean` | upper/lower paths 分别标为 `zero/pi` |
| `two_route_phase_pair_amplitude_cancels` | `QuantumRelativityDiscretePhaseBridge.lean` | phase-induced two-path finite sum 为 `0` |
| `two_route_phase_cancelled_born_weight_zero` | `QuantumRelativityDiscretePhaseBridge.lean` | phase-induced 相消后 Born-shaped candidate weight 为 `0` |

## S5e · 离散作用量相位候选

目标：把 S5d 的整条 path phase label 往前推一层，证明 two-step path phase 可由 edge phase increments 组成，并得到 upper/lower 相对相位 `pi`。

| 项 | 内容 |
|---|---|
| Lean 出口 | `discrete_action_phase_bridge_summary` |
| 最低 theorem 形态 | `discretePhaseAdd`、`TwoStepEdgePhaseCandidate`、`edgePhaseInducedTwoStepPhaseCandidate`、`two_route_upper_accumulated_phase`、`two_route_lower_accumulated_phase`、`two_route_edge_action_phase_difference`、`two_route_edge_action_pair_amplitude_cancels` |
| 失败记录 | 若 edge phase 无法稳定接回 S5d phase candidate，记录为 `structure mismatch`；finite path-family sum 与 continuous action law 由后续层承接 |
| 文档读法 | 正面写明已证 discrete edge-action phase accumulation candidate；physical action functional、Hamiltonian/unitary law、path integral 与 empirical prediction 仍需后续结构 |
| 边界保留 | S5e 的 Lean 出口已经把 `zero/pi` path phase 改写为 edge increments 的累积；它尚未闭合连续作用量或一般路径求和 |

通过判准：

```text
Lean 中有 finite phase composition；
two-step path phase 由两条 edge phase increments 累积；
upper accumulated phase = zero；
lower accumulated phase = pi；
relative phase = pi；
edge-action-induced finite two-path amplitude cancels；
finite path-family sum、连续 action law 与 path integral 仍在 theorem 外。
```

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `discrete_action_phase_bridge_summary` | `QuantumRelativityDiscreteActionBridge.lean` | two-route cancellation 可由 edge phase accumulation 导出 |
| `discretePhaseAdd`、`discretePhaseRelative` | `QuantumRelativityDiscreteActionBridge.lean` | 二值相位合成与相对相位候选 |
| `TwoStepEdgePhaseCandidate.pathPhase` | `QuantumRelativityDiscreteActionBridge.lean` | two-step path phase 由 edge increments 合成 |
| `two_route_upper_accumulated_phase`、`two_route_lower_accumulated_phase` | `QuantumRelativityDiscreteActionBridge.lean` | upper/lower 分别累积为 `zero/pi` |
| `two_route_edge_action_phase_difference` | `QuantumRelativityDiscreteActionBridge.lean` | lower 相对 upper 为 `pi` |
| `two_route_edge_action_pair_amplitude_cancels` | `QuantumRelativityDiscreteActionBridge.lean` | edge-action-induced two-path finite sum 为 `0` |
| `two_route_edge_action_cancelled_born_weight_zero` | `QuantumRelativityDiscreteActionBridge.lean` | edge-action-induced 相消后 Born-shaped candidate weight 为 `0` |

## S5f · 有限路径族求和候选

目标：把 S5c/S5e 的 two-path pair sum 改写成 finite same-endpoint path family 上的有限求和接口，为后续 path-sum algebra 留出稳定入口。

| 项 | 内容 |
|---|---|
| Lean 出口 | `finite_path_sum_bridge_summary` |
| 最低 theorem 形态 | `FiniteTwoStepPathFamily`、`finitePathFamilyAmplitudeSum`、`finitePathFamilyBornWeight`、`two_route_family_sum_eq_pair_sum`、`two_route_finite_family_amplitude_cancels` |
| 失败记录 | 若 list-family 无法保持 endpoint ledger，记录为 `structure mismatch`；path-sum algebra 由 S5g 承接，all-path enumeration 由后续层承接 |
| 文档读法 | 正面写明已证 finite path-family sum candidate；path-sum algebra 已由 S5g 承接，path integral、continuous action law、Born rule derivation 与 empirical prediction 仍需后续结构 |
| 边界保留 | S5f 的 Lean 出口已经把 upper/lower pair 嵌入有限路径族求和；append / permutation / reverse stability 已由 S5g 承接，它尚未闭合任意路径枚举、一般路径积分或真实测量概率律 |

通过判准：

```text
Lean 中有 finite same-endpoint two-step path family；
family 中每条 path 共享 start/stop endpoint；
finite family amplitude sum 可接回 Born-shaped boundary；
two-route family sum 等于原 pair sum；
two-route finite-family amplitude cancels；
append / permutation / reverse stability 由 S5g 承接；
all-path enumeration 与 path integral 仍在 theorem 外。
```

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `finite_path_sum_bridge_summary` | `QuantumRelativityFinitePathSumBridge.lean` | two-route upper/lower pair 作为 finite path family instance，关闭 family sum cancellation 与 Born-shaped zero boundary |
| `FiniteTwoStepPathFamily`、`HasFiniteTwoStepPathFamily` | `QuantumRelativityFinitePathSumBridge.lean` | 有限 list 形式的 same-endpoint two-step path family |
| `finitePathFamilyAmplitudeSum`、`finitePathFamilyBornWeight` | `QuantumRelativityFinitePathSumBridge.lean` | 对 family 作有限振幅求和，并接回 `ampProb` boundary |
| `two_route_family_paths_share_endpoints` | `QuantumRelativityFinitePathSumBridge.lean` | two-route family 中每条 path 同起点同终点 |
| `two_route_family_sum_eq_pair_sum` | `QuantumRelativityFinitePathSumBridge.lean` | finite family sum 与 S5c/S5e pair sum 相等 |
| `two_route_finite_family_amplitude_cancels` | `QuantumRelativityFinitePathSumBridge.lean` | edge-action-induced finite family sum 为 `0` |
| `two_route_finite_family_born_weight_zero` | `QuantumRelativityFinitePathSumBridge.lean` | finite-family 相消后 Born-shaped candidate weight 为 `0` |

## S5g · 有限路径族求和代数候选

目标：在 S5f 的有限路径族求和接口上补最小 list algebra，证明 append、permutation、reverse 与 cancellation stability。

| 项 | 内容 |
|---|---|
| Lean 出口 | `finite_path_sum_algebra_bridge_summary` |
| 最低 theorem 形态 | `appendFiniteTwoStepPathFamilies`、`reverseFiniteTwoStepPathFamily`、`finite_path_family_amplitude_sum_append`、`finite_path_family_amplitude_sum_perm`、`finite_path_family_amplitude_sum_reverse`、`finite_path_family_append_cancels_of_canceling_summands` |
| 失败记录 | 若 append 无法保持 endpoint ledger，记录为 `structure mismatch`；all-path enumeration 与 path integral 由后续层承接 |
| 文档读法 | 正面写明已证 finite path-sum algebra candidate；all-path enumeration、path integral、Born rule derivation 与 empirical prediction 仍需后续结构 |
| 边界保留 | S5g 的 Lean 出口只证明给定 finite lists 的代数稳定性；endpoint-indexed family 已由 S5h 承接，它尚未闭合全部路径枚举、连续测度、一般路径积分或真实测量概率律 |

通过判准：

```text
Lean 中有 endpoint-compatible append；
finite family amplitude sum over append 等于两族和之和；
permutation / reverse 不改变 finite family amplitude sum；
两个已相消的 endpoint-compatible families append 后仍相消；
all-path enumeration、continuous action law 与 path integral 仍在 theorem 外。
```

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `finite_path_sum_algebra_bridge_summary` | `QuantumRelativityFinitePathSumAlgebraBridge.lean` | 合取 append / permutation / reverse stability 与 two-route cancellation stability |
| `appendFiniteTwoStepPathFamilies` | `QuantumRelativityFinitePathSumAlgebraBridge.lean` | 同端点 ledger 的有限路径族可拼接 |
| `reverseFiniteTwoStepPathFamily` | `QuantumRelativityFinitePathSumAlgebraBridge.lean` | 反序保留 endpoint ledger |
| `finite_path_family_amplitude_sum_append` | `QuantumRelativityFinitePathSumAlgebraBridge.lean` | 拼接族的候选振幅和等于两族候选振幅和之和 |
| `finite_path_family_amplitude_sum_perm` | `QuantumRelativityFinitePathSumAlgebraBridge.lean` | list permutation 不改变候选振幅和 |
| `finite_path_family_amplitude_sum_reverse` | `QuantumRelativityFinitePathSumAlgebraBridge.lean` | list reverse 不改变候选振幅和 |
| `finite_path_family_append_cancels_of_canceling_summands` | `QuantumRelativityFinitePathSumAlgebraBridge.lean` | 两个已相消的同端点有限族拼接后仍相消 |
| `two_route_double_family_amplitude_cancels` | `QuantumRelativityFinitePathSumAlgebraBridge.lean` | two-route cancelled family 与其反序拼接后仍相消 |

## S5h · 端点索引路径族候选

目标：把 S5f 的同端点 ledger 收紧成 endpoint-indexed finite family，使路径端点成为路径族索引的一部分。

| 项 | 内容 |
|---|---|
| Lean 出口 | `endpoint_indexed_path_family_bridge_summary` |
| 最低 theorem 形态 | `EndpointPair`、`EndpointTwoStepPath`、`EndpointIndexedTwoStepPathFamily`、`endpointIndexedFamilyOfFinitePathFamily`、`endpoint_indexed_family_sum_of_finite_family`、`endpoint_indexed_family_born_weight_of_finite_family` |
| 失败记录 | 若 dependent endpoint index 无法保持原 finite sum，记录为 `structure mismatch`；filter/support normalization 已由 S5i 承接，all-path enumeration 由后续层承接 |
| 文档读法 | 正面写明已证 endpoint-indexed finite path-family candidate；all-path enumeration、path integral、Born rule derivation 与 empirical prediction 仍需后续结构 |
| 边界保留 | S5h 的 Lean 出口只把给定 finite family 转为 endpoint-indexed family；filter/support normalization 已由 S5i 承接，它尚未闭合全部路径枚举、quotient 去重、一般路径积分或真实测量概率律 |

通过判准：

```text
Lean 中有 endpoint pair；
two-step path 携带其 endpoint index 的等式证明；
S5f finite family 可转成 endpoint-indexed finite family；
转换保持 finite amplitude sum 与 Born-shaped weight；
two-route endpoint-indexed family 仍相消；
filter/support normalization 已由 S5i 承接；all-path enumeration 与 path integral 仍在 theorem 外。
```

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `endpoint_indexed_path_family_bridge_summary` | `QuantumRelativityEndpointIndexedPathFamilyBridge.lean` | 合取 endpoint-indexed conversion、sum preservation、Born-shaped preservation 与 two-route cancellation |
| `EndpointPair`、`EndpointTwoStepPath` | `QuantumRelativityEndpointIndexedPathFamilyBridge.lean` | endpoint pair 与携带端点证明的 two-step path |
| `EndpointIndexedTwoStepPathFamily` | `QuantumRelativityEndpointIndexedPathFamilyBridge.lean` | 路径列表依赖同一个 endpoint index |
| `endpointIndexedFamilyOfFinitePathFamily` | `QuantumRelativityEndpointIndexedPathFamilyBridge.lean` | S5f finite family 转成 endpoint-indexed family |
| `endpoint_indexed_family_sum_of_finite_family` | `QuantumRelativityEndpointIndexedPathFamilyBridge.lean` | endpoint-indexed 转换保持候选振幅和 |
| `endpoint_indexed_family_born_weight_of_finite_family` | `QuantumRelativityEndpointIndexedPathFamilyBridge.lean` | endpoint-indexed 转换保持 Born-shaped weight |
| `two_route_endpoint_indexed_family_amplitude_cancels` | `QuantumRelativityEndpointIndexedPathFamilyBridge.lean` | two-route endpoint-indexed family 仍相消 |

## S5i · 端点支撑规范化候选

目标：在 S5h 的 endpoint-indexed finite family 上补最小 finite support/filter normalization 和 duplicate handling boundary。

| 项 | 内容 |
|---|---|
| Lean 出口 | `endpoint_support_normalization_bridge_summary` |
| 最低 theorem 形态 | `filterEndpointIndexedTwoStepPathFamily`、`EndpointFamilyFilterComplete`、`endpoint_indexed_family_filter_sum_eq_of_removed_zero`、`endpoint_indexed_family_filter_born_weight_eq_of_removed_zero`、`duplicateEndpointIndexedTwoStepPathFamily`、`endpoint_indexed_family_duplicate_sum` |
| 失败记录 | 若 filter 无法保持 dependent endpoint index，记录为 `structure mismatch`；若 duplicate 被误读为去重，记录为 `conceptual mismatch` |
| 文档读法 | 正面写明已证 endpoint support normalization candidate；quotient 去重、all-path enumeration、path integral、Born rule derivation 与 empirical prediction 仍需后续结构 |
| 边界保留 | S5i 的 Lean 出口只处理给定 endpoint-indexed finite list 的筛选与重复展开；它尚未闭合路径等价商、全部路径枚举、连续测度、一般路径积分或真实测量概率律 |

通过判准：

```text
Lean 中有保持 endpoint index 的 finite filter；
被筛掉路径振幅为 0 时，filter 后的 amplitude sum 不变；
对应 Born-shaped weight 不变；
duplicated family 的 amplitude sum 显式等于 sum + sum；
zero-sum family duplicate 后仍相消；
quotient 去重、all-path enumeration 与 path integral 仍在 theorem 外。
```

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `endpoint_support_normalization_bridge_summary` | `QuantumRelativityEndpointSupportNormalizationBridge.lean` | 合取 amplitude-complete filter preservation、duplicate handling 与 two-route witness |
| `filterEndpointIndexedTwoStepPathFamily` | `QuantumRelativityEndpointSupportNormalizationBridge.lean` | 保持 endpoint index 的有限路径筛选 |
| `EndpointFamilyFilterComplete` | `QuantumRelativityEndpointSupportNormalizationBridge.lean` | 被筛掉路径候选振幅为 `0` 的支撑完备条件 |
| `endpoint_indexed_family_filter_sum_eq_of_removed_zero` | `QuantumRelativityEndpointSupportNormalizationBridge.lean` | amplitude-complete filter 保持候选振幅和 |
| `endpoint_indexed_family_filter_born_weight_eq_of_removed_zero` | `QuantumRelativityEndpointSupportNormalizationBridge.lean` | amplitude-complete filter 保持 Born-shaped weight |
| `endpoint_indexed_family_duplicate_sum` | `QuantumRelativityEndpointSupportNormalizationBridge.lean` | duplicate family 的候选振幅和为 `sum + sum` |
| `two_route_filtered_endpoint_family_amplitude_cancels` | `QuantumRelativityEndpointSupportNormalizationBridge.lean` | two-route filtered endpoint family 仍相消 |
| `two_route_duplicated_endpoint_family_amplitude_cancels` | `QuantumRelativityEndpointSupportNormalizationBridge.lean` | two-route duplicated endpoint family 仍相消 |

## S5j · 双路径枚举候选

目标：只对 `twoRouteProcess` 的 `source -> _ -> target` two-step witness 做有限 middle enumeration，证明 endpoint-indexed family 的 middle list 完整覆盖 toy source/target middle。

| 项 | 内容 |
|---|---|
| Lean 出口 | `two_route_enumeration_bridge_summary` |
| 最低 theorem 形态 | `endpointIndexedMiddleList`、`twoRouteSourceTargetMiddleEnumeration`、`two_route_endpoint_indexed_middle_list_eq`、`two_route_source_target_middle_upper_or_lower`、`two_route_source_target_middle_complete` |
| 失败记录 | 若 toy step relation 无法推出 middle exhaustion，记录为 `Lean proof failure`；若把 toy enumeration 写成 general all-path enumeration，记录为 `conceptual mismatch` |
| 文档读法 | 正面写明已证 two-route toy source/target two-step enumeration；general all-path enumeration、path integral、Born rule derivation 与 empirical prediction 仍需后续结构 |
| 边界保留 | S5j 的 Lean 出口只证明四态 toy process 的 two-step middle exhaustion；它尚未闭合任意长度路径、任意过程枚举、路径等价商、连续测度、一般路径积分或真实测量概率律 |

通过判准：

```text
endpoint-indexed two-route family 的 middle list 是 [upper, lower]；
任意 source/target two-step witness 的 middle 是 upper 或 lower；
任意 source/target two-step witness 的 middle 出现在 endpoint family middle list 中；
general all-path enumeration 与 path integral 仍在 theorem 外。
```

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `two_route_enumeration_bridge_summary` | `QuantumRelativityTwoRouteEnumerationBridge.lean` | 合取 toy middle enumeration、endpoint family completeness 与 S5i boundary |
| `two_route_endpoint_indexed_middle_list_eq` | `QuantumRelativityTwoRouteEnumerationBridge.lean` | endpoint-indexed two-route family 的 middle list 为 `[upper, lower]` |
| `two_route_source_target_middle_upper_or_lower` | `QuantumRelativityTwoRouteEnumerationBridge.lean` | toy source/target two-step witness 的 middle 只能是 upper 或 lower |
| `two_route_source_target_middle_mem_endpoint_family` | `QuantumRelativityTwoRouteEnumerationBridge.lean` | toy source/target middle 出现在 endpoint-indexed family middle list 中 |
| `two_route_source_target_middle_complete` | `QuantumRelativityTwoRouteEnumerationBridge.lean` | source/target middle completeness 的公开 predicate |

## S5k · 路径身份键候选

目标：把 two-step witness 的可见路径身份先压成 `(start, middle, stop)` key，给后续 quotient 或去重提供机器可查的边界。

| 项 | 内容 |
|---|---|
| Lean 出口 | `path_identity_bridge_summary` |
| 最低 theorem 形态 | `TwoStepPathKey`、`twoStepPathKey`、`two_step_path_key_eq_start`、`two_step_path_key_eq_middle`、`two_route_upper_lower_keys_distinct`、`two_route_source_target_key_complete` |
| 失败记录 | 若 key equality 与 witness proof fields 混淆，记录为 `conceptual mismatch`；若 source/target key enumeration 失败，记录为 `Lean proof failure` |
| 文档读法 | 正面写明已证 visible path-key boundary；finite visible-key quotient candidate 已由 S5l 承接，proof-field path equality、general all-path enumeration、path integral、Born rule derivation 与 empirical prediction 仍需后续结构 |
| 边界保留 | S5k 不证明真正 quotient type，只证明 key equality 对可见路径数据的保持与 toy source/target key completeness |

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `path_identity_bridge_summary` | `QuantumRelativityPathIdentityBridge.lean` | 合取 visible key boundary、two-route key separation 与 S5j middle completeness |
| `TwoStepPathKey`、`twoStepPathKey` | `QuantumRelativityPathIdentityBridge.lean` | 抽出 `start/middle/stop` 可见路径身份 |
| `two_step_path_key_eq_start`、`two_step_path_key_eq_middle`、`two_step_path_key_eq_stop` | `QuantumRelativityPathIdentityBridge.lean` | key equality 保持可见路径数据 |
| `two_route_upper_lower_keys_distinct` | `QuantumRelativityPathIdentityBridge.lean` | upper/lower displayed paths 的 key 不同 |
| `two_route_source_target_key_complete` | `QuantumRelativityPathIdentityBridge.lean` | toy source/target path key 落在 displayed key enumeration 中 |

## S5l · 有限键商候选

目标：把 visible key equality 明确成 quotient-candidate relation，并证明 key-compatible amplitudes 能降到 key 层的有限求和边界。

| 项 | 内容 |
|---|---|
| Lean 出口 | `finite_key_quotient_bridge_summary` |
| 最低 theorem 形态 | `TwoStepPathKeyEquivalent`、`PathAmplitudeFactorsThroughKey`、`key_equivalent_paths_amplitude_eq`、`endpoint_indexed_key_sum_eq_path_sum_of_factor`、`two_route_key_amplitude_sum_cancels` |
| 失败记录 | 若把 candidate relation 冒充真正 quotient type，记录为 `scope overclaim`；若 key-compatible descent 失败，记录为 `Lean proof failure` |
| 文档读法 | 正面写明已证 finite visible-key quotient candidate；quotient type construction、proof-field path equality、general all-path enumeration、path integral、Born rule derivation 与 empirical prediction 仍需后续结构 |
| 边界保留 | S5l 不构造 `Quot`，只证明 key-equivalence、key-compatible amplitude descent、duplicate compensation 与 two-route key-level cancellation |

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `finite_key_quotient_bridge_summary` | `QuantumRelativityFiniteKeyQuotientBridge.lean` | 合取 quotient-candidate relation、key compatibility、duplicate compensation 与 two-route key cancellation |
| `TwoStepPathKeyEquivalent` | `QuantumRelativityFiniteKeyQuotientBridge.lean` | visible key equality 作为 candidate relation |
| `key_equivalent_paths_amplitude_eq` | `QuantumRelativityFiniteKeyQuotientBridge.lean` | key-compatible amplitudes 在同 key paths 上相同 |
| `endpoint_indexed_key_sum_eq_path_sum_of_factor` | `QuantumRelativityFiniteKeyQuotientBridge.lean` | endpoint-indexed path sum 可在 factor-through-key 条件下降到 key-list sum |
| `two_route_key_born_weight_zero` | `QuantumRelativityFiniteKeyQuotientBridge.lean` | two-route key-level cancellation 接回 Born-shaped zero boundary |

## S6 · 几何与度规候选接口

目标：从因果事件网络推进到几何候选接口，但只在有 theorem 时声称具体结构。

| 项 | 内容 |
|---|---|
| Lean 出口 | 新增粗粒化事件、邻域、距离候选、拓扑候选或 metric recovery boundary theorem |
| 最低 theorem 形态 | `coarse_event_neighborhood`、`metric_recovery_candidate_boundary` 或同类命名 |
| 失败记录 | 若无法从因果结构恢复几何，记录为 `conceptual gap`，并保留在后续结构表中 |
| 文档更新 | 可写“几何恢复接口 pending”；通过后按 theorem 写“候选接口关闭” |
| 后续结构 | Lorentzian geometry、Einstein equation、曲率动力学或广义相对论需要独立恢复结构与 theorem |

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
| 文档更新 | 列出待验证差异、所需数据、判准和失败条件 |
| 后续结构 | 经验预言、实验验证或 phenomenology 闭合需要数据接口与验证记录 |

通过判准：

```text
每个经验候选都有状态、所需数据、判准和失败路径；
没有数据时保持 pending。
```

## S8 · 统一摘要 theorem

目标：当前面阶段的 Lean 出口逐步关闭后，写更强的统一摘要 theorem。该 theorem 按其内容命名为“stepwise”或“candidate”，把已经闭合的结构合取成当前阶段的统一摘要。

| 项 | 内容 |
|---|---|
| Lean 出口 | 新增聚合 theorem，合取已关闭的实例、概率核、路径/因果、量子候选、几何候选和经验 ledger 边界 |
| 最低 theorem 形态 | `stepwise_unification_candidate_summary` |
| 失败记录 | 若任何子阶段未关闭，摘要 theorem 必须缺席或只合取已关闭部分 |
| 文档更新 | 说明“统一”在本文件中表示形式接口逐渐汇聚；物理统一读法随后续结构和 theorem 增强 |
| 后续结构 | 终局理论、万有理论、量子引力解决或经验闭合完成需要完整动力学、几何、概率律和经验 ledger 合取 |

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
失败类型：Lean proof failure / build failure / infra failure / conceptual mismatch / empirical interface pending
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
| 2026-05-08 | S5b | success | 新增 nonzero path-amplitude candidate witness；关闭非零候选振幅到 valid / Reachable / causalBefore 的边界，仍不证明相位律、路径求和、真实干涉律或经验闭合 |
| 2026-05-08 | S5c | success | 新增 two-path finite cancellation candidate；关闭 same-endpoint / different-middle two-step pair 的 `1 + (-1) = 0` 与 Born-shaped zero boundary，仍不证明 path integral、相位动力学、真实干涉律或经验闭合 |
| 2026-05-08 | S5d | success | 新增 discrete phase-label candidate；关闭 `zero/pi` 到 `1/-1` 的映射、upper/lower phase labels 与 phase-induced two-path cancellation，仍不证明 continuous phase、action/Hamiltonian law、path integral 或经验闭合 |
| 2026-05-08 | S5e | success | 新增 discrete edge-action phase accumulation candidate；关闭 edge increments 到 path phase、relative phase `pi` 与 edge-action-induced two-path cancellation，仍不证明 finite path-family sum、continuous phase/action law、path integral 或经验闭合 |
| 2026-05-08 | S5f | success | 新增 finite path-family sum candidate；关闭 two-route upper/lower family sum cancellation 与 Born-shaped zero boundary；path-sum algebra 已由 S5g 承接，仍不证明 all-path enumeration、path integral 或经验闭合 |
| 2026-05-08 | S5g | success | 新增 finite path-sum algebra candidate；关闭 append / permutation / reverse stability 与 cancellation stability；endpoint-indexed family 已由 S5h 承接，仍不证明 all-path enumeration、path integral 或经验闭合 |
| 2026-05-08 | S5h | success | 新增 endpoint-indexed finite path-family candidate；关闭 same-endpoint family 到 endpoint-indexed family 的转换、sum/weight preservation 与 two-route endpoint-indexed cancellation；filter/support normalization 已由 S5i 承接，仍不证明 all-path enumeration、path integral 或经验闭合 |
| 2026-05-08 | S5i | success | 新增 endpoint support normalization candidate；关闭 amplitude-complete filter preservation、Born-shaped preservation、duplicate expansion 与 duplicated zero-sum cancellation，仍不证明 quotient 去重、all-path enumeration、path integral 或经验闭合 |
| 2026-05-08 | S5j | success | 新增 two-route source/target enumeration candidate；关闭 toy source/target two-step middle enumeration 与 endpoint family middle completeness，仍不证明 general all-path enumeration、path integral 或经验闭合 |
| 2026-05-08 | S5k | success | 新增 finite two-step path identity-key candidate；关闭 visible key boundary、two-route key separation 与 toy source/target key completeness；finite visible-key quotient candidate 已由 S5l 承接，仍不证明 quotient type construction、general all-path enumeration、path integral 或经验闭合 |
| 2026-05-08 | S5l | success | 新增 finite visible-key quotient candidate；关闭 key-equivalence、key-compatible amplitude descent、duplicate compensation 与 two-route key-level cancellation，仍不证明 quotient type construction、general all-path enumeration、path integral 或经验闭合 |

## 统一用语正名

本文中的“统一”按已经关闭的形式结构来读。只要含义对应 theorem 与文档锚点，就按其正名使用：

| 词 | 在本路线中的含义 | 结构依据 |
|---|---|---|
| 逐步统一 | 多个形式接口逐步合取到同一个候选 bridge summary | S0-S5l 已关闭的 summary theorem 与路线日志 |
| 候选统一 | Lean 中有更强的 typed skeleton，且把未闭合经验项接入 pending ledger | `FiniteProcess`、S2-S5l 候选接口、后续 S7 ledger |
| 最小统一摘要 | 已关闭 theorem 的保守合取，作为当前阶段的统一读法 | `markov_causal_bridge_summary` 与各阶段 `*_summary` theorem |

推荐正名句：

```text
本路线追求逐步增强的形式统一候选；
每一步以 Lean 出口、文档锚点和失败记录实事求是地确认含义；
已经关闭的 summary theorem 就是当前阶段的统一内容，
尚未闭合的概率律、真实 quantum channel law、几何恢复与经验 ledger
作为后续结构继续推进。
```
