# 大统一逐步验证路线

目标：把 Markov-因果桥从最小 typed skeleton 推进为逐步增强的验证程序。本文把“统一”限定为已经关闭或计划关闭的形式接口；量子引力、general Hamiltonian/unitary amplitude dynamics、measurement semantics、度规恢复和经验闭合分别作为后续结构单独推进。

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
-> 路径商类候选
-> 规范代表元候选
-> 商支撑枚举候选
-> 商支撑代数候选
-> 观测账本候选
-> 作用量相位律候选
-> 逐步统一候选摘要
-> 有限概率归一化候选
-> 归一化质量求和候选
-> Born 权重条件归一候选
-> Born 分布边界候选
-> channelCompose 候选
-> channelCompose 结合律候选
-> sum-over-middle 通道组合候选
-> composed support 的 Born/probability boundary
-> unitary/CPTP ledger
-> Born rule 推导候选
-> 路径权重乘法候选
-> 非平凡量子通道律候选
-> 概率幅到测量权重候选
-> 作用相位到测量权重链
-> 有限相位演化候选
-> 连续作用量泛函候选
-> 路径空间作用量泛函候选
-> 有限作用量极值候选
-> 几何候选接口
-> 经验 pending ledger
-> 更强统一摘要 theorem
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
lake build SSBX.Foundation.Modern.QuantumRelativityPathQuotientBridge
lake build SSBX.Foundation.Modern.QuantumRelativityCanonicalRepresentativeBridge
lake build SSBX.Foundation.Modern.QuantumRelativityQuotientSupportBridge
lake build SSBX.Foundation.Modern.QuantumRelativityQuotientSupportAlgebraBridge
lake build SSBX.Foundation.Modern.QuantumRelativityObservableLedgerBridge
lake build SSBX.Foundation.Modern.QuantumRelativityActionPhaseLawBridge
lake build SSBX.Foundation.Modern.QuantumRelativityStepwiseUnificationBridge
lake build SSBX.Foundation.Modern.QuantumRelativityFiniteProbabilityNormalizationBridge
lake build SSBX.Foundation.Modern.QuantumRelativityNormalizedMassBridge
lake build SSBX.Foundation.Modern.QuantumRelativityBornWeightNormalizationBridge
lake build SSBX.Foundation.Modern.QuantumRelativityBornDistributionBridge
lake build SSBX.Foundation.Modern.QuantumRelativityChannelComposeBridge
lake build SSBX.Foundation.Modern.QuantumRelativityChannelComposeAssociativityBridge
lake build SSBX.Foundation.Modern.QuantumRelativitySumOverMiddleChannelBridge
lake build SSBX.Foundation.Modern.QuantumRelativitySumOverMiddleBornBoundaryBridge
lake build SSBX.Foundation.Modern.QuantumRelativityUnitaryCPTPLedgerBridge
lake build SSBX.Foundation.Modern.QuantumRelativityBornRuleDerivationBridge
lake build SSBX.Foundation.Modern.QuantumRelativityPathWeightMultiplicationBridge
lake build SSBX.Foundation.Modern.QuantumRelativityNontrivialChannelLawBridge
lake build SSBX.Foundation.Modern.QuantumRelativityBornMeasurementBridge
lake build SSBX.Foundation.Modern.QuantumRelativityActionAmplitudeMeasurementBridge
lake build SSBX.Foundation.Modern.QuantumRelativityFinitePhaseEvolutionBridge
lake build SSBX.Foundation.Modern.QuantumRelativityContinuousActionFunctionalBridge
lake build SSBX.Foundation.Modern.QuantumRelativityPathSpaceActionFunctionalBridge
lake build SSBX.Foundation.Modern.QuantumRelativityFiniteActionExtremumBridge
lake build SSBX
git diff --check --
```

## S0 · 基线重审

目标：确认现有 Markov-因果桥只关闭最小骨架，不把最小骨架误读为物理统一。

| 项 | 内容 |
|---|---|
| Lean 出口 | 保持 `markov_causal_bridge_summary`、`measurement_event_alignment`、`markov_bridge_not_direct_language_addition` 为 `machineChecked` |
| 文档出口 | 本文件与验证计划明确列出未关闭项：stochastic semantics、general all-path enumeration、path integral、general Hamiltonian/unitary amplitude dynamics、smooth/infinite-dimensional path-space action functional、continuous variation space、stationary action principle、general Hilbert measurement、POVM/PVM、decoherence、physical unitary/CPTP/Kraus/density channel law、干涉、因果偏序、度规恢复、经验闭合；finite row sum-one boundary 已由 S9 后续关闭，Markov/amplitude compatibility 下的 Born rule derivation 已由 S18 关闭，finite path-weight multiplication 已由 S19 关闭，nontrivial finite quantum-channel law 已由 S20 关闭，one-qubit computational-basis measurement weights 已由 S21 关闭，finite action branch to measurement weights chain 已由 S22 关闭，finite period-two phase evolution 已由 S23 关闭，displayed continuous action-coordinate functional 已由 S24 关闭，finite path-space action functional 已由 S25 关闭，finite action extremum boundary 已由 S26 关闭 |
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
| 文档更新 | 说明新增 path witness composition 与 code-successor/no-self-loop 约束；path-weight multiplication 已由 S19 承接，未证明的因果集公理继续列为未纳入 |
| 后续结构 | stochastic semantics、general all-path enumeration、path integral、spacetime、light cone、Lorentzian metric 或完整 causal set theory 需要额外结构与 theorem |

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
| `path_weight_multiplication_bridge_summary` | `QuantumRelativityPathWeightMultiplicationBridge.lean` | S19 已关闭 finite kernel path 的 weight append law |

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
| 后续结构 | 候选测量律要成为经验证实的量子概率律，需要在 S5q 最小 ledger 上继续加入数据判准和经验验证接口 |

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
| 边界保留 | S5k 不证明 quotient class，只证明 key equality 对可见路径数据的保持与 toy source/target key completeness；quotient class 已由 S5m 承接 |

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
| 文档读法 | 正面写明已证 finite visible-key quotient candidate；visible-key quotient class 已由 S5m 承接，proof-field path equality、general all-path enumeration、path integral、Born rule derivation 与 empirical prediction 仍需后续结构 |
| 边界保留 | S5l 不构造 `Quot`，只证明 key-equivalence、key-compatible amplitude descent、duplicate compensation 与 two-route key-level cancellation |

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `finite_key_quotient_bridge_summary` | `QuantumRelativityFiniteKeyQuotientBridge.lean` | 合取 quotient-candidate relation、key compatibility、duplicate compensation 与 two-route key cancellation |
| `TwoStepPathKeyEquivalent` | `QuantumRelativityFiniteKeyQuotientBridge.lean` | visible key equality 作为 candidate relation |
| `key_equivalent_paths_amplitude_eq` | `QuantumRelativityFiniteKeyQuotientBridge.lean` | key-compatible amplitudes 在同 key paths 上相同 |
| `endpoint_indexed_key_sum_eq_path_sum_of_factor` | `QuantumRelativityFiniteKeyQuotientBridge.lean` | endpoint-indexed path sum 可在 factor-through-key 条件下降到 key-list sum |
| `two_route_key_born_weight_zero` | `QuantumRelativityFiniteKeyQuotientBridge.lean` | two-route key-level cancellation 接回 Born-shaped zero boundary |

## S5m · 路径商类候选

目标：把 S5l 的 visible-key equivalence 包装成 Lean `Setoid` / `Quot`，并证明 visible key 与 key-level amplitude 可下降到 quotient class。

| 项 | 内容 |
|---|---|
| Lean 出口 | `path_quotient_bridge_summary` |
| 最低 theorem 形态 | `twoStepPathKeySetoid`、`TwoStepPathKeyQuotient`、`twoStepPathQuotientClass`、`quotientVisibleKey`、`quotient_key_amplitude_matches_path_of_factor`、`two_route_source_target_quotient_complete` |
| 失败记录 | 若 quotient class 与 proof-field equality 混淆，记录为 `scope overclaim`；若 quotient descent 失败，记录为 `Lean proof failure` |
| 文档读法 | 正面写明已证 visible-key quotient class construction；two-route canonical representative 已由 S5n 承接，general choice function、proof-field path equality、general all-path enumeration、path integral、Born rule derivation 与 empirical prediction 仍需后续结构 |
| 边界保留 | S5m 不证明原 witness proof fields 相等，不选一般 representative，不枚举一般路径空间 |

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `path_quotient_bridge_summary` | `QuantumRelativityPathQuotientBridge.lean` | 合取 quotient class construction、quotient descent 与 two-route quotient completeness |
| `twoStepPathKeySetoid`、`TwoStepPathKeyQuotient` | `QuantumRelativityPathQuotientBridge.lean` | 以 visible-key equality 构造 `Setoid` 与 `Quot` |
| `quotientVisibleKey`、`quotient_visible_key_mk` | `QuantumRelativityPathQuotientBridge.lean` | quotient class 可读回 visible key |
| `quotient_key_amplitude_matches_path_of_factor` | `QuantumRelativityPathQuotientBridge.lean` | key-compatible amplitude 可下降到 quotient class |
| `two_route_upper_lower_quotient_classes_distinct`、`two_route_source_target_quotient_complete` | `QuantumRelativityPathQuotientBridge.lean` | two-route quotient classes 保持可区分并完成 toy source/target enumeration |

## S5n · 规范代表元候选

目标：为 two-route toy source/target quotient classes 选出 displayed upper/lower representatives，并证明任意 toy source/target two-step path 的商类有这些代表元。

| 项 | 内容 |
|---|---|
| Lean 出口 | `canonical_representative_bridge_summary` |
| 最低 theorem 形态 | `CanonicalRepresentativeFor`、`two_route_upper_canonical_represents`、`two_route_lower_canonical_represents`、`two_route_source_target_has_canonical_representative` |
| 失败记录 | 若把 toy representative 冒充 general choice function，记录为 `scope overclaim`；若 representative completeness 失败，记录为 `Lean proof failure` |
| 文档读法 | 正面写明已证 two-route canonical representative boundary；general choice function、proof-field path equality、general all-path enumeration、path integral、Born rule derivation 与 empirical prediction 仍需后续结构 |
| 边界保留 | S5n 不为任意 process 或任意 quotient class 选代表元，只处理 two-route toy source/target quotient classes |

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `canonical_representative_bridge_summary` | `QuantumRelativityCanonicalRepresentativeBridge.lean` | 合取 displayed representatives、representative completeness 与 S5m quotient completeness |
| `CanonicalRepresentativeFor` | `QuantumRelativityCanonicalRepresentativeBridge.lean` | witness 代表某个 quotient class |
| `two_route_source_target_has_canonical_representative` | `QuantumRelativityCanonicalRepresentativeBridge.lean` | 任意 toy source/target path 的 quotient class 由 upper/lower displayed path 代表 |

## S5o · 商支撑枚举候选

目标：把 two-route displayed quotient classes 升级为有限 quotient-support list，并证明支撑覆盖、visible-key readback、quotient-level cancellation 与 Born-shaped zero boundary。

| 项 | 内容 |
|---|---|
| Lean 出口 | `quotient_support_bridge_summary` |
| 最低 theorem 形态 | `quotientSupportAmplitudeSum`、`quotientSupportVisibleKeys`、`two_route_source_target_quotient_support_complete`、`two_route_quotient_support_amplitude_sum_cancels` |
| 失败记录 | 若 quotient support sum 与 key sum 只差定义展开，记录具体失败 theorem 与修正；若覆盖失败，记录为 `Lean proof failure` |
| 文档读法 | 正面写明已证 finite quotient-support boundary；quotient-support algebra、general all-path enumeration、path integral、Born rule derivation 与 empirical prediction 仍需后续结构 |
| 边界保留 | S5o 不枚举任意 process 的全部路径，只处理 two-route toy source/target quotient support |

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `quotient_support_bridge_summary` | `QuantumRelativityQuotientSupportBridge.lean` | 合取 quotient support coverage、visible-key readback、cancellation、representative completeness 与文构造覆盖 |
| `two_route_quotient_support_visible_keys_eq` | `QuantumRelativityQuotientSupportBridge.lean` | displayed quotient support 可回读为 displayed key list |
| `two_route_quotient_support_amplitude_sum_cancels` | `QuantumRelativityQuotientSupportBridge.lean` | quotient-support 层保持 `1 + (-1) = 0` |

## S5p · 商支撑代数候选

目标：为 finite quotient-support lists 增加 append / permutation / reverse / duplicate algebra，并证明 two-route quotient-support cancellation 在这些有限操作下稳定。

| 项 | 内容 |
|---|---|
| Lean 出口 | `quotient_support_algebra_bridge_summary` |
| 最低 theorem 形态 | `quotient_support_amplitude_sum_append`、`quotient_support_amplitude_sum_perm`、`quotient_support_amplitude_sum_reverse`、`quotient_support_duplicate_cancels_of_canceling` |
| 失败记录 | 若 dependent type 显式标注导致 namespace mismatch，记录对应 process 名称与修正；若 algebra law 失败，记录为 `Lean proof failure` |
| 文档读法 | 正面写明已证 quotient-support finite list algebra；general all-path enumeration、path integral、Born rule derivation 与 empirical prediction 仍需后续结构 |
| 边界保留 | S5p 不把 finite list algebra 误读为一般 path integral |

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `quotient_support_algebra_bridge_summary` | `QuantumRelativityQuotientSupportAlgebraBridge.lean` | 合取 quotient-support algebra、two-route cancellation stability 与文构造覆盖 |
| `two_route_reversed_quotient_support_amplitude_cancels` | `QuantumRelativityQuotientSupportAlgebraBridge.lean` | two-route support 反序后仍相消 |
| `two_route_double_quotient_support_amplitude_cancels` | `QuantumRelativityQuotientSupportAlgebraBridge.lean` | support append reversed support 后仍相消 |

## S5q · 观测账本候选

目标：把 two-route quotient-support cancellation 登记到一个 observable ledger entry 中，同时明确 pending entry 不是 empirical closure。

| 项 | 内容 |
|---|---|
| Lean 出口 | `observable_ledger_bridge_summary` |
| 最低 theorem 形态 | `ObservableLedgerEntry`、`EmpiricalClosureStatus`、`pending_not_empirically_closed`、`twoRouteCancellationObservableLedgerEntry`、`two_route_observable_ledger_not_empirically_closed` |
| 失败记录 | 若 pending status 与 empirical closure 被混淆，记录为 `scope overclaim`；若 ledger boundary 不能接回 S5p sum/weight，记录为 `Lean proof failure` |
| 文档读法 | 正面写明已证 observable ledger candidate boundary；外部数据、误差模型、可测预言 theorem 与 empirical closure 仍需后续结构 |
| 边界保留 | S5q 只登记候选账本项，不证明实验闭合、数据校准、Born rule 推导、path integral 或 continuous action law |

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `observable_ledger_bridge_summary` | `QuantumRelativityObservableLedgerBridge.lean` | 合取 two-route pending ledger entry、zero sum/weight、S5p double-support cancellation 与文构造覆盖 |
| `pending_not_empirically_closed` | `QuantumRelativityObservableLedgerBridge.lean` | pending entry 与 externally closed status 不相容 |
| `two_route_observable_ledger_amplitude_zero` | `QuantumRelativityObservableLedgerBridge.lean` | two-route ledger entry 的 displayed amplitude sum 为 `0` |
| `two_route_observable_ledger_weight_zero` | `QuantumRelativityObservableLedgerBridge.lean` | two-route ledger entry 的 Born-shaped candidate weight 为 `0` |
| `two_route_observable_ledger_not_empirically_closed` | `QuantumRelativityObservableLedgerBridge.lean` | two-route ledger entry 保持 pending，不被读成 empirical closure |

## S5r · 作用量相位律候选

目标：把 S5q 的 quotient-support cancellation 进一步写成 finite action index 到 phase/amplitude 的 law candidate，并接回 pending ledger。

| 项 | 内容 |
|---|---|
| Lean 出口 | `action_phase_law_bridge_summary` |
| 最低 theorem 形态 | `actionIndexPhase`、`actionIndexAmplitude`、`QuotientActionPhaseLawCandidate`、`two_route_action_phase_support_amplitude_cancels`、`twoRouteActionPhaseObservableLedgerEntry` |
| 失败记录 | 若 quotient readback 展开后无法化简，记录 `Quot.lift` 暴露点；若 action law 不能接回 ledger，记录为 `Lean proof failure` |
| 文档读法 | 正面写明已证 finite period-two action-to-phase law candidate；displayed continuous action functional 已由 S24 承接，finite quotient path-space action functional 已由 S25 承接，smooth/infinite-dimensional path-space action functional、Hamiltonian/unitary dynamics、path integral 与 empirical closure 仍需后续结构 |
| 边界保留 | S5r 不把 finite action index 误读为连续作用量或真实动力学 |

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `action_phase_law_bridge_summary` | `QuantumRelativityActionPhaseLawBridge.lean` | 合取 finite action-phase law、pending ledger boundary 与文构造覆盖 |
| `action_index_zero_one_amplitudes_cancel` | `QuantumRelativityActionPhaseLawBridge.lean` | index `0/1` 分别导出 `1/-1` 并相消 |
| `two_route_action_phase_support_amplitude_cancels` | `QuantumRelativityActionPhaseLawBridge.lean` | finite action law 在 two-route quotient support 上相消 |
| `two_route_action_phase_support_born_weight_zero` | `QuantumRelativityActionPhaseLawBridge.lean` | action-phase support sum 接回 Born-shaped zero boundary |
| `two_route_action_phase_observable_ledger_not_empirically_closed` | `QuantumRelativityActionPhaseLawBridge.lean` | action-phase ledger entry 保持 pending |

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

目标：在 S5q 已经给出的最小 observable ledger boundary 上继续加厚，接入外部数据、误差模型、阈值和可测预言 theorem。

| 项 | 内容 |
|---|---|
| Lean 出口 | 扩展 `ObservableLedgerEntry`，或新增 `ObservableCandidate`、`PredictionBoundary`、data/calibration structure |
| 最低 theorem 形态 | `observable_candidate_has_boundary`、`prediction_requires_external_data`、`calibrated_prediction_requires_external_data` |
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
| Lean 出口 | `stepwise_unification_candidate_summary` |
| 最低 theorem 形态 | 合取 concrete bridge、finite probability boundary、`71232` grid、S5r action-phase cancellation、S5q ledger boundary、tagged noncollapse 与 Wen coverage |
| 失败记录 | 已记录 namespace/defeq failure；若后续子阶段未关闭，摘要 theorem 只合取已关闭部分 |
| 文档更新 | 已新增《逐步统一候选摘要 · Markov桥S8》；说明“统一”在本文件中表示形式接口逐渐汇聚 |
| 后续结构 | 终局理论、万有理论、量子引力解决或经验闭合完成需要完整动力学、几何、概率律和经验 ledger 合取 |

通过判准：

```text
摘要 theorem 只合取已经 machine-checked 的阶段；
未关闭阶段在 theorem 外作为 pending ledger 保留。
```

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `stepwise_unification_candidate_summary` | `QuantumRelativityStepwiseUnificationBridge.lean` | 当前已关闭 finite bridge / probability / grid / action-phase / ledger boundaries 的聚合摘要 |
| `PendingBeyondS5r` | `QuantumRelativityStepwiseUnificationBridge.lean` | sum-one、Born derivation、continuous action、path integral、data、unitary/CPTP、metric recovery、empirical closure 保持显式 pending |
| `pending_boundary_not_closed_by_s5r` | `QuantumRelativityStepwiseUnificationBridge.lean` | 每个 pending boundary 在本层 `ClosedByStepwiseS5r = false` |

## S9 · 有限概率归一化候选

目标：把 S2 的 finite probability-kernel denominator interface 升级到最小 finite row sum-one boundary。S9 不做 Born rule 推导，只证明 concrete 与 `71232` grid kernel 的非终端行在显式 row support 上归一为 `1`。

| 项 | 内容 |
|---|---|
| Lean 出口 | `finite_probability_normalization_bridge_summary` |
| 最低 theorem 形态 | 合取 `FiniteSumOneProbabilityBoundaryClosed`、concrete/grid finite probability projection、`71232` grid length、`PendingBeyondS9` 与 Wen coverage |
| 失败记录 | 已记录 list-sum / `Fin` singleton / Rat coercion failure；修正为直接分支证明 |
| 文档更新 | 已新增《有限概率归一化候选 · Markov桥S9》 |
| 后续结构 | Markov/amplitude compatibility 下的 Born rule derivation 已由 S18 承接；unitary/CPTP、metric recovery 与 empirical closure 继续 pending |

通过判准：

```text
concrete 与 grid kernel 均有 sound/complete row support；
rowWeightSum = rowTotal；
非终端行的 normalizedRowTotalCandidate = 1。
```

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `finite_probability_normalization_bridge_summary` | `QuantumRelativityFiniteProbabilityNormalizationBridge.lean` | finite row sum-one probability boundary 已关闭 |
| `FiniteSumOneProbabilityBoundaryClosed` | `QuantumRelativityFiniteProbabilityNormalizationBridge.lean` | concrete/grid row support 与非终端行归一合取 |
| `PendingBeyondS9` | `QuantumRelativityFiniteProbabilityNormalizationBridge.lean` | sum-one row boundary 不再列入 pending；Born derivation 等较大边界仍 pending |

## S10 · 归一化质量求和候选

目标：把 S9 的 row-total candidate 改写为逐项 normalized mass 的有限概率分布律。S10 不做 Born rule 推导，只证明在已显示 row support 上，`normalizedMass = weight / rowTotal` 的有限和为 `1`。

| 项 | 内容 |
|---|---|
| Lean 出口 | `normalized_mass_bridge_summary` |
| 最低 theorem 形态 | 合取 `FiniteSumOneProbabilityBoundaryClosed`、`FiniteNormalizedMassBoundaryClosed`、concrete/grid finite probability projection、`71232` grid length、`PendingBeyondS10` 与 Wen coverage |
| 失败记录 | 已记录 direct concrete/grid 展开 proof 试探；修正为泛型 algebra bridge |
| 文档更新 | 已新增《归一化质量求和候选 · Markov桥S10》 |
| 后续结构 | 条件式 Born weight 非负与 sum-one、Born distribution boundary、channel composition、metric recovery 与 empirical closure 继续推进 |

通过判准：

```text
rowWeightSum_eq_rowTotal 有独立命名出口；
normalizedMassSum = normalizedRowTotalCandidate；
任一 normalizable finite row support 的 normalizedMass 求和为 1；
concrete 与 grid 非终端行均实例化。
```

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `rowWeightSum_eq_rowTotal` | `QuantumRelativityFiniteProbabilityNormalizationBridge.lean` | S9 row-weight sum law 的命名出口 |
| `normalizedMass_sum_one` | `QuantumRelativityNormalizedMassBridge.lean` | finite row support 上的 classical probability law |
| `normalized_mass_bridge_summary` | `QuantumRelativityNormalizedMassBridge.lean` | concrete/grid normalized mass sum-one boundary 已关闭 |
| `PendingBeyondS10` | `QuantumRelativityNormalizedMassBridge.lean` | amplitude/Born normalized support 与 Born derivation 等较大边界仍 pending |

## S11 · Born 权重条件归一候选

目标：先做条件式 Born 权重律。S11 不从动力学或 Markov 权重推出 Born rule，只证明有限 amplitude support 一旦由 `ampProb` 归一，则 S5 的 `candidateWeight` 非负且 finite sum 为 `1`。

| 项 | 内容 |
|---|---|
| Lean 出口 | `born_weight_normalization_bridge_summary` |
| 最低 theorem 形态 | 合取 S9/S10 finite probability facts、`ConditionalBornWeightNormalizationBoundaryClosed`、unit support witness、`PendingBeyondS11` 与 Wen coverage |
| 失败记录 | 已记录 `List.map` 字段投影 simp failure；修正为 list induction |
| 文档更新 | 已新增《Born权重条件归一候选 · Markov桥S11》 |
| 后续结构 | `born_distribution_boundary`、channel composition、continuous action law、path integral、metric recovery 与 empirical closure 继续推进 |

通过判准：

```text
amplitudeSupportWeightSum 定义 finite ampProb sum；
bornCandidateWeightSum_eq_amplitudeSupportWeightSum；
born_weight_nonnegative_and_sum_one_if_normalized；
unitAmplitudeSupport 作为最小 normalized witness。
```

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `bornCandidateWeightSum_eq_amplitudeSupportWeightSum` | `QuantumRelativityBornWeightNormalizationBridge.lean` | candidateWeight sum 与 ampProb support sum 对齐 |
| `born_weight_nonnegative_and_sum_one_if_normalized` | `QuantumRelativityBornWeightNormalizationBridge.lean` | normalized finite amplitude support 的条件式概率律 |
| `born_weight_normalization_bridge_summary` | `QuantumRelativityBornWeightNormalizationBridge.lean` | conditional Born-weight normalization boundary 已关闭 |
| `PendingBeyondS11` | `QuantumRelativityBornWeightNormalizationBridge.lean` | Born distribution boundary 与 Born derivation 等较大边界仍 pending |

## S12 · Born 分布边界候选

目标：把 S11 的 conditional Born-weight law 装进 finite probability distribution interface。S12 保留 amplitude support、amplitude sum、candidate support 与 `candidateWeight` projection 的同一 boundary object。

| 项 | 内容 |
|---|---|
| Lean 出口 | `born_distribution_bridge_summary` |
| 最低 theorem 形态 | 合取 S9/S10/S11 probability facts、`BornDistributionBoundaryClosed`、`PendingBeyondS12` 与 Wen coverage |
| 失败记录 | 已记录结构字段 `simp` failure；修正为显式 existential witness |
| 文档更新 | 已新增《Born分布边界候选 · Markov桥S12》 |
| 后续结构 | `channelCompose`、continuous action law、path integral、metric recovery 与 empirical closure 继续推进 |

通过判准：

```text
FiniteProbabilityDistributionInterface；
BornDistributionBoundary；
born_distribution_boundary；
born_distribution_bridge_summary。
```

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `born_distribution_boundary` | `QuantumRelativityBornDistributionBridge.lean` | normalized finite amplitude support 进入 finite probability distribution boundary |
| `born_distribution_bridge_summary` | `QuantumRelativityBornDistributionBridge.lean` | S9-S12 probability-side boundaries 的合取摘要 |
| `PendingBeyondS12` | `QuantumRelativityBornDistributionBridge.lean` | channel composition 与 Born derivation 等较大边界仍 pending |

## S13 · channelCompose 候选

目标：给 S4 的 `QuantumChannelSkeleton` 加入最小 composition operation。S13 不证明物理 Hilbert/unitary/CPTP/Kraus/density-matrix channel law，只证明 current skeleton 的候选组合保持 support-to-step soundness。

| 项 | 内容 |
|---|---|
| Lean 出口 | `channel_compose_bridge_summary` |
| 最低 theorem 形态 | 合取 `BornDistributionBoundaryClosed`、`ChannelCompositionBoundaryClosed`、concrete/grid channel candidates、`PendingBeyondS13` 与 Wen coverage |
| 失败记录 | stdin 试探一次通过；保留“不是 physical channel law”的概念边界 |
| 文档更新 | 已新增《channelCompose候选 · Markov桥S13》 |
| 后续结构 | associativity / identity obstruction 已由 S14 承接；继续推进 sum-over-middle composition、probability push-forward、unitary/CPTP ledger、metric recovery 与 empirical closure |

通过判准：

```text
channelCompose；
channelCompose_amplitude；
channelCompose_keeps_left_classical_boundary；
channelCompose_support_implies_step；
channel_compose_bridge_summary。
```

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `channelCompose_amplitude` | `QuantumRelativityChannelComposeBridge.lean` | composed amplitude 是逐点乘积 |
| `channelCompose_keeps_left_classical_boundary` | `QuantumRelativityChannelComposeBridge.lean` | composition 保留左侧 finite classical boundary |
| `channelCompose_support_implies_step` | `QuantumRelativityChannelComposeBridge.lean` | nonzero composed amplitude 仍推出 process step |
| `channel_compose_bridge_summary` | `QuantumRelativityChannelComposeBridge.lean` | current skeleton channel composition boundary 已关闭 |
| `PendingBeyondS13` | `QuantumRelativityChannelComposeBridge.lean` | physical channel law、unitary/CPTP 与 empirical closure 仍 pending |

## S14 · channelCompose 结合律与 identity obstruction

目标：关闭 S13 pointwise `channelCompose` 的 associativity boundary，同时明确普通 diagonal identity channel 在当前 support-respecting skeleton 中为什么不能直接给出。

| 项 | 内容 |
|---|---|
| Lean 出口 | `channel_compose_associativity_bridge_summary` |
| 最低 theorem 形态 | 合取 `ChannelCompositionBoundaryClosed`、`ChannelComposeAssociativityBoundaryClosed`、concrete/grid diagonal identity obstruction 与 Wen coverage |
| 失败记录 | theorem 试探一次修正：`QuantumAmplitudeSupport` 需先展开后重写 diagonal amplitude |
| 文档更新 | 已新增《channelCompose结合律候选 · Markov桥S14》 |
| 后续结构 | sum-over-middle composition、probability push-forward、unitary/CPTP ledger |

通过判准：

```text
channelCompose_associative_amplitude；
channelCompose_associative_classical_boundary；
no_self_step_blocks_channel_diagonal_identity；
channel_compose_associativity_bridge_summary。
```

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `channelCompose_associative_amplitude` | `QuantumRelativityChannelComposeAssociativityBridge.lean` | pointwise composition 重新括号化后 amplitude 相同 |
| `channelCompose_associative_classical_boundary` | `QuantumRelativityChannelComposeAssociativityBridge.lean` | 重新括号化后仍保留最左侧 classical boundary |
| `no_self_step_blocks_channel_diagonal_identity` | `QuantumRelativityChannelComposeAssociativityBridge.lean` | diagonal identity amplitude 会推出 self-step，因此被 no-self-step process 阻塞 |
| `channel_compose_associativity_bridge_summary` | `QuantumRelativityChannelComposeAssociativityBridge.lean` | S14 algebra/obstruction boundary 已关闭 |

## S15 · sum-over-middle 通道组合候选

目标：补上经中间态求和的 finite channel-composition boundary。S15 不把结果塞回当前 one-step `QuantumChannelSkeleton`，只证明非零 endpoint sum 推出 two-step reachability。

| 项 | 内容 |
|---|---|
| Lean 出口 | `sum_over_middle_channel_bridge_summary` |
| 最低 theorem 形态 | 合取 `ChannelCompositionBoundaryClosed`、`ChannelComposeAssociativityBoundaryClosed`、`SumOverMiddleChannelBoundaryClosed`、concrete two-step witness 与 Wen coverage |
| 失败记录 | theorem 试探一次修正：`List.mem_map` 的等式方向需用 `rw [hbeq]`，concrete support proof 需展开 `QuantumAmplitudeSupport` |
| 文档更新 | 已新增《sum-over-middle通道组合候选 · Markov桥S15》 |
| 后续结构 | composed support 的 Born/probability boundary、unitary/CPTP ledger、metric recovery 与 empirical closure |

通过判准：

```text
sumOverMiddleChannelAmplitude；
TwoStepReachableViaList；
sumOverMiddle_support_implies_two_step；
SumOverMiddleChannelBoundaryClosed；
concrete_sumOverMiddle_prepared_measured_amplitude；
sum_over_middle_channel_bridge_summary。
```

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `sumOverMiddle_support_implies_two_step` | `QuantumRelativitySumOverMiddleChannelBridge.lean` | 非零 finite middle-list endpoint sum 推出某个 listed middle 的 two-step witness |
| `sum_over_middle_channel_boundary_closed` | `QuantumRelativitySumOverMiddleChannelBridge.lean` | 任意 middle list 与两个 channel candidates 都有 sum-over-middle boundary object |
| `concrete_sumOverMiddle_prepared_measured_amplitude` | `QuantumRelativitySumOverMiddleChannelBridge.lean` | concrete `prepared -> evolved -> measured` 的 composed endpoint amplitude 为 `1` |
| `concrete_prepared_measured_not_one_step` | `QuantumRelativitySumOverMiddleChannelBridge.lean` | 同一 endpoint pair 不是 concrete one-step edge |
| `sum_over_middle_channel_bridge_summary` | `QuantumRelativitySumOverMiddleChannelBridge.lean` | S15 finite middle-list composition boundary 已关闭 |

## S16 · sum-over-middle Born 边界候选

目标：把 S15 composed endpoint amplitude support 接到 S12 finite Born distribution boundary。S16 仍是条件式：support 已由 `ampProb` 归一时才给出 probability interface。

| 项 | 内容 |
|---|---|
| Lean 出口 | `sum_over_middle_born_distribution_bridge_summary` |
| 最低 theorem 形态 | 合取 `SumOverMiddleChannelBoundaryClosed`、`BornDistributionBoundaryClosed`、`SumOverMiddleBornDistributionBoundaryClosed`、concrete `[1]` support 与 Wen coverage |
| 失败记录 | concrete dependent existential witness 展开时触发 `whnf` heartbeat timeout；改用 generic closed boundary + concrete normalized input |
| 文档更新 | 已新增《sum-over-middle Born边界候选 · Markov桥S16》 |
| 后续结构 | unitary/CPTP ledger、metric recovery 与 empirical closure |

通过判准：

```text
sumOverMiddleEndpointAmplitudeSupport；
SumOverMiddleBornDistributionBoundary；
sum_over_middle_born_distribution_boundary；
sum_over_middle_born_distribution_boundary_closed；
concrete_sumOverMiddle_endpoint_amplitude_support；
concrete_composed_endpoint_amplitude_support_normalized；
sum_over_middle_born_distribution_bridge_summary。
```

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `sum_over_middle_born_distribution_boundary` | `QuantumRelativitySumOverMiddleBornBoundaryBridge.lean` | normalized composed endpoint amplitude support 进入 S12 finite Born boundary |
| `sum_over_middle_born_distribution_boundary_closed` | `QuantumRelativitySumOverMiddleBornBoundaryBridge.lean` | 条件式 composed Born boundary 对任意 endpoint support 关闭 |
| `concrete_sumOverMiddle_endpoint_amplitude_support` | `QuantumRelativitySumOverMiddleBornBoundaryBridge.lean` | concrete composed support 的 amplitude list 为 `[1]` |
| `concrete_composed_endpoint_amplitude_support_normalized` | `QuantumRelativitySumOverMiddleBornBoundaryBridge.lean` | concrete composed support normalized |
| `sum_over_middle_born_distribution_bridge_summary` | `QuantumRelativitySumOverMiddleBornBoundaryBridge.lean` | S16 composed Born boundary 已关闭 |

## S17 · unitary/CPTP 账本边界

目标：把 S13-S16 已关闭 channel/probability skeleton 与 physical Hilbert/unitary/CPTP/Kraus/density-matrix channel law 的缺口放入同一个 typed ledger。S17 不证明 physical channel law，只关闭 required-but-not-closed ledger。

| 项 | 内容 |
|---|---|
| Lean 出口 | `unitary_cptp_ledger_bridge_summary` |
| 最低 theorem 形态 | 合取 `BornDistributionBoundaryClosed`、`SumOverMiddleChannelBoundaryClosed`、`SumOverMiddleBornDistributionBoundaryClosed`、current closed items、unitary/CPTP required-but-not-closed items 与 Wen coverage |
| 失败记录 | 无 Lean proof failure；ledger items 均为 finite inductive cases |
| 文档更新 | 已新增《unitary-CPTP账本边界 · Markov桥S17》 |
| 后续结构 | 非平凡 finite channel law 已由 S20 承接；physical unitary/CPTP/Kraus/density-matrix law、metric recovery 与 empirical closure 仍需额外结构 |

通过判准：

```text
CurrentChannelBoundaryItem；
current_channel_boundary_closed_by_s17；
UnitaryCPTPLedgerItem；
unitary_cptp_ledger_required_but_not_closed_by_s17；
unitary_cptp_ledger_bridge_summary。
```

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `current_channel_boundary_closed_by_s17` | `QuantumRelativityUnitaryCPTPLedgerBridge.lean` | S13-S16 当前 skeleton items 被登记为 closed |
| `unitary_cptp_ledger_required_but_not_closed_by_s17` | `QuantumRelativityUnitaryCPTPLedgerBridge.lean` | Hilbert/Kraus/density/CPTP 等物理项 required but not closed |
| `unitary_cptp_ledger_bridge_summary` | `QuantumRelativityUnitaryCPTPLedgerBridge.lean` | S17 ledger boundary 已关闭 |

## S18 · Born rule 推导候选

目标：把 S9/S10 Markov row probability law、S11/S12 Born distribution boundary 与 S4/S5 amplitude bridge 接起来。S18 证明：若同一 row support 上有 `MarkovAmplitudeCompatibility`，即 `ampProb amplitude = normalizedMass`，则 Markov row normalization 推出 normalized amplitude support，并接入 S12 finite Born distribution boundary。

| 项 | 内容 |
|---|---|
| Lean 出口 | `born_rule_derivation_bridge_summary` |
| 最低 theorem 形态 | 合取 `BornDistributionBoundaryClosed`、`SumOverMiddleBornDistributionBoundaryClosed`、`MarkovAmplitudeBornRuleDerivationClosed`、concrete prepared-row witness 与 Wen coverage |
| 失败记录 | Rat-to-Real list sum cast、`List.map_map` composition shape、concrete row support projection 展开均已记录 |
| 文档更新 | 已新增《Born rule推导候选 · Markov桥S18》 |
| 后续结构 | general Hamiltonian/unitary amplitude dynamics、measurement semantics、decoherence、unitary/CPTP、metric recovery 与 empirical closure |

通过判准：

```text
list_map_rat_sum_cast；
realNormalizedMassSum_eq_one；
MarkovAmplitudeCompatibility；
markov_amplitude_support_normalized；
born_candidate_weights_match_markov_masses；
markov_amplitude_born_rule_derivation；
concrete_prepared_born_rule_from_markov_amplitude_bridge；
born_rule_derivation_bridge_summary。
```

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `MarkovAmplitudeCompatibility` | `QuantumRelativityBornRuleDerivationBridge.lean` | Markov row support、amplitude support 与 `ampProb = normalizedMass` 的兼容接口 |
| `markov_amplitude_support_normalized` | `QuantumRelativityBornRuleDerivationBridge.lean` | compatibility + Markov row normalization 推出 amplitude support normalized |
| `born_candidate_weights_match_markov_masses` | `QuantumRelativityBornRuleDerivationBridge.lean` | S5 candidateWeight 在 support 上等于 Markov normalizedMass |
| `markov_amplitude_born_rule_derivation` | `QuantumRelativityBornRuleDerivationBridge.lean` | compatibility 下接入 S12 Born distribution boundary |
| `concrete_prepared_born_rule_from_markov_amplitude_bridge` | `QuantumRelativityBornRuleDerivationBridge.lean` | concrete prepared row witness |
| `born_rule_derivation_bridge_summary` | `QuantumRelativityBornRuleDerivationBridge.lean` | S18 Born-rule derivation boundary 已关闭 |

## S19 · 路径权重乘法候选

目标：把 S3 中旧 `pathWeight` 占位接口推进为可计算的 finite kernel path weight。S19 保留旧 `pathWeight = 1` 的 placeholder multiplication，同时新增 `KernelEdge` / `KernelPath` 精化层：路径权重是有限 edge weights product，append composition 的权重等于左右路径权重乘积。

| 项 | 内容 |
|---|---|
| Lean 出口 | `path_weight_multiplication_bridge_summary` |
| 最低 theorem 形态 | 合取 `PathWeightMultiplicationBoundaryClosed`、concrete two-step weight witness、S3 reachability / causalBefore、pending ledger 与 Wen coverage |
| 失败记录 | indexed inductive `refl` 分支参数与 concrete `KernelPath.refl` 的 `K := concreteKernel` 显式参数失败均已记录 |
| 文档更新 | 已新增《路径权重乘法候选 · Markov桥S19》 |
| 后续结构 | stochastic independence semantics、general all-path enumeration、path integral、general Hamiltonian/unitary amplitude dynamics、unitary/CPTP、metric recovery 与 empirical closure |

通过判准：

```text
current_pathWeight_compose_multiplicative；
KernelEdge；
KernelPath.weight；
KernelPath.append；
KernelPath.weight_append；
concrete_two_step_path_weight_multiplicative；
path_weight_multiplication_bridge_summary。
```

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `current_pathWeight_compose_multiplicative` | `QuantumRelativityPathWeightMultiplicationBridge.lean` | 旧 endpoint-only `pathWeight = 1` placeholder law |
| `KernelPath.weight_append` | `QuantumRelativityPathWeightMultiplicationBridge.lean` | finite kernel path append 的 weight multiplication law |
| `concrete_two_step_path_weight_multiplicative` | `QuantumRelativityPathWeightMultiplicationBridge.lean` | concrete prepared/evolved/measured 二步路径权重乘法 |
| `path_weight_multiplication_bridge_summary` | `QuantumRelativityPathWeightMultiplicationBridge.lean` | S19 path-weight multiplication boundary 已关闭 |

## S20 · 非平凡量子通道律候选

目标：把 S15 中已有的 concrete nonzero channel witness 升级为独立的 finite support-respecting channel law。S20 不证明 physical unitary/CPTP/Kraus/density-matrix theorem；它证明当前 `QuantumChannelSkeleton` 中只要展示非零 amplitude，就推出 process step、carried classical support 与 Born-shaped boundary，并给 concrete bridge 一个非零二步组合 witness。

| 项 | 内容 |
|---|---|
| Lean 出口 | `nontrivial_quantum_channel_law_bridge_summary` |
| 最低 theorem 形态 | 合取 `NontrivialQuantumChannelLawClosed`、S12/S16 Born boundary、S19 path-weight law、pending ledger 与 Wen coverage |
| 失败记录 | `AmplitudeSupportNormalized` namespace 漏 open；dependent Born existential witness 展开触发 `whnf` heartbeat timeout，改为合取 S16 closed boundary 与 concrete normalized support |
| 文档更新 | 已新增《非平凡量子通道律候选 · Markov桥S20》 |
| 后续结构 | Hilbert carrier、linear operator semantics、unitary evolution、CPTP、Kraus、density matrix、general Hamiltonian/unitary amplitude dynamics、measurement semantics、metric recovery 与 empirical closure |

通过判准：

```text
NontrivialChannelAmplitudeWitness；
nontrivial_channel_amplitude_law；
concrete_prepared_evolved_nontrivial_channel_law；
concrete_evolved_measured_nontrivial_channel_law；
concrete_nontrivial_sum_over_middle_channel_law；
nontrivial_quantum_channel_law_bridge_summary。
```

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `nontrivial_channel_amplitude_law` | `QuantumRelativityNontrivialChannelLawBridge.lean` | nonzero channel amplitude -> step / classical support / Born-shaped boundary |
| `concrete_prepared_evolved_nontrivial_channel_law` | `QuantumRelativityNontrivialChannelLawBridge.lean` | concrete prepared -> evolved amplitude `1` 的非零通道律 |
| `concrete_evolved_measured_nontrivial_channel_law` | `QuantumRelativityNontrivialChannelLawBridge.lean` | concrete evolved -> measured amplitude `1` 的非零通道律 |
| `concrete_nontrivial_sum_over_middle_channel_law` | `QuantumRelativityNontrivialChannelLawBridge.lean` | concrete prepared -> measured composed amplitude `1`，并接 two-step witness 与 normalized `[1]` support |
| `nontrivial_quantum_channel_law_bridge_summary` | `QuantumRelativityNontrivialChannelLawBridge.lean` | S20 nontrivial finite quantum-channel law boundary 已关闭 |

## S21 · 概率幅到测量权重候选

目标：把 `Quantum.lean` 中 one-qubit computational-basis Born rule 接入 Markov bridge 主线。S21 不证明一般 Hilbert measurement、POVM/PVM、decoherence 或测量问题；它只证明 normalized qubit 的两个 computational-basis measurement weights 非负且和为 `1`。

| 项 | 内容 |
|---|---|
| Lean 出口 | `born_measurement_bridge_summary` |
| 最低 theorem 形态 | 合取 `ComputationalBasisBornMeasurementClosed`、S18 Markov/amplitude Born derivation、S20 nontrivial channel law、pending ledger 与 Wen coverage |
| 失败记录 | 本轮实现未出现 Lean 证明失败；边界保留为一般测量理论 pending |
| 文档更新 | 已新增《概率幅到测量权重 · Markov桥S21》 |
| 后续结构 | 一般 Hilbert measurement、PVM/POVM、spectral semantics、decoherence、measurement problem 与 empirical closure |

通过判准：

```text
ComputationalBasisMeasurementWeights；
computational_basis_weight0_eq_ampProb；
computational_basis_weight1_eq_ampProb；
born_rule_gives_normalized_measurement_weights；
computational_basis_measurement_weights_normalized；
born_measurement_bridge_summary。
```

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `computational_basis_weight0_eq_ampProb` | `QuantumRelativityBornMeasurementBridge.lean` | `|0⟩` 分支权重等于 `ampProb (ψ 0)` |
| `computational_basis_weight1_eq_ampProb` | `QuantumRelativityBornMeasurementBridge.lean` | `|1⟩` 分支权重等于 `ampProb (ψ 1)` |
| `born_rule_gives_normalized_measurement_weights` | `QuantumRelativityBornMeasurementBridge.lean` | normalized qubit 的二值 measurement weights 非负且和为 `1` |
| `computational_basis_measurement_weights_normalized` | `QuantumRelativityBornMeasurementBridge.lean` | record 接口下的 normalized measurement weights |
| `born_measurement_bridge_summary` | `QuantumRelativityBornMeasurementBridge.lean` | S21 one-qubit Born measurement boundary 已关闭 |

## S22 · 作用相位到测量权重链

目标：把 S5r 的 finite action/phase law 与 S21 的 measurement weights 接成一条窄链。S22 不证明 continuous action functional、Hamiltonian dynamics、unitary time evolution、general path integral 或 general Hilbert measurement；displayed continuous action-coordinate functional 由 S24 后续承接。S22 只证明 finite action branch 可推出 action amplitude、normalized qubit 与二值 measurement-event weights。

| 项 | 内容 |
|---|---|
| Lean 出口 | `action_amplitude_measurement_bridge_summary` |
| 最低 theorem 形态 | 合取 `TwoRouteActionPhaseLawBoundaryComplete`、`ActionToBornMeasurementChainClosed`、S21 measurement boundary、pending ledger 与 Wen coverage |
| 失败记录 | 初次 build 缺少 discrete phase / path quotient / two-route namespace，导致 `DiscretePhase`、`twoStepPathQuotientClass` 与 `twoRouteUpperPath` 解析失败；补 open 后通过 |
| 文档更新 | 已新增《作用相位到测量权重链 · Markov桥S22》 |
| 后续结构 | displayed continuous action-coordinate functional 已由 S24 承接，finite quotient path-space action functional 已由 S25 承接；smooth/infinite-dimensional path-space action functional、Hamiltonian/unitary dynamics、general path integral、general Hilbert measurement、PVM/POVM、decoherence 与 empirical closure |

通过判准：

```text
ActionMeasurementBranch；
action_branch_qubit_normalized；
action_branch_born_measurement_weights；
action_branch_outcome_weights_normalized；
two_route_action_indices_match_measurement_branches；
action_amplitude_measurement_bridge_summary。
```

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `action_branch_qubit_normalized` | `QuantumRelativityActionAmplitudeMeasurementBridge.lean` | finite action branch 诱导的 qubit 已归一 |
| `action_branch_born_measurement_weights` | `QuantumRelativityActionAmplitudeMeasurementBridge.lean` | action-induced qubit 可接 S21 measurement weights |
| `action_branch_outcome_weights_normalized` | `QuantumRelativityActionAmplitudeMeasurementBridge.lean` | `zero/one` measurement outcomes 的 weights 非负且和为 `1` |
| `two_route_action_indices_match_measurement_branches` | `QuantumRelativityActionAmplitudeMeasurementBridge.lean` | S5r two-route action indices 与 S22 branches 对齐 |
| `action_amplitude_measurement_bridge_summary` | `QuantumRelativityActionAmplitudeMeasurementBridge.lean` | S22 finite action-to-measurement chain 已关闭 |

## S23 · 有限相位演化候选

目标：把 S22 的 displayed action amplitude 升级成 finite period-two phase evolution candidate。S23 不证明 Hamiltonian generator、continuous-time unitary group、Schrödinger dynamics、general path integral 或 general Hilbert measurement；它只证明 branch-indexed `1/-1` phase operation 可生成 S22 的 action-induced qubits，并保持 computational-basis Born weights。

| 项 | 内容 |
|---|---|
| Lean 出口 | `finite_phase_evolution_bridge_summary` |
| 最低 theorem 形态 | 合取 `FinitePhaseEvolutionClosed`、S22 action-to-measurement chain、S21 measurement boundary、pending ledger 与 Wen coverage |
| 失败记录 | 初次 proof 试探中 normalization preservation 的 `simp` 留下 `bornProb0 ψ + bornProb1 ψ = 1`；改为 `simpa ... using hψ` 后通过 |
| 文档更新 | 已新增《有限相位演化候选 · Markov桥S23》 |
| 后续结构 | displayed continuous action functional 已由 S24 承接；Hamiltonian generator、continuous-time unitary group、self-adjoint operator semantics、general Schrödinger dynamics、general path integral、general Hilbert measurement、PVM/POVM、decoherence 与 empirical closure 仍 pending |

通过判准：

```text
phaseEvolveBranch；
phase_evolve_upper_is_identity；
phase_evolve_lower_period_two；
phase_evolution_reaches_action_branch_qubits；
phase_evolve_branch_bornProb0_preserved；
phase_evolve_branch_bornProb1_preserved；
phase_evolve_branch_measurement_weights_normalized；
finite_phase_evolution_bridge_summary。
```

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `phase_evolve_upper_is_identity` | `QuantumRelativityFinitePhaseEvolutionBridge.lean` | upper branch finite phase 为 identity |
| `phase_evolve_lower_period_two` | `QuantumRelativityFinitePhaseEvolutionBridge.lean` | lower branch finite phase 连续作用两次回到原 state |
| `phase_evolution_reaches_action_branch_qubits` | `QuantumRelativityFinitePhaseEvolutionBridge.lean` | finite phase evolution 生成 S22 的 `ket0 / negKet1` action-induced qubits |
| `phase_evolve_branch_bornProb0_preserved`、`phase_evolve_branch_bornProb1_preserved` | `QuantumRelativityFinitePhaseEvolutionBridge.lean` | finite phase 不改变 computational-basis Born weights |
| `phase_evolve_branch_measurement_weights_normalized` | `QuantumRelativityFinitePhaseEvolutionBridge.lean` | normalized input 经 finite phase evolution 后仍接入 S21 measurement-weight interface |
| `finite_phase_evolution_bridge_summary` | `QuantumRelativityFinitePhaseEvolutionBridge.lean` | S23 finite phase-evolution boundary 已关闭 |

## S24 · 连续作用量泛函候选

目标：把 S23 的 finite phase operation 接到一个 displayed continuous action-coordinate functional。S24 不证明 path-space action functional、Euler-Lagrange equations、Hamiltonian generator、continuous-time unitary group、general Schrödinger dynamics、general path integral 或 general Hilbert measurement；finite quotient path-space action functional 由 S25 后续承接。S24 只证明 `S(t)=t` 连续，且在 branch times `0/1` 采样后回到既有 action index、phase amplitude 与 S23 Born-weight preservation。

| 项 | 内容 |
|---|---|
| Lean 出口 | `continuous_action_functional_bridge_summary` |
| 最低 theorem 形态 | 合取 `ContinuousActionFunctionalClosed`、S23 finite phase evolution、S22 action-to-measurement chain、S21 measurement boundary、pending ledger 与 Wen coverage |
| 失败记录 | 第一次 build 中 `branch_continuous_action_value_matches_index` 用 `rfl` 失败；改用 `norm_num` 展开 `Nat -> ℝ` coercion 与 displayed functional 后通过 |
| 文档更新 | 已新增《连续作用量泛函候选 · Markov桥S24》 |
| 后续结构 | finite quotient path-space action functional 已由 S25 承接；smooth/infinite-dimensional path-space action functional、Euler-Lagrange equations、Hamiltonian generator、continuous-time unitary group、self-adjoint operator semantics、general Schrödinger dynamics、general path integral、general Hilbert measurement、PVM/POVM、decoherence 与 empirical closure |

通过判准：

```text
ContinuousActionFunctionalCandidate；
displayed_continuous_action_functional_continuous；
branch_continuous_action_value_matches_index；
continuous_action_sampled_amplitude_eq_branch_amplitude；
continuous_action_phase_evolve_eq_finite_phase_evolve；
continuous_action_phase_evolution_reaches_action_branch_qubits；
continuous_action_phase_evolve_measurement_weights_normalized；
continuous_action_functional_bridge_summary。
```

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `displayed_continuous_action_functional_continuous` | `QuantumRelativityContinuousActionFunctionalBridge.lean` | displayed action functional `S(t)=t` 连续 |
| `branch_continuous_action_value_matches_index` | `QuantumRelativityContinuousActionFunctionalBridge.lean` | branch samples `S(0)/S(1)` 回到 action index `0/1` |
| `continuous_action_sampled_amplitude_eq_branch_amplitude` | `QuantumRelativityContinuousActionFunctionalBridge.lean` | sampled action index 推出的 amplitude 等于 branch amplitude |
| `continuous_action_phase_evolve_eq_finite_phase_evolve` | `QuantumRelativityContinuousActionFunctionalBridge.lean` | continuous-action-induced evolution 与 S23 finite phase evolution 一致 |
| `continuous_action_phase_evolve_measurement_weights_normalized` | `QuantumRelativityContinuousActionFunctionalBridge.lean` | normalized input 经 displayed continuous action sample 后仍接入 measurement-weight interface |
| `continuous_action_functional_bridge_summary` | `QuantumRelativityContinuousActionFunctionalBridge.lean` | S24 displayed continuous action functional boundary 已关闭 |

## S25 · 路径空间作用量泛函候选

目标：把 S24 的 displayed continuous action-coordinate samples 接到 finite visible-key quotient path space。S25 不证明 smooth/infinite-dimensional path-space action functional、variational principle、Euler-Lagrange equations、Hamiltonian generator、continuous-time unitary group、general Schrödinger dynamics、general path integral 或 general Hilbert measurement；它只证明 two-route quotient path classes 上的 action values `0/1` 与 S5r action index、S24 continuous samples、S5r amplitude sum cancellation 一致。

| 项 | 内容 |
|---|---|
| Lean 出口 | `path_space_action_functional_bridge_summary` |
| 最低 theorem 形态 | 合取 `FinitePathSpaceActionFunctionalClosed`、S24 continuous action boundary、S5r action-phase law、S23 finite phase evolution、S22/S21 measurement boundary、pending ledger 与 Wen coverage |
| 失败记录 | 若构建失败，记录是否为 quotient class 展开、Real coercion 或 namespace resolution；当前设计避免把 finite quotient support 误读为 smooth path space |
| 文档更新 | 已新增《路径空间作用量泛函候选 · Markov桥S25》 |
| 后续结构 | smooth/infinite-dimensional path-space action functional、variational principle、Euler-Lagrange equations、Hamiltonian generator、continuous-time unitary group、self-adjoint operator semantics、general Schrödinger dynamics、general path integral、general Hilbert measurement、PVM/POVM、decoherence 与 empirical closure |

通过判准：

```text
FinitePathSpaceActionFunctionalCandidate；
twoRoutePathSpaceActionFunctional；
two_route_upper_path_space_action_value；
two_route_lower_path_space_action_value；
two_route_path_space_action_index_matches_action_phase_law；
branch_path_space_action_value_eq_continuous_action_value；
path_space_action_sampled_amplitude_eq_action_phase_amplitude；
quotientSupportPathSpaceActionAmplitudeSum_eq_action_phase_sum；
two_route_path_space_action_support_amplitude_cancels；
two_route_path_space_action_support_born_weight_zero；
path_space_action_functional_bridge_summary。
```

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `two_route_upper_path_space_action_value`、`two_route_lower_path_space_action_value` | `QuantumRelativityPathSpaceActionFunctionalBridge.lean` | two-route quotient path classes 的 action values 为 `0/1` |
| `two_route_path_space_action_index_matches_action_phase_law` | `QuantumRelativityPathSpaceActionFunctionalBridge.lean` | finite path-space action index 与 S5r action-phase law 一致 |
| `branch_path_space_action_value_eq_continuous_action_value` | `QuantumRelativityPathSpaceActionFunctionalBridge.lean` | branch path quotient 读法与 S24 continuous sample 一致 |
| `two_route_path_space_action_support_amplitude_cancels` | `QuantumRelativityPathSpaceActionFunctionalBridge.lean` | path-space action-induced quotient-support amplitude sum 为 `0` |
| `path_space_action_functional_bridge_summary` | `QuantumRelativityPathSpaceActionFunctionalBridge.lean` | S25 finite path-space action functional boundary 已关闭 |

## S26 · 有限作用量极值候选

目标：把 S25 的 two-route finite path-space action values 推到 displayed finite support 上的 action-gap / finite-minimum boundary。S26 不证明 smooth/infinite-dimensional path-space action functional、continuous variation space、stationary action principle、Euler-Lagrange equations、Hamiltonian generator、continuous-time unitary group、general Schrödinger dynamics、general path integral 或 general Hilbert measurement；它只证明 two-route quotient support 上 lower action 比 upper action 大 `1`，upper 是 finite action minimum，lower 不是。

| 项 | 内容 |
|---|---|
| Lean 出口 | `finite_action_extremum_bridge_summary` |
| 最低 theorem 形态 | 合取 `TwoRouteFiniteActionExtremumClosed`、S25 path-space action boundary、S24 continuous action boundary、S5r action-phase law、S23 finite phase evolution、S22/S21 measurement boundary、pending ledger 与 Wen coverage |
| 失败记录 | 若构建失败，记录是否为 list membership、quotient class rewrite、Real order proof 或 namespace resolution；当前设计避免把 finite support minimum 误读为 stationary action principle |
| 文档更新 | 已新增《有限作用量极值候选 · Markov桥S26》 |
| 后续结构 | smooth/infinite-dimensional path-space action functional、continuous variation space、stationary action principle、Euler-Lagrange equations、Hamiltonian generator、continuous-time unitary group、self-adjoint operator semantics、general Schrödinger dynamics、general path integral、general Hilbert measurement、PVM/POVM、decoherence 与 empirical closure |

通过判准：

```text
finiteActionGap；
FiniteActionMinimumOnSupport；
two_route_upper_in_action_extremum_support；
two_route_lower_in_action_extremum_support；
two_route_upper_to_lower_action_gap；
two_route_lower_to_upper_action_gap；
two_route_lower_action_eq_upper_plus_one；
two_route_upper_is_finite_action_minimum；
two_route_lower_not_finite_action_minimum；
finite_action_extremum_bridge_summary。
```

当前状态：

| theorem | 文件 | 读法 |
|---|---|---|
| `finiteActionGap`、`FiniteActionMinimumOnSupport` | `QuantumRelativityFiniteActionExtremumBridge.lean` | finite quotient support 上的 action gap 与 minimum predicate |
| `two_route_upper_to_lower_action_gap`、`two_route_lower_to_upper_action_gap` | `QuantumRelativityFiniteActionExtremumBridge.lean` | upper/lower action difference 分别为 `1` 与 `-1` |
| `two_route_lower_action_eq_upper_plus_one` | `QuantumRelativityFiniteActionExtremumBridge.lean` | lower action 等于 upper action 加 `1` |
| `two_route_upper_is_finite_action_minimum` | `QuantumRelativityFiniteActionExtremumBridge.lean` | upper 是 displayed finite support 上的 action minimum |
| `two_route_lower_not_finite_action_minimum` | `QuantumRelativityFiniteActionExtremumBridge.lean` | lower 不是 displayed finite support 上的 action minimum |
| `finite_action_extremum_bridge_summary` | `QuantumRelativityFiniteActionExtremumBridge.lean` | S26 finite action extremum boundary 已关闭 |

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
| 2026-05-08 | S2 | success | 新增 finite probability-kernel denominator interface；关闭非终端行分母非零与权重上界，仍不证明 sum-one 概率律、Born rule、physical unitary/CPTP/Kraus/density-matrix channel law 或经验闭合 |
| 2026-05-08 | S3 | success | 新增 path composition and local causal constraints；关闭组合 path witness 的可达/因果读法与 concrete/grid no-self-loop，仍不证明完整偏序、局部有限 causal set、light cone 或 metric recovery |
| 2026-05-08 | S4 | success | 新增 classical Markov / quantum amplitude-channel 分层接口；关闭 layer separation、channel candidate 到 S2 边界的投影与非零振幅支持精化，仍不证明干涉、Born rule 推导、physical Hilbert/unitary/CPTP/Kraus/density-matrix channel law 或经验闭合 |
| 2026-05-08 | S5 | success | 新增 path amplitude / interference / Born-shaped candidate interface；关闭候选组合等式、相消 witness 与 `ampProb` boundary，仍不证明真实干涉律、Born rule 推导、physical Hilbert/unitary/CPTP/Kraus/density-matrix channel law 或经验闭合 |
| 2026-05-08 | S5b | success | 新增 nonzero path-amplitude candidate witness；关闭非零候选振幅到 valid / Reachable / causalBefore 的边界，仍不证明相位律、路径求和、真实干涉律或经验闭合 |
| 2026-05-08 | S5c | success | 新增 two-path finite cancellation candidate；关闭 same-endpoint / different-middle two-step pair 的 `1 + (-1) = 0` 与 Born-shaped zero boundary，仍不证明 path integral、相位动力学、真实干涉律或经验闭合 |
| 2026-05-08 | S5d | success | 新增 discrete phase-label candidate；关闭 `zero/pi` 到 `1/-1` 的映射、upper/lower phase labels 与 phase-induced two-path cancellation，仍不证明 continuous phase、action/Hamiltonian law、path integral 或经验闭合 |
| 2026-05-08 | S5e | success | 新增 discrete edge-action phase accumulation candidate；关闭 edge increments 到 path phase、relative phase `pi` 与 edge-action-induced two-path cancellation，仍不证明 finite path-family sum、continuous phase/action law、path integral 或经验闭合 |
| 2026-05-08 | S5f | success | 新增 finite path-family sum candidate；关闭 two-route upper/lower family sum cancellation 与 Born-shaped zero boundary；path-sum algebra 已由 S5g 承接，仍不证明 all-path enumeration、path integral 或经验闭合 |
| 2026-05-08 | S5g | success | 新增 finite path-sum algebra candidate；关闭 append / permutation / reverse stability 与 cancellation stability；endpoint-indexed family 已由 S5h 承接，仍不证明 all-path enumeration、path integral 或经验闭合 |
| 2026-05-08 | S5h | success | 新增 endpoint-indexed finite path-family candidate；关闭 same-endpoint family 到 endpoint-indexed family 的转换、sum/weight preservation 与 two-route endpoint-indexed cancellation；filter/support normalization 已由 S5i 承接，仍不证明 all-path enumeration、path integral 或经验闭合 |
| 2026-05-08 | S5i | success | 新增 endpoint support normalization candidate；关闭 amplitude-complete filter preservation、Born-shaped preservation、duplicate expansion 与 duplicated zero-sum cancellation，仍不证明 quotient 去重、all-path enumeration、path integral 或经验闭合 |
| 2026-05-08 | S5j | success | 新增 two-route source/target enumeration candidate；关闭 toy source/target two-step middle enumeration 与 endpoint family middle completeness，仍不证明 general all-path enumeration、path integral 或经验闭合 |
| 2026-05-08 | S5k | success | 新增 finite two-step path identity-key candidate；关闭 visible key boundary、two-route key separation 与 toy source/target key completeness；finite visible-key quotient candidate 已由 S5l 承接，quotient class 已由 S5m 承接，two-route canonical representative 已由 S5n 承接，仍不证明 general choice function、general all-path enumeration、path integral 或经验闭合 |
| 2026-05-08 | S5l | success | 新增 finite visible-key quotient candidate；关闭 key-equivalence、key-compatible amplitude descent、duplicate compensation 与 two-route key-level cancellation；visible-key quotient class 已由 S5m 承接，仍不证明 general all-path enumeration、path integral 或经验闭合 |
| 2026-05-08 | S5m | success | 新增 visible-key quotient class candidate；关闭 `Setoid` / `Quot` construction、quotient descent 与 two-route quotient completeness；two-route canonical representative 已由 S5n 承接，仍不证明 general choice function、general all-path enumeration、path integral 或经验闭合 |
| 2026-05-08 | S5n | success | 新增 two-route canonical representative candidate；关闭 displayed representatives 与 toy source/target representative completeness；finite quotient-support enumeration 已由 S5o 承接，仍不证明 general choice function、general all-path enumeration、path integral 或经验闭合 |
| 2026-05-08 | S5o | failure retained / success | 第一次 quotient-support build 因 `rfl` 未展开 `quotientKeyAmplitude` 与 `Function.comp_def` 失败；修正后新增 finite quotient-support candidate，关闭 support coverage、visible-key readback、quotient-level cancellation 与 Born-shaped zero boundary；quotient-support algebra 已由 S5p 承接，仍不证明 general all-path enumeration、path integral 或经验闭合 |
| 2026-05-08 | S5p | failure retained / success | 第一次 quotient-support algebra build 因显式 `twoRouteProcess` 类型标注解析到不同 namespace 下的同名 process 失败；移除显式返回类型后新增 quotient-support algebra candidate，关闭 append / permutation / reverse stability、duplicate zero-sum cancellation 与 two-route algebraic cancellation stability，仍不证明 general all-path enumeration、path integral 或经验闭合 |
| 2026-05-09 | S5q | success | 新增 observable ledger candidate boundary；关闭 pending entry 与 empirical closure 的区分、two-route cancellation ledger entry 的 zero sum/weight 与 pending status，仍不证明数据校准、可测预言 theorem、path integral 或经验闭合 |
| 2026-05-09 | S5r | failure retained / success | 第一次 action-phase law build 因展开 `quotientVisibleKey` 暴露 `Quot.lift` 导致 quotient readback 化简失败；修正后新增 finite action-to-phase law candidate，关闭 action index `0/1` 到 `1/-1` 的 quotient-support cancellation 与 pending ledger registration |
| 2026-05-09 | S8 | failure retained / success | 第一次 stepwise summary build 因 operator-cell grid 与 path-quotient support namespace/defeq 解析失败；修正后关闭 current stepwise unification candidate summary，并显式列出 `PendingBeyondS5r` |
| 2026-05-09 | S9 | failure retained / success | 第一次 finite probability normalization build 因 concrete row list-sum、grid singleton `Fin` 化简与 Rat coercion 递归深度失败；修正后关闭 concrete/grid finite row sum-one boundary，并显式列出 `PendingBeyondS9` |
| 2026-05-09 | S10 | failure retained / success | direct concrete/grid 展开 proof 可过但不够结构化；改为泛型 `normalizedMassSum_eq_normalizedRowTotalCandidate`，关闭 `normalizedMass_sum_one` 与 concrete/grid normalized mass sum-one boundary |
| 2026-05-09 | S11 | failure retained / success | `simp` 不能直接改写 `(candidateWeight ∘ bornRuleCandidate)` 的 list sum；改用 list induction 后关闭 conditional Born-weight normalization boundary |
| 2026-05-09 | S12 | failure retained / success | `simp [bornDistributionBoundary]` 未自动拆出 dependent distribution fields；改为显式 existential witness 后关闭 finite Born distribution boundary |
| 2026-05-09 | S13 | success | `channelCompose` stdin 试探一次通过；关闭 current skeleton 的 channel composition candidate，仍不证明 physical Hilbert/unitary/CPTP/Kraus/density-matrix channel law |
| 2026-05-09 | S14 | failure retained / success | 第一次 identity obstruction 试探中未展开 `QuantumAmplitudeSupport` 导致 rewrite 找不到目标；展开 support 后关闭 pointwise associativity 与 diagonal identity obstruction |
| 2026-05-09 | S15 | failure retained / success | 第一次 sum-over-middle support proof 试探中 `List.mem_map` 等式方向写反；改为 `rw [hbeq]` 并展开 `QuantumAmplitudeSupport` 后关闭 finite middle-list composition 的 two-step boundary |
| 2026-05-09 | S16 | failure retained / success | concrete dependent existential witness 展开到 structure fields 时触发 `whnf` heartbeat timeout；保留 generic closed boundary 与 concrete normalized `[1]` input，关闭 composed Born boundary |
| 2026-05-09 | S17 | success | 新增 unitary/CPTP ledger boundary；S13-S16 current skeleton items closed，physical Hilbert/Kraus/density/CPTP items required but not closed |
| 2026-05-09 | S18 | failure retained / success | 第一次 build 中 Rat list sum cast、`List.map_map` composition shape 与 concrete row support projection 展开失败；补 `list_map_rat_sum_cast`、改用 composition shape、展开 `concreteFiniteRowSupportNormalization` 后关闭 Markov/amplitude compatibility 下的 Born-rule derivation |
| 2026-05-09 | S19 | failure retained / success | 第一次 build 中 indexed inductive `refl` 分支写成带参数形式，且 concrete `KernelPath.refl` 未显式指定 `K := concreteKernel`；修正后关闭 finite kernel path 的 weight append law |
| 2026-05-09 | S20 | failure retained / success | 第一次 build 中 `AmplitudeSupportNormalized` namespace 漏 open；dependent Born existential witness 展开触发 `whnf` heartbeat timeout，改为合取 S16 closed boundary 与 concrete normalized support 后关闭 nontrivial finite quantum-channel law |
| 2026-05-09 | S21 | success | 新增 one-qubit computational-basis Born measurement weights bridge；关闭 normalized qubit 的 `bornProb0` / `bornProb1` 非负与 sum-one，仍不证明一般 Hilbert measurement、POVM/PVM、decoherence 或 measurement problem |
| 2026-05-09 | S22 | failure retained / success | 第一次 build 因 namespace 未 open 导致 `DiscretePhase` 与 quotient/two-route names 解析失败；修正后关闭 finite action branch -> action amplitude -> normalized qubit -> measurement-event weights chain |
| 2026-05-09 | S23 | failure retained / success | 第一次 proof 试探中 normalization preservation 的 `simp` 留下 `bornProb0 ψ + bornProb1 ψ = 1`；改用 `simpa ... using hψ` 后关闭 finite phase evolution -> Born-weight preservation boundary |
| 2026-05-09 | S24 | failure retained / success | 第一次 build 中 `branch_continuous_action_value_matches_index` 用 `rfl` 失败；改用 `norm_num` 展开 coercion 与 displayed action functional 后关闭 continuous action functional -> sampled phase boundary |
| 2026-05-09 | S25 | failure retained / success | 第一次 build 中未 open `QuantumRelativityPathIdentityBridge`，导致 `twoStepPathKey` 无法解析和展开；补 namespace 后关闭 finite path-space action functional candidate、S5r action-index compatibility、S24 sample compatibility 与 quotient-support action-induced cancellation |
| 2026-05-09 | S26 | failure retained / success | 第一次 build 中 `rw [hq]` 已关闭 reflexive order goal，后续 `exact le_rfl` 变成 no goals；同时文件末尾需先关闭 `noncomputable section` 再关闭 namespace。修正后新增 finite action extremum boundary，关闭 lower-minus-upper action gap、upper finite minimum 与 lower non-minimum |

## 统一用语正名

本文中的“统一”按已经关闭的形式结构来读。只要含义对应 theorem 与文档锚点，就按其正名使用：

| 词 | 在本路线中的含义 | 结构依据 |
|---|---|---|
| 逐步统一 | 多个形式接口逐步合取到同一个候选 bridge summary | S0-S26 已关闭的 summary theorem 与路线日志 |
| 候选统一 | Lean 中有更强的 typed skeleton，且把未闭合经验项接入 pending ledger | `FiniteProcess`、S2-S5r 候选接口、S5q/S5r pending ledger boundary、S8-S26 pending list |
| 最小统一摘要 | 已关闭 theorem 的保守合取，作为当前阶段的统一读法 | `stepwise_unification_candidate_summary`、`finite_probability_normalization_bridge_summary`、`normalized_mass_bridge_summary`、`born_weight_normalization_bridge_summary`、`born_distribution_bridge_summary`、`channel_compose_bridge_summary`、`channel_compose_associativity_bridge_summary`、`sum_over_middle_channel_bridge_summary`、`sum_over_middle_born_distribution_bridge_summary`、`unitary_cptp_ledger_bridge_summary`、`born_rule_derivation_bridge_summary`、`path_weight_multiplication_bridge_summary`、`nontrivial_quantum_channel_law_bridge_summary`、`born_measurement_bridge_summary`、`action_amplitude_measurement_bridge_summary`、`finite_phase_evolution_bridge_summary`、`continuous_action_functional_bridge_summary`、`path_space_action_functional_bridge_summary`、`finite_action_extremum_bridge_summary` |

推荐正名句：

```text
本路线追求逐步增强的形式统一候选；
每一步以 Lean 出口、文档锚点和失败记录实事求是地确认含义；
已经关闭的 summary theorem 就是当前阶段的统一内容，
尚未闭合的 stochastic semantics、general all-path enumeration、path integral、smooth/infinite-dimensional path-space action functional、general Hamiltonian/unitary amplitude dynamics、measurement semantics、decoherence、physical unitary/CPTP/Kraus/density channel law、几何恢复、数据校准与经验闭合
作为后续结构继续推进。
```
