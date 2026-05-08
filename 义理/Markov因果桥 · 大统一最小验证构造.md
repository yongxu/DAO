# Markov因果桥 · 大统一最小验证构造

**前置**：[量子与相对论整合方向 · 从桥到新理论](量子与相对论整合方向%20·%20从桥到新理论.md) · [文构造完备与直相加边界](文构造完备与直相加边界.md) · [有限概率核接口 · Markov桥S2](有限概率核接口%20·%20Markov桥S2.md) · [路径组合与因果约束 · Markov桥S3](路径组合与因果约束%20·%20Markov桥S3.md) · [经典Markov与量子振幅分层 · Markov桥S4](经典Markov与量子振幅分层%20·%20Markov桥S4.md) · [干涉与测量律候选 · Markov桥S5](干涉与测量律候选%20·%20Markov桥S5.md) · [非零路径振幅候选 · Markov桥S5b](非零路径振幅候选%20·%20Markov桥S5b.md) · [双路径相消候选 · Markov桥S5c](双路径相消候选%20·%20Markov桥S5c.md) · [离散相位标记候选 · Markov桥S5d](离散相位标记候选%20·%20Markov桥S5d.md) · [离散作用量相位候选 · Markov桥S5e](离散作用量相位候选%20·%20Markov桥S5e.md) · [有限路径族求和候选 · Markov桥S5f](有限路径族求和候选%20·%20Markov桥S5f.md) · [有限路径族求和代数候选 · Markov桥S5g](有限路径族求和代数候选%20·%20Markov桥S5g.md) · [端点索引路径族候选 · Markov桥S5h](端点索引路径族候选%20·%20Markov桥S5h.md) · [端点支撑规范化候选 · Markov桥S5i](端点支撑规范化候选%20·%20Markov桥S5i.md) · [双路径枚举候选 · Markov桥S5j](双路径枚举候选%20·%20Markov桥S5j.md) · [路径身份键候选 · Markov桥S5k](路径身份键候选%20·%20Markov桥S5k.md) · [有限键商候选 · Markov桥S5l](有限键商候选%20·%20Markov桥S5l.md) · [路径商类候选 · Markov桥S5m](路径商类候选%20·%20Markov桥S5m.md) · [规范代表元候选 · Markov桥S5n](规范代表元候选%20·%20Markov桥S5n.md) · [商支撑枚举候选 · Markov桥S5o](商支撑枚举候选%20·%20Markov桥S5o.md) · [商支撑代数候选 · Markov桥S5p](商支撑代数候选%20·%20Markov桥S5p.md) · [观测账本候选 · Markov桥S5q](观测账本候选%20·%20Markov桥S5q.md) · [作用量相位律候选 · Markov桥S5r](作用量相位律候选%20·%20Markov桥S5r.md) · [逐步统一候选摘要 · Markov桥S8](逐步统一候选摘要%20·%20Markov桥S8.md) · [量子与相对论直统一不可能 · 当前语言NoGo](量子与相对论直统一不可能%20·%20当前语言NoGo.md) · [`markov-causal-bridge-plan`](../formal/SSBX/notes/markov-causal-bridge-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| tagged 物理语言边界 | `Foundation/Modern/QuantumRelativityNoGo.lean` | `tagged_addition_noncollapse` 排除 tagged sum 自动坍缩 | `machineChecked` |
| 文构造覆盖修正 | `Foundation/Modern/QuantumRelativityWenBoundary.lean` | `wen_constructive_boundary_summary` 证明 `192 × 371` 覆盖不受 tagged 边界否定 | `machineChecked` |
| 中介桥方向 | `Foundation/Modern/QuantumRelativityIntegration.lean` | `only_mediated_bridge_is_framework_route` 定位正向路线为中介桥 | `machineChecked` |
| 桥项双投影 | `Foundation/Modern/QuantumRelativityIntegration.lean` | `BridgeTerm`、`bridge_projections_same_one`、`bridge_projections_not_current_identity` | `machineChecked` |
| Markov-因果桥载体 | `Foundation/Modern/QuantumRelativityMarkovBridge.lean` | `FiniteProcess`、`state_code_within_bound`、`ProcessPath`、`path_implies_reachable` | `machineChecked` |
| Markov 读法 | `Foundation/Modern/QuantumRelativityMarkovBridge.lean` | `MarkovKernelSkeleton`、`positive_weight_implies_step`、`pathWeight` | `machineChecked` |
| 因果读法 | `Foundation/Modern/QuantumRelativityMarkovBridge.lean` | `CausalEvent`、`causalBefore`、`step_implies_causal_before` | `machineChecked` |
| 测量-事件对齐 | `Foundation/Modern/QuantumRelativityMarkovBridge.lean` | `MeasurementEventBridge`、`measurement_event_alignment` | `machineChecked` |
| 桥接边界 | `Foundation/Modern/QuantumRelativityMarkovBridge.lean` | `MeasurementEventBridge.toBridgeTerm`、`measurement_event_bridge_term_keeps_faces`、`markov_bridge_keeps_quantum_and_relativity_faces`、`markov_bridge_same_one_not_identity`、`markov_bridge_not_direct_language_addition` | `machineChecked` |
| 公开摘要 | `Foundation/Modern/QuantumRelativityMarkovBridge.lean` | `markov_causal_bridge_summary` | `machineChecked` |
| concrete witness | `Foundation/Modern/QuantumRelativityConcreteBridge.lean` | `concrete_bridge_summary` 给出三状态 `prepared → evolved → measured` 实例 | `machineChecked` |
| `71232` grid bridge | `Foundation/Modern/OperatorCellGridMarkovBridge.lean` | `operator_cell_grid_markov_causal_bridge_summary` 把 `371 × 192` 覆盖网格作为有限过程状态空间 | `machineChecked` |
| S2 有限概率核接口 | `Foundation/Modern/QuantumRelativityFiniteProbabilityBridge.lean` | `finite_probability_bridge_summary` 关闭 finite denominator / bounded weights interface | `machineChecked` |
| S3 路径组合与因果约束 | `Foundation/Modern/QuantumRelativityPathCausalBridge.lean` | `path_causal_bridge_summary` 关闭 path witness composition 与 code-successor/no-self-loop | `machineChecked` |
| S4 Markov / amplitude-channel 分层 | `Foundation/Modern/QuantumRelativityAmplitudeChannelBridge.lean` | `amplitude_channel_bridge_summary` 关闭 layer separation、channel boundary projection 与 support refinement | `machineChecked` |
| S5 干涉与测量律候选 | `Foundation/Modern/QuantumRelativityInterferenceBridge.lean` | `interference_bridge_summary` 关闭 path amplitude、interference witness 与 Born-shaped boundary candidate | `machineChecked` |
| S5b 非零路径振幅候选 | `Foundation/Modern/QuantumRelativityNonzeroPathAmplitudeBridge.lean` | `nonzero_path_amplitude_bridge_summary` 关闭非零 path-amplitude candidate witness 与 causal boundary | `machineChecked` |
| S5c 双路径相消候选 | `Foundation/Modern/QuantumRelativityTwoPathInterferenceBridge.lean` | `two_path_interference_bridge_summary` 关闭 two-path finite cancellation candidate 与 Born-shaped zero boundary | `machineChecked` |
| S5d 离散相位标记候选 | `Foundation/Modern/QuantumRelativityDiscretePhaseBridge.lean` | `discrete_phase_bridge_summary` 关闭 `zero/pi` 到 `1/-1` 的候选导出 | `machineChecked` |
| S5e 离散作用量相位候选 | `Foundation/Modern/QuantumRelativityDiscreteActionBridge.lean` | `discrete_action_phase_bridge_summary` 关闭 edge phase accumulation、relative phase `pi` 与 induced cancellation | `machineChecked` |
| S5f 有限路径族求和候选 | `Foundation/Modern/QuantumRelativityFinitePathSumBridge.lean` | `finite_path_sum_bridge_summary` 关闭 finite same-endpoint path family sum 与 Born-shaped zero boundary | `machineChecked` |
| S5g 有限路径族求和代数候选 | `Foundation/Modern/QuantumRelativityFinitePathSumAlgebraBridge.lean` | `finite_path_sum_algebra_bridge_summary` 关闭 append / permutation / reverse stability 与 cancellation stability | `machineChecked` |
| S5h 端点索引路径族候选 | `Foundation/Modern/QuantumRelativityEndpointIndexedPathFamilyBridge.lean` | `endpoint_indexed_path_family_bridge_summary` 关闭 endpoint-indexed conversion 与 sum/weight preservation | `machineChecked` |
| S5i 端点支撑规范化候选 | `Foundation/Modern/QuantumRelativityEndpointSupportNormalizationBridge.lean` | `endpoint_support_normalization_bridge_summary` 关闭 amplitude-complete filter 与 duplicate handling boundary | `machineChecked` |
| S5j 双路径枚举候选 | `Foundation/Modern/QuantumRelativityTwoRouteEnumerationBridge.lean` | `two_route_enumeration_bridge_summary` 关闭 two-route toy source/target middle enumeration | `machineChecked` |
| S5k 路径身份键候选 | `Foundation/Modern/QuantumRelativityPathIdentityBridge.lean` | `path_identity_bridge_summary` 关闭 visible path-key boundary 与 toy key completeness | `machineChecked` |
| S5l 有限键商候选 | `Foundation/Modern/QuantumRelativityFiniteKeyQuotientBridge.lean` | `finite_key_quotient_bridge_summary` 关闭 key-equivalence、key-compatible amplitude descent 与 key-level cancellation | `machineChecked` |
| S5m 路径商类候选 | `Foundation/Modern/QuantumRelativityPathQuotientBridge.lean` | `path_quotient_bridge_summary` 关闭 visible-key quotient class construction 与 quotient completeness | `machineChecked` |
| S5n 规范代表元候选 | `Foundation/Modern/QuantumRelativityCanonicalRepresentativeBridge.lean` | `canonical_representative_bridge_summary` 关闭 two-route displayed representative boundary | `machineChecked` |
| S5o 商支撑枚举候选 | `Foundation/Modern/QuantumRelativityQuotientSupportBridge.lean` | `quotient_support_bridge_summary` 关闭 quotient support enumeration 与 quotient-level cancellation | `machineChecked` |
| S5p 商支撑代数候选 | `Foundation/Modern/QuantumRelativityQuotientSupportAlgebraBridge.lean` | `quotient_support_algebra_bridge_summary` 关闭 quotient-support algebra 与 cancellation stability | `machineChecked` |
| S5q 观测账本候选 | `Foundation/Modern/QuantumRelativityObservableLedgerBridge.lean` | `observable_ledger_bridge_summary` 关闭 pending observable ledger boundary | `machineChecked` |
| S5r 作用量相位律候选 | `Foundation/Modern/QuantumRelativityActionPhaseLawBridge.lean` | `action_phase_law_bridge_summary` 关闭 finite action-to-phase law candidate | `machineChecked` |
| S8 逐步统一候选摘要 | `Foundation/Modern/QuantumRelativityStepwiseUnificationBridge.lean` | `stepwise_unification_candidate_summary` 合取当前已关闭结构与 pending boundary list | `machineChecked` |
| S9 有限概率归一化候选 | `Foundation/Modern/QuantumRelativityFiniteProbabilityNormalizationBridge.lean` | `finite_probability_normalization_bridge_summary` 关闭 concrete/grid finite row sum-one boundary | `machineChecked` |
| S10 归一化质量求和候选 | `Foundation/Modern/QuantumRelativityNormalizedMassBridge.lean` | `normalized_mass_bridge_summary` 关闭 concrete/grid normalized mass sum-one boundary | `machineChecked` |

> 本文回答第三个问题：
>
> **如果中介桥是正向整合方向，第一块最小可验证构造应当是什么？**
>
> 答：先不要从完整 Hilbert 空间、Lorentzian geometry 或量子引力方程开始，而从一个有限过程结构开始。这个有限过程同时允许两种投影：一侧读成 Markov / 测量过程，另一侧读成事件 / 因果结构。若终端状态在两种读法下可对齐，则“测量结果成为事件”至少获得一个可检查的 typed skeleton。

---

## 〇 · Claim Block

本文主张很窄：

```text
最小桥接尝试 =
  有限过程载体
  + Markov / 测量投影
  + 因果 / 事件投影
  + 终端状态的测量-事件对齐
  + 有限概率核分母接口
  + 路径 witness 组合与 code-successor 方向约束
  + 经典 Markov / 量子振幅-通道候选分层
  + 路径振幅 / 干涉 / Born-shaped boundary 候选接口
  + 非零路径振幅候选 witness 与 causal boundary
  + 双路径有限相消候选 witness
  + 离散相位标记候选 witness
  + 离散 edge-action 相位累积候选 witness
  + 有限路径族求和候选 witness
  + 有限路径族求和代数候选 witness
  + 端点索引路径族候选 witness
  + 端点支撑规范化候选 witness
  + 双路径枚举候选 witness
  + 路径身份键候选 witness
  + 有限键商候选 witness
  + 路径商类候选 witness
  + 规范代表元候选 witness
  + 商支撑枚举候选 witness
  + 商支撑代数候选 witness
  + 观测账本候选 witness
  + 作用量相位律候选 witness
  + 逐步统一候选摘要
  + 有限概率归一化候选 witness
  + 仍服从 tagged physical-language noncollapse
  + 不否定 192 × 371 文构造覆盖
```

这不是量子引力理论，也不是“大统一已经完成”。它只把上一层的“中介桥方向”推进为一个候选最小构造：同一个有限过程对象可以被双读，终端状态可以同时被读为测量结果与事件记录，非终端 Markov 行可带有限分母候选，显式 path witness 可以组合成可达 / 因果读法，classical Markov 层与 quantum amplitude/channel candidate 层被形式地区分，并且 path amplitude、相消 witness、Born-shaped boundary、非零 path-amplitude witness、two-path finite cancellation witness、discrete phase-label witness、edge-action phase accumulation witness、finite path-family sum witness、finite path-sum algebra witness、endpoint-indexed finite family witness、endpoint support normalization witness、two-route toy enumeration witness、visible path-key witness、finite visible-key quotient candidate、visible-key quotient class witness、two-route canonical representative witness、finite quotient-support witness、quotient-support algebra witness、pending observable ledger witness、finite action-to-phase law witness、finite row sum-one normalization witness 与 normalized mass sum-one witness 可以作为候选接口被记录；S8 把这些已关闭结构的当前核心合取为 stepwise summary theorem，S9 继续关闭 finite Markov row normalization boundary，S10 把 row-total candidate 改写成逐项 rational probability mass law，并显式列出仍未关闭边界。

公开摘要为：

```lean
theorem markov_causal_bridge_summary :
    HasMarkovProjection P
    ∧ HasCausalProjection P
    ∧ MeasurementEventsAlign b
    ∧ keepsQuantumFace MarkovCausalRoute = true
    ∧ keepsRelativityFace MarkovCausalRoute = true
    ∧ sameOne .quantumSpace .relativisticSpacetime
    ∧ ¬ CurrentPhysicalUnity .quantumSpace .relativisticSpacetime
    ∧ ¬ DirectUnificationByAddition
```

该 theorem 已通过 `lake build SSBX.Foundation.Modern.QuantumRelativityMarkovBridge`。

---

## 〇一 · 边界声明

本文只给 companion 文档与最小构造边界，不声称完成物理统一。

| 说法 | 本文状态 | 精确含义 |
|---|---|---|
| 当前 tagged 物理语言不自动坍缩 | `machineChecked` | 复用 `tagged_addition_noncollapse` |
| `192 × 371` 文构造覆盖 | `machineChecked` | 复用 `wen_constructive_boundary_summary`；它不是 tagged 边界的否定对象 |
| 正向方向应为中介桥 | `machineChecked` | 复用 `only_mediated_bridge_is_framework_route` |
| Markov-因果桥是候选中介载体 | `machineChecked` typed skeleton | Lean 模块已构建通过 |
| 终端状态可读成测量结果与事件记录 | `machineChecked` typed skeleton | 由 `measurement_event_alignment` 关闭 |
| 该桥不是 tagged-language collapse | `machineChecked` bridge target | 复用 `markov_bridge_not_direct_language_addition` |
| 三状态 concrete witness | `machineChecked` | `concrete_bridge_summary` 证明至少有一个具体有限 bridge instance |
| `71232` operator-cell grid bridge | `machineChecked` | `operator_cell_grid_markov_causal_bridge_summary` 将 `192 × 371` 覆盖网格接入 `FiniteProcess` |
| 有限概率核 denominator / bounded weights | `machineChecked` | `finite_probability_bridge_summary` 证明非终端行分母非零，权重受行分母约束 |
| 路径组合与 no-self-loop 方向性 | `machineChecked` | `path_causal_bridge_summary` 证明组合 path witness 给出 reachability / causalBefore，concrete 与 grid 一步转移无自环 |
| quantum amplitude / channel candidate layer | `machineChecked` typed skeleton | `amplitude_channel_bridge_summary` 证明候选层与 classical Markov 层分开，并保留 S2 边界 |
| path amplitude / interference / Born-shaped candidate | `machineChecked` typed skeleton | `interference_bridge_summary` 证明 S5 候选接口存在并保留 S4 边界 |
| nonzero path-amplitude candidate witness | `machineChecked` typed skeleton | `nonzero_path_amplitude_bridge_summary` 证明非零候选振幅给出 valid / Reachable / causalBefore |
| two-path finite cancellation candidate | `machineChecked` typed skeleton | `two_path_interference_bridge_summary` 证明同端点、不同中间态候选路径的 `1 + (-1) = 0` 与 Born-shaped zero boundary |
| discrete phase-label candidate | `machineChecked` typed skeleton | `discrete_phase_bridge_summary` 证明 `zero/pi` 标签导出 `1/-1` 并保持 two-path cancellation |
| discrete edge-action phase candidate | `machineChecked` typed skeleton | `discrete_action_phase_bridge_summary` 证明 edge phase increments 累积为 path phase、relative phase `pi` 并保持 two-path cancellation |
| finite path-family sum candidate | `machineChecked` typed skeleton | `finite_path_sum_bridge_summary` 证明 two-route upper/lower pair 可作为 finite same-endpoint path family 求和，并保持 cancellation 与 Born-shaped zero boundary |
| finite path-sum algebra candidate | `machineChecked` typed skeleton | `finite_path_sum_algebra_bridge_summary` 证明 append / permutation / reverse stability 与 cancellation stability |
| endpoint-indexed finite family candidate | `machineChecked` typed skeleton | `endpoint_indexed_path_family_bridge_summary` 证明 S5f family 可转为 endpoint-indexed family，并保持 sum/weight |
| endpoint support normalization candidate | `machineChecked` typed skeleton | `endpoint_support_normalization_bridge_summary` 证明 amplitude-complete finite filter 保持 sum/weight，并显式处理 duplicate expansion |
| two-route toy enumeration candidate | `machineChecked` typed skeleton | `two_route_enumeration_bridge_summary` 证明 toy source/target two-step middle 只能是 `upper` 或 `lower` |
| visible path-key candidate | `machineChecked` typed skeleton | `path_identity_bridge_summary` 证明 key equality 保持 `start/middle/stop`，并关闭 toy key completeness |
| finite visible-key quotient candidate | `machineChecked` typed skeleton | `finite_key_quotient_bridge_summary` 证明 key-equivalence、key-compatible amplitude descent、duplicate compensation 与 two-route key-level cancellation |
| visible-key quotient class candidate | `machineChecked` typed skeleton | `path_quotient_bridge_summary` 证明 `Setoid` / `Quot` construction、quotient descent 与 two-route quotient completeness |
| two-route canonical representative candidate | `machineChecked` typed skeleton | `canonical_representative_bridge_summary` 证明 displayed upper/lower representatives 与 toy source/target representative completeness |
| finite quotient-support candidate | `machineChecked` typed skeleton | `quotient_support_bridge_summary` 证明 quotient support coverage、visible-key readback、quotient-level cancellation 与 Born-shaped zero boundary |
| quotient-support algebra candidate | `machineChecked` typed skeleton | `quotient_support_algebra_bridge_summary` 证明 append / permutation / reverse stability、duplicate zero-sum cancellation 与 two-route algebraic stability |
| observable ledger candidate | `machineChecked` typed skeleton | `observable_ledger_bridge_summary` 证明 two-route cancellation 可登记为 pending observable entry，且 pending entry 不等于 empirical closure |
| finite action-to-phase law candidate | `machineChecked` typed skeleton | `action_phase_law_bridge_summary` 证明 action index `0/1` 导出 `1/-1`，在 quotient support 上相消并接回 pending ledger |
| stepwise unification candidate summary | `machineChecked` theorem | `stepwise_unification_candidate_summary` 合取当前 finite bridge / probability / grid / action-phase / ledger boundaries |
| finite row sum-one normalization | `machineChecked` theorem | S9 证明 concrete/grid 非终端行 normalized-row-total candidate 为 `1` |
| normalized mass sum-one law | `machineChecked` theorem | S10 证明 concrete/grid 非终端行逐项 `normalizedMass` 求和为 `1` |
| Born rule 从 Markov / 振幅桥的推导 | 未纳入本轮 | S10 不证明振幅平方律或物理测量概率律 |
| 真实干涉、真实 quantum channel law、Born rule 推导 | 未纳入本轮 | S5/S5b/S5c/S5d/S5e/S5f/S5g/S5h/S5i/S5j/S5k/S5l/S5m/S5n/S5o/S5p/S5q/S5r 已开候选接口；还需要 unitary/CPTP、连续相位/作用量动力学、general choice function、general all-path enumeration、一般 path integral、可测预言 theorem 或 Markov 到 Born 的推导 |
| Lorentzian geometry / 度规恢复 | 未纳入本轮 | 初版只保留事件与可达因果接口 |
| 完整反对称性、局部有限性、经典极限 | 未纳入本轮 | S3 只排除一步自环；完整因果集结构需要更强 theorem |
| 经验预言与实验闭合 | 部分接口已入账 | S5q 已有 pending observable ledger entry；仍无数据接口、误差模型、阈值或实验闭合 |

边界句：

```text
Markov 因果桥只验证“测量结果作为事件”的有限过程骨架；
它不证明完整量子理论、不证明广义相对论、不证明二者的最终统一。
```

---

## 〇二 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| tagged 物理语言边界 | `tagged_addition_noncollapse` | 现成量子语言与相对论语言的 tagged addition 不自动坍缩为直接统一项 |
| 文构造覆盖 | `wen_constructive_boundary_summary` | `192 × 371` 覆盖与 tagged 边界相容 |
| 中介桥方向 | `only_mediated_bridge_is_framework_route` | 若保留两面并新增中介，正向路线是 `mediatedBridge` |
| 桥项双投影 | `BridgeTerm`、`bridge_projections_same_one`、`bridge_projections_not_current_identity` | 中介项可双投影、同根，但不是当前 face identity |

typed skeleton / machineChecked in this branch：

| 轴 | 目标锚点 | 当前状态 |
|---|---|---|
| 有限过程载体 | `FiniteProcess`、`state_code_within_bound` | `machineChecked` typed skeleton |
| 路径接口 | `ProcessPath`、`path_implies_reachable` | `machineChecked` typed skeleton |
| 终端测量候选 | `terminal_as_measurement_candidate` | `machineChecked` typed skeleton |
| Markov 支持 / 权重 | `MarkovKernelSkeleton` | `machineChecked` typed skeleton |
| 非零权重推出一步可达 | `positive_weight_implies_step` | `machineChecked` theorem |
| 因果事件投影 | `CausalEvent`、`causalBefore` | `machineChecked` typed skeleton |
| 一步转移推出因果先后 | `step_implies_causal_before` | `machineChecked` theorem |
| 测量-事件桥 | `MeasurementEventBridge` | `machineChecked` typed skeleton |
| 测量事件对齐 | `measurement_event_alignment` | `machineChecked` theorem |
| 桥项投影 | `MeasurementEventBridge.toBridgeTerm`、`measurement_event_bridge_term_keeps_faces` | `machineChecked` theorem |
| Markov 桥保留两面 | `markov_bridge_keeps_quantum_and_relativity_faces` | `machineChecked` theorem |
| 同根非同一 | `markov_bridge_same_one_not_identity` | `machineChecked` theorem |
| 公开摘要 | `markov_causal_bridge_summary` | `machineChecked` theorem |
| 具体三状态实例 | `concrete_bridge_summary` | `machineChecked` theorem |
| operator-cell grid 实例 | `operator_cell_grid_markov_causal_bridge_summary` | `machineChecked` theorem |
| 有限概率核接口 | `FiniteProbabilityKernelSkeleton`、`RowNormalizable` | `machineChecked` typed skeleton |
| 非终端行分母非零 | `finiteMassCandidate_denominator_positive_if_not_terminal` | `machineChecked` theorem |
| S2 公开摘要 | `finite_probability_bridge_summary` | `machineChecked` theorem |
| 路径 witness 组合 | `ComposableProcessPaths`、`composeProcessPaths` | `machineChecked` typed skeleton |
| 组合路径可达 / 因果读法 | `composed_path_reachable`、`composed_path_causal_before` | `machineChecked` theorem |
| code-successor / no-self-loop | `CodeSuccessorStep`、`code_monotone_step_no_self_loop` | `machineChecked` theorem |
| S3 公开摘要 | `path_causal_bridge_summary` | `machineChecked` theorem |
| Markov / amplitude-channel 分层 | `BridgeLayerKind`、`amplitude_layer_is_not_markov_kernel`、`channel_layer_is_not_markov_kernel` | `machineChecked` theorem |
| amplitude skeleton | `QuantumAmplitudeSkeleton`、`HasQuantumAmplitudeProjection` | `machineChecked` typed skeleton |
| channel skeleton | `QuantumChannelSkeleton`、`HasQuantumChannelCandidate` | `machineChecked` typed skeleton |
| channel 保留经典边界 | `channel_projection_keeps_markov_boundary`、`channel_amplitude_support_refines_classical` | `machineChecked` theorem |
| 非零振幅支持尊重 step | `channel_amplitude_support_implies_step` | `machineChecked` theorem |
| S4 公开摘要 | `amplitude_channel_bridge_summary` | `machineChecked` theorem |
| path amplitude skeleton | `PathAmplitudeSkeleton`、`HasPathAmplitudeProjection` | `machineChecked` typed skeleton |
| path amplitude composition | `amplitude_path_composition` | `machineChecked` theorem |
| interference witness | `InterferenceCandidate`、`interference_candidate` | `machineChecked` typed witness |
| Born-shaped boundary | `BornRuleCandidateBoundary`、`born_rule_candidate_boundary`、`born_rule_candidate_nonnegative` | `machineChecked` theorem |
| S5 公开摘要 | `interference_bridge_summary` | `machineChecked` theorem |
| nonzero path-amplitude boundary | `nonzero_path_amplitude_implies_valid`、`nonzero_path_amplitude_implies_reachable`、`nonzero_path_amplitude_implies_causal_before` | `machineChecked` theorem |
| concrete 非零 path witness | `concretePreparedMeasuredPath`、`concrete_prepared_measured_path_nonzero_amplitude` | `machineChecked` theorem |
| S5b 公开摘要 | `nonzero_path_amplitude_bridge_summary` | `machineChecked` theorem |
| two-step path witness | `TwoStepPathWitness`、`SameEndpointTwoStepPair` | `machineChecked` typed skeleton |
| two-route toy witness | `twoRouteProcess`、`twoRouteFiniteProbabilityKernel`、`twoRouteQuantumChannelSkeleton` | `machineChecked` typed skeleton |
| two-path cancellation | `two_route_pair_amplitude_cancels`、`two_route_cancelled_born_weight_zero` | `machineChecked` theorem |
| S5c 公开摘要 | `two_path_interference_bridge_summary` | `machineChecked` theorem |
| discrete phase label | `DiscretePhase`、`discretePhaseAmplitude` | `machineChecked` typed skeleton |
| phase-induced cancellation | `two_route_phase_pair_amplitude_cancels`、`two_route_phase_cancelled_born_weight_zero` | `machineChecked` theorem |
| S5d 公开摘要 | `discrete_phase_bridge_summary` | `machineChecked` theorem |
| edge-action phase candidate | `TwoStepEdgePhaseCandidate`、`HasTwoStepEdgePhaseCandidate` | `machineChecked` typed skeleton |
| edge phase accumulation | `TwoStepEdgePhaseCandidate.pathPhase`、`two_route_upper_accumulated_phase`、`two_route_lower_accumulated_phase` | `machineChecked` theorem |
| relative phase | `two_route_edge_action_phase_difference` | `machineChecked` theorem |
| edge-action-induced cancellation | `two_route_edge_action_pair_amplitude_cancels`、`two_route_edge_action_cancelled_born_weight_zero` | `machineChecked` theorem |
| S5e 公开摘要 | `discrete_action_phase_bridge_summary` | `machineChecked` theorem |
| finite path family | `FiniteTwoStepPathFamily`、`HasFiniteTwoStepPathFamily` | `machineChecked` typed skeleton |
| finite path-family sum | `finitePathFamilyAmplitudeSum`、`finitePathFamilyBornWeight`、`finite_path_family_born_boundary` | `machineChecked` theorem |
| two-route family compatibility | `two_route_family_sum_eq_pair_sum`、`two_route_finite_family_amplitude_cancels`、`two_route_finite_family_born_weight_zero` | `machineChecked` theorem |
| S5f 公开摘要 | `finite_path_sum_bridge_summary` | `machineChecked` theorem |
| finite path-family algebra | `appendFiniteTwoStepPathFamilies`、`reverseFiniteTwoStepPathFamily` | `machineChecked` typed skeleton |
| finite sum stability | `finite_path_family_amplitude_sum_append`、`finite_path_family_amplitude_sum_perm`、`finite_path_family_amplitude_sum_reverse` | `machineChecked` theorem |
| cancellation stability | `finite_path_family_append_cancels_of_canceling_summands`、`two_route_double_family_amplitude_cancels` | `machineChecked` theorem |
| S5g 公开摘要 | `finite_path_sum_algebra_bridge_summary` | `machineChecked` theorem |
| endpoint-indexed family | `EndpointPair`、`EndpointTwoStepPath`、`EndpointIndexedTwoStepPathFamily` | `machineChecked` typed skeleton |
| endpoint-indexed conversion | `endpointIndexedFamilyOfFinitePathFamily`、`endpoint_indexed_family_sum_of_finite_family`、`endpoint_indexed_family_born_weight_of_finite_family` | `machineChecked` theorem |
| S5h 公开摘要 | `endpoint_indexed_path_family_bridge_summary` | `machineChecked` theorem |
| endpoint support filter | `filterEndpointIndexedTwoStepPathFamily`、`EndpointFamilyFilterComplete` | `machineChecked` typed skeleton |
| endpoint support preservation | `endpoint_indexed_family_filter_sum_eq_of_removed_zero`、`endpoint_indexed_family_filter_born_weight_eq_of_removed_zero` | `machineChecked` theorem |
| duplicate handling | `duplicateEndpointIndexedTwoStepPathFamily`、`endpoint_indexed_family_duplicate_sum`、`endpoint_indexed_family_duplicate_cancels_of_canceling` | `machineChecked` theorem |
| S5i 公开摘要 | `endpoint_support_normalization_bridge_summary` | `machineChecked` theorem |
| two-route middle enumeration | `endpointIndexedMiddleList`、`twoRouteSourceTargetMiddleEnumeration`、`two_route_source_target_middle_upper_or_lower` | `machineChecked` theorem |
| two-route enumeration completeness | `two_route_source_target_middle_mem_endpoint_family`、`two_route_source_target_middle_complete` | `machineChecked` theorem |
| S5j 公开摘要 | `two_route_enumeration_bridge_summary` | `machineChecked` theorem |
| visible path key | `TwoStepPathKey`、`twoStepPathKey` | `machineChecked` typed skeleton |
| key equality boundary | `two_step_path_key_eq_start`、`two_step_path_key_eq_middle`、`two_step_path_key_eq_stop` | `machineChecked` theorem |
| two-route key completeness | `two_route_upper_lower_keys_distinct`、`two_route_source_target_key_complete` | `machineChecked` theorem |
| S5k 公开摘要 | `path_identity_bridge_summary` | `machineChecked` theorem |
| finite key quotient candidate | `TwoStepPathKeyEquivalent`、`PathAmplitudeFactorsThroughKey`、`twoStepKeyAmplitudeSum` | `machineChecked` typed skeleton |
| key-compatible descent | `key_equivalent_paths_amplitude_eq`、`endpoint_indexed_key_sum_eq_path_sum_of_factor` | `machineChecked` theorem |
| two-route key cancellation | `two_route_key_amplitude_sum_cancels`、`two_route_key_born_weight_zero`、`two_route_duplicated_key_born_weight_zero` | `machineChecked` theorem |
| S5l 公开摘要 | `finite_key_quotient_bridge_summary` | `machineChecked` theorem |
| quotient class construction | `twoStepPathKeySetoid`、`TwoStepPathKeyQuotient`、`twoStepPathQuotientClass` | `machineChecked` typed skeleton |
| quotient descent | `quotientVisibleKey`、`quotientKeyAmplitude`、`quotient_key_amplitude_matches_path_of_factor` | `machineChecked` theorem |
| two-route quotient completeness | `two_route_upper_lower_quotient_classes_distinct`、`two_route_source_target_quotient_complete` | `machineChecked` theorem |
| S5m 公开摘要 | `path_quotient_bridge_summary` | `machineChecked` theorem |
| canonical representative predicate | `CanonicalRepresentativeFor` | `machineChecked` typed skeleton |
| two-route representative completeness | `two_route_upper_canonical_represents`、`two_route_lower_canonical_represents`、`two_route_source_target_has_canonical_representative` | `machineChecked` theorem |
| S5n 公开摘要 | `canonical_representative_bridge_summary` | `machineChecked` theorem |
| quotient support sum | `quotientSupportAmplitudeSum`、`quotientSupportBornWeight` | `machineChecked` typed skeleton |
| quotient support readback | `quotientSupportVisibleKeys`、`two_route_quotient_support_visible_keys_eq` | `machineChecked` theorem |
| quotient support cancellation | `two_route_quotient_support_amplitude_sum_cancels`、`two_route_quotient_support_born_weight_zero` | `machineChecked` theorem |
| S5o 公开摘要 | `quotient_support_bridge_summary` | `machineChecked` theorem |
| quotient-support algebra | `appendQuotientSupports`、`reverseQuotientSupport`、`duplicateQuotientSupport` | `machineChecked` typed skeleton |
| quotient-support stability | `quotient_support_amplitude_sum_append`、`quotient_support_amplitude_sum_perm`、`quotient_support_amplitude_sum_reverse` | `machineChecked` theorem |
| quotient-support algebraic cancellation | `two_route_reversed_quotient_support_amplitude_cancels`、`two_route_double_quotient_support_amplitude_cancels` | `machineChecked` theorem |
| S5p 公开摘要 | `quotient_support_algebra_bridge_summary` | `machineChecked` theorem |
| observable ledger entry | `ObservableLedgerEntry`、`ObservableLedgerPending`、`EmpiricallyClosed` | `machineChecked` typed skeleton |
| pending / closure boundary | `pending_not_empirically_closed`、`two_route_observable_ledger_not_empirically_closed` | `machineChecked` theorem |
| observable ledger zero boundary | `two_route_observable_ledger_amplitude_zero`、`two_route_observable_ledger_weight_zero` | `machineChecked` theorem |
| S5q 公开摘要 | `observable_ledger_bridge_summary` | `machineChecked` theorem |
| finite action-to-phase law | `actionIndexPhase`、`actionIndexAmplitude`、`QuotientActionPhaseLawCandidate` | `machineChecked` typed skeleton |
| action-phase support cancellation | `two_route_action_phase_support_amplitude_cancels`、`two_route_action_phase_support_born_weight_zero` | `machineChecked` theorem |
| action-phase ledger entry | `twoRouteActionPhaseObservableLedgerEntry`、`two_route_action_phase_observable_ledger_not_empirically_closed` | `machineChecked` theorem |
| S5r 公开摘要 | `action_phase_law_bridge_summary` | `machineChecked` theorem |
| pending boundary list | `PendingBeyondS5r`、`ClosedByStepwiseS5r` | `machineChecked` typed skeleton |
| S8 公开摘要 | `stepwise_unification_candidate_summary` | `machineChecked` theorem |
| finite row support normalization | `FiniteRowSupportNormalization`、`rowWeightSum`、`normalizedRowTotalCandidate` | `machineChecked` typed skeleton |
| concrete/grid row normalization | `concrete_normalized_row_total_candidate_eq_one`、`operatorCellGrid_normalized_row_total_candidate_eq_one` | `machineChecked` theorem |
| S9 公开摘要 | `finite_probability_normalization_bridge_summary` | `machineChecked` theorem |
| normalized mass sum | `normalizedMassSum`、`normalizedMass_sum_one` | `machineChecked` theorem |
| concrete/grid normalized mass law | `concrete_normalizedMass_sum_one`、`operatorCellGrid_normalizedMass_sum_one` | `machineChecked` theorem |
| S10 公开摘要 | `normalized_mass_bridge_summary` | `machineChecked` theorem |

未纳入本轮：

| 轴 | 状态 | 说明 |
|---|---|---|
| Born rule 从 Markov 桥的推导 | 未纳入本轮 | S10 已关闭 finite Markov normalized mass law；仍未从振幅结构推出物理测量概率律 |
| 路径权重乘法定律 | 未纳入本轮 | `pathWeight` 可先作为接口占位 |
| 非平凡量子通道律 | 未纳入本轮 | S4 只有 candidate skeleton；没有 unitary evolution、CPTP、Kraus 或 density-matrix law |
| 真实干涉律 | 未纳入本轮 | S5/S5b/S5c/S5d/S5e/S5f/S5g/S5h/S5i/S5j/S5k/S5l/S5m/S5n/S5o/S5p/S5q/S5r 有相消 witness、非零候选 path witness、two-path finite cancellation candidate、discrete phase-label candidate、edge-action phase accumulation candidate、finite path-family sum candidate、finite path-sum algebra candidate、endpoint-indexed finite family candidate、endpoint support normalization candidate、two-route toy enumeration candidate、visible path-key candidate、finite visible-key quotient candidate、visible-key quotient class candidate、two-route canonical representative candidate、finite quotient-support candidate、quotient-support algebra candidate、pending observable ledger boundary 与 finite action-to-phase law candidate；没有 general choice function、general all-path enumeration、一般 path integral、连续相位/作用量演化或可测预言 theorem |
| 完整因果集公理 | 未纳入本轮 | S3 只证明组合 witness 与一步 no-self-loop；不证明完整偏序、局部有限性或 manifold recovery |
| 度规与曲率 | 未纳入本轮 | 需要几何极限或额外重建结构 |
| 经验闭合 | 未纳入本轮 | S5q 已有 pending observable ledger entry；尚无外部数据、误差模型、阈值与数据判准 |

正面闭合范围：**Markov-因果桥的最小 typed skeleton、S2 有限概率核接口、S3 路径/因果约束、S4 Markov/amplitude-channel 分层候选、S5 interference/Born-shaped candidate、S5b nonzero path-amplitude candidate、S5c two-path finite cancellation candidate、S5d discrete phase-label candidate、S5e discrete edge-action phase candidate、S5f finite path-family sum candidate、S5g finite path-sum algebra candidate、S5h endpoint-indexed finite family candidate、S5i endpoint support normalization candidate、S5j two-route toy enumeration candidate、S5k visible path-key candidate、S5l finite visible-key quotient candidate、S5m visible-key quotient class candidate、S5n displayed canonical representative candidate、S5o finite quotient-support candidate、S5p quotient-support algebra candidate、S5q observable ledger candidate boundary、S5r finite action-to-phase law candidate、S8 stepwise summary、S9 finite row normalization 与 S10 normalized mass law 已在 Lean 中关闭。它已经把有限过程双读、测量-事件对齐、同根非同一、tagged-language noncollapse 保持、非终端行分母非零、权重上界、finite row sum-one normalization、normalized mass sum-one law、path witness 组合、一步 no-self-loop、layer separation、channel 到 S2 边界的投影、path amplitude candidate、相消 witness、`ampProb` boundary、非零候选振幅到 valid / Reachable / causalBefore 的边界、同端点不同中间态两路径候选相消、`zero/pi` 离散相位标签到 `1/-1` 的候选导出、edge phase increments 到 path phase 的累积、relative phase `pi`、edge-action-induced cancellation、finite same-endpoint path family sum、append / permutation / reverse stability、endpoint-indexed conversion、amplitude-complete filter preservation、duplicate handling boundary、toy source/target middle enumeration、visible path-key boundary、toy source/target key completeness、key-compatible amplitude descent、finite key duplicate compensation、two-route key-level cancellation、quotient class construction、two-route quotient completeness、displayed representative completeness、quotient-support cancellation、quotient-support algebraic stability、pending observable ledger boundary、finite action index law、current stepwise summary、finite row normalized total 与 finite classical probability law 都压成了可检查 theorem。**

尚未闭合的范围同样应实事求是列出：Born rule 从 Markov / 振幅桥的推导、真实干涉律、真实 quantum channel law、完整因果偏序、度规恢复、数据校准或经验闭合仍需要后续结构；这不削弱 S5c-S5r、S9 与 S10 的正面推进，只防止把候选边界误读成已完成的物理定律。同时，本轮结论不否定 `192 × 371` 文构造覆盖。

---

## 一 · 最小载体：有限过程

第一步的中介载体不是连续时空，也不是完整态空间，而是有限过程：

```text
Finite Markov-Causal Process
├─ state：带有有界自然数编码的有限状态骨架
├─ initial：初态
├─ terminal：终态谓词
├─ step：一步转移关系
└─ path：从初态到终态的有效过程记录
```

它的优势是可先在 Lean 中证明结构事实：

| 结构事实 | 目标锚点 | 读法 |
|---|---|---|
| 状态编码落在有限界内 | `state_code_within_bound` | 本轮至少把“有限”写成有界编码见证 |
| 有效路径给出可达关系 | `path_implies_reachable` | 过程中的路径不是散点集合，而是方向性连接 |
| 终端状态可作测量候选 | `terminal_as_measurement_candidate` | 到达终端时，状态可进入“结果 / 记录”读法 |

这里的“有限”不是最终世界图像，只是第一轮验证策略：先用最少依赖关闭双读骨架，再决定哪些接口需要升级。

---

## 二 · Markov 读法

在 Markov 读法中，同一过程被看成状态转移系统：

| Markov 侧对象 | 初版读法 | 非目标 |
|---|---|---|
| 状态 | 候选测量前后的过程节点 | 不等同完整 Hilbert 态 |
| 转移 | 下一步支持集或权重 | S10 只在 concrete/grid 非终端行关闭有限 normalized mass law，不等同 Born rule |
| 路径 | 可能历史 | 不先证明路径积分 |
| 终端 | 测量结果候选 | 不先证明 Born rule |

初版使用 `Nat` 权重，只证明：

```text
权重非零 -> 存在一步转移
```

也就是本轮已关闭的 theorem：

```lean
theorem positive_weight_implies_step :
    ...
```

这只证明 Markov skeleton 与过程转移一致，不证明真实概率模型已经完成。

---

## 三 · 因果读法

在因果读法中，同一过程被看成事件结构：

| 因果侧对象 | 初版读法 | 非目标 |
|---|---|---|
| 状态投影 | 候选事件 | 不等同连续时空点 |
| 一步转移 | 直接因果边 | 不等同光锥几何 |
| 可达闭包 | 过去 / 未来方向 | 不先证明完整偏序 |
| 终端状态 | 事件记录 | 不先恢复度规 |

本轮已关闭的 theorem 是：

```lean
theorem step_implies_causal_before :
    ...
```

它只表达“过程方向可以被读成因果方向”。反过来的完备性、反对称性、局部有限性、Lorentzian geometry 与 metric recovery 都不在本轮。

---

## 四 · 测量-事件对齐

桥接的最小突破点在终端状态：

| 同一底层状态 | Markov / 测量读法 | 因果 / 事件读法 |
|---|---|---|
| `s : State` 且 `terminal s` | 测量结果候选 | 事件记录候选 |

实际结构可读成：

```lean
structure MeasurementEventBridge where
  terminalState : State
  isTerminal : terminal terminalState

def MeasurementEventBridge.measurementCandidate ...
def MeasurementEventBridge.eventRecord ...
def MeasurementEventBridge.toBridgeTerm ...
```

本轮已关闭的 theorem：

```lean
theorem measurement_event_alignment :
    ...
```

概念读法是：

```text
同一个终端状态
= 在 Markov 投影下的测量结果
= 在因果投影下的事件记录
```

这一步不把量子项和相对论项直接相加。它是在一个新中介载体中给出共享底层状态，再分别投影到两套读法。因此它只保留 tagged-language noncollapse 边界：

```lean
tagged_addition_noncollapse
```

---

## 五 · 与中介桥层对接

上一层 `QuantumRelativityIntegration` 已经证明：

```text
正向路线 = mediatedBridge
```

本层要做的是把 `mediatedBridge` 的空位具体化为一个有限过程候选：

| 上一层抽象项 | 本层候选解释 |
|---|---|
| `BridgeTerm` | 有限 Markov-因果过程的双投影 |
| `quantumProjection` | Markov / 测量侧读法 |
| `relativityProjection` | 因果 / 事件侧读法 |
| `sameOne` | 两投影共享同一底层过程 |
| `¬ CurrentPhysicalUnity` | 两投影不被偷换成旧语言对象同一 |

本轮已关闭这些桥接 theorem：

```lean
theorem measurement_event_bridge_term_keeps_faces :
    b.toBridgeTerm.quantumFace = .quantumSpace
    ∧ b.toBridgeTerm.relativityFace = .relativisticSpacetime

theorem markov_bridge_keeps_quantum_and_relativity_faces :
    keepsQuantumFace MarkovCausalRoute = true
    ∧ keepsRelativityFace MarkovCausalRoute = true

theorem markov_bridge_same_one_not_identity :
    sameOne .quantumSpace .relativisticSpacetime
    ∧ ¬ CurrentPhysicalUnity .quantumSpace .relativisticSpacetime
```

因此，“中介桥方向”现在获得了第一块可复用的有限构造。但这仍只是 typed skeleton，不是物理动力学或经验闭合。

---

## 六 · Exploration Directions

后续探索分层推进，不在本文档中提前打勾。

| 方向 | 目标 | 当前状态 |
|---|---|---|
| 概率核 | 从支持集 / `Nat` 权重升级到 finite denominator interface，并补 finite row sum-one 与 normalized mass law | S2 已关闭有限分母接口；S9 已关闭 concrete/grid row normalization；S10 已关闭 classical finite probability law |
| 路径/因果约束 | 组合 path witness 与 code-successor/no-self-loop | S3 已关闭最小接口 |
| 量子通道候选 | 从经典转移旁开 channel / amplitude skeleton | S4 已关闭候选接口 |
| 干涉候选 | 让路径振幅接口承载相消 witness 与 Born-shaped boundary | S5 已关闭候选接口 |
| 非零路径振幅候选 | 非零候选振幅投回 valid / Reachable / causalBefore | S5b 已关闭候选接口 |
| 双路径相消候选 | 同端点、不同中间态 two-step paths 的 `1 + (-1) = 0` 与 Born-shaped zero boundary | S5c 已关闭候选接口 |
| 离散相位标记候选 | `zero/pi` 标签导出 `1/-1` 并保持 two-path cancellation | S5d 已关闭候选接口 |
| 离散作用量相位候选 | edge phase increments 累积为 path phase，relative phase 为 `pi`，并保持 two-path cancellation | S5e 已关闭候选接口 |
| 有限路径族求和候选 | two-route upper/lower pair 作为 finite same-endpoint path family 求和，并保持 cancellation | S5f 已关闭候选接口 |
| 有限路径族求和代数候选 | append / permutation / reverse stability 与 cancellation stability | S5g 已关闭候选接口 |
| 端点索引路径族候选 | S5f family 可转为 endpoint-indexed family，并保持候选振幅和与 Born-shaped weight | S5h 已关闭候选接口 |
| 端点支撑规范化候选 | amplitude-complete filter 保持候选振幅和与 Born-shaped weight，duplicate expansion 显式给出 `sum + sum` | S5i 已关闭候选接口 |
| 双路径枚举候选 | twoRoute source/target two-step middle 只能是 `upper` 或 `lower` | S5j 已关闭 toy 候选接口 |
| 路径身份键候选 | `(start, middle, stop)` key 保持可见路径身份，upper/lower keys 不同 | S5k 已关闭候选接口 |
| 有限键商候选 | visible-key equivalence、key-compatible amplitude descent 与 two-route key-level cancellation | S5l 已关闭候选接口 |
| 路径商类候选 | `Setoid` / `Quot` construction、quotient descent 与 two-route quotient completeness | S5m 已关闭候选接口 |
| 规范代表元候选 | two-route toy quotient classes 有 displayed upper/lower representatives | S5n 已关闭候选接口 |
| 商支撑枚举候选 | two-route quotient support coverage、visible-key readback 与 quotient-level cancellation | S5o 已关闭候选接口 |
| 商支撑代数候选 | quotient-support append / permutation / reverse / duplicate cancellation stability | S5p 已关闭候选接口 |
| 观测账本候选 | two-route quotient-support cancellation 登记为 pending observable ledger entry | S5q 已关闭候选接口 |
| 作用量相位律候选 | finite action index `0/1` 导出 `1/-1`，并在 quotient support 上相消 | S5r 已关闭候选接口 |
| 逐步统一候选摘要 | 当前已关闭 finite bridge / probability / grid / action-phase / ledger boundaries 的合取摘要 | S8 已关闭当前摘要 |
| 真实干涉律 | 一般 path integral、连续相位/作用量演化与可测相消 | 未纳入本轮 |
| 因果局部性 | 下一步只依赖局部过去或邻域 | 未纳入本轮 |
| 因果集接口 | 加入偏序、局部有限性与事件网络公理 | 未纳入本轮 |
| 几何极限 | 从稳定可达结构恢复粗粒度时空 / 度规 | 未纳入本轮 |
| 经典极限 | 回收普通事件记录与宏观因果结构 | 未纳入本轮 |
| 经验接口 | 在 S5q 账本基础上接入数据、误差模型、阈值与可测预言 theorem | S5q 已关闭最小 pending ledger；数据接口未纳入本轮 |

探索顺序建议：

```text
有限过程双读
-> 测量-事件对齐
-> Markov 权重与路径接口
-> 有限概率核接口
-> 路径组合与因果约束加强
-> classical Markov / quantum amplitude-channel 分层
-> path amplitude / interference / Born-shaped candidate
-> nonzero path-amplitude candidate witness
-> two-path finite cancellation candidate
-> discrete phase-label candidate
-> discrete edge-action phase accumulation candidate
-> finite path-family sum candidate
-> finite path-sum algebra candidate
-> endpoint-indexed finite family candidate
-> endpoint support normalization candidate
-> two-route toy enumeration candidate
-> visible path-key candidate
-> finite visible-key quotient candidate
-> visible-key quotient class candidate
-> displayed canonical representative candidate
-> finite quotient-support candidate
-> quotient-support algebra candidate
-> observable ledger candidate
-> finite action-to-phase law candidate
-> stepwise unification candidate summary
-> 连续相位/作用量律 / 一般 path integral / 真实干涉律 / 真实 channel law
-> 几何与经验接口
```

---

## 七 · Result Log

记录格式：成功只记录已有可检查产物；失败或未完成不打勾。

| 日期 | 项目 | 结果 | 说明 |
|---|---|---|---|
| 2026-05-08 | companion Markdown | success | 本文档创建，给出最小 Markov-因果桥构造、边界声明、审计与验证命令 |
| 2026-05-08 | Lean module | success | `QuantumRelativityMarkovBridge.lean` 创建并通过目标构建 |
| 2026-05-08 | finite carrier audit | success | 原草案只写 `State : Type`；后补 `stateCode/stateBound/stateCode_lt_bound/stateCode_injective`，把“有限”收窄为有界编码 skeleton |
| 2026-05-08 | `BridgeTerm` projection | success | 新增 `MeasurementEventBridge.toBridgeTerm` 与 `measurement_event_bridge_term_keeps_faces`，把本层桥接到上一层 tag-level `BridgeTerm` |
| 2026-05-08 | first native `lake build` | infrastructure failure / retained | 新 worktree 首次构建卡在 `mathlib4` 克隆超过十分钟，尚未进入 Lean 检查；这不是 theorem 失败 |
| 2026-05-08 | cache-assisted `lake build SSBX.Foundation.Modern.QuantumRelativityMarkovBridge` | success | 改用主 worktree 同 revision 依赖缓存后通过，输出 `Build completed successfully (6 jobs).` |
| 2026-05-08 | `markov_causal_bridge_summary` | `machineChecked` | 关闭 Markov 投影、因果投影、测量-事件对齐、两面保留、同根非同一、tagged-language noncollapse 保持 |
| 2026-05-08 | `192 × 371` correction | `machineChecked` | 新增 `QuantumRelativityWenBoundary.lean` 与《文构造完备与直相加边界》，确认文构造覆盖不受 tagged-language 边界否定 |
| 2026-05-08 | `lake build SSBX` | success with existing warnings | 顶层 import 构建通过，输出 `Build completed successfully (2888 jobs).`；警告来自既有 Wen 模块 unused simp args，不来自本轮新增 Markov / WenBoundary / ConcreteBridge / OperatorCellGrid 模块 |
| 2026-05-08 | verification plan | success | 新增 `formal/SSBX/notes/markov-causal-bridge-verification-plan.md`，记录回归验证、锚点审计、边界审计、升级路线与失败模板 |
| 2026-05-08 | concrete bridge witness | success | 新增 `QuantumRelativityConcreteBridge.lean`，关闭三状态 `prepared → evolved → measured` bridge witness |
| 2026-05-08 | operator-cell grid bridge | success | 新增 `OperatorCellGridMarkovBridge.lean`，把 `371 × 192 = 71232` 覆盖网格作为 `FiniteProcess` 状态空间 |
| 2026-05-08 | stepwise plan | success | 新增 `unification-stepwise-plan.md`，记录 S0-S8 逐步验证路线；S1 已关闭 |
| 2026-05-08 | finite probability-kernel interface | success | 新增 `QuantumRelativityFiniteProbabilityBridge.lean` 与《有限概率核接口 · Markov桥S2》，关闭 concrete 与 `71232` grid 的非终端行分母非零和权重上界 |
| 2026-05-08 | path composition and local causal constraints | success | 新增 `QuantumRelativityPathCausalBridge.lean` 与《路径组合与因果约束 · Markov桥S3》，关闭 path witness composition、组合后 reachability / causalBefore 与 concrete/grid no-self-loop |
| 2026-05-08 | amplitude-channel layer separation | success | 新增 `QuantumRelativityAmplitudeChannelBridge.lean` 与《经典Markov与量子振幅分层 · Markov桥S4》，关闭 classical Markov / quantum amplitude-channel candidate 分层、channel 到 S2 boundary 投影与非零振幅支持精化 |
| 2026-05-08 | interference and Born-shaped candidate | success | 新增 `QuantumRelativityInterferenceBridge.lean` 与《干涉与测量律候选 · Markov桥S5》，关闭 path amplitude candidate、相消 witness 与 `ampProb` boundary |
| 2026-05-08 | nonzero path-amplitude candidate witness | success | 新增 `QuantumRelativityNonzeroPathAmplitudeBridge.lean` 与《非零路径振幅候选 · Markov桥S5b》，关闭非零候选振幅到 valid / Reachable / causalBefore 的边界 |
| 2026-05-08 | two-path finite cancellation candidate | success | 新增 `QuantumRelativityTwoPathInterferenceBridge.lean` 与《双路径相消候选 · Markov桥S5c》，关闭同端点、不同中间态两路径候选振幅 `1 + (-1) = 0` 与 Born-shaped zero boundary |
| 2026-05-08 | discrete phase-label candidate | success | 新增 `QuantumRelativityDiscretePhaseBridge.lean` 与《离散相位标记候选 · Markov桥S5d》，关闭 `zero/pi` 标签导出 `1/-1` 与 phase-induced two-path cancellation |
| 2026-05-08 | discrete edge-action phase candidate | success | 新增 `QuantumRelativityDiscreteActionBridge.lean` 与《离散作用量相位候选 · Markov桥S5e》，关闭 edge increments 到 path phase、relative phase `pi` 与 edge-action-induced two-path cancellation |
| 2026-05-08 | finite path-family sum candidate | success | 新增 `QuantumRelativityFinitePathSumBridge.lean` 与《有限路径族求和候选 · Markov桥S5f》，关闭 finite same-endpoint path family sum、two-route family cancellation 与 Born-shaped zero boundary |
| 2026-05-08 | finite path-sum algebra candidate | success | 新增 `QuantumRelativityFinitePathSumAlgebraBridge.lean` 与《有限路径族求和代数候选 · Markov桥S5g》，关闭 append / permutation / reverse stability 与 cancellation stability |
| 2026-05-08 | endpoint-indexed finite family candidate | success | 新增 `QuantumRelativityEndpointIndexedPathFamilyBridge.lean` 与《端点索引路径族候选 · Markov桥S5h》，关闭 endpoint-indexed conversion、sum/weight preservation 与 two-route endpoint-indexed cancellation |
| 2026-05-08 | endpoint support normalization candidate | success | 新增 `QuantumRelativityEndpointSupportNormalizationBridge.lean` 与《端点支撑规范化候选 · Markov桥S5i》，关闭 amplitude-complete filter preservation、duplicate expansion 与 duplicated zero-sum cancellation |
| 2026-05-08 | two-route source/target enumeration candidate | success | 新增 `QuantumRelativityTwoRouteEnumerationBridge.lean` 与《双路径枚举候选 · Markov桥S5j》，关闭 toy source/target two-step middle enumeration 与 endpoint family completeness |
| 2026-05-08 | finite two-step path identity-key candidate | success | 新增 `QuantumRelativityPathIdentityBridge.lean` 与《路径身份键候选 · Markov桥S5k》，关闭 visible key boundary 与 toy source/target key completeness |
| 2026-05-08 | finite visible-key quotient candidate | success | 新增 `QuantumRelativityFiniteKeyQuotientBridge.lean` 与《有限键商候选 · Markov桥S5l》，关闭 key-equivalence、key-compatible amplitude descent、duplicate compensation 与 two-route key-level cancellation |
| 2026-05-08 | visible-key quotient class candidate | success | 新增 `QuantumRelativityPathQuotientBridge.lean` 与《路径商类候选 · Markov桥S5m》，关闭 quotient class construction、quotient descent 与 two-route quotient completeness |
| 2026-05-08 | two-route canonical representative candidate | success | 新增 `QuantumRelativityCanonicalRepresentativeBridge.lean` 与《规范代表元候选 · Markov桥S5n》，关闭 displayed representatives 与 toy source/target representative completeness |
| 2026-05-08 | finite quotient-support candidate | failure retained / success | 新增 `QuantumRelativityQuotientSupportBridge.lean` 与《商支撑枚举候选 · Markov桥S5o》；第一次 build 因 `rfl` 未展开 quotient amplitude / function composition 失败，修正后关闭 support coverage、visible-key readback、quotient-level cancellation 与 Born-shaped zero boundary |
| 2026-05-08 | quotient-support algebra candidate | failure retained / success | 新增 `QuantumRelativityQuotientSupportAlgebraBridge.lean` 与《商支撑代数候选 · Markov桥S5p》；第一次 build 因显式 `twoRouteProcess` 类型标注解析到不同 namespace 失败，修正后关闭 append / permutation / reverse stability、duplicate zero-sum cancellation 与 two-route algebraic stability |
| 2026-05-09 | observable ledger candidate boundary | success | 新增 `QuantumRelativityObservableLedgerBridge.lean` 与《观测账本候选 · Markov桥S5q》，关闭 pending observable ledger entry、zero sum/weight 与 pending-not-empirically-closed boundary |
| 2026-05-09 | finite action-to-phase law candidate | failure retained / success | 新增 `QuantumRelativityActionPhaseLawBridge.lean` 与《作用量相位律候选 · Markov桥S5r》；第一次 build 因 quotient readback 展开失败，修正后关闭 action index `0/1` 到 `1/-1` 的 quotient-support cancellation 与 pending ledger registration |
| 2026-05-09 | stepwise unification candidate summary | failure retained / success | 新增 `QuantumRelativityStepwiseUnificationBridge.lean` 与《逐步统一候选摘要 · Markov桥S8》；第一次 build 因 namespace/defeq 解析失败，修正后关闭 current stepwise summary |

---

## 八 · Validation Command

Lean 验证命令：

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
lake build SSBX
```

文档与索引格式检查：

```bash
git diff --check --
```

一句话总结：

> Markov 因果桥不是最终统一理论，而是把“测量结果成为事件”压成有限、双投影、可验证的 skeleton；本轮已关闭抽象桥、三状态 concrete witness、`71232` operator-cell grid bridge、S2 有限概率核分母接口、S3 路径/因果约束、S4 量子振幅-通道候选分层、S5 干涉 / Born-shaped 候选接口、S5b 非零路径振幅候选 witness、S5c 双路径有限相消候选、S5d 离散相位标记候选、S5e 离散作用量相位候选、S5f 有限路径族求和候选、S5g 有限路径族求和代数候选、S5h 端点索引路径族候选、S5i 端点支撑规范化候选、S5j 双路径枚举候选、S5k 路径身份键候选、S5l 有限键商候选、S5m 路径商类候选、S5n 规范代表元候选、S5o 商支撑枚举候选、S5p 商支撑代数候选、S5q 观测账本候选、S5r 作用量相位律候选、S8 逐步统一候选摘要、S9 有限概率归一化候选与 S10 归一化质量求和候选，后续处理 Born rule derivation、amplitude/Born normalized support、连续相位/作用量律、一般 path integral、真实 channel law、完整因果集、几何极限与带数据校准的经验接口。
