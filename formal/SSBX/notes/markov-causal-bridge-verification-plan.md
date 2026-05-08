# Markov-Causal Bridge Verification Plan

目标：把 Markov-因果桥从“已能构建的 typed skeleton”推进到可重复验证的研究程序。本文只定义验证流程，不新增物理 claim。

关联文件：

| 文件 | 作用 |
|---|---|
| `formal/SSBX/Foundation/Modern/QuantumRelativityNoGo.lean` | tagged 物理语言非坍缩边界 |
| `formal/SSBX/Foundation/Modern/QuantumRelativityWenBoundary.lean` | `192 × 371` 文构造覆盖与 tagged 边界相容性 |
| `formal/SSBX/Foundation/Modern/QuantumRelativityMarkovBridge.lean` | 当前 machine-checked Lean 骨架 |
| `formal/SSBX/Foundation/Modern/QuantumRelativityConcreteBridge.lean` | 三状态 concrete bridge witness |
| `formal/SSBX/Foundation/Modern/OperatorCellGridMarkovBridge.lean` | `71232` operator-cell grid bridge process |
| `formal/SSBX/Foundation/Modern/QuantumRelativityFiniteProbabilityBridge.lean` | S2 finite probability-kernel denominator interface |
| `formal/SSBX/Foundation/Modern/QuantumRelativityPathCausalBridge.lean` | S3 path composition and local causal constraints |
| `formal/SSBX/Foundation/Modern/QuantumRelativityAmplitudeChannelBridge.lean` | S4 classical Markov / quantum amplitude-channel layered interface |
| `formal/SSBX/Foundation/Modern/QuantumRelativityInterferenceBridge.lean` | S5 path amplitude / interference / Born-shaped candidate interface |
| `formal/SSBX/Foundation/Modern/QuantumRelativityNonzeroPathAmplitudeBridge.lean` | S5b nonzero path-amplitude candidate witness |
| `formal/SSBX/Foundation/Modern/QuantumRelativityTwoPathInterferenceBridge.lean` | S5c two-path finite cancellation candidate |
| `formal/SSBX/Foundation/Modern/QuantumRelativityDiscretePhaseBridge.lean` | S5d discrete phase-label candidate |
| `formal/SSBX/Foundation/Modern/QuantumRelativityDiscreteActionBridge.lean` | S5e discrete edge-action phase accumulation candidate |
| `formal/SSBX/Foundation/Modern/QuantumRelativityFinitePathSumBridge.lean` | S5f finite path-family sum candidate |
| `formal/SSBX/Foundation/Modern/QuantumRelativityFinitePathSumAlgebraBridge.lean` | S5g finite path-sum algebra candidate |
| `formal/SSBX/Foundation/Modern/QuantumRelativityEndpointIndexedPathFamilyBridge.lean` | S5h endpoint-indexed finite path-family candidate |
| `formal/SSBX/Foundation/Modern/QuantumRelativityEndpointSupportNormalizationBridge.lean` | S5i endpoint support normalization candidate |
| `formal/SSBX/Foundation/Modern/QuantumRelativityTwoRouteEnumerationBridge.lean` | S5j two-route source/target enumeration candidate |
| `formal/SSBX/Foundation/Modern/QuantumRelativityPathIdentityBridge.lean` | S5k finite two-step path identity-key candidate |
| `formal/SSBX/Foundation/Modern/QuantumRelativityFiniteKeyQuotientBridge.lean` | S5l finite visible-key quotient candidate |
| `formal/SSBX/Foundation/Modern/QuantumRelativityPathQuotientBridge.lean` | S5m visible-key quotient class candidate |
| `formal/SSBX/Foundation/Modern/QuantumRelativityCanonicalRepresentativeBridge.lean` | S5n two-route canonical representative candidate |
| `formal/SSBX/Foundation/Modern/QuantumRelativityQuotientSupportBridge.lean` | S5o finite quotient-support candidate |
| `formal/SSBX/Foundation/Modern/QuantumRelativityQuotientSupportAlgebraBridge.lean` | S5p quotient-support algebra candidate |
| `formal/SSBX/Foundation/Modern/QuantumRelativityObservableLedgerBridge.lean` | S5q observable ledger candidate boundary |
| `formal/SSBX/Foundation/Modern/QuantumRelativityActionPhaseLawBridge.lean` | S5r finite action-to-phase law candidate |
| `formal/SSBX/Foundation/Modern/QuantumRelativityStepwiseUnificationBridge.lean` | S8 current stepwise unification candidate summary |
| `formal/SSBX/Foundation/Modern/QuantumRelativityFiniteProbabilityNormalizationBridge.lean` | S9 finite probability normalization candidate |
| `formal/SSBX/Foundation/Modern/QuantumRelativityNormalizedMassBridge.lean` | S10 normalized finite mass probability law |
| `formal/SSBX/Foundation/Modern/QuantumRelativityBornWeightNormalizationBridge.lean` | S11 conditional Born-weight normalization law |
| `formal/SSBX/notes/markov-causal-bridge-plan.md` | 探索计划与完成记录 |
| `formal/SSBX/notes/unification-stepwise-plan.md` | 逐步完善到候选统一的阶段路线 |
| `义理/文构造完备与直相加边界.md` | 对 `current-language no-go` 旧说法的正名 |
| `义理/Markov因果桥 · 大统一最小验证构造.md` | 义理边界与 theorem 锚点说明 |
| `义理/有限概率核接口 · Markov桥S2.md` | S2 有限概率核接口 companion 文档 |
| `义理/路径组合与因果约束 · Markov桥S3.md` | S3 路径组合与局部因果约束 companion 文档 |
| `义理/经典Markov与量子振幅分层 · Markov桥S4.md` | S4 经典 Markov 与量子振幅 / 通道候选分层 companion 文档 |
| `义理/干涉与测量律候选 · Markov桥S5.md` | S5 干涉与测量律候选 companion 文档 |
| `义理/非零路径振幅候选 · Markov桥S5b.md` | S5b 非零路径振幅候选 companion 文档 |
| `义理/双路径相消候选 · Markov桥S5c.md` | S5c 双路径相消候选 companion 文档 |
| `义理/离散相位标记候选 · Markov桥S5d.md` | S5d 离散相位标记候选 companion 文档 |
| `义理/离散作用量相位候选 · Markov桥S5e.md` | S5e 离散作用量相位候选 companion 文档 |
| `义理/有限路径族求和候选 · Markov桥S5f.md` | S5f 有限路径族求和候选 companion 文档 |
| `义理/有限路径族求和代数候选 · Markov桥S5g.md` | S5g 有限路径族求和代数 companion 文档 |
| `义理/端点索引路径族候选 · Markov桥S5h.md` | S5h 端点索引路径族 companion 文档 |
| `义理/端点支撑规范化候选 · Markov桥S5i.md` | S5i 端点支撑规范化 companion 文档 |
| `义理/双路径枚举候选 · Markov桥S5j.md` | S5j 双路径枚举 companion 文档 |
| `义理/路径身份键候选 · Markov桥S5k.md` | S5k 路径身份键 companion 文档 |
| `义理/有限键商候选 · Markov桥S5l.md` | S5l 有限键商 companion 文档 |
| `义理/路径商类候选 · Markov桥S5m.md` | S5m 路径商类 companion 文档 |
| `义理/规范代表元候选 · Markov桥S5n.md` | S5n 规范代表元 companion 文档 |
| `义理/商支撑枚举候选 · Markov桥S5o.md` | S5o 商支撑枚举 companion 文档 |
| `义理/商支撑代数候选 · Markov桥S5p.md` | S5p 商支撑代数 companion 文档 |
| `义理/观测账本候选 · Markov桥S5q.md` | S5q 观测账本 companion 文档 |
| `义理/作用量相位律候选 · Markov桥S5r.md` | S5r 作用量相位律 companion 文档 |
| `义理/逐步统一候选摘要 · Markov桥S8.md` | S8 逐步统一候选摘要 companion 文档 |
| `义理/有限概率归一化候选 · Markov桥S9.md` | S9 有限概率归一化 companion 文档 |
| `义理/归一化质量求和候选 · Markov桥S10.md` | S10 normalized mass sum-one companion 文档 |
| `义理/Born权重条件归一候选 · Markov桥S11.md` | S11 conditional Born-weight normalization companion 文档 |

## 当前验证结论

- [x] `QuantumRelativityMarkovBridge.lean` 可单独构建。
- [x] `SSBX` 顶层入口可构建并导入新模块。
- [x] `markov_causal_bridge_summary` 已关闭有限过程双读、测量-事件对齐、两面保留、同根非同一、tagged physical-language noncollapse 保持。
- [x] `MeasurementEventBridge.toBridgeTerm` 已把本层桥接到上一层 tag-level `BridgeTerm`。
- [x] `wen_constructive_boundary_summary` 已确认 `192 × 371` 文构造覆盖不受 tagged-language 边界否定。
- [x] `concrete_bridge_summary` 已给出三状态 `prepared → evolved → measured` concrete bridge witness。
- [x] `operator_cell_grid_markov_causal_bridge_summary` 已把 `371 × 192 = 71232` operator-cell grid 用作 finite process 状态空间。
- [x] `finite_probability_bridge_summary` 已关闭 concrete 与 `71232` grid 的有限概率核接口：非终端行分母非零，权重受行分母约束。
- [x] `path_causal_bridge_summary` 已关闭 path witness composition、组合后 reachability / `causalBefore`、concrete 与 grid 的 code-successor/no-self-loop 约束。
- [x] `amplitude_channel_bridge_summary` 已关闭 classical Markov / quantum amplitude-channel 分层候选接口：layer separation、channel candidate 到 S2 boundary 的投影、非零振幅支持精化。
- [x] `interference_bridge_summary` 已关闭 path amplitude / interference / Born-shaped candidate interface：路径振幅候选、相消 witness、`ampProb` boundary。
- [x] `nonzero_path_amplitude_bridge_summary` 已关闭 nonzero path-amplitude candidate witness：非零候选振幅推出 valid / Reachable / causalBefore，并给 concrete bridge 一个非零 path witness。
- [x] `two_path_interference_bridge_summary` 已关闭 two-path finite cancellation candidate：同端点、不同中间态的 two-step candidate paths 携带 `1` 与 `-1`，有限和为 `0`，并接回 Born-shaped zero boundary。
- [x] `discrete_phase_bridge_summary` 已关闭 discrete phase-label candidate：`zero/pi` 标签导出 `1/-1`，upper/lower paths 携带相反标签，并保持 phase-induced two-path cancellation。
- [x] `discrete_action_phase_bridge_summary` 已关闭 discrete edge-action phase accumulation candidate：edge phase increments 累积为 two-step path phase，upper/lower relative phase 为 `pi`，并保持 induced two-path cancellation。
- [x] `finite_path_sum_bridge_summary` 已关闭 finite path-family sum candidate：upper/lower two-route witness 作为 finite same-endpoint path family，其 family amplitude sum 等于 pair sum、相消为 `0`，并接回 Born-shaped zero boundary。
- [x] `finite_path_sum_algebra_bridge_summary` 已关闭 finite path-sum algebra candidate：finite path-family sums 的 append / permutation / reverse stability 与 cancellation stability 已形式化。
- [x] `endpoint_indexed_path_family_bridge_summary` 已关闭 endpoint-indexed finite path-family candidate：S5f family 可转为 endpoint-indexed family，并保持候选振幅和与 Born-shaped weight。
- [x] `endpoint_support_normalization_bridge_summary` 已关闭 endpoint support normalization candidate：amplitude-complete finite filter 保持 sum/weight，duplicate expansion 与 duplicated zero-sum cancellation 已形式化。
- [x] `two_route_enumeration_bridge_summary` 已关闭 two-route source/target enumeration candidate：toy source/target two-step witness 的 middle 必在 `[upper, lower]`，并接回 endpoint-indexed family middle list。
- [x] `path_identity_bridge_summary` 已关闭 finite two-step path identity-key candidate：key equality 保持可见 `start/middle/stop`，two-route upper/lower keys 不同，toy source/target key enumeration complete。
- [x] `finite_key_quotient_bridge_summary` 已关闭 finite visible-key quotient candidate：visible-key equality 是 quotient-candidate equivalence relation，key-compatible amplitudes 可降到 key 层，two-route key-level cancellation 与 duplicate compensation 已形式化。
- [x] `path_quotient_bridge_summary` 已关闭 visible-key quotient class candidate：`Setoid` / `Quot` 已构造，visible key 与 key-level amplitude 可下降到 quotient class，two-route quotient classes distinct 且 toy source/target quotient enumeration complete。
- [x] `canonical_representative_bridge_summary` 已关闭 two-route canonical representative candidate：upper/lower displayed paths 代表自身 quotient class，任意 toy source/target two-step path 的 quotient class 由 displayed upper/lower path 代表。
- [x] `quotient_support_bridge_summary` 已关闭 finite quotient-support candidate：two-route quotient support 覆盖 toy source/target quotient classes，可回读 visible keys，并保持 quotient-level cancellation 与 Born-shaped zero boundary。
- [x] `quotient_support_algebra_bridge_summary` 已关闭 quotient-support algebra candidate：append / permutation / reverse stability、duplicate zero-sum cancellation 与 two-route algebraic cancellation stability 已形式化。
- [x] `observable_ledger_bridge_summary` 已关闭 observable ledger candidate boundary：two-route quotient-support cancellation 可登记为 pending observable ledger entry，且 pending entry 不等于 empirical closure。
- [x] `action_phase_law_bridge_summary` 已关闭 finite action-to-phase law candidate：period-two action index 导出 `1/-1`，在 quotient support 上相消，并接回 pending observable ledger。
- [x] `stepwise_unification_candidate_summary` 已关闭 current stepwise unification candidate summary：concrete bridge、finite probability、`71232` grid、S5r action-phase cancellation、pending ledger 与未闭合边界列表已合取。
- [x] `finite_probability_normalization_bridge_summary` 已关闭 finite row sum-one probability boundary：concrete 与 `71232` grid kernel 都有显式 row support，非终端行 normalized-row-total candidate 为 `1`。
- [x] `normalized_mass_bridge_summary` 已关闭 finite normalized mass probability law：`rowWeightSum_eq_rowTotal` 有命名出口，且 concrete/grid 非终端行的逐项 `normalizedMass` 求和为 `1`。
- [x] `born_weight_normalization_bridge_summary` 已关闭 conditional finite Born-weight normalization law：若有限 amplitude support 已由 `ampProb` 归一，则所有 `candidateWeight` 非负且有限和为 `1`。
- [x] 首次新 worktree 原生构建的 `mathlib4` 克隆阻塞已记录为基础设施失败，不当作 theorem 失败。
- [ ] 尚未验证 Born rule 从 Markov 桥的推导、continuous phase/action law、general all-path enumeration、一般 path integral、真实可测干涉律、unitary / CPTP quantum channel law、完整因果偏序、局部有限 causal set、度规恢复、数据校准、可测预言 theorem 或经验闭合。

## 每次变更的最低验证门槛

任何改动触及本桥相关 Lean 或文档时，至少执行：

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
lake build SSBX
git diff --check --
```

通过标准：

| 门槛 | 通过标准 | 失败处理 |
|---|---|---|
| 目标模块构建 | `Build completed successfully` | 修 Lean；若失败来自依赖或网络，记录为 infra failure |
| 顶层入口构建 | `lake build SSBX` 通过 | 检查 import 顺序、命名冲突、旧模块影响 |
| 格式检查 | `git diff --check` 无输出 | 修尾随空格、冲突标记、缩进问题 |
| 状态词自审 | 无 stale `unchecked/planned/build pending` | 更新文档状态或撤回对应勾选 |

状态词自审命令：

```bash
rg -n "待处理|future|deferred|部分相关|佛|唯识|analogy|unchecked|planned|build pending|not run|not edited|failure-to-close" formal/SSBX/notes/markov-causal-bridge-plan.md formal/SSBX/notes/markov-causal-bridge-verification-plan.md formal/SSBX/notes/unification-stepwise-plan.md '义理/Markov因果桥 · 大统一最小验证构造.md' '义理/'*'Markov桥S'*.md
```

## Theorem 锚点审计

每次修改后确认这些锚点仍存在：

| 层 | 锚点 | 当前状态 |
|---|---|---|
| 有限载体 | `FiniteProcess`、`state_code_within_bound` | `machineChecked` |
| 路径与可达 | `ProcessPath`、`Reachable`、`path_implies_reachable` | `machineChecked` |
| Markov 读法 | `MarkovKernelSkeleton`、`positive_weight_implies_step`、`pathWeight` | `machineChecked` |
| 因果读法 | `CausalEvent`、`causalBefore`、`step_implies_causal_before` | `machineChecked` |
| 测量-事件对齐 | `MeasurementEventBridge`、`measurement_event_alignment` | `machineChecked` |
| 上层桥项投影 | `MeasurementEventBridge.toBridgeTerm`、`measurement_event_bridge_term_keeps_faces` | `machineChecked` |
| 中介路线边界 | `MarkovCausalRoute`、`markov_causal_route_is_framework_route` | `machineChecked` |
| 文构造边界修正 | `wen_constructive_boundary_summary` | `machineChecked` |
| concrete bridge witness | `concrete_bridge_summary` | `machineChecked` |
| operator-cell grid bridge | `operator_cell_grid_markov_causal_bridge_summary` | `machineChecked` |
| finite probability-kernel interface | `finite_probability_bridge_summary` | `machineChecked` |
| path composition and local causal constraints | `path_causal_bridge_summary` | `machineChecked` |
| classical Markov / quantum amplitude-channel layering | `amplitude_channel_bridge_summary` | `machineChecked` |
| path amplitude / interference candidate boundary | `interference_bridge_summary` | `machineChecked` |
| nonzero path-amplitude candidate witness | `nonzero_path_amplitude_bridge_summary` | `machineChecked` |
| two-path finite cancellation candidate | `two_path_interference_bridge_summary` | `machineChecked` |
| discrete phase-label candidate | `discrete_phase_bridge_summary` | `machineChecked` |
| discrete edge-action phase candidate | `discrete_action_phase_bridge_summary` | `machineChecked` |
| finite path-family sum candidate | `finite_path_sum_bridge_summary` | `machineChecked` |
| finite path-sum algebra candidate | `finite_path_sum_algebra_bridge_summary` | `machineChecked` |
| endpoint-indexed path-family candidate | `endpoint_indexed_path_family_bridge_summary` | `machineChecked` |
| endpoint support normalization candidate | `endpoint_support_normalization_bridge_summary` | `machineChecked` |
| two-route source/target enumeration candidate | `two_route_enumeration_bridge_summary` | `machineChecked` |
| finite two-step path identity-key candidate | `path_identity_bridge_summary` | `machineChecked` |
| finite visible-key quotient candidate | `finite_key_quotient_bridge_summary` | `machineChecked` |
| visible-key quotient class candidate | `path_quotient_bridge_summary` | `machineChecked` |
| two-route canonical representative candidate | `canonical_representative_bridge_summary` | `machineChecked` |
| finite quotient-support candidate | `quotient_support_bridge_summary` | `machineChecked` |
| quotient-support algebra candidate | `quotient_support_algebra_bridge_summary` | `machineChecked` |
| observable ledger candidate boundary | `observable_ledger_bridge_summary` | `machineChecked` |
| finite action-to-phase law candidate | `action_phase_law_bridge_summary` | `machineChecked` |
| current stepwise unification candidate summary | `stepwise_unification_candidate_summary` | `machineChecked` |
| finite row sum-one normalization boundary | `finite_probability_normalization_bridge_summary` | `machineChecked` |
| finite normalized mass probability law | `normalized_mass_bridge_summary` | `machineChecked` |
| conditional Born-weight normalization law | `born_weight_normalization_bridge_summary` | `machineChecked` |
| tagged-language noncollapse 保持 | `markov_bridge_not_direct_language_addition` | `machineChecked` |
| 公开摘要 | `markov_causal_bridge_summary` | `machineChecked` |

审计命令：

```bash
rg -n "theorem|structure|def" formal/SSBX/Foundation/Modern/QuantumRelativityMarkovBridge.lean formal/SSBX/Foundation/Modern/QuantumRelativityConcreteBridge.lean formal/SSBX/Foundation/Modern/OperatorCellGridMarkovBridge.lean
```

## 边界审计

本桥当前已经闭合的正面内容：

```text
同一个有限过程骨架
  可以有 Markov / 测量读法
  可以有因果 / 事件读法
  终端状态可以对齐成测量候选与事件记录
  可以承载与 classical Markov layer 分开的 quantum amplitude/channel candidate layer
  可以承载 path amplitude / interference-shaped / Born-shaped candidate interface
  可以承载非零 path-amplitude candidate witness，并投回 valid / Reachable / causalBefore
  可以承载同端点、不同中间态 two-step paths 的有限相消候选
  可以承载离散 phase-label 到候选振幅的导出接口
  可以承载 edge phase increments 到 two-step path phase 的累积接口
  可以承载 finite same-endpoint path family 的候选振幅求和接口
  可以承载 finite path-family sum 的 append / permutation / reverse stability
  可以承载 endpoint-indexed finite path-family conversion
  可以承载 amplitude-complete finite filter 与 duplicate handling boundary
  可以承载 two-route source/target middle enumeration、visible path-key、visible-key quotient class、canonical representative、finite quotient support 与 quotient-support algebra
  可以把 quotient-support cancellation 登记为 pending observable ledger entry，并证明 pending entry 不等于 empirical closure
  可以把 finite action index `0/1` 导出为 `1/-1` 并在 quotient support 上相消
  可以把当前已关闭结构合取成 current stepwise unification candidate summary
  可以给 concrete 与 71232 grid kernel 显式 row support，并让非终端行归一为 1
  可以把 row support 上的逐项 normalizedMass 求和为 1，形成 finite classical probability law
  可以在 finite amplitude support 已由 ampProb 归一时，推出 Born-shaped candidateWeight 非负且求和为 1
  同时保持当前 tagged 物理语言 noncollapse 边界
```

本桥后续需要补的结构：

| 后续结构 | 当前缺口 |
|---|---|
| 量子引力 | 还需要动力学、连续极限、量子场或引力方程 |
| Born rule 推导 | S11 已关闭条件式 finite Born-weight law；还需要从振幅结构推出无条件归一化测量概率律 |
| 真实干涉律 | S5/S5b/S5c/S5d/S5e/S5f/S5g/S5h/S5i/S5j/S5k/S5l/S5m/S5n/S5o/S5p/S5q/S5r 已有 path amplitude、非零 witness、two-path finite cancellation candidate、discrete phase-label candidate、edge-action phase accumulation candidate、finite path-family sum candidate、finite path-sum algebra candidate、endpoint-indexed finite family candidate、endpoint support normalization candidate、two-route toy enumeration candidate、visible path-key candidate、finite visible-key quotient candidate、visible-key quotient class candidate、two-route canonical representative candidate、finite quotient-support candidate、quotient-support algebra candidate、pending observable ledger boundary 与 finite action-to-phase law candidate；还需要 general choice function、general all-path enumeration、一般 path integral、连续相位动力学、可测预言 theorem 或经验闭合 |
| 真实 quantum channel law | S4 的 `QuantumChannelSkeleton` 是 candidate interface；还需要 unitary evolution、CPTP、Kraus 或 density-matrix law |
| 完整因果集或时空度规 | S3 已关闭一步 no-self-loop；还需要偏序全公理、Lorentzian geometry 或 metric recovery theorem |
| 经验预言 | S5q 已给出 pending observable ledger entry；还需要外部数据、观测量、误差模型、阈值或数据判准 |

文档若使用这些更强术语，应同步补上相应 formal structure 与验证记录；没有新增结构时，按当前已闭合 theorem 命名。

## 下一轮升级验证路线

每一步都必须新增 Lean 锚点、更新义理边界、记录成功或失败。

| 阶段 | 目标 | 验证出口 |
|---|---|---|
| V1 | 给出一个具体有限实例 | 已由 `concrete_bridge_summary` 与 `operator_cell_grid_markov_causal_bridge_summary` 关闭 |
| V2 | 从 `Nat` 权重升级到有限概率核 | 已由 `finite_probability_bridge_summary` 关闭 finite denominator / bounded weights interface |
| V3 | 加强路径 / 因果组合 | 已由 `path_causal_bridge_summary` 关闭 path witness composition；`pathWeight` 乘法仍 pending |
| V4 | 加强因果结构 | S3 已关闭 code-successor/no-self-loop；完整偏序、局部有限性仍 pending |
| V5 | 引入 quantum channel / amplitude skeleton | 已由 `amplitude_channel_bridge_summary` 关闭候选接口；真实 channel law 仍 pending |
| V6 | 引入 path amplitude / interference / Born-shaped candidate | 已由 `interference_bridge_summary` 关闭候选接口；真实干涉律和 Born-rule derivation 仍 pending |
| V6b | 引入 nonzero path-amplitude candidate witness | 已由 `nonzero_path_amplitude_bridge_summary` 关闭非零候选接口；真实相位律、一般路径求和和可测干涉仍 pending |
| V6c | 引入 two-path finite cancellation candidate | 已由 `two_path_interference_bridge_summary` 关闭 same-endpoint / different-middle two-step pair 与 `1 + (-1) = 0`；一般 path integral、phase/action law 和可测干涉仍 pending |
| V6d | 引入 discrete phase-label candidate | 已由 `discrete_phase_bridge_summary` 关闭 `zero/pi` 标签到 `1/-1` 的导出；continuous phase、action/Hamiltonian law、path integral 与可测干涉仍 pending |
| V6e | 引入 discrete edge-action phase accumulation candidate | 已由 `discrete_action_phase_bridge_summary` 关闭 edge increments 到 path phase、relative phase `pi` 与 induced cancellation；finite path-family sum 已由 V6f 承接，continuous action law 与 path integral 仍 pending |
| V6f | 引入 finite path-family sum candidate | 已由 `finite_path_sum_bridge_summary` 关闭 same-endpoint finite family、family amplitude sum 与 two-route cancellation；path-sum algebra 已由 V6g 承接，continuous action law 与 path integral 仍 pending |
| V6g | 引入 finite path-sum algebra candidate | 已由 `finite_path_sum_algebra_bridge_summary` 关闭 append / permutation / reverse stability 与 cancellation stability；endpoint-indexed family 已由 V6h 承接，all-path enumeration、continuous action law 与 path integral 仍 pending |
| V6h | 引入 endpoint-indexed finite path-family candidate | 已由 `endpoint_indexed_path_family_bridge_summary` 关闭 endpoint-indexed conversion、sum preservation 与 two-route endpoint-indexed cancellation；filter/support normalization 已由 V6i 承接，all-path enumeration、continuous action law 与 path integral 仍 pending |
| V6i | 引入 endpoint support normalization candidate | 已由 `endpoint_support_normalization_bridge_summary` 关闭 amplitude-complete filter preservation、Born-shaped preservation 与 duplicate handling boundary；two-route toy enumeration 已由 V6j 承接，quotient 去重、general all-path enumeration、continuous action law 与 path integral 仍 pending |
| V6j | 引入 two-route source/target enumeration candidate | 已由 `two_route_enumeration_bridge_summary` 关闭 toy source/target two-step middle enumeration；proof-field path equality、quotient 去重、general all-path enumeration、continuous action law 与 path integral 仍 pending |
| V6k | 引入 finite two-step path identity-key candidate | 已由 `path_identity_bridge_summary` 关闭 visible key boundary 与 toy source/target key completeness；finite visible-key quotient candidate 已由 V6l 承接，proof-field path equality、general all-path enumeration、continuous action law 与 path integral 仍 pending |
| V6l | 引入 finite visible-key quotient candidate | 已由 `finite_key_quotient_bridge_summary` 关闭 key-equivalence、key-compatible amplitude descent、duplicate compensation 与 two-route key-level cancellation；visible-key quotient class 已由 V6m 承接，proof-field path equality、general all-path enumeration、continuous action law 与 path integral 仍 pending |
| V6m | 引入 visible-key quotient class candidate | 已由 `path_quotient_bridge_summary` 关闭 `Setoid`/`Quot` construction、quotient descent 与 two-route quotient completeness；two-route canonical representative 已由 V6n 承接，general choice function、proof-field path equality、general all-path enumeration、continuous action law 与 path integral 仍 pending |
| V6n | 引入 two-route canonical representative candidate | 已由 `canonical_representative_bridge_summary` 关闭 displayed representative boundary；finite quotient-support enumeration 已由 V6o 承接，general choice function、proof-field path equality、general all-path enumeration、continuous action law 与 path integral 仍 pending |
| V6o | 引入 finite quotient-support candidate | 已由 `quotient_support_bridge_summary` 关闭 quotient support coverage、visible-key readback、quotient-level cancellation 与 Born-shaped zero boundary；quotient-support algebra 已由 V6p 承接，general all-path enumeration、continuous action law 与 path integral 仍 pending |
| V6p | 引入 quotient-support algebra candidate | 已由 `quotient_support_algebra_bridge_summary` 关闭 append / permutation / reverse stability、duplicate zero-sum cancellation 与 two-route algebraic cancellation stability；general all-path enumeration、continuous action law 与 path integral 仍 pending |
| V7 | 经验接口 | 已由 `observable_ledger_bridge_summary` 关闭 two-route cancellation 进入 pending observable ledger 的最小边界；外部数据、误差模型、观测量与可测预言 theorem 仍 pending |
| V7b | 引入 finite action-to-phase law candidate | 已由 `action_phase_law_bridge_summary` 关闭 action index `0/1` 到 `1/-1` 的 quotient-support cancellation 与 pending ledger registration；continuous action law、path integral 与数据校准仍 pending |
| V8 | 当前统一摘要 theorem | 已由 `stepwise_unification_candidate_summary` 合取当前已关闭结构，并用 `PendingBeyondS5r` 明确未闭合边界 |
| V9 | 引入 finite probability normalization candidate | 已由 `finite_probability_normalization_bridge_summary` 关闭 concrete/grid finite row sum-one boundary；Born rule derivation、amplitude/Born normalized support、unitary/CPTP 与 empirical closure 仍 pending |
| V10 | 引入 normalized finite mass probability law | 已由 `normalized_mass_bridge_summary` 关闭 concrete/grid 非终端行逐项 `normalizedMass` sum-one；下一步进入 conditional Born weights |
| V11 | 引入 conditional Born-weight normalization law | 已由 `born_weight_normalization_bridge_summary` 关闭 normalized amplitude support 条件下的 candidateWeight 非负与 sum-one；下一步进入 `born_distribution_boundary` |

## 失败记录模板

失败不能删除，应写入探索计划或本文：

```text
日期：
目标：
命令 / theorem：
失败类型：Lean proof failure / build failure / infra failure / conceptual mismatch
失败原因：
保留结论：
下一步：
```

## 当前命令记录

已执行并通过：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
lake build SSBX.Foundation.Modern.QuantumRelativityWenBoundary
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
lake build SSBX
git diff --check --
```

备注：`lake build SSBX` 仍会输出既有 Wen 模块的 unused simp args linter 警告；本轮新增 Markov / WenBoundary / ConcreteBridge / OperatorCellGrid / FiniteProbabilityBridge / PathCausalBridge / AmplitudeChannelBridge / InterferenceBridge / NonzeroPathAmplitudeBridge / TwoPathInterferenceBridge / DiscretePhaseBridge / DiscreteActionBridge / FinitePathSumBridge / FinitePathSumAlgebraBridge / EndpointIndexedPathFamilyBridge / EndpointSupportNormalizationBridge / TwoRouteEnumerationBridge / PathIdentityBridge / FiniteKeyQuotientBridge / PathQuotientBridge / CanonicalRepresentativeBridge / QuotientSupportBridge / QuotientSupportAlgebraBridge / ObservableLedgerBridge / ActionPhaseLawBridge / StepwiseUnificationBridge 模块无警告。
