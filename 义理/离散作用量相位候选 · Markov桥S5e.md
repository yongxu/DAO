# 离散作用量相位候选 · Markov桥S5e

**前置**：[Markov因果桥 · 大统一最小验证构造](Markov因果桥%20·%20大统一最小验证构造.md) · [有限路径族求和候选 · Markov桥S5f](有限路径族求和候选%20·%20Markov桥S5f.md) · [离散相位标记候选 · Markov桥S5d](离散相位标记候选%20·%20Markov桥S5d.md) · [双路径相消候选 · Markov桥S5c](双路径相消候选%20·%20Markov桥S5c.md) · [非零路径振幅候选 · Markov桥S5b](非零路径振幅候选%20·%20Markov桥S5b.md) · [干涉与测量律候选 · Markov桥S5](干涉与测量律候选%20·%20Markov桥S5.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| 离散相位合成 | `Foundation/Modern/QuantumRelativityDiscreteActionBridge.lean` | `discretePhaseAdd`、`discretePhaseRelative` | `machineChecked` typed skeleton |
| edge-action phase candidate | `Foundation/Modern/QuantumRelativityDiscreteActionBridge.lean` | `TwoStepEdgePhaseCandidate`、`HasTwoStepEdgePhaseCandidate` | `machineChecked` typed skeleton |
| edge phase 到 path phase | `Foundation/Modern/QuantumRelativityDiscreteActionBridge.lean` | `TwoStepEdgePhaseCandidate.pathPhase` | `machineChecked` |
| S5d 接口导出 | `Foundation/Modern/QuantumRelativityDiscreteActionBridge.lean` | `edgePhaseInducedTwoStepPhaseCandidate`、`edgePhaseInducedTwoStepAmplitudeCandidate` | `machineChecked` typed skeleton |
| two-route edge phases | `Foundation/Modern/QuantumRelativityDiscreteActionBridge.lean` | `twoRouteEdgePhase`、`twoRouteDiscreteActionCandidate` | `machineChecked` |
| accumulated phase | `Foundation/Modern/QuantumRelativityDiscreteActionBridge.lean` | `two_route_upper_accumulated_phase`、`two_route_lower_accumulated_phase` | `machineChecked` |
| relative phase | `Foundation/Modern/QuantumRelativityDiscreteActionBridge.lean` | `two_route_edge_action_phase_difference` | `machineChecked` |
| edge-action-induced cancellation | `Foundation/Modern/QuantumRelativityDiscreteActionBridge.lean` | `two_route_edge_action_pair_amplitude_cancels`、`two_route_edge_action_cancelled_born_weight_zero` | `machineChecked` |
| S5e 公开摘要 | `Foundation/Modern/QuantumRelativityDiscreteActionBridge.lean` | `discrete_action_phase_bridge_summary` | `machineChecked` |
| S5f 后续闭合 | `Foundation/Modern/QuantumRelativityFinitePathSumBridge.lean` | `finite_path_sum_bridge_summary` 把 two-route sum 推到 finite path-family sum | `machineChecked` |

---

## 〇 · Claim Block

S5e 的主张：

```text
S5d discrete phase labels
+ finite phase composition zero/pi
+ edge-level phase increments
+ two-step path phase accumulation
+ upper path phase = zero
+ lower path phase = pi
+ relative phase = pi
= edge-action-induced two-path cancellation candidate
```

正面结论是：

```text
S5e 已把 S5d 的路径相位标签
推进为由两条边的 phase increments 累积得到的 path phase；
upper route 的 accumulated phase 为 zero，
lower route 的 accumulated phase 为 pi，
二者相对相位为 pi，
并继续导出 `1/-1` 候选振幅与 two-path finite cancellation。
```

公开摘要为：

```lean
theorem discrete_action_phase_bridge_summary :
    HasTwoStepEdgePhaseCandidate twoRouteProcess
    ∧ HasTwoStepPhaseCandidate twoRouteProcess
    ∧ HasTwoStepPathAmplitudeCandidate twoRouteProcess
    ∧ twoRouteDiscreteActionCandidate.pathPhase twoRouteUpperPath =
        DiscretePhase.zero
    ∧ twoRouteDiscreteActionCandidate.pathPhase twoRouteLowerPath =
        DiscretePhase.pi
    ∧ discretePhaseRelative
        (twoRouteDiscreteActionCandidate.pathPhase twoRouteUpperPath)
        (twoRouteDiscreteActionCandidate.pathPhase twoRouteLowerPath) =
          DiscretePhase.pi
    ∧ ...
    ∧ twoStepPairAmplitudeSum
        (edgePhaseInducedTwoStepAmplitudeCandidate
          twoRouteDiscreteActionCandidate)
        twoRouteUpperLowerPair = 0
    ∧ WenConstructiveCoverage
```

该 theorem 已通过 `lake build SSBX.Foundation.Modern.QuantumRelativityDiscreteActionBridge`。

---

## 〇一 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| phase composition | `discretePhaseAdd` | `zero/pi` 的有限合成表 |
| relative phase | `discretePhaseRelative` | 二值相位中的相对相位候选 |
| edge-action phase candidate | `TwoStepEdgePhaseCandidate` | 每条 supported edge 可携带 phase increment |
| path phase accumulation | `TwoStepEdgePhaseCandidate.pathPhase` | two-step path 的 phase 由两条 edge phase 合成 |
| S5d phase interface | `edgePhaseInducedTwoStepPhaseCandidate` | edge phase accumulation 可接回 S5d `TwoStepPhaseCandidate` |
| S5c amplitude interface | `edgePhaseInducedTwoStepAmplitudeCandidate` | accumulated phase 可接回 S5c amplitude candidate |
| upper route phase | `two_route_upper_accumulated_phase` | `zero + zero = zero` |
| lower route phase | `two_route_lower_accumulated_phase` | `zero + pi = pi` |
| relative phase | `two_route_edge_action_phase_difference` | lower 相对 upper 为 `pi` |
| induced amplitudes | `two_route_edge_action_upper_amplitude`、`two_route_edge_action_lower_amplitude` | accumulated phase 导出 `1/-1` |
| two-path cancellation | `two_route_edge_action_pair_amplitude_cancels` | edge-action-induced 两路径有限和为 `0` |
| Born-shaped zero | `two_route_edge_action_cancelled_born_weight_zero` | 相消后候选权重为 `0` |
| 公开摘要 | `discrete_action_phase_bridge_summary` | 合取 edge action、phase accumulation、relative phase、cancellation 与 Wen coverage |

后续结构：

| 轴 | 状态 | 说明 |
|---|---|---|
| continuous phase group | 后续结构 | 需要连续角度、`U(1)`、指数映射或等价接口 |
| action functional | 后续结构 | 需要从路径或场构造 action，并推出相位 |
| Hamiltonian / unitary evolution | 后续结构 | 需要时间演化算子与 law |
| finite path-family sum | S5f 已关闭 | 已由 `finite_path_sum_bridge_summary` 把 two-route pair 扩展为 finite same-endpoint path family sum |
| path integral | 后续结构 | 需要路径空间、测度、极限或 over-all-paths sum |
| Born rule derivation | 后续结构 | 仍只复用 `ampProb` boundary |
| empirical closure | 后续结构 | S5q 已补 pending observable ledger；仍需要数据判准与实验闭合 |

本轮闭合范围：**S5e 已在 Lean 中关闭“edge phase increments -> two-step path phase accumulation -> relative phase pi -> induced two-path cancellation”的候选接口；S5f 已在后续文件中把该 two-route sum 接到 finite path-family sum。**

---

## 一 · 为什么这一步比 S5d 更强

S5d 已证明：

```text
upper path -> phase zero -> amplitude 1
lower path -> phase pi   -> amplitude -1
```

S5e 把 phase label 再往前推一层：

```text
upper path:
  source -> upper  : zero
  upper  -> target : zero
  accumulated      : zero

lower path:
  source -> lower  : zero
  lower  -> target : pi
  accumulated      : pi
```

这使“相反相位”不再只是整条 path 的外部标签，而是由 edge-level increments 累积得到的 path-level label。

---

## 二 · 后续承接

S5e 后的直接增强 S5f 已关闭：

```text
two-path finite sum
-> finite path-family sum
-> endpoint amplitude as a finite sum over candidate paths
```

下一步应在 S5f 的有限族接口上处理 append / permutation / cancellation stability 等 path-sum algebra；连续 path integral 仍等有限族代数稳定后再进入。

---

## 三 · Validation Command

Lean 验证命令：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityDiscreteActionBridge
lake build SSBX
```

文档与格式检查：

```bash
python3 scripts/docs_next.py build --out docs-next/_generated --clean
python3 scripts/docs_next.py check --out docs-next/_generated --strict
git diff --check --
```
