# 作用相位到测量权重链 · Markov桥S22

**前置**：[作用量相位律候选 · Markov桥S5r](作用量相位律候选%20·%20Markov桥S5r.md) · [Born rule推导候选 · Markov桥S18](Born%20rule推导候选%20·%20Markov桥S18.md) · [概率幅到测量权重 · Markov桥S21](概率幅到测量权重%20·%20Markov桥S21.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| action branch | `Foundation/Modern/QuantumRelativityActionAmplitudeMeasurementBridge.lean` | `ActionMeasurementBranch` | `machineChecked` |
| action amplitude | `Foundation/Modern/QuantumRelativityActionAmplitudeMeasurementBridge.lean` | `ActionMeasurementBranch.amplitude`、`action_branch_upper_qubit_amplitude0`、`action_branch_lower_qubit_amplitude1` | `machineChecked` |
| normalized qubit | `Foundation/Modern/QuantumRelativityActionAmplitudeMeasurementBridge.lean` | `action_branch_qubit_normalized` | `machineChecked` |
| Born weights | `Foundation/Modern/QuantumRelativityActionAmplitudeMeasurementBridge.lean` | `action_branch_born_measurement_weights` | `machineChecked` |
| measurement-event weights | `Foundation/Modern/QuantumRelativityActionAmplitudeMeasurementBridge.lean` | `action_branch_outcome_weights_normalized` | `machineChecked` |
| two-route alignment | `Foundation/Modern/QuantumRelativityActionAmplitudeMeasurementBridge.lean` | `two_route_action_indices_match_measurement_branches` | `machineChecked` |
| S22 summary | `Foundation/Modern/QuantumRelativityActionAmplitudeMeasurementBridge.lean` | `action_amplitude_measurement_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S22 的主张是把三个已关闭接口串成一条更窄的推出链：

```text
finite action branch
-> action index 0 / 1
-> induced phase amplitude 1 / -1
-> one-qubit computational-basis state
-> Born measurement weights
-> two-outcome measurement-event weights sum to 1
```

公开摘要为：

```lean
theorem action_amplitude_measurement_bridge_summary :
    TwoRouteActionPhaseLawBoundaryComplete
    ∧ ActionToBornMeasurementChainClosed
    ∧ ComputationalBasisBornMeasurementClosed
    ∧ (∀ b : PendingBeyondS22, ClosedByStepwiseS22 b = false)
    ∧ WenConstructiveCoverage
```

---

## 〇一 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| action branch | `ActionMeasurementBranch.upper/lower` | 当前链条只展示两条有限 branch |
| action -> amplitude | `ActionMeasurementBranch.upper_amplitude`、`ActionMeasurementBranch.lower_amplitude` | action index `0/1` 分别给出 amplitude `1/-1` |
| amplitude -> qubit | `actionBranchQubit` | upper 放入 `|0⟩`，lower 放入带 `-1` phase 的 `|1⟩` |
| qubit normalization | `action_branch_qubit_normalized` | 两个 action-induced qubit 都满足 `computationalBasisNormalized` |
| Born weights | `action_branch_born_measurement_weights` | 复用 S21 得到二值 measurement weights 非负且归一 |
| measurement-event distribution | `action_branch_outcome_weights_normalized` | `zero/one` 两个 outcome weights 非负且和为 `1` |
| two-route 接回 | `two_route_action_indices_match_measurement_branches` | S5r two-route action indices 与 S22 upper/lower branches 对齐 |

未纳入本轮：

| 项 | 原因 |
|---|---|
| continuous action functional | 仍只有 finite action index `0/1` |
| Hamiltonian dynamics / unitary time evolution | 没有连续时间演化算子或 Schrödinger 方程 |
| general path integral | 没有一般 all-path enumeration 或极限求和 |
| general Hilbert measurement | S21/S22 仍限定 one-qubit computational basis |
| PVM / POVM | 没有谱理论、投影族或 positive operator-valued measure 结构 |
| decoherence / empirical closure | 没有环境模型、trace-out、数据校准或实验判准 |

本轮闭合范围：**finite action branch 到 one-qubit computational-basis measurement weights 的 typed chain**。

---

## 一 · 为什么这一步比 S21 更强

S21 证明的是：

```text
normalized qubit
-> bornProb0 >= 0
-> bornProb1 >= 0
-> bornProb0 + bornProb1 = 1
```

S22 额外补上前一段来源：

```text
ActionMeasurementBranch.upper -> action index 0 -> amplitude 1 -> ket0
ActionMeasurementBranch.lower -> action index 1 -> amplitude -1 -> negKet1
```

因此 S22 不是单独再证明 Born rule，而是把 S5r 的 action/phase branch 和 S21 的 measurement weights 接成一个可检查链。

---

## 二 · 边界读法

这里的“amplitude dynamics”只按 finite typed skeleton 读：

```text
finite action branch
-> displayed amplitude
-> displayed qubit state
```

它不是物理 Hamiltonian dynamics。要走到物理级，还需要新增：

```text
Hamiltonian / action functional
-> unitary or CPTP evolution
-> general measurement semantics
-> data-bearing observable predictions
```

---

## 三 · 失败记录

S22 第一次 build：

```text
命令：lake build SSBX.Foundation.Modern.QuantumRelativityActionAmplitudeMeasurementBridge
失败点 1：未显式 open `QuantumRelativityDiscretePhaseBridge`，导致 `DiscretePhase` namespace 不一致
失败点 2：未显式 open `QuantumRelativityPathQuotientBridge` / `QuantumRelativityTwoPathInterferenceBridge`，导致 `twoStepPathQuotientClass` 与 `twoRouteUpperPath` 无法解析到既有定义
修正：补齐 open namespace，并把 action branch amplitude proof 改为复用既有 `upper_amplitude` / `lower_amplitude`
结果：目标模块 build 通过
```

---

## 四 · Validation Command

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityActionAmplitudeMeasurementBridge
```
