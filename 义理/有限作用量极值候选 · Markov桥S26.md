# 有限作用量极值候选 · Markov桥S26

**前置**：[路径空间作用量泛函候选 · Markov桥S25](路径空间作用量泛函候选%20·%20Markov桥S25.md) · [连续作用量泛函候选 · Markov桥S24](连续作用量泛函候选%20·%20Markov桥S24.md) · [作用量相位律候选 · Markov桥S5r](作用量相位律候选%20·%20Markov桥S5r.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**后续**：[有限因果局部性候选 · Markov桥S27](有限因果局部性候选%20·%20Markov桥S27.md) 已把 S3 的 one-step causal boundary 推到 finite localFuture list，并接回本页的 S26 summary。

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| finite action gap | `Foundation/Modern/QuantumRelativityFiniteActionExtremumBridge.lean` | `finiteActionGap` | `machineChecked` |
| finite support minimum | `Foundation/Modern/QuantumRelativityFiniteActionExtremumBridge.lean` | `FiniteActionMinimumOnSupport` | `machineChecked` |
| two-route support membership | `Foundation/Modern/QuantumRelativityFiniteActionExtremumBridge.lean` | `two_route_upper_in_action_extremum_support`、`two_route_lower_in_action_extremum_support` | `machineChecked` |
| action gap | `Foundation/Modern/QuantumRelativityFiniteActionExtremumBridge.lean` | `two_route_upper_to_lower_action_gap`、`two_route_lower_to_upper_action_gap` | `machineChecked` |
| finite minimum | `Foundation/Modern/QuantumRelativityFiniteActionExtremumBridge.lean` | `two_route_upper_is_finite_action_minimum`、`two_route_lower_not_finite_action_minimum` | `machineChecked` |
| S26 summary | `Foundation/Modern/QuantumRelativityFiniteActionExtremumBridge.lean` | `finite_action_extremum_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S26 关闭的是一个有限支撑上的作用量极值候选：

```text
two-route quotient support
-> finite path-space action functional from S25
-> upper action value 0
-> lower action value 1
-> lower-minus-upper action gap 1
-> upper is a finite action minimum on the displayed support
-> lower is not such a minimum
```

公开摘要为：

```lean
theorem finite_action_extremum_bridge_summary :
    TwoRouteFiniteActionExtremumClosed
    ∧ FinitePathSpaceActionFunctionalClosed
    ∧ ContinuousActionFunctionalClosed
    ∧ TwoRouteActionPhaseLawBoundaryComplete
    ∧ FinitePhaseEvolutionClosed
    ∧ ActionToBornMeasurementChainClosed
    ∧ ComputationalBasisBornMeasurementClosed
    ∧ (∀ b : PendingBeyondS26, ClosedByStepwiseS26 b = false)
    ∧ WenConstructiveCoverage
```

---

## 〇一 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| finite action gap | `finiteActionGap` | 在两个 quotient path classes 之间读取有限 action difference |
| displayed support membership | `two_route_upper_in_action_extremum_support`、`two_route_lower_in_action_extremum_support` | upper/lower 都在 two-route source/target quotient support 中 |
| lower-minus-upper gap | `two_route_upper_to_lower_action_gap` | 从 upper 到 lower 的 action gap 为 `1` |
| reverse gap | `two_route_lower_to_upper_action_gap` | 从 lower 到 upper 的 action gap 为 `-1` |
| action ordering | `two_route_lower_action_eq_upper_plus_one` | lower action 等于 upper action 加 `1` |
| finite minimum | `two_route_upper_is_finite_action_minimum` | upper 在 displayed finite support 上是 action minimum |
| non-minimum witness | `two_route_lower_not_finite_action_minimum` | lower 不是该 support 上的 action minimum |

未纳入本轮：

| 项 | 原因 |
|---|---|
| smooth or infinite-dimensional path-space action functional | 仍只处理 two-route finite quotient support |
| continuous variation space | 没有 tangent/variation/boundary-condition structure |
| stationary action principle | finite minimum 不等于连续变分 stationary theorem |
| Euler-Lagrange equations | 没有从极值推出运动方程 |
| Hamiltonian generator / continuous-time unitary group | 没有 Legendre transform、self-adjoint generator、Stone theorem 或 `U(t+s)=U(t)U(s)` |
| general Schrödinger dynamics | 没有一般 Hilbert 空间微分动力学 |
| general path integral | 没有路径空间 measure、积分或极限 |
| general Hilbert measurement / PVM / POVM | 仍沿用 one-qubit computational basis 的后续链 |
| decoherence / empirical closure | 没有环境模型、trace-out、数据校准或可测预言 theorem |

本轮闭合范围：**two-route finite quotient support 上的 action-gap 与 finite-minimum candidate**。

---

## 一 · 为什么这一步比 S25 更强

S25 证明的是：

```text
quotient path class
-> action value 0 / 1
-> action phase amplitude
-> quotient-support cancellation
```

S26 增加的是 order/extremum 读法：

```text
same quotient support
-> compare action values
-> lower - upper = 1
-> upper is finite minimum
-> lower is not finite minimum
```

因此 S26 不只是记录 action values，而是把这些 values 组织成可检查的有限极值边界。

---

## 二 · 边界读法

这里的“极值”必须按窄义读：

```text
finite list support
-> pointwise real-valued action
-> minimum over that finite list
```

它不是完整物理最小作用量原理。完整物理级还需要：

```text
smooth / infinite-dimensional path space
allowed variations and boundary conditions
stationary-action theorem
Euler-Lagrange equations
Hamiltonian / unitary dynamics
general path integral
data-bearing observable predictions
```

---

## 三 · 失败记录

S26 第一次 build：

```text
命令：lake build SSBX.Foundation.Modern.QuantumRelativityFiniteActionExtremumBridge
失败点：two_route_upper_is_finite_action_minimum 与文件末尾 namespace/section close
原因：一个 `rw [hq]` 已经把 reflexive order goal 关闭，后续 `exact le_rfl` 变成 no goals；同时 `noncomputable section` 需要先 `end` 再关闭 namespace
修正：删除多余 `exact le_rfl`，并在 namespace 结束前补 `end`
结果：目标模块 build 通过
```

本轮保留的理论边界是：不把 two-route finite minimum 写成 stationary action principle，也不把 action gap 写成 Hamiltonian dynamics。

Lean 层若出现构建失败，应记录在本文并保留失败原因；当前目标模块的验证命令为：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityFiniteActionExtremumBridge
```
