# 路径空间作用量泛函候选 · Markov桥S25

**前置**：[作用量相位律候选 · Markov桥S5r](作用量相位律候选%20·%20Markov桥S5r.md) · [有限相位演化候选 · Markov桥S23](有限相位演化候选%20·%20Markov桥S23.md) · [连续作用量泛函候选 · Markov桥S24](连续作用量泛函候选%20·%20Markov桥S24.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| finite path-space action functional | `Foundation/Modern/QuantumRelativityPathSpaceActionFunctionalBridge.lean` | `FinitePathSpaceActionFunctionalCandidate`、`twoRoutePathSpaceActionFunctional` | `machineChecked` |
| path action values | `Foundation/Modern/QuantumRelativityPathSpaceActionFunctionalBridge.lean` | `two_route_upper_path_space_action_value`、`two_route_lower_path_space_action_value` | `machineChecked` |
| action-index compatibility | `Foundation/Modern/QuantumRelativityPathSpaceActionFunctionalBridge.lean` | `two_route_path_space_action_index_matches_action_phase_law` | `machineChecked` |
| S24 sampling compatibility | `Foundation/Modern/QuantumRelativityPathSpaceActionFunctionalBridge.lean` | `branch_path_space_action_value_eq_continuous_action_value` | `machineChecked` |
| induced amplitudes | `Foundation/Modern/QuantumRelativityPathSpaceActionFunctionalBridge.lean` | `path_space_action_sampled_amplitude_eq_action_phase_amplitude`、`quotientSupportPathSpaceActionAmplitudeSum_eq_action_phase_sum` | `machineChecked` |
| quotient-support cancellation | `Foundation/Modern/QuantumRelativityPathSpaceActionFunctionalBridge.lean` | `two_route_path_space_action_support_amplitude_cancels`、`two_route_path_space_action_support_born_weight_zero` | `machineChecked` |
| S25 summary | `Foundation/Modern/QuantumRelativityPathSpaceActionFunctionalBridge.lean` | `path_space_action_functional_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S25 关闭的是一个有限路径空间上的作用量泛函候选：

```text
two-route visible-key quotient path space
-> finite path-space action functional S([path])
-> upper path action value 0
-> lower path action value 1
-> S5r finite action-index law
-> S24 continuous action-coordinate samples
-> quotient-support amplitude sum 1 + (-1) = 0
-> Born-shaped zero boundary
```

公开摘要为：

```lean
theorem path_space_action_functional_bridge_summary :
    FinitePathSpaceActionFunctionalClosed
    ∧ ContinuousActionFunctionalClosed
    ∧ TwoRouteActionPhaseLawBoundaryComplete
    ∧ FinitePhaseEvolutionClosed
    ∧ ActionToBornMeasurementChainClosed
    ∧ ComputationalBasisBornMeasurementClosed
    ∧ (∀ b : PendingBeyondS25, ClosedByStepwiseS25 b = false)
    ∧ WenConstructiveCoverage
```

---

## 〇一 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| finite path-space action functional | `twoRoutePathSpaceActionFunctional` | 在 two-route quotient path classes 上给出实值作用量 |
| upper/lower action values | `two_route_upper_path_space_action_value`、`two_route_lower_path_space_action_value` | upper path 取 `0`，lower path 取 `1` |
| action-index compatibility | `two_route_path_space_action_index_matches_action_phase_law` | path-space action index 与 S5r finite action-to-phase law 一致 |
| continuous sample compatibility | `branch_path_space_action_value_eq_continuous_action_value` | branch 读法与 S24 的 `S(t)=t` 采样值一致 |
| induced amplitudes | `path_space_action_sampled_amplitude_eq_action_phase_amplitude` | path-space action 推出的 amplitude 与 S5r action-phase amplitude 一致 |
| quotient support cancellation | `two_route_path_space_action_support_amplitude_cancels` | two-route quotient support 上的 action-induced amplitude sum 为 `0` |
| Born-shaped zero boundary | `two_route_path_space_action_support_born_weight_zero` | 相消后的 `ampProb` candidate weight 为 `0` |

未纳入本轮：

| 项 | 原因 |
|---|---|
| smooth or infinite-dimensional path-space action functional | 当前只处理 finite visible-key quotient path space |
| variational principle | 没有 stationarity、variation 或 boundary-condition theorem |
| Euler-Lagrange equations | 没有从作用量极值得到运动方程 |
| Hamiltonian generator | 没有 Legendre transform、self-adjoint generator 或动力学生成律 |
| continuous-time unitary group | 没有 `U(t+s)=U(t)U(s)`、强连续性或 Stone theorem |
| general Schrödinger dynamics | 没有微分方程或一般 Hilbert 空间动力学 |
| general path integral | 没有路径空间 measure、积分或极限 |
| general Hilbert measurement / PVM / POVM | 仍沿用 one-qubit computational basis 的后续链 |
| decoherence / empirical closure | 没有环境模型、trace-out、数据校准或可测预言 theorem |

本轮闭合范围：**finite quotient path space 上的 action functional candidate**。

---

## 一 · 为什么这一步比 S24 更强

S24 给出的是：

```text
displayed real action coordinate t
-> S(t)=t
-> branch samples 0 / 1
```

S25 把 action 的定义域从 branch coordinate 推到 finite quotient path space：

```text
visible-key quotient path class [path]
-> S([path]) = 0 or 1
-> same action index as S5r
-> same sampled amplitude as S24/S5r
```

因此 S25 不只是给 `0/1` 两个点命名，而是把这两个 action values 绑定到 two-route quotient path classes。

---

## 二 · 边界读法

这里的“路径空间作用量泛函”必须按窄义读：

```text
finite quotient path support
-> real-valued action functional
-> action index compatibility
-> finite amplitude sum
```

它不是完整物理作用量原理。完整物理级还需要：

```text
smooth / infinite-dimensional path space
variational principle
Euler-Lagrange equations
Hamiltonian / unitary dynamics
general path integral
data-bearing observable predictions
```

---

## 三 · 失败记录

S25 第一次 build：

```text
命令：lake build SSBX.Foundation.Modern.QuantumRelativityPathSpaceActionFunctionalBridge
失败点：two_route_lower_path_space_action_value、branch_path_space_action_value_eq_continuous_action_value
原因：未 open `QuantumRelativityPathIdentityBridge`，导致 `twoStepPathKey` 无法解析和展开，lower branch 的 action value 不能化简到 `1`
修正：补 `open SSBX.Foundation.Modern.QuantumRelativityPathIdentityBridge`
结果：目标模块 build 通过
```

本轮设计时保留的边界是：不把 finite quotient support 写成 smooth path space，也不把 `S([path]) = 0/1` 写成物理作用量原理。若后续要推进，需要先新增 path manifold、variation 或 Hamiltonian semantics。

Lean 层若出现构建失败，应记录在本文并保留失败原因；当前目标模块的验证命令为：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityPathSpaceActionFunctionalBridge
```
