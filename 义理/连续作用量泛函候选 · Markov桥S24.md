# 连续作用量泛函候选 · Markov桥S24

**前置**：[作用量相位律候选 · Markov桥S5r](作用量相位律候选%20·%20Markov桥S5r.md) · [有限相位演化候选 · Markov桥S23](有限相位演化候选%20·%20Markov桥S23.md) · [作用相位到测量权重链 · Markov桥S22](作用相位到测量权重链%20·%20Markov桥S22.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**后续**：[路径空间作用量泛函候选 · Markov桥S25](路径空间作用量泛函候选%20·%20Markov桥S25.md) 已把本页的 continuous action-coordinate samples 接到 finite visible-key quotient path space。

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| continuous action functional | `Foundation/Modern/QuantumRelativityContinuousActionFunctionalBridge.lean` | `ContinuousActionFunctionalCandidate`、`displayedContinuousActionFunctional` | `machineChecked` |
| continuity | `Foundation/Modern/QuantumRelativityContinuousActionFunctionalBridge.lean` | `displayed_continuous_action_functional_continuous` | `machineChecked` |
| branch sampling | `Foundation/Modern/QuantumRelativityContinuousActionFunctionalBridge.lean` | `branchContinuousActionValue`、`branch_continuous_action_value_matches_index` | `machineChecked` |
| sampled amplitude | `Foundation/Modern/QuantumRelativityContinuousActionFunctionalBridge.lean` | `continuous_action_sampled_amplitude_eq_branch_amplitude` | `machineChecked` |
| phase evolution handoff | `Foundation/Modern/QuantumRelativityContinuousActionFunctionalBridge.lean` | `continuous_action_phase_evolve_eq_finite_phase_evolve`、`continuous_action_phase_evolution_reaches_action_branch_qubits` | `machineChecked` |
| Born preservation | `Foundation/Modern/QuantumRelativityContinuousActionFunctionalBridge.lean` | `continuous_action_phase_evolve_bornProb0_preserved`、`continuous_action_phase_evolve_bornProb1_preserved`、`continuous_action_phase_evolve_measurement_weights_normalized` | `machineChecked` |
| S24 summary | `Foundation/Modern/QuantumRelativityContinuousActionFunctionalBridge.lean` | `continuous_action_functional_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S24 关闭的是一个窄的 displayed continuous action functional：

```text
displayed real action coordinate t
-> continuous action functional S(t) = t
-> branch samples S(0) = 0, S(1) = 1
-> existing action indices 0 / 1
-> sampled phase amplitudes 1 / -1
-> S23 finite phase evolution
-> Born weights preserved
```

公开摘要为：

```lean
theorem continuous_action_functional_bridge_summary :
    ContinuousActionFunctionalClosed
    ∧ FinitePhaseEvolutionClosed
    ∧ ActionToBornMeasurementChainClosed
    ∧ ComputationalBasisBornMeasurementClosed
    ∧ (∀ b : PendingBeyondS24, ClosedByStepwiseS24 b = false)
    ∧ WenConstructiveCoverage
```

---

## 〇一 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| displayed continuous action functional | `displayedContinuousActionFunctional` | 当前层给出 `S(t)=t` 的实值 action-coordinate functional |
| continuity | `displayed_continuous_action_functional_continuous` | `S` 在实数拓扑下连续 |
| branch sampling | `upper_continuous_action_value`、`lower_continuous_action_value` | upper/lower branch 采样值为 `0/1` |
| finite index recovery | `branch_continuous_action_value_matches_index` | 连续 action sample 回到 S22 的 finite action index |
| sampled phase amplitude | `continuous_action_sampled_amplitude_eq_branch_amplitude` | sampled action index 推出的 amplitude 等于 branch amplitude |
| S23 handoff | `continuous_action_phase_evolve_eq_finite_phase_evolve` | continuous-action-induced evolution 与 S23 finite phase evolution 一致 |
| Born-weight preservation | `continuous_action_phase_evolve_measurement_weights_normalized` | normalized input 经 continuous-action sample 后仍接入 normalized measurement-weight boundary |

未纳入本轮：

| 项 | 原因 |
|---|---|
| finite quotient path-space action functional | 已由 S25 承接；本页只处理 displayed real action coordinate |
| smooth or infinite-dimensional path-space action functional | 当前没有 path manifold、variation 或 measure structure |
| Euler-Lagrange equations | 没有变分、极值、边界条件或 stationarity theorem |
| Hamiltonian generator | 没有 Legendre transform、self-adjoint generator 或动力学生成律 |
| continuous-time unitary group | 没有 `U(t+s)=U(t)U(s)`、强连续性或 Stone theorem |
| general Schrödinger dynamics | 没有微分方程或一般 Hilbert 空间动力学 |
| general path integral | 没有路径空间 measure、积分或极限 |
| general Hilbert measurement / PVM / POVM | 仍沿用 one-qubit computational basis |
| decoherence / empirical closure | 没有环境模型、trace-out、数据校准或可测预言 theorem |

本轮闭合范围：**displayed continuous action-coordinate functional and its two branch samples**。

---

## 一 · 为什么这一步比 S23 更强

S23 证明的是：

```text
branch action amplitude
-> finite phase evolution
-> Born weights preserved
```

S24 补上前一段来源：

```text
ContinuousActionFunctionalCandidate
-> S(t)=t is continuous
-> S(0)=0, S(1)=1
-> action index 0/1
-> amplitude 1/-1
```

因此 S24 不是只说“有限相位可演化”，而是把这个有限相位接到一个连续 action-coordinate functional 的两个采样点。

---

## 二 · 边界读法

这里的“连续作用量泛函”必须按窄义读：

```text
displayed real coordinate t
-> continuous real-valued action S(t)
-> two sampled branch values
```

它不是完整物理作用量原理。完整物理级还需要：

```text
path-space action functional
variational principle
Euler-Lagrange equations
Hamiltonian / unitary dynamics
general path integral
data-bearing observable predictions
```

---

## 三 · 失败记录

S24 第一次 build：

```text
命令：lake build SSBX.Foundation.Modern.QuantumRelativityContinuousActionFunctionalBridge
失败点：branch_continuous_action_value_matches_index
原因：`rfl` 不会自动把 `Nat -> ℝ` coercion 与 displayed functional 展开成同一项
修正：改用 `norm_num [branchContinuousActionValue, branchActionTime, displayedContinuousActionFunctional, ActionMeasurementBranch.actionIndex]`
结果：目标模块 build 通过
```

S24 试探阶段还发现：

```text
`ℝ` 上的 action functional 定义需放入 `noncomputable section`
```

该问题是 Lean 可计算性标记，不是 theorem obstruction。

---

## 四 · Validation Command

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityContinuousActionFunctionalBridge
```
