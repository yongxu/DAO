# 有限相位演化候选 · Markov桥S23

**前置**：[作用量相位律候选 · Markov桥S5r](作用量相位律候选%20·%20Markov桥S5r.md) · [作用相位到测量权重链 · Markov桥S22](作用相位到测量权重链%20·%20Markov桥S22.md) · [概率幅到测量权重 · Markov桥S21](概率幅到测量权重%20·%20Markov桥S21.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| finite phase evolution | `Foundation/Modern/QuantumRelativityFinitePhaseEvolutionBridge.lean` | `phaseEvolveBranch` | `machineChecked` |
| period-two law | `Foundation/Modern/QuantumRelativityFinitePhaseEvolutionBridge.lean` | `phase_evolve_upper_is_identity`、`phase_evolve_lower_period_two` | `machineChecked` |
| action-qubit generation | `Foundation/Modern/QuantumRelativityFinitePhaseEvolutionBridge.lean` | `phase_evolve_upper_ket0`、`phase_evolve_lower_ket1`、`phase_evolution_reaches_action_branch_qubits` | `machineChecked` |
| Born-weight preservation | `Foundation/Modern/QuantumRelativityFinitePhaseEvolutionBridge.lean` | `phase_evolve_branch_bornProb0_preserved`、`phase_evolve_branch_bornProb1_preserved` | `machineChecked` |
| measurement boundary | `Foundation/Modern/QuantumRelativityFinitePhaseEvolutionBridge.lean` | `phase_evolve_branch_measurement_weights_normalized` | `machineChecked` |
| S23 summary | `Foundation/Modern/QuantumRelativityFinitePhaseEvolutionBridge.lean` | `finite_phase_evolution_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S23 的主张是把 S22 的 displayed action amplitude 改成一个有限演化候选：

```text
finite action branch
-> phase amplitude 1 / -1
-> branch-indexed phase evolution on a qubit
-> S22 action-induced qubit
-> Born weights preserved
-> normalized measurement weights preserved
```

公开摘要为：

```lean
theorem finite_phase_evolution_bridge_summary :
    FinitePhaseEvolutionClosed
    ∧ ActionToBornMeasurementChainClosed
    ∧ ComputationalBasisBornMeasurementClosed
    ∧ (∀ b : PendingBeyondS23, ClosedByStepwiseS23 b = false)
    ∧ WenConstructiveCoverage
```

---

## 〇一 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| finite phase evolution | `phaseEvolveBranch` | branch action amplitude 作为全局相位作用在 one-qubit state 上 |
| upper identity | `phase_evolve_upper_is_identity` | upper branch 的相位演化是 identity |
| lower period two | `phase_evolve_lower_period_two` | lower branch 连续作用两次回到原 state |
| S22 qubit generation | `phase_evolve_upper_ket0`、`phase_evolve_lower_ket1` | `ket0 / ket1` 经有限相位演化得到 S22 的 `ket0 / negKet1` |
| Born-weight preservation | `phase_evolve_branch_bornProb0_preserved`、`phase_evolve_branch_bornProb1_preserved` | `1/-1` 有限相位不改变 computational-basis Born weights |
| measurement boundary | `phase_evolve_branch_measurement_weights_normalized` | 若输入 qubit 已归一，则演化后仍接入 S21 normalized measurement-weight interface |

未纳入本轮：

| 项 | 原因 |
|---|---|
| Hamiltonian generator | 这里只是 branch-indexed finite phase，不构造 self-adjoint Hamiltonian |
| continuous-time unitary group | 没有 `t ↦ U(t)`、群律、强连续性或微分方程 |
| Schrödinger dynamics | 没有 `i dψ/dt = Hψ` |
| general path integral | 没有一般路径空间、measure/integral 或极限 |
| general Hilbert measurement / PVM / POVM | 仍沿用 one-qubit computational basis |
| decoherence / empirical closure | 没有环境、trace-out、数据校准或可测预言 theorem |

本轮闭合范围：**finite period-two phase evolution candidate for one-qubit computational-basis states**。

---

## 一 · 为什么这一步比 S22 更强

S22 证明的是：

```text
finite action branch
-> displayed amplitude
-> displayed qubit
-> measurement-event weights
```

S23 额外补上一个 finite dynamics-shaped step：

```text
phaseEvolveBranch b ψ := amplitude(b) * ψ
```

因此 S23 不再只是把 amplitude 填进 qubit，而是证明这个 finite phase operation：

```text
reaches the S22 qubits
preserves Born weights
preserves normalized measurement-weight boundary
```

---

## 二 · 边界读法

这里的“演化”只在 typed skeleton 内读：

```text
branch-indexed period-two phase operation
on one-qubit computational-basis state
```

它不是完整物理动力学。完整物理级还需要：

```text
Hamiltonian or action functional
continuous unitary/CPTP evolution
general Hilbert measurement
data-bearing observable predictions
```

---

## 三 · 失败记录

S23 第一次 proof 试探：

```text
目标：phase_evolve_branch_normalization_preserved
失败点：`simp` 化简后留下目标 `bornProb0 ψ + bornProb1 ψ = 1`
原因：`hψ` 的形式是 `computationalBasisNormalized ψ`，需要按定义回读成 `bornTotal ψ = 1`
修正：使用 `simpa [computationalBasisNormalized, bornTotal, ...] using hψ`
结果：目标模块 build 通过
```

---

## 四 · Validation Command

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityFinitePhaseEvolutionBridge
```
