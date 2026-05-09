# 概率幅到测量权重 · Markov桥S21

**前置**：[Born rule推导候选 · Markov桥S18](Born%20rule推导候选%20·%20Markov桥S18.md) · [非平凡量子通道律候选 · Markov桥S20](非平凡量子通道律候选%20·%20Markov桥S20.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| measurement weights | `Foundation/Modern/QuantumRelativityBornMeasurementBridge.lean` | `ComputationalBasisMeasurementWeights` | `machineChecked` |
| amplitude projection | `Foundation/Modern/QuantumRelativityBornMeasurementBridge.lean` | `computational_basis_weight0_eq_ampProb`、`computational_basis_weight1_eq_ampProb` | `machineChecked` |
| normalized weights | `Foundation/Modern/QuantumRelativityBornMeasurementBridge.lean` | `born_rule_gives_normalized_measurement_weights` | `machineChecked` |
| packaged boundary | `Foundation/Modern/QuantumRelativityBornMeasurementBridge.lean` | `computational_basis_measurement_weights_normalized` | `machineChecked` |
| S21 summary | `Foundation/Modern/QuantumRelativityBornMeasurementBridge.lean` | `born_measurement_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S21 只接入 one-qubit computational-basis 版本：

```lean
theorem born_rule_gives_normalized_measurement_weights
    (ψ : Qubit) (hψ : computationalBasisNormalized ψ) :
    0 ≤ bornProb0 ψ ∧ 0 ≤ bornProb1 ψ
      ∧ bornProb0 ψ + bornProb1 ψ = 1
```

读法：

| 条件 | 含义 |
|---|---|
| `0 ≤ bornProb0 ψ` | `|0⟩` 分支的测量权重非负 |
| `0 ≤ bornProb1 ψ` | `|1⟩` 分支的测量权重非负 |
| `bornProb0 ψ + bornProb1 ψ = 1` | 归一化 qubit 的二值测量权重和为一 |

公开摘要为：

```lean
theorem born_measurement_bridge_summary :
    ComputationalBasisBornMeasurementClosed
    ∧ MarkovAmplitudeBornRuleDerivationClosed
    ∧ NontrivialQuantumChannelLawClosed
    ∧ (∀ b : PendingBeyondS21, ClosedByStepwiseS21 b = false)
    ∧ WenConstructiveCoverage
```

---

## 〇一 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| 概率幅到权重 | `computational_basis_weight0_eq_ampProb`、`computational_basis_weight1_eq_ampProb` | 两个 basis 分支的测量权重分别是 `ampProb (ψ 0)` 与 `ampProb (ψ 1)` |
| one-qubit Born rule | `born_rule_gives_normalized_measurement_weights` | normalized qubit 给出二值非负归一测量权重 |
| record 接口 | `computational_basis_measurement_weights_normalized` | 把 theorem 装入 `ComputationalBasisMeasurementWeights` |
| 与前层合取 | `born_measurement_bridge_summary` | 合取 S18 Markov/amplitude Born derivation、S20 nontrivial channel law 与 S21 measurement-weight boundary |

未纳入本轮：

| 项 | 原因 |
|---|---|
| 一般 Hilbert 空间测量 | 需要更大的 Hilbert / operator / inner-product 语义 |
| POVM / projection-valued measures | 需要算子谱、投影族或 positive operator-valued measure 结构 |
| 退相干 | 需要动力学、环境模型与 trace-out 语义 |
| 测量问题 | 不是当前 typed skeleton 可直接解决的问题 |
| 经验闭合 | 需要数据校准、观测记录与误差模型 |

本轮闭合范围：**computational basis / one qubit / normalized state 下，从概率幅 `ampProb` 到二值测量权重的非负归一边界**。

---

## 一 · 为什么这比 S18 更靠近测量

S18 证明的是：

```text
Markov row probability
+ amplitude compatibility
-> normalized amplitude support
-> finite Born distribution boundary
```

S21 处理的对象更窄，但更直接面向测量读法：

```text
Qubit ψ : Fin 2 -> ℂ
+ computationalBasisNormalized ψ
-> bornProb0 ψ >= 0
-> bornProb1 ψ >= 0
-> bornProb0 ψ + bornProb1 ψ = 1
```

也就是说，S21 不再只说“finite support 可包装成 Born-shaped distribution”，而是在一比特 computational basis 上给出显式的两个测量权重。

---

## 二 · 边界读法

这里的 Born rule 是窄版本：

```text
computational basis
one qubit
normalized state
two displayed weights
```

它不等于完整量子测量理论。完整理论还需要 Hilbert-space carrier、observable / projection / POVM、测量公设、退相干或实验闭合。

---

## 三 · Validation Command

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityBornMeasurementBridge
```
