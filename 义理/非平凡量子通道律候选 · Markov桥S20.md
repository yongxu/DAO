# 非平凡量子通道律候选 · Markov桥S20

**前置**：[sum-over-middle通道组合候选 · Markov桥S15](sum-over-middle通道组合候选%20·%20Markov桥S15.md) · [sum-over-middle Born边界候选 · Markov桥S16](sum-over-middle%20Born边界候选%20·%20Markov桥S16.md) · [unitary-CPTP账本边界 · Markov桥S17](unitary-CPTP账本边界%20·%20Markov桥S17.md) · [Born rule推导候选 · Markov桥S18](Born%20rule推导候选%20·%20Markov桥S18.md) · [路径权重乘法候选 · Markov桥S19](路径权重乘法候选%20·%20Markov桥S19.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| nonzero channel witness | `Foundation/Modern/QuantumRelativityNontrivialChannelLawBridge.lean` | `NontrivialChannelAmplitudeWitness` | `machineChecked` |
| finite channel law | `Foundation/Modern/QuantumRelativityNontrivialChannelLawBridge.lean` | `nontrivial_channel_amplitude_law` | `machineChecked` |
| concrete nonzero edges | `Foundation/Modern/QuantumRelativityNontrivialChannelLawBridge.lean` | `concretePreparedEvolvedChannelWitness`、`concreteEvolvedMeasuredChannelWitness` | `machineChecked` |
| concrete edge laws | `Foundation/Modern/QuantumRelativityNontrivialChannelLawBridge.lean` | `concrete_prepared_evolved_nontrivial_channel_law`、`concrete_evolved_measured_nontrivial_channel_law` | `machineChecked` |
| composed channel law | `Foundation/Modern/QuantumRelativityNontrivialChannelLawBridge.lean` | `concrete_nontrivial_sum_over_middle_channel_law` | `machineChecked` |
| S20 summary | `Foundation/Modern/QuantumRelativityNontrivialChannelLawBridge.lean` | `nontrivial_quantum_channel_law_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S20 的主张：

```text
nonzero channel amplitude
+ support-respecting QuantumChannelSkeleton
= process step
  + carried classical support
  + Born-shaped ampProb boundary
```

在 concrete witness 上：

```text
prepared -> evolved amplitude = 1
evolved -> measured amplitude = 1
sum over middle evolved: prepared -> measured amplitude = 1
composed endpoint amplitude support = [1]
```

公开摘要为：

```lean
theorem nontrivial_quantum_channel_law_bridge_summary :
    NontrivialQuantumChannelLawClosed
    ∧ BornDistributionBoundaryClosed
    ∧ SumOverMiddleBornDistributionBoundaryClosed
    ∧ PathWeightMultiplicationBoundaryClosed
    ∧ (∀ b : PendingBeyondS20, ClosedByStepwiseS20 b = false)
    ∧ WenConstructiveCoverage
```

---

## 〇一 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| 非零 channel amplitude witness | `NontrivialChannelAmplitudeWitness` | channel 中显式展示一条非零振幅边 |
| support law | `nontrivial_channel_amplitude_law` | 非零振幅推出 `P.step` 与 carried classical support |
| Born-shaped boundary | `NontrivialChannelAmplitudeWitness.born_weight_boundary` | displayed amplitude 的 candidateWeight 等于 `ampProb` |
| concrete nonzero one-step edges | `concretePreparedEvolvedChannelWitness`、`concreteEvolvedMeasuredChannelWitness` | concrete channel 在两条一步边上振幅均为 `1` |
| concrete composed amplitude | `concrete_nontrivial_sum_over_middle_channel_law` | 经 `evolved` 求和得到 `prepared -> measured` amplitude `1` 与 two-step witness |
| composed Born input | `concrete_sumOverMiddle_endpoint_amplitude_support`、`concrete_composed_endpoint_amplitude_support_normalized` | composed endpoint support 为 `[1]`，可接回 S16 finite Born boundary |
| 公开摘要 | `nontrivial_quantum_channel_law_bridge_summary` | 合取 S20 law、S12/S16 Born boundary、S19 path-weight law、pending ledger 与 Wen coverage |

未纳入本轮：

| 轴 | 状态 | 说明 |
|---|---|---|
| Hilbert-space unitary law | required but not closed | S20 不引入 Hilbert carrier 或 inner product preservation theorem |
| CPTP / Kraus / density matrix | required but not closed | 不证明 complete positivity、trace preservation、Kraus representation 或 density-matrix semantics |
| dynamics / measurement semantics | required but not closed | 不证明 amplitude dynamics、measurement postulate、decoherence |
| path integral / empirical closure | required but not closed | 不证明一般路径积分、metric recovery、数据校准或经验闭合 |

本轮闭合范围：**finite support-respecting quantum-channel skeleton 的非平凡非零通道律**。S21 后续把 Born rule 的 one-qubit computational-basis 版本接到显式 measurement weights。

---

## 一 · 为什么这一步比 S13-S17 更强

S13 的 `channelCompose` 是 pointwise composition；S14 关闭 associativity 并记录 diagonal identity obstruction；S15/S16 给出 sum-over-middle 与 composed Born boundary；S17 把 physical unitary/CPTP 所需结构登记为 ledger。

S20 补上的不是另一个 ledger，而是一个正向 law：

```lean
theorem nontrivial_channel_amplitude_law
    (w : NontrivialChannelAmplitudeWitness C) :
    P.step w.source w.target
      ∧ C.classicalBoundary.support w.source w.target
      ∧ (bornRuleCandidate w.amplitude).candidateWeight = ampProb w.amplitude
```

也就是说，只要 channel skeleton 中有一条非零 amplitude，它就不再是零占位；它必须落在过程一步转移上，并且被 carried classical support 支撑。

---

## 二 · 边界读法

“非平凡量子通道律”在 S20 中只按当前 finite skeleton 读：

```text
nontrivial = 有非零 channel amplitude witness
channel law = 非零 amplitude -> step + classical support + Born-shaped boundary
composition = concrete sum-over-middle amplitude = 1
Born boundary = composed support [1] 已 normalized，可接入 S16
```

它不是 physical quantum channel law 的完整闭合。Hilbert / unitary / CPTP / Kraus / density-matrix 仍保留为后续结构。

---

## 三 · Validation Command

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityNontrivialChannelLawBridge
```
