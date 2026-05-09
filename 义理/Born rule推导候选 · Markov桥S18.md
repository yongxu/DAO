# Born rule推导候选 · Markov桥S18

**前置**：[Born分布边界候选 · Markov桥S12](Born分布边界候选%20·%20Markov桥S12.md) · [unitary-CPTP账本边界 · Markov桥S17](unitary-CPTP账本边界%20·%20Markov桥S17.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| real Markov mass sum | `Foundation/Modern/QuantumRelativityBornRuleDerivationBridge.lean` | `realNormalizedMassSum`、`realNormalizedMassSum_eq_one` | `machineChecked` |
| compatibility interface | `Foundation/Modern/QuantumRelativityBornRuleDerivationBridge.lean` | `MarkovAmplitudeCompatibility` | `machineChecked` |
| support normalization theorem | `Foundation/Modern/QuantumRelativityBornRuleDerivationBridge.lean` | `markov_amplitude_support_normalized` | `machineChecked` |
| Born/Markov matching theorem | `Foundation/Modern/QuantumRelativityBornRuleDerivationBridge.lean` | `born_candidate_weights_match_markov_masses` | `machineChecked` |
| derivation theorem | `Foundation/Modern/QuantumRelativityBornRuleDerivationBridge.lean` | `markov_amplitude_born_rule_derivation` | `machineChecked` |
| concrete witness | `Foundation/Modern/QuantumRelativityBornRuleDerivationBridge.lean` | `concrete_prepared_born_rule_from_markov_amplitude_bridge` | `machineChecked` |
| S18 summary | `Foundation/Modern/QuantumRelativityBornRuleDerivationBridge.lean` | `born_rule_derivation_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S18 的主张：

```text
normalized finite Markov row
+ amplitude assignment on the same row support
+ bridge equation: ampProb amplitude = normalizedMass
= normalized finite amplitude support
= S12 finite Born distribution boundary
```

公开摘要为：

```lean
theorem born_rule_derivation_bridge_summary :
    BornDistributionBoundaryClosed
    ∧ SumOverMiddleBornDistributionBoundaryClosed
    ∧ MarkovAmplitudeBornRuleDerivationClosed
    ∧ AmplitudeSupportNormalized
        concretePreparedMarkovAmplitudeCompatibility.amplitudeSupport
    ∧ (∀ b : PendingBeyondS18, ClosedByStepwiseS18 b = false)
    ∧ WenConstructiveCoverage
```

---

## 〇一 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| Markov row probability | `realNormalizedMassSum_eq_one` | S10 的 rational `normalizedMassSum = 1` 可读成 real-valued finite probability sum |
| Markov/amplitude compatibility | `MarkovAmplitudeCompatibility` | 同一 row support 上要求 `ampProb amplitude = normalizedMass` |
| amplitude support normalization | `markov_amplitude_support_normalized` | compatibility + row normalization 推出 `AmplitudeSupportNormalized` |
| Born distribution boundary | `markov_amplitude_born_rule_derivation` | normalized amplitude support 接入 S12 `BornDistributionBoundary` |
| weight matching | `born_candidate_weights_match_markov_masses` | 每个 Born candidate weight 都来自一个 Markov normalized mass |
| concrete witness | `concrete_prepared_born_rule_from_markov_amplitude_bridge` | concrete `prepared` 行的 `[1]` amplitude witness 完成同一推导 |

required but not closed：

| 轴 | 状态 |
|---|---|
| dynamics generating amplitudes | `ClosedByStepwiseS18 .amplitudeConstructionFromDynamics = false` |
| measurement postulate semantics | required but not closed |
| decoherence boundary | required but not closed |
| unitary/CPTP channel law | required but not closed |
| general path integral | required but not closed |
| metric recovery | required but not closed |
| empirical closure | required but not closed |

本轮闭合范围：**Born rule 从 Markov row probability 与 amplitude bridge compatibility 的有限 typed-skeleton 推导**。

---

## 一 · 边界读法

S18 解决的是 S12 之后留下的形式缺口：S12 只说“若 amplitude support 已归一，则 Born weights 成为有限概率分布”；S18 进一步证明“若这个 amplitude support 来自一个已归一 Markov row，并逐点满足 `ampProb = normalizedMass`，则归一化不是额外假设，而由 Markov row law 推出”。

这不是经验物理的最终 Born rule。还没有证明真实动力学必然给出这些 amplitude、没有测量公设语义、没有 decoherence、没有 unitary/CPTP channel law，也没有实验数据闭合。

---

## 二 · 失败记录

S18 第一次 build：

```text
命令：lake build SSBX.Foundation.Modern.QuantumRelativityBornRuleDerivationBridge
失败点 1：`exact_mod_cast` 不能自动把 Rat list sum cast 成 Real list sum
修正：新增 `list_map_rat_sum_cast`，先 cast rational sum，再改写为 real entry sum
失败点 2：`List.map_map` 后目标出现 `(ampProb ∘ amplitudeOf)`，直接 `rw` 找不到 lambda 版本
修正：把 pointwise sum theorem 的函数写成 composition 形状
失败点 3：concrete row support projection 未被 `simp [concreteRowSupport]` 展开
修正：同时展开 `concreteFiniteRowSupportNormalization`
结果：目标模块 build 通过
```

---

## 三 · Validation Command

Lean 验证命令：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityBornRuleDerivationBridge
```
