# Born权重条件归一候选 · Markov桥S11

**前置**：[归一化质量求和候选 · Markov桥S10](归一化质量求和候选%20·%20Markov桥S10.md) · [干涉与测量律候选 · Markov桥S5](干涉与测量律候选%20·%20Markov桥S5.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| finite amplitude support | `Foundation/Modern/QuantumRelativityBornWeightNormalizationBridge.lean` | `amplitudeSupportWeightSum`、`AmplitudeSupportNormalized` | `machineChecked` |
| candidate support | `Foundation/Modern/QuantumRelativityBornWeightNormalizationBridge.lean` | `bornCandidateBoundarySupport`、`bornCandidateWeightSum` | `machineChecked` |
| candidate / ampProb bridge | `Foundation/Modern/QuantumRelativityBornWeightNormalizationBridge.lean` | `bornCandidateWeightSum_eq_amplitudeSupportWeightSum` | `machineChecked` |
| conditional law | `Foundation/Modern/QuantumRelativityBornWeightNormalizationBridge.lean` | `born_weight_nonnegative_and_sum_one_if_normalized` | `machineChecked` |
| closed boundary | `Foundation/Modern/QuantumRelativityBornWeightNormalizationBridge.lean` | `ConditionalBornWeightNormalizationBoundaryClosed` | `machineChecked` |
| unit witness | `Foundation/Modern/QuantumRelativityBornWeightNormalizationBridge.lean` | `unitAmplitudeSupport`、`unit_amplitude_support_born_weight_law` | `machineChecked` |
| S11 summary | `Foundation/Modern/QuantumRelativityBornWeightNormalizationBridge.lean` | `born_weight_normalization_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S11 的主张：

```text
finite amplitude support
+ candidateWeight = ampProb amplitude
+ amplitude support already normalized by ampProb
= all candidateWeights nonnegative
+ finite candidateWeight sum = 1
```

这是条件式闭合：它不从 Markov 权重推出 Born rule，也不从动力学推出归一化；它只证明一旦有限 amplitude support 已由 `ampProb` 归一，现有 `BornRuleCandidateBoundary.candidateWeight` 就形成有限概率律。

公开摘要为：

```lean
theorem born_weight_normalization_bridge_summary :
    FiniteSumOneProbabilityBoundaryClosed
    ∧ FiniteNormalizedMassBoundaryClosed
    ∧ ConditionalBornWeightNormalizationBoundaryClosed
    ∧ ((∀ c : BornRuleCandidateBoundary,
          c ∈ bornCandidateBoundarySupport unitAmplitudeSupport ->
            0 ≤ c.candidateWeight)
        ∧ bornCandidateWeightSum unitAmplitudeSupport = 1)
    ∧ (∀ b : PendingBeyondS11, ClosedByStepwiseS11 b = false)
    ∧ WenConstructiveCoverage
```

该 theorem 已通过：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityBornWeightNormalizationBridge
```

---

## 〇一 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| finite support weight | `amplitudeSupportWeightSum` | 对有限 amplitude support 的 `ampProb` 求和 |
| support normalized assumption | `AmplitudeSupportNormalized` | support 的 `ampProb` 权重和为 `1` |
| candidate support | `bornCandidateBoundarySupport` | 每个 amplitude 接到 S5 的 `bornRuleCandidate` |
| candidate sum bridge | `bornCandidateWeightSum_eq_amplitudeSupportWeightSum` | `candidateWeight` 求和等于 `ampProb` 求和 |
| conditional Born weights | `born_weight_nonnegative_and_sum_one_if_normalized` | support 已归一时，candidate weights 非负且求和为 `1` |
| unit witness | `unit_amplitude_support_born_weight_law` | `[1]` 作为最小 normalized support witness |

明确未关闭：

| 轴 | 状态 |
|---|---|
| Born-rule derivation | `ClosedByStepwiseS11 .bornRuleDerivation = false` |
| Born distribution boundary | `ClosedByStepwiseS11 .bornDistributionBoundary = false` |
| continuous action law | `ClosedByStepwiseS11 .continuousActionLaw = false` |
| general path integral | `ClosedByStepwiseS11 .generalPathIntegral = false` |
| measurable prediction data | `ClosedByStepwiseS11 .measurablePredictionData = false` |
| unitary/CPTP channel law | `ClosedByStepwiseS11 .unitaryCPTPChannelLaw = false` |
| metric recovery | `ClosedByStepwiseS11 .metricRecovery = false` |
| empirical closure | `ClosedByStepwiseS11 .empiricalClosure = false` |

本轮闭合范围：**有限 amplitude support 的条件式 Born-shaped probability law**。这不是 Born rule 推导，也不是物理测量律、unitary/CPTP 动力学、路径积分、度规恢复或经验闭合。

---

## 一 · 失败记录

S11 第一次证明试探：

```text
命令：lake env lean --stdin
失败点：`simp` 不能直接把 `(candidateWeight ∘ bornRuleCandidate)` 的 list sum 改写成 `ampProb` list sum
原因：结构字段投影穿过 `List.map` 后没有自动展开到已有 boundary theorem
修正：对 support list 做 induction；cons 分支用 `change` 暴露头项与 tail sum，再 `rw [born_rule_candidate_boundary, ih]`
结果：`bornCandidateWeightSum_eq_amplitudeSupportWeightSum` 与条件式 theorem 均通过
```

---

## 二 · 下一步

S11 之后按当前顺序进入：

```text
born_distribution_boundary
```

目标是把 amplitude sum / finite support / candidateWeight 接到同一个 finite probability interface，而不是只保留一个 normalized list theorem。

---

## 三 · Validation Command

Lean 验证命令：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityBornWeightNormalizationBridge
```
