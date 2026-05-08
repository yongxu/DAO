# Born分布边界候选 · Markov桥S12

**前置**：[Born权重条件归一候选 · Markov桥S11](Born权重条件归一候选%20·%20Markov桥S11.md) · [归一化质量求和候选 · Markov桥S10](归一化质量求和候选%20·%20Markov桥S10.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| finite probability interface | `Foundation/Modern/QuantumRelativityBornDistributionBridge.lean` | `FiniteProbabilityDistributionInterface` | `machineChecked` |
| amplitude sum | `Foundation/Modern/QuantumRelativityBornDistributionBridge.lean` | `amplitudeSupportAmplitudeSum` | `machineChecked` |
| finite distribution | `Foundation/Modern/QuantumRelativityBornDistributionBridge.lean` | `bornFiniteProbabilityDistribution` | `machineChecked` |
| boundary object | `Foundation/Modern/QuantumRelativityBornDistributionBridge.lean` | `BornDistributionBoundary`、`bornDistributionBoundary` | `machineChecked` |
| public theorem | `Foundation/Modern/QuantumRelativityBornDistributionBridge.lean` | `born_distribution_boundary` | `machineChecked` |
| closed boundary | `Foundation/Modern/QuantumRelativityBornDistributionBridge.lean` | `BornDistributionBoundaryClosed`、`born_distribution_boundary_closed` | `machineChecked` |
| S12 summary | `Foundation/Modern/QuantumRelativityBornDistributionBridge.lean` | `born_distribution_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S12 的主张：

```text
normalized finite amplitude support
+ amplitudeSupportAmplitudeSum
+ bornCandidateBoundarySupport
+ candidateWeight projection
= FiniteProbabilityDistributionInterface
```

S11 证明的是条件式 list law。S12 把这条 law 装入一个有限概率分布接口，并在同一个 boundary object 里保留 amplitude support、amplitude sum、candidate support 与 `candidateWeight` 投影。

公开摘要为：

```lean
theorem born_distribution_bridge_summary :
    FiniteSumOneProbabilityBoundaryClosed
    ∧ FiniteNormalizedMassBoundaryClosed
    ∧ ConditionalBornWeightNormalizationBoundaryClosed
    ∧ BornDistributionBoundaryClosed
    ∧ (∀ b : PendingBeyondS12, ClosedByStepwiseS12 b = false)
    ∧ WenConstructiveCoverage
```

该 theorem 已通过：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityBornDistributionBridge
```

---

## 〇一 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| finite distribution interface | `FiniteProbabilityDistributionInterface` | support list、weight function、非负性、sum-one |
| amplitude sum | `amplitudeSupportAmplitudeSum` | 有限 amplitude support 的 complex sum 被记录进 boundary |
| candidate support | `bornCandidateBoundarySupport` | 从 amplitude support 进入 S5 的 Born-shaped candidate |
| candidate weight projection | `candidate_weight_boundary` | distribution weight 与 `c.candidateWeight` 对齐 |
| public boundary | `born_distribution_boundary` | 任一 normalized amplitude support 给出 `BornDistributionBoundary` |
| summary | `born_distribution_bridge_summary` | S9/S10/S11/S12 当前概率侧结构合取 |

明确未关闭：

| 轴 | 状态 |
|---|---|
| Born-rule derivation | `ClosedByStepwiseS12 .bornRuleDerivation = false` |
| channel composition | `ClosedByStepwiseS12 .channelComposition = false` |
| continuous action law | `ClosedByStepwiseS12 .continuousActionLaw = false` |
| general path integral | `ClosedByStepwiseS12 .generalPathIntegral = false` |
| measurable prediction data | `ClosedByStepwiseS12 .measurablePredictionData = false` |
| unitary/CPTP channel law | `ClosedByStepwiseS12 .unitaryCPTPChannelLaw = false` |
| metric recovery | `ClosedByStepwiseS12 .metricRecovery = false` |
| empirical closure | `ClosedByStepwiseS12 .empiricalClosure = false` |

本轮闭合范围：**把 conditional Born-weight law 装入 finite probability distribution interface**。这不是 Born rule 推导，也不是 channel composition、unitary/CPTP 动力学、路径积分、度规恢复或经验闭合。

---

## 一 · 失败记录

S12 第一次 theorem 试探：

```text
命令：lake env lean --stdin
失败点：`simp [bornDistributionBoundary]` 不能自动拆出 distribution.support / distribution.weight_sum_one 的全部合取
原因：结构字段和 dependent constructor 展开后，Lean 未自动应用 `bornFiniteProbabilityDistribution.support` 与 `weight_sum_one`
修正：在 `born_distribution_boundary` 中显式 `refine` existential witness，并逐项给 `rfl` / `weight_sum_one`
结果：`born_distribution_boundary` 通过
```

---

## 二 · 下一步

S12 之后按当前顺序进入：

```text
channelCompose
```

目标是证明候选 channel composition 的有限接口。该步骤应复用 S10-S12 的 probability / amplitude distribution 接口，而不是空造 composition 名称。

---

## 三 · Validation Command

Lean 验证命令：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityBornDistributionBridge
```
