# 归一化质量求和候选 · Markov桥S10

**前置**：[有限概率归一化候选 · Markov桥S9](有限概率归一化候选%20·%20Markov桥S9.md) · [逐步统一候选摘要 · Markov桥S8](逐步统一候选摘要%20·%20Markov桥S8.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**后继**：[Born权重条件归一候选 · Markov桥S11](Born权重条件归一候选%20·%20Markov桥S11.md) 已关闭 normalized finite amplitude support 条件下的 `candidateWeight` 非负与 sum-one。

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| S9 named row law | `Foundation/Modern/QuantumRelativityFiniteProbabilityNormalizationBridge.lean` | `rowWeightSum_eq_rowTotal` | `machineChecked` |
| normalized mass sum | `Foundation/Modern/QuantumRelativityNormalizedMassBridge.lean` | `normalizedMassSum`、`normalizedMassSum_eq_normalizedRowTotalCandidate` | `machineChecked` |
| generic probability law | `Foundation/Modern/QuantumRelativityNormalizedMassBridge.lean` | `normalizedMass_sum_one` | `machineChecked` |
| concrete witness | `Foundation/Modern/QuantumRelativityNormalizedMassBridge.lean` | `concrete_normalizedMass_sum_one` | `machineChecked` |
| grid witness | `Foundation/Modern/QuantumRelativityNormalizedMassBridge.lean` | `operatorCellGrid_normalizedMass_sum_one` | `machineChecked` |
| S10 pending boundary | `Foundation/Modern/QuantumRelativityNormalizedMassBridge.lean` | `PendingBeyondS10`、`pending_boundary_not_closed_by_s10` | `machineChecked` |
| S10 summary | `Foundation/Modern/QuantumRelativityNormalizedMassBridge.lean` | `normalized_mass_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S10 的主张：

```text
explicit finite row support
+ rowWeightSum = rowTotal
+ normalizedMass(a,b) = weight(a,b) / rowTotal(a)
+ non-terminal row denominator ≠ 0
= sum_b normalizedMass(a,b) = 1
```

S9 已经关闭“先求权重和、再除以行分母”的 normalized-row-total candidate。S10 把它改写为更接近概率分布的形式：在显式有限 row support 上逐项计算 rational mass，再对这些 mass 求和。

公开摘要为：

```lean
theorem normalized_mass_bridge_summary :
    FiniteSumOneProbabilityBoundaryClosed
    ∧ FiniteNormalizedMassBoundaryClosed
    ∧ HasFiniteProbabilityProjection concreteProcess
    ∧ HasFiniteProbabilityProjection operatorCellGridProcess
    ∧ allOperatorCells.length = 94976
    ∧ (∀ b : PendingBeyondS10, ClosedByStepwiseS10 b = false)
    ∧ WenConstructiveCoverage
```

该 theorem 已通过：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityNormalizedMassBridge
```

---

## 〇一 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| row weight law | `rowWeightSum_eq_rowTotal` | S9 的 row support 权重求和定律有独立命名出口 |
| entry mass sum | `normalizedMassSum` | 在显式 row support 上对逐项 rational mass 求和 |
| algebra bridge | `normalizedMassSum_eq_normalizedRowTotalCandidate` | 逐项除法求和等于 S9 的“先求和后除法”候选 |
| classical probability law | `normalizedMass_sum_one` | 任一 normalizable row 若有 finite row support normalization，则 normalized masses 求和为 `1` |
| concrete law | `concrete_normalizedMass_sum_one` | concrete 非终端行给出 rational probability law |
| grid law | `operatorCellGrid_normalizedMass_sum_one` | `94976` grid 非终端行给出 rational probability law |
| S10 boundary | `FiniteNormalizedMassBoundaryClosed` | concrete/grid normalized mass sum-one boundary 已闭合 |

明确未关闭：

| 轴 | 状态 |
|---|---|
| amplitude/Born normalized support | `ClosedByStepwiseS10 .amplitudeBornNormalizedSupport = false` |
| Born-rule derivation | `ClosedByStepwiseS10 .bornRuleDerivation = false` |
| continuous action law | `ClosedByStepwiseS10 .continuousActionLaw = false` |
| general path integral | `ClosedByStepwiseS10 .generalPathIntegral = false` |
| measurable prediction data | `ClosedByStepwiseS10 .measurablePredictionData = false` |
| unitary/CPTP channel law | `ClosedByStepwiseS10 .unitaryCPTPChannelLaw = false` |
| metric recovery | `ClosedByStepwiseS10 .metricRecovery = false` |
| empirical closure | `ClosedByStepwiseS10 .empiricalClosure = false` |

本轮闭合范围：**从 Nat 权重进入 Rat 概率质量，并证明显式有限支撑上的 classical probability law**。这不是 Born rule 推导，也不是量子测量律、unitary/CPTP 动力学、路径积分、度规恢复或经验闭合。

---

## 一 · 失败记录

S10 先做了一个可弃用的 direct proof 试探：

```text
命令：lake env lean --stdin
试探：直接对 concrete/grid 展开 normalizedMassSum
结果：可证，但只能得到两个孤立计算证明
改进：改为泛型引理 normalizedMassSum_eq_normalizedRowTotalCandidate；
      再由 S9 的 rowWeightSum_eq_rowTotal 得到 normalizedMass_sum_one
```

该改法保留了失败路径的结论：直接计算能过，但结构性不足，不适合作为后续 Born/channel 接口的根基。

---

## 二 · 下一步

S10 之后的条件式 Born 权重已由 S11 完成：

```text
finite amplitude support
+ candidateWeight/amplitude norm
+ normalized support assumption
= Born-shaped weights are nonnegative and sum to 1
```

已关闭 theorem 名：

```text
born_weight_nonnegative_and_sum_one_if_normalized
```

---

## 三 · Validation Command

Lean 验证命令：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityNormalizedMassBridge
```
