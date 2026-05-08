# 有限概率归一化候选 · Markov桥S9

**前置**：[有限概率核接口 · Markov桥S2](有限概率核接口%20·%20Markov桥S2.md) · [逐步统一候选摘要 · Markov桥S8](逐步统一候选摘要%20·%20Markov桥S8.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**后继**：[归一化质量求和候选 · Markov桥S10](归一化质量求和候选%20·%20Markov桥S10.md) 已把本文件的 row-total candidate 改写为逐项 `normalizedMass` 的 finite probability law。

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| row-support operator | `Foundation/Modern/QuantumRelativityFiniteProbabilityNormalizationBridge.lean` | `rowWeightSum`、`normalizedMass`、`normalizedRowTotalCandidate` | `machineChecked` |
| row-support structure | `Foundation/Modern/QuantumRelativityFiniteProbabilityNormalizationBridge.lean` | `FiniteRowSupportNormalization`、`HasFiniteRowSupportNormalization` | `machineChecked` |
| row law出口 | `Foundation/Modern/QuantumRelativityFiniteProbabilityNormalizationBridge.lean` | `rowWeightSum_eq_rowTotal` | `machineChecked` |
| concrete witness | `Foundation/Modern/QuantumRelativityFiniteProbabilityNormalizationBridge.lean` | `concreteFiniteRowSupportNormalization`、`concrete_normalized_row_total_candidate_eq_one` | `machineChecked` |
| grid witness | `Foundation/Modern/QuantumRelativityFiniteProbabilityNormalizationBridge.lean` | `operatorCellGridFiniteRowSupportNormalization`、`operatorCellGrid_normalized_row_total_candidate_eq_one` | `machineChecked` |
| S9 pending boundary | `Foundation/Modern/QuantumRelativityFiniteProbabilityNormalizationBridge.lean` | `PendingBeyondS9`、`pending_boundary_not_closed_by_s9` | `machineChecked` |
| S9 summary | `Foundation/Modern/QuantumRelativityFiniteProbabilityNormalizationBridge.lean` | `finite_probability_normalization_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S9 的主张：

```text
finite probability kernel denominator interface
+ explicit finite row support
+ row weight sum = rowTotal
+ non-terminal row denominator ≠ 0
= normalized-row-total candidate = 1
```

这一步关闭的是 **finite row sum-one probability boundary**：concrete 三状态 kernel 与 `71232` operator-cell grid kernel 的每个非终端行，都有显式有限 row support，并且 row support 上的权重总和等于该行分母，因此 rational normalized-row-total candidate 为 `1`。

公开摘要为：

```lean
theorem finite_probability_normalization_bridge_summary :
    FiniteSumOneProbabilityBoundaryClosed
    ∧ HasFiniteProbabilityProjection concreteProcess
    ∧ HasFiniteProbabilityProjection operatorCellGridProcess
    ∧ allOperatorCells.length = 71232
    ∧ (∀ b : PendingBeyondS9, ClosedByStepwiseS9 b = false)
    ∧ WenConstructiveCoverage
```

该 theorem 已通过：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityFiniteProbabilityNormalizationBridge
```

---

## 〇一 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| row support | `FiniteRowSupportNormalization` | 行支撑列表 sound / complete for positive weights |
| row sum | `rowWeightSum`、`row_weight_sum_eq_rowTotal` | 显示支撑上的权重和等于行分母 |
| rational mass candidate | `normalizedMass`、`normalizedRowTotalCandidate` | 候选概率质量使用 `Rat` 分母读法 |
| concrete normalization | `concrete_normalized_row_total_candidate_eq_one` | concrete 非终端行归一为 `1` |
| grid normalization | `operatorCellGrid_normalized_row_total_candidate_eq_one` | `71232` grid 非终端行归一为 `1` |
| S9 boundary | `FiniteSumOneProbabilityBoundaryClosed` | finite sum-one row boundary 已闭合 |
| pending after S9 | `PendingBeyondS9` | sum-one row boundary 不再列入 pending；更大物理边界仍 pending |

明确未关闭：

| 轴 | 状态 |
|---|---|
| Born-rule derivation | `ClosedByStepwiseS9 .bornRuleDerivation = false` |
| continuous action law | `ClosedByStepwiseS9 .continuousActionLaw = false` |
| general path integral | `ClosedByStepwiseS9 .generalPathIntegral = false` |
| measurable prediction data | `ClosedByStepwiseS9 .measurablePredictionData = false` |
| unitary/CPTP channel law | `ClosedByStepwiseS9 .unitaryCPTPChannelLaw = false` |
| metric recovery | `ClosedByStepwiseS9 .metricRecovery = false` |
| empirical closure | `ClosedByStepwiseS9 .empiricalClosure = false` |

本轮闭合范围：**有限 Markov kernel 行支撑归一**。这不是 Born rule 推导，也不是量子测量律、unitary/CPTP 动力学、度规恢复或经验闭合。

---

## 一 · 失败记录

S9 第一次目标构建失败：

```text
命令：lake build SSBX.Foundation.Modern.QuantumRelativityFiniteProbabilityNormalizationBridge
失败点：concrete row list-sum 化简、operator-cell grid singleton `Fin` 化简、grid row normalized theorem 的 `exact_mod_cast`
原因：泛型展开让 Lean 保留了 `List.map ... []` / singleton map 目标；grid theorem 中直接套用泛型 Rat coercion 触发递归深度
修正：concrete row sum 改为 `native_decide`；grid row sum 对 terminal / non-terminal 分支做直接 `change`；grid normalized theorem 先证明 rowTotal = 1 再 `norm_num`
结果：目标构建通过
```

---

## 二 · 下一步

S9 之后，最省力的下一步先由 S10 完成：把 row-total candidate 改写为逐项 `normalizedMass` 的 finite sum-one law。随后进入 amplitude / Born 分布边界：

```text
finite amplitude support
-> Born-shaped weights are nonnegative
-> if amplitude support is normalized, Born-shaped weights sum to 1
-> push forward to observable ledger
```

这会把 S9 的 classical finite normalization 与 S5/S5r 的 amplitude/action-phase support 连接起来。

---

## 三 · Validation Command

Lean 验证命令：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityFiniteProbabilityNormalizationBridge
```
