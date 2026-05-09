# channelCompose候选 · Markov桥S13

**前置**：[Born分布边界候选 · Markov桥S12](Born分布边界候选%20·%20Markov桥S12.md) · [经典Markov与量子振幅分层 · Markov桥S4](经典Markov与量子振幅分层%20·%20Markov桥S4.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**后继**：[channelCompose结合律候选 · Markov桥S14](channelCompose结合律候选%20·%20Markov桥S14.md) 已关闭 pointwise `channelCompose` 的 associativity boundary，并记录 diagonal identity obstruction；[sum-over-middle通道组合候选 · Markov桥S15](sum-over-middle通道组合候选%20·%20Markov桥S15.md) 已关闭 finite middle-list composition 的 two-step boundary。

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| composition operator | `Foundation/Modern/QuantumRelativityChannelComposeBridge.lean` | `channelCompose` | `machineChecked` |
| amplitude law | `Foundation/Modern/QuantumRelativityChannelComposeBridge.lean` | `channelCompose_amplitude` | `machineChecked` |
| classical boundary | `Foundation/Modern/QuantumRelativityChannelComposeBridge.lean` | `channelCompose_keeps_left_classical_boundary` | `machineChecked` |
| support soundness | `Foundation/Modern/QuantumRelativityChannelComposeBridge.lean` | `channelCompose_support_implies_step` | `machineChecked` |
| closed boundary | `Foundation/Modern/QuantumRelativityChannelComposeBridge.lean` | `ChannelCompositionBoundaryClosed`、`channel_composition_boundary_closed` | `machineChecked` |
| concrete/grid witness | `Foundation/Modern/QuantumRelativityChannelComposeBridge.lean` | `concrete_channelCompose_self_keeps_boundary`、`operatorCellGrid_channelCompose_self_keeps_boundary` | `machineChecked` |
| S13 summary | `Foundation/Modern/QuantumRelativityChannelComposeBridge.lean` | `channel_compose_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S13 的主张：

```text
QuantumChannelSkeleton left
+ QuantumChannelSkeleton right
= channelCompose left right
  where amplitude = left.amplitude * right.amplitude
  and classicalBoundary = left.classicalBoundary
```

`channelCompose` 是当前 skeleton 的候选组合接口：组合后的 amplitude layer 逐点相乘；若组合 amplitude 非零，则左 amplitude 非零，因此仍由左 channel 的 support soundness 推出 process step。classical finite probability boundary 明确保留左侧 channel 的 boundary。

公开摘要为：

```lean
theorem channel_compose_bridge_summary :
    BornDistributionBoundaryClosed
    ∧ ChannelCompositionBoundaryClosed
    ∧ HasQuantumChannelCandidate concreteProcess
    ∧ HasQuantumChannelCandidate operatorCellGridProcess
    ∧ (channelCompose concreteQuantumChannelSkeleton
        concreteQuantumChannelSkeleton).classicalBoundary =
          concreteFiniteProbabilityKernel
    ∧ (channelCompose operatorCellGridQuantumChannelSkeleton
        operatorCellGridQuantumChannelSkeleton).classicalBoundary =
          operatorCellGridFiniteProbabilityKernel
    ∧ (∀ b : PendingBeyondS13, ClosedByStepwiseS13 b = false)
    ∧ WenConstructiveCoverage
```

该 theorem 已通过：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityChannelComposeBridge
```

---

## 〇一 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| compose operator | `channelCompose` | 当前 channel skeleton 的候选组合 |
| amplitude multiplication | `channelCompose_amplitude` | composition amplitude 是逐点乘积 |
| classical boundary retention | `channelCompose_keeps_left_classical_boundary` | composition 保留左侧 finite classical boundary |
| step soundness | `channelCompose_support_implies_step` | 非零 composition amplitude 仍推出 process step |
| probability dependency | `BornDistributionBoundaryClosed` | S12 finite Born distribution boundary 被 summary 保留 |
| concrete/grid witness | concrete/grid self-compose theorems | 自组合保留各自 finite probability kernel |

明确未关闭：

| 轴 | 状态 |
|---|---|
| Born-rule derivation | `ClosedByStepwiseS13 .bornRuleDerivation = false` |
| physical channel law | `ClosedByStepwiseS13 .physicalChannelLaw = false` |
| continuous action law | `ClosedByStepwiseS13 .continuousActionLaw = false` |
| general path integral | `ClosedByStepwiseS13 .generalPathIntegral = false` |
| measurable prediction data | `ClosedByStepwiseS13 .measurablePredictionData = false` |
| unitary/CPTP channel law | `ClosedByStepwiseS13 .unitaryCPTPChannelLaw = false` |
| metric recovery | `ClosedByStepwiseS13 .metricRecovery = false` |
| empirical closure | `ClosedByStepwiseS13 .empiricalClosure = false` |

本轮闭合范围：**current skeleton 的 channel composition candidate**。这不是物理 quantum channel law，也不是 unitary/CPTP、Kraus composition、路径积分、度规恢复或经验闭合。

---

## 一 · 失败记录

S13 的关键 proof 先以 `lake env lean --stdin` 试探：

```text
目标：定义 channelCompose 并证明 support-to-step
结果：一次通过
保留结论：composition 使用左侧 classicalBoundary；这是最小保守接口，不声称物理通道组合律
```

没有 Lean proof failure。后续若要做更强 channel law，需要新增结构字段，例如 unitary/CPTP/Kraus 或 density-matrix law，而不是把本层 `channelCompose` 误读为物理闭合。

---

## 二 · 下一步

本轮五项顺序已经走完：

```text
rowWeightSum_eq_rowTotal
normalizedMass_sum_one
born_weight_nonnegative_and_sum_one_if_normalized
born_distribution_boundary
channelCompose
```

S14 已完成 pointwise associativity，并证明当前 support-respecting skeleton 中 diagonal identity 会被 no-self-step process 阻塞。S15 已从 pointwise composition 进入 sum-over-middle composition，并证明非零 endpoint sum 只能推出 two-step support；S20 已把 concrete nonzero channel witness 升级为 finite support-respecting nonzero channel law。physical unitary/CPTP/Kraus/density-matrix law 仍需额外结构。

---

## 三 · Validation Command

Lean 验证命令：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityChannelComposeBridge
```
