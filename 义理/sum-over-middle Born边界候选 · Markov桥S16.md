# sum-over-middle Born边界候选 · Markov桥S16

**前置**：[sum-over-middle通道组合候选 · Markov桥S15](sum-over-middle通道组合候选%20·%20Markov桥S15.md) · [Born分布边界候选 · Markov桥S12](Born分布边界候选%20·%20Markov桥S12.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**后继**：[unitary-CPTP账本边界 · Markov桥S17](unitary-CPTP账本边界%20·%20Markov桥S17.md) 已把 S13-S16 已关闭 skeleton 与 physical channel law 未关闭项放入同一个 ledger；[非平凡量子通道律候选 · Markov桥S20](非平凡量子通道律候选%20·%20Markov桥S20.md) 已复用本文件的 composed Born boundary，并关闭 finite support-respecting nonzero channel law。

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| endpoint amplitude support | `Foundation/Modern/QuantumRelativitySumOverMiddleBornBoundaryBridge.lean` | `sumOverMiddleEndpointAmplitudeSupport` | `machineChecked` |
| composed Born boundary | `Foundation/Modern/QuantumRelativitySumOverMiddleBornBoundaryBridge.lean` | `SumOverMiddleBornDistributionBoundary` | `machineChecked` |
| conditional construction | `Foundation/Modern/QuantumRelativitySumOverMiddleBornBoundaryBridge.lean` | `sum_over_middle_born_distribution_boundary` | `machineChecked` |
| closed boundary | `Foundation/Modern/QuantumRelativitySumOverMiddleBornBoundaryBridge.lean` | `SumOverMiddleBornDistributionBoundaryClosed`、`sum_over_middle_born_distribution_boundary_closed` | `machineChecked` |
| concrete support | `Foundation/Modern/QuantumRelativitySumOverMiddleBornBoundaryBridge.lean` | `concrete_sumOverMiddle_endpoint_amplitude_support`、`concrete_composed_endpoint_amplitude_support_normalized` | `machineChecked` |
| S16 summary | `Foundation/Modern/QuantumRelativitySumOverMiddleBornBoundaryBridge.lean` | `sum_over_middle_born_distribution_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S16 的主张：

```text
endpointSupport : List (State × State)
  -> composed amplitude support via S15 sum-over-middle amplitude

if that amplitude support is already ampProb-normalized,
then S12 gives a BornDistributionBoundary.
```

也就是说，本轮不从 dynamics 推导 Born rule，而是把“已归一的 composed amplitude support”接入既有 finite probability distribution interface。

公开摘要为：

```lean
theorem sum_over_middle_born_distribution_bridge_summary :
    SumOverMiddleChannelBoundaryClosed
    ∧ BornDistributionBoundaryClosed
    ∧ SumOverMiddleBornDistributionBoundaryClosed
    ∧ sumOverMiddleEndpointAmplitudeSupport [ConcreteState.evolved]
        concreteStepQuantumChannelSkeleton concreteStepQuantumChannelSkeleton
        concreteComposedEndpointSupport = [1]
    ∧ AmplitudeSupportNormalized
        (sumOverMiddleEndpointAmplitudeSupport [ConcreteState.evolved]
          concreteStepQuantumChannelSkeleton concreteStepQuantumChannelSkeleton
          concreteComposedEndpointSupport)
    ∧ WenConstructiveCoverage
```

---

## 〇一 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| endpoint support to amplitude support | `sumOverMiddleEndpointAmplitudeSupport` | 显式 endpoint pair list 映射到 composed amplitude list |
| conditional Born boundary | `sum_over_middle_born_distribution_boundary` | 若 composed amplitude support 已归一，则得到 S12 `BornDistributionBoundary` |
| closed interface | `SumOverMiddleBornDistributionBoundaryClosed` | 条件式 boundary 对任意 finite endpoint support 都成立 |
| concrete support | `concrete_sumOverMiddle_endpoint_amplitude_support` | concrete `[prepared, measured]` endpoint support 产生 amplitude support `[1]` |
| concrete normalization | `concrete_composed_endpoint_amplitude_support_normalized` | concrete composed support 复用 S11 unit amplitude normalization |

本轮闭合范围：**sum-over-middle composed endpoint support 到 finite Born distribution boundary 的条件式接口**。

明确未关闭：

| 轴 | 状态 |
|---|---|
| Born rule derivation | 仍未从动力学或测量公理推出无条件 Born rule |
| unitarity/CPTP | 仍无 Hilbert/Kraus/density-matrix channel law |
| path integral | 仍只处理 finite endpoint list 和 finite middle list |
| empirical closure | 仍无数据、误差模型、阈值或实验闭合 |

---

## 一 · 失败记录

S16 的 proof 先以 `lake env lean --stdin` 试探：

```text
目标：给 concrete composed endpoint support 构造显式 Born boundary witness
失败类型：Lean proof failure / heartbeat timeout
原因：dependent existential witness 展开到 concrete structure fields 时触发 `whnf` 心跳上限
保留结论：泛型 `SumOverMiddleBornDistributionBoundaryClosed` 已关闭；concrete 侧保留 `[1]` amplitude support 与 normalized theorem，足够作为条件式 boundary 的输入
后继：S17 已把 unitary/CPTP ledger boundary 落地；若需要 concrete existential 展开，可单独优化 witness 的定义等式
```

---

## 二 · Validation Command

Lean 验证命令：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativitySumOverMiddleBornBoundaryBridge
```
