# unitary-CPTP账本边界 · Markov桥S17

**前置**：[sum-over-middle Born边界候选 · Markov桥S16](sum-over-middle%20Born边界候选%20·%20Markov桥S16.md) · [channelCompose结合律候选 · Markov桥S14](channelCompose结合律候选%20·%20Markov桥S14.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**后继**：[Born rule推导候选 · Markov桥S18](Born%20rule推导候选%20·%20Markov桥S18.md) 已关闭 Markov/amplitude compatibility 下的 finite typed-skeleton Born-rule derivation；[非平凡量子通道律候选 · Markov桥S20](非平凡量子通道律候选%20·%20Markov桥S20.md) 已关闭 finite support-respecting nonzero channel law。physical unitary/CPTP/Kraus/density-matrix law 仍按本文件 ledger 保留为 required but not closed。

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| closed current items | `Foundation/Modern/QuantumRelativityUnitaryCPTPLedgerBridge.lean` | `CurrentChannelBoundaryItem`、`ClosedByStepwiseS17Boundary` | `machineChecked` |
| current item theorem | `Foundation/Modern/QuantumRelativityUnitaryCPTPLedgerBridge.lean` | `current_channel_boundary_closed_by_s17` | `machineChecked` |
| physical ledger items | `Foundation/Modern/QuantumRelativityUnitaryCPTPLedgerBridge.lean` | `UnitaryCPTPLedgerItem`、`RequiredForPhysicalChannelLaw`、`ClosedByStepwiseS17` | `machineChecked` |
| required pending theorem | `Foundation/Modern/QuantumRelativityUnitaryCPTPLedgerBridge.lean` | `unitary_cptp_ledger_required_but_not_closed_by_s17` | `machineChecked` |
| S17 summary | `Foundation/Modern/QuantumRelativityUnitaryCPTPLedgerBridge.lean` | `unitary_cptp_ledger_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S17 的主张：

```text
S13-S16 close useful channel/probability typed skeletons.

Physical Hilbert/unitary/CPTP/Kraus/density-matrix channel law requires more:
Hilbert carrier, linear operators, inner product preservation,
density matrices, complete positivity, trace preservation,
Kraus semantics, unitary evolution law, and empirical calibration.

Those requirements are required, but not closed by the current skeleton.
```

公开摘要为：

```lean
theorem unitary_cptp_ledger_bridge_summary :
    BornDistributionBoundaryClosed
    ∧ SumOverMiddleChannelBoundaryClosed
    ∧ SumOverMiddleBornDistributionBoundaryClosed
    ∧ (∀ item : CurrentChannelBoundaryItem,
        ClosedByStepwiseS17Boundary item = true)
    ∧ (∀ item : UnitaryCPTPLedgerItem,
        RequiredForPhysicalChannelLaw item = true
          ∧ ClosedByStepwiseS17 item = false)
    ∧ WenConstructiveCoverage
```

---

## 〇一 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| finite classical boundary | `CurrentChannelBoundaryItem.finiteClassicalBoundary` | S2/S9-S10 的 finite probability side 已有形式接口 |
| support-respecting amplitude | `CurrentChannelBoundaryItem.supportRespectingAmplitude` | S4 channel skeleton 保留 support-to-step boundary |
| pointwise composition | `CurrentChannelBoundaryItem.pointwiseComposition` | S13 已关闭 current skeleton 的 pointwise composition |
| pointwise associativity | `CurrentChannelBoundaryItem.pointwiseAssociativity` | S14 已关闭 reassociation boundary |
| sum-over-middle two-step boundary | `CurrentChannelBoundaryItem.sumOverMiddleTwoStepBoundary` | S15 已关闭 finite middle-list two-step support |
| conditional composed Born boundary | `CurrentChannelBoundaryItem.conditionalComposedBornBoundary` | S16 已关闭 composed endpoint support 的条件式 Born boundary |

required but not closed / machineChecked ledger：

| 轴 | Lean item | 状态 |
|---|---|---|
| Hilbert carrier | `hilbertSpaceCarrier` | `RequiredForPhysicalChannelLaw = true` 且 `ClosedByStepwiseS17 = false` |
| linear operators | `linearOperatorSemantics` | required but not closed |
| inner product preservation | `innerProductPreservation` | required but not closed |
| density matrix semantics | `densityMatrixSemantics` | required but not closed |
| complete positivity | `completePositivity` | required but not closed |
| trace preservation | `tracePreservation` | required but not closed |
| Kraus representation | `krausRepresentation` | required but not closed |
| unitary evolution law | `unitaryEvolutionLaw` | required but not closed |
| empirical calibration | `empiricalCalibration` | required but not closed |

本轮闭合范围：**把当前 channel/probability skeleton 已关闭项与 physical unitary/CPTP law 未关闭项放入同一个可检查 ledger**。S20 后续关闭了非零 channel amplitude 的 finite law，但不改变本文件对 Hilbert / CPTP / Kraus / density-matrix law 的 required-but-not-closed 判断。

---

## 一 · 边界读法

S17 不是退回保守主义，而是把路线变清楚：S13-S16 已经确实给出组合、结合、sum-over-middle、composed Born boundary 的形式接口；这些内容可以作为后续统一候选的一部分。只是 physical quantum channel law 还需要 Hilbert / density matrix / CPTP 等额外语义。

---

## 二 · Validation Command

Lean 验证命令：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityUnitaryCPTPLedgerBridge
```
