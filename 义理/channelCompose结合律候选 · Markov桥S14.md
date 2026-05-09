# channelCompose结合律候选 · Markov桥S14

**前置**：[channelCompose候选 · Markov桥S13](channelCompose候选%20·%20Markov桥S13.md) · [路径组合与因果约束 · Markov桥S3](路径组合与因果约束%20·%20Markov桥S3.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**后继**：[sum-over-middle通道组合候选 · Markov桥S15](sum-over-middle通道组合候选%20·%20Markov桥S15.md) 已关闭 finite middle-list composition 的 two-step support boundary。

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| associativity amplitude | `Foundation/Modern/QuantumRelativityChannelComposeAssociativityBridge.lean` | `channelCompose_associative_amplitude` | `machineChecked` |
| associativity boundary | `Foundation/Modern/QuantumRelativityChannelComposeAssociativityBridge.lean` | `ChannelComposeAssociativityBoundaryClosed`、`channel_compose_associativity_boundary_closed` | `machineChecked` |
| identity obstruction | `Foundation/Modern/QuantumRelativityChannelComposeAssociativityBridge.lean` | `no_self_step_blocks_channel_diagonal_identity` | `machineChecked` |
| concrete/grid obstruction | `Foundation/Modern/QuantumRelativityChannelComposeAssociativityBridge.lean` | `concrete_no_channel_diagonal_identity`、`operatorCellGrid_no_channel_diagonal_identity` | `machineChecked` |
| S14 summary | `Foundation/Modern/QuantumRelativityChannelComposeAssociativityBridge.lean` | `channel_compose_associativity_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S14 的主张：

```text
(left ⋄ middle) ⋄ right
and
left ⋄ (middle ⋄ right)

have the same pointwise amplitude and the same left classical boundary.
```

这里的 `⋄` 是 S13 的 `channelCompose`。因为 S13 的组合是逐点乘法，结合律可以由复数乘法结合律关闭。classical boundary 是 left-biased，所以两种括号化都保留最左侧 channel 的 finite classical boundary。

公开摘要为：

```lean
theorem channel_compose_associativity_bridge_summary :
    ChannelCompositionBoundaryClosed
    ∧ ChannelComposeAssociativityBoundaryClosed
    ∧ (∀ C : QuantumChannelSkeleton concreteProcess,
        ¬ ChannelDiagonalIdentityCandidate C)
    ∧ (∀ C : QuantumChannelSkeleton operatorCellGridProcess,
        ¬ ChannelDiagonalIdentityCandidate C)
    ∧ WenConstructiveCoverage
```

---

## 〇一 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| pointwise associativity | `channelCompose_associative_amplitude` | reassociation 不改变 composed amplitude |
| boundary associativity | `channelCompose_associative_classical_boundary` | reassociation 不改变 left classical boundary |
| closed algebra boundary | `ChannelComposeAssociativityBoundaryClosed` | current skeleton 的 pointwise associativity 已闭合 |
| diagonal identity obstruction | `no_self_step_blocks_channel_diagonal_identity` | 若 process 无一步自环，则 diagonal identity amplitude 不可作为当前 channel skeleton |
| concrete/grid obstruction | concrete/grid obstruction theorems | S3 的 no-self-loop 约束阻止 concrete/grid 的 diagonal identity candidate |

本轮闭合范围：**S13 pointwise `channelCompose` 的结合律，以及当前 support-respecting skeleton 中 diagonal identity 的阻塞边界**。

明确未关闭：

| 轴 | 状态 |
|---|---|
| unitary/CPTP identity law | 当前 skeleton 未带 Hilbert/Kraus/density-matrix 字段 |
| sum-over-middle composition | S15 另开；S14 只处理 pointwise composition |
| physical quantum channel law | 仍需额外结构，不由 S14 推出 |
| empirical closure | 仍未纳入 |

---

## 一 · Identity Obstruction

普通量子通道的 identity 通常在对角线给 `1`。但当前 `QuantumAmplitudeSkeleton` 有字段：

```lean
amplitude_support_implies_step :
  ∀ a b, amplitude a b ≠ 0 -> P.step a b
```

因此若要求 `amplitude a a = 1`，就会推出 `P.step a a`。对于 S3 已证明的一步无自环过程，这正好矛盾。S14 不把这个矛盾当成失败，而是把它登记为结构边界：当前 skeleton 是 support-respecting transition skeleton，不是完整 quantum channel algebra。

---

## 二 · Validation Command

Lean 验证命令：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityChannelComposeAssociativityBridge
```
