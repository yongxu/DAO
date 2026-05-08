# sum-over-middle通道组合候选 · Markov桥S15

**前置**：[channelCompose结合律候选 · Markov桥S14](channelCompose结合律候选%20·%20Markov桥S14.md) · [经典Markov与量子振幅分层 · Markov桥S4](经典Markov与量子振幅分层%20·%20Markov桥S4.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| finite support lemma | `Foundation/Modern/QuantumRelativitySumOverMiddleChannelBridge.lean` | `list_sum_ne_zero_has_nonzero_entry` | `machineChecked` |
| endpoint amplitude | `Foundation/Modern/QuantumRelativitySumOverMiddleChannelBridge.lean` | `sumOverMiddleChannelAmplitude` | `machineChecked` |
| two-step support | `Foundation/Modern/QuantumRelativitySumOverMiddleChannelBridge.lean` | `TwoStepReachableViaList`、`sumOverMiddle_support_implies_two_step` | `machineChecked` |
| composition boundary | `Foundation/Modern/QuantumRelativitySumOverMiddleChannelBridge.lean` | `SumOverMiddleChannelComposition`、`SumOverMiddleChannelBoundaryClosed` | `machineChecked` |
| concrete witness | `Foundation/Modern/QuantumRelativitySumOverMiddleChannelBridge.lean` | `concrete_sumOverMiddle_prepared_measured_amplitude`、`concrete_prepared_measured_not_one_step` | `machineChecked` |
| S15 summary | `Foundation/Modern/QuantumRelativitySumOverMiddleChannelBridge.lean` | `sum_over_middle_channel_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S15 的主张：

```text
composedAmplitude(a,c)
  = sum over listed middle b of left(a,b) * right(b,c)

if composedAmplitude(a,c) is nonzero,
then there exists a listed b with a -> b and b -> c.
```

这一步补上 S13/S14 没有处理的真实组合形状：经中间态求和。它不把结果强行装回当前 `QuantumChannelSkeleton`，因为当前 skeleton 要求非零 amplitude 直接推出一步 `P.step a c`；而 sum-over-middle 的自然结论是 two-step reachability。

公开摘要为：

```lean
theorem sum_over_middle_channel_bridge_summary :
    ChannelCompositionBoundaryClosed
    ∧ ChannelComposeAssociativityBoundaryClosed
    ∧ SumOverMiddleChannelBoundaryClosed
    ∧ sumOverMiddleChannelAmplitude [ConcreteState.evolved]
        concreteStepQuantumChannelSkeleton concreteStepQuantumChannelSkeleton
        ConcreteState.prepared ConcreteState.measured = 1
    ∧ ¬ concreteProcess.step ConcreteState.prepared ConcreteState.measured
    ∧ TwoStepReachableViaList (P := concreteProcess) [ConcreteState.evolved]
        ConcreteState.prepared ConcreteState.measured
    ∧ WenConstructiveCoverage
```

---

## 〇一 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| finite sum support | `list_sum_ne_zero_has_nonzero_entry` | 有限复数列表求和非零则至少一项非零 |
| sum-over-middle amplitude | `sumOverMiddleChannelAmplitude` | endpoint amplitude 是显式中间态列表上的有限和 |
| two-step soundness | `sumOverMiddle_support_implies_two_step` | 非零 endpoint sum 推出某个 middle 上的两段 step |
| boundary object | `SumOverMiddleChannelComposition` | 组合对象记录 amplitude boundary 与 support-to-two-step boundary |
| closed boundary | `sum_over_middle_channel_boundary_closed` | 任意两个 channel candidates 与 finite middle list 都有该 boundary object |
| concrete separation | `concrete_sumOverMiddle_prepared_measured_amplitude` + `concrete_prepared_measured_not_one_step` | `prepared -> evolved -> measured` 的 composed amplitude 为 `1`，但 `prepared -> measured` 不是一步边 |

本轮闭合范围：**finite sum-over-middle channel composition 的 two-step boundary**。

明确未关闭：

| 轴 | 状态 |
|---|---|
| 把 sum-over-middle 结果作为当前 one-step `QuantumChannelSkeleton` | 当前 skeleton 的 support law 不允许；需要新的 reachability/channel law |
| unitary/CPTP/Kraus/density-matrix law | 尚未提供 Hilbert 或 density-matrix 语义 |
| general path integral | 本轮只对显式 finite middle list 求和 |
| Born rule derivation | 本轮不从 composed amplitude 推出无条件测量概率律 |
| empirical closure | 无外部数据、误差模型或实验判准 |

---

## 一 · 为什么不是 S13 的重复

S13 的 `channelCompose` 是逐点乘法：

```text
(left ⋄ right)(a,b) = left(a,b) * right(a,b)
```

它能保留一步支持，因为非零 composed amplitude 直接给出左侧同一 `(a,b)` 的非零 amplitude。

S15 的组合是：

```text
(right ∘ left)(a,c) = Σ_b left(a,b) * right(b,c)
```

非零结果只说明至少存在某个中间态 `b`，使 `a -> b` 与 `b -> c` 都成立。它自然进入 two-step boundary，而不是一步边。

---

## 二 · 失败记录

S15 的 proof 先以 `lake env lean --stdin` 试探：

```text
目标：证明 sum-over-middle support 推出 two-step witness
第一次失败：`rw [← hbeq]` 方向错；`List.mem_map` 给出的等式方向是 product = x
修正：改用 `rw [hbeq]`，把目标化为 `x ≠ 0`
第二个易错点：concrete amplitude support proof 需要先展开 `QuantumAmplitudeSupport`
保留结论：该组合不能冒充当前 one-step channel skeleton；two-step support 是正确出口
```

---

## 三 · Validation Command

Lean 验证命令：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativitySumOverMiddleChannelBridge
```
