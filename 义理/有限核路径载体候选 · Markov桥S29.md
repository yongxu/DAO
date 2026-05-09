# 有限核路径载体候选 · Markov桥S29

**前置**：[路径权重乘法候选 · Markov桥S19](路径权重乘法候选%20·%20Markov桥S19.md) · [有限因果区间候选 · Markov桥S28](有限因果区间候选%20·%20Markov桥S28.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| displayed kernel carrier | `Foundation/Modern/QuantumRelativityFiniteKernelPathCarrierBridge.lean` | `DisplayedKernelPathCarrier` | `machineChecked` |
| path readback | `Foundation/Modern/QuantumRelativityFiniteKernelPathCarrierBridge.lean` | `DisplayedKernelPathCarrier.reachable`、`DisplayedKernelPathCarrier.causal_before` | `machineChecked` |
| path weight | `Foundation/Modern/QuantumRelativityFiniteKernelPathCarrierBridge.lean` | `DisplayedKernelPathCarrier.weight_eq_path_weight` | `machineChecked` |
| path-local interval | `Foundation/Modern/QuantumRelativityFiniteKernelPathCarrierBridge.lean` | `SoundKernelTwoStepPathLocalIntervalCandidate`、`kernel_path_local_interval_sound_closed` | `machineChecked` |
| concrete carrier | `Foundation/Modern/QuantumRelativityFiniteKernelPathCarrierBridge.lean` | `concretePreparedMeasuredKernelCarrier` | `machineChecked` |
| two-route carriers | `Foundation/Modern/QuantumRelativityFiniteKernelPathCarrierBridge.lean` | `twoRouteUpperKernelCarrier`、`twoRouteLowerKernelCarrier` | `machineChecked` |
| S29 summary | `Foundation/Modern/QuantumRelativityFiniteKernelPathCarrierBridge.lean` | `finite_kernel_path_carrier_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S29 关闭的是一个有限 kernel path 的 displayed carrier 候选：

```text
finite KernelPath
-> displayed finite carrier list
-> endpoints are in the carrier
-> path reads back as Reachable / causalBefore
-> carrier weight is the KernelPath weight
-> a single two-step kernel path has a sound path-local interval
-> concrete and two-route examples attach to S28 intervals
```

公开摘要为：

```lean
theorem finite_kernel_path_carrier_bridge_summary :
    FiniteKernelPathCarrierClosed
    ∧ KernelPathLocalIntervalSoundClosed
    ∧ FiniteCausalIntervalClosed
    ∧ PathWeightMultiplicationBoundaryClosed
    ∧ concretePreparedMeasuredKernelCarrier.carrier =
      closedTwoStepIntervalPoints concretePreparedMeasuredInterval
    ∧ concretePreparedMeasuredKernelCarrier.weight = 1
    ∧ twoRouteUpperKernelCarrier.weight = 1
    ∧ twoRouteLowerKernelCarrier.weight = 1
    ∧ causalBefore (P := concreteProcess)
      ⟨ConcreteState.prepared⟩ ⟨ConcreteState.measured⟩
    ∧ causalBefore (P := twoRouteProcess)
      ⟨TwoRouteState.source⟩ ⟨TwoRouteState.target⟩
    ∧ (∀ b : PendingBeyondS29, ClosedByStepwiseS29 b = false)
    ∧ WenConstructiveCoverage
```

---

## 〇一 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| displayed carrier | `DisplayedKernelPathCarrier` | 一个 finite `KernelPath` 可配一个 finite carrier list |
| endpoints | `start_mem`、`stop_mem` | carrier 明确包含路径端点 |
| readback | `DisplayedKernelPathCarrier.reachable`、`causal_before` | kernel path 可读回 S3 的 `Reachable` / `causalBefore` |
| weight | `DisplayedKernelPathCarrier.weight_eq_path_weight` | carrier 的 weight 只是底层 kernel path weight |
| path-local interval soundness | `SoundKernelTwoStepPathLocalIntervalCandidate.step_law` | 单条二步 kernel path 的 displayed middle 给出左右 step |
| path-local causal readback | `SoundKernelTwoStepPathLocalIntervalCandidate.causal_law` | 单条二步 kernel path 的 displayed middle 给出左右 causalBefore |
| concrete witness | `concretePreparedMeasuredKernelCarrier` | concrete carrier 等于 S28 closed interval points |
| two-route witnesses | `twoRouteUpperKernelCarrier`、`twoRouteLowerKernelCarrier` | upper/lower two-route path 各有 displayed carrier，权重均为 `1` |
| S29 summary | `finite_kernel_path_carrier_bridge_summary` | S29 接回 S28 interval 与 S19 path-weight boundary |

未纳入本轮：

| 项 | 原因 |
|---|---|
| global path enumeration | 本轮只附带 displayed carrier，不枚举所有 paths |
| arbitrary-length causal intervals | 没有证明任意端点的全路径区间或全局 finite interval |
| full causal set local finiteness | 没有全局 `{x | causalBefore a x ∧ causalBefore x b}` 枚举 |
| general path integral | carrier list 不是路径积分测度或所有路径求和 |
| Lorentzian geometry / metric recovery | 没有连续几何、光锥或度规恢复 |
| empirical closure | 没有数据、误差模型、阈值或可测预言 theorem |

本轮闭合范围：**finite KernelPath 的 displayed carrier / weight / causal readback interface**。

---

## 一 · 为什么这一步必要

S19 已经给出有限 kernel path 与权重乘法；S28 已经给出 displayed two-step causal interval。S29 把二者接起来：

```text
KernelPath
-> displayed carrier
-> S28 interval points
-> path weight
-> causalBefore
```

这让“路径上的有限载体”从解释文字变成 typed skeleton，但不把 displayed carrier 误读成全局因果区间。

本页还补了一个更窄的 path-local interval：

```text
left positive kernel edge + right positive kernel edge
-> carrier = [a, m, c]
-> step a m and step m c
-> causalBefore a m and causalBefore m c
```

这个接口只证明单条二步 kernel path 的 soundness；它不证明端点间只有这个 middle，也不证明 S28 式 complete interval。

---

## 二 · Validation Command

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityFiniteKernelPathCarrierBridge
lake build SSBX
python3 scripts/docs_next.py build --out docs-next/_generated --clean
python3 scripts/docs_next.py check --out docs-next/_generated --strict
git diff --check --
```

自审搜索：

```bash
rg -n "全局 path enumeration|arbitrary-length causal interval|full causal set local finiteness|path integral|Lorentzian geometry|metric recovery" formal/SSBX/Foundation/Modern formal/SSBX/notes 义理 docs-next/10_formal_形式/modern.md
```

---

## 三 · 下一步

S29 后续应拆成；第一步已由 S30 承接：

```text
displayed carrier
-> recursive carrier from KernelPath constructors
-> finite path family carriers
-> endpoint-indexed all-path enumeration
-> only then discuss global finite causal interval
```

S30 已给 `KernelPath` 本身定义 recursive point carrier，并证明它生成 canonical `DisplayedKernelPathCarrier`。再下一步应转向 endpoint-indexed finite carrier family 和 two-route toy completeness boundary。
