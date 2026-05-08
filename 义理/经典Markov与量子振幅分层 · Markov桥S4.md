# 经典Markov与量子振幅分层 · Markov桥S4

**前置**：[Markov因果桥 · 大统一最小验证构造](Markov因果桥%20·%20大统一最小验证构造.md) · [有限概率核接口 · Markov桥S2](有限概率核接口%20·%20Markov桥S2.md) · [路径组合与因果约束 · Markov桥S3](路径组合与因果约束%20·%20Markov桥S3.md) · [干涉与测量律候选 · Markov桥S5](干涉与测量律候选%20·%20Markov桥S5.md) · [量子物理语言 · 从虚到测](量子物理语言%20·%20从虚到测.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| 分层标签 | `Foundation/Modern/QuantumRelativityAmplitudeChannelBridge.lean` | `BridgeLayerKind`、`finiteProbabilityKernelLayer`、`amplitudeSkeletonLayer`、`channelSkeletonLayer` | `machineChecked` |
| 非同层边界 | `Foundation/Modern/QuantumRelativityAmplitudeChannelBridge.lean` | `amplitude_layer_is_not_markov_kernel`、`channel_layer_is_not_markov_kernel` | `machineChecked` |
| 振幅候选接口 | `Foundation/Modern/QuantumRelativityAmplitudeChannelBridge.lean` | `QuantumAmplitudeSupport`、`QuantumAmplitudeSkeleton`、`HasQuantumAmplitudeProjection` | `machineChecked` typed skeleton |
| 通道候选接口 | `Foundation/Modern/QuantumRelativityAmplitudeChannelBridge.lean` | `QuantumChannelSkeleton`、`HasQuantumChannelCandidate` | `machineChecked` typed skeleton |
| 经典边界投影 | `Foundation/Modern/QuantumRelativityAmplitudeChannelBridge.lean` | `QuantumChannelSkeleton.toFiniteProbabilityKernel`、`channel_projection_keeps_markov_boundary` | `machineChecked` |
| 支持精化 | `Foundation/Modern/QuantumRelativityAmplitudeChannelBridge.lean` | `channel_amplitude_support_refines_classical`、`channel_amplitude_support_implies_step` | `machineChecked` |
| concrete/grid 候选 | `Foundation/Modern/QuantumRelativityAmplitudeChannelBridge.lean` | `concreteQuantumChannelSkeleton`、`operatorCellGridQuantumChannelSkeleton` | `machineChecked` |
| S4 公开摘要 | `Foundation/Modern/QuantumRelativityAmplitudeChannelBridge.lean` | `amplitude_channel_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S4 的主张很窄：

```text
已有 Markov / 因果桥
+ S2 finite denominator boundary
+ S3 path witness / local causal boundary
+ 独立 amplitude skeleton
+ channel skeleton carrying the classical boundary
+ theorem 标记 classical Markov layer ≠ quantum amplitude/channel layer
= classical Markov / quantum amplitude-channel layered interface candidate
```

它不证明 Born rule，不证明干涉，不证明 unitary evolution，不证明 CPTP quantum channel law，不证明量子引力或经验闭合。

公开摘要为：

```lean
theorem amplitude_channel_bridge_summary :
    HasFiniteProbabilityProjection concreteProcess
    ∧ HasQuantumAmplitudeProjection concreteProcess
    ∧ HasQuantumChannelCandidate concreteProcess
    ∧ HasFiniteProbabilityProjection operatorCellGridProcess
    ∧ HasQuantumAmplitudeProjection operatorCellGridProcess
    ∧ HasQuantumChannelCandidate operatorCellGridProcess
    ∧ amplitudeSkeletonLayer ≠ finiteProbabilityKernelLayer
    ∧ channelSkeletonLayer ≠ finiteProbabilityKernelLayer
    ∧ ...
    ∧ WenConstructiveCoverage
```

该 theorem 已通过 `lake build SSBX.Foundation.Modern.QuantumRelativityAmplitudeChannelBridge`。

---

## 〇一 · 边界声明

| 说法 | 本文状态 | 精确含义 |
|---|---|---|
| 经典 Markov 层与振幅层不同 | `machineChecked` | `amplitude_layer_is_not_markov_kernel` 只证明 layer tag 非同一 |
| 经典 Markov 层与通道层不同 | `machineChecked` | `channel_layer_is_not_markov_kernel` 只证明 layer tag 非同一 |
| 振幅候选可存在 | `machineChecked` typed skeleton | 目前只要求非零振幅支持 process step |
| 通道候选可存在 | `machineChecked` typed skeleton | 目前只携带 amplitude layer 与 S2 classical boundary |
| 通道候选保留经典边界 | `machineChecked` | `channel_projection_keeps_markov_boundary` 给出 S2 有限概率核投影 |
| 非零振幅精化经典支持 | `machineChecked` | `channel_amplitude_support_refines_classical` 与 `channel_amplitude_support_implies_step` |
| concrete/grid 最小候选 | `machineChecked` | 使用 zero amplitude placeholder，避免偷渡物理通道律 |
| one-qubit computational-basis Born fact | `machineChecked` reused | 只复用 `Quantum.lean` 中已有 theorem，不由 Markov 桥推出 |
| Born rule derivation from Markov bridge | 未纳入本轮 | S4 不从 Markov 权重推出振幅平方律 |
| interference / phase cancellation | S4 未纳入；S5 已开候选接口 | 见《干涉与测量律候选 · Markov桥S5》；真实干涉律仍未纳入 |
| unitary evolution / CPTP channel law | 未纳入本轮 | 没有 Kraus、density matrix、trace preservation 或 complete positivity |
| quantum gravity / empirical closure | 未纳入本轮 | 没有动力学、几何恢复、观测量 ledger 或数据判准 |

边界句：

```text
S4 关闭的是 layer separation 与 support refinement；
它打开量子振幅 / 通道候选接口，
但不把经典 Markov 权重解释成 Born 概率。
```

---

## 〇二 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| 分层枚举 | `BridgeLayerKind` | 明确 classical Markov、quantum amplitude、quantum channel 三层 |
| Markov 与 amplitude 非同一 | `amplitude_layer_is_not_markov_kernel` | 形式层面不把复幅候选等同经典有限概率核 |
| Markov 与 channel 非同一 | `channel_layer_is_not_markov_kernel` | 形式层面不把通道候选等同经典有限概率核 |
| 振幅支持 | `QuantumAmplitudeSupport` | 非零复幅作为支持谓词 |
| 振幅骨架 | `QuantumAmplitudeSkeleton` | 非零振幅必须尊重 `FiniteProcess.step` |
| 通道骨架 | `QuantumChannelSkeleton` | 通道候选携带 amplitude layer 与 S2 classical boundary |
| 经典边界保持 | `channel_projection_keeps_markov_boundary` | 通道候选可投影回 finite probability-kernel boundary |
| 支持精化 | `channel_amplitude_support_refines_classical` | 非零振幅先精化到 classical support |
| step 精化 | `channel_amplitude_support_implies_step` | 非零振幅最终尊重 process step |
| concrete/grid 候选 | `concreteQuantumChannelSkeleton`、`operatorCellGridQuantumChannelSkeleton` | S1/S2/S3 witness 可承载 S4 候选接口 |
| 公开摘要 | `amplitude_channel_bridge_summary` | 合取 concrete、grid、layer separation、support refinement、既有 Born fact 与 Wen coverage |

未纳入本轮：

| 轴 | 状态 | 说明 |
|---|---|---|
| 非零物理振幅 | 未纳入本轮 | 当前 concrete/grid 候选使用 zero amplitude placeholder |
| 干涉候选 | S4 未纳入；S5 已开单独接口 | S5 记录 path amplitude candidate、相消 witness 与 Born-shaped boundary |
| 真实干涉律 | 未纳入本轮 | 没有非零路径动力学、路径求和、相位演化或可测相消 |
| Markov 到 Born 的推导 | 未纳入本轮 | S4 只复用 `Quantum.lean` 的 one-qubit theorem，不从桥推出 Born rule |
| unitary / CPTP | 未纳入本轮 | 尚无 Hilbert-space operator law、Kraus representation、trace preservation |
| 真实 quantum channel | 未纳入本轮 | `QuantumChannelSkeleton` 是 candidate interface，不是物理通道定理 |
| 几何与经验闭合 | 未纳入本轮 | 没有度规恢复、动力学方程或实验数据接口 |

本轮闭合范围：**S4 已在 Lean 中关闭 classical Markov layer 与 quantum amplitude/channel candidate layer 的分层边界，并证明 channel candidate 保留 S2 classical finite-probability boundary；它不关闭 Born rule 推导、干涉、unitary evolution、CPTP channel law、量子引力、几何恢复或经验闭合。**

---

## 一 · 为什么要分层

S2 的 `FiniteProbabilityKernelSkeleton` 只给出：

```text
support / weight / rowTotal / denominator boundary
```

这仍是 classical Markov 读法。若直接把它叫做 quantum channel，就会把“有限权重”偷换成“复振幅演化”或“量子测量律”。S4 因此先做一个很小的动作：给旧层和新层各自打 tag，并证明 tag 不同。

```lean
theorem amplitude_layer_is_not_markov_kernel :
    amplitudeSkeletonLayer ≠ finiteProbabilityKernelLayer

theorem channel_layer_is_not_markov_kernel :
    channelSkeletonLayer ≠ finiteProbabilityKernelLayer
```

这不是深物理定理，但它是后续不偷换概念的形式护栏。

---

## 二 · 支持精化

S4 的 channel candidate 不声称有真实量子通道律。它只规定：

```text
nonzero amplitude
-> carried classical support
-> process step
```

对应 Lean theorem 是：

```lean
theorem channel_amplitude_support_refines_classical ...
theorem channel_amplitude_support_implies_step ...
```

这个方向很弱，但足以记录“振幅候选不能跑出当前过程边界”。如果下一步要加入干涉或 unitary law，应该在这个接口之上加结构，而不是重写 S2/S3 的 Markov/causal boundary。

---

## 三 · zero placeholder 的意义

concrete 与 `71232` grid 当前使用 zero amplitude skeleton：

```text
all amplitudes = 0
```

这让 S4 可以先证明接口存在、分层不混淆、classical boundary 可投影，而不提前伪造非平凡量子动力学。它是保守占位，不是物理模型。

---

## 四 · 与既有 Quantum.lean 的关系

S4 的公开摘要合取了 `Quantum.lean` 中已有的 one-qubit computational-basis theorem：

```lean
computational_basis_born_rule
```

这只表示仓库中已有一个局部 Born-rule-shaped theorem 可被并列记录。S4 不从 Markov bridge 推导该 theorem，也不把 S2 finite denominator 解释成振幅平方。

---

## 五 · Validation Command

Lean 验证命令：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityAmplitudeChannelBridge
lake build SSBX
```

文档与格式检查：

```bash
git diff --check -- formal/SSBX/Foundation/Modern/QuantumRelativityAmplitudeChannelBridge.lean formal/SSBX/Foundation/Modern/QuantumRelativityInterferenceBridge.lean formal/SSBX.lean formal/SSBX/notes/unification-stepwise-plan.md formal/SSBX/notes/markov-causal-bridge-verification-plan.md formal/SSBX/notes/markov-causal-bridge-plan.md docs-next/10_formal_形式/modern.md '义理/经典Markov与量子振幅分层 · Markov桥S4.md' '义理/干涉与测量律候选 · Markov桥S5.md' '义理/Markov因果桥 · 大统一最小验证构造.md' '义理/有限概率核接口 · Markov桥S2.md' '义理/路径组合与因果约束 · Markov桥S3.md'
```
