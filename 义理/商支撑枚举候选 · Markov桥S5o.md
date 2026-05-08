# 商支撑枚举候选 · Markov桥S5o

**前置**：[Markov因果桥 · 大统一最小验证构造](Markov因果桥%20·%20大统一最小验证构造.md) · [规范代表元候选 · Markov桥S5n](规范代表元候选%20·%20Markov桥S5n.md) · [路径商类候选 · Markov桥S5m](路径商类候选%20·%20Markov桥S5m.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| quotient support sum | `Foundation/Modern/QuantumRelativityQuotientSupportBridge.lean` | `quotientSupportAmplitudeSum`、`quotientSupportBornWeight` | `machineChecked` |
| visible-key readback | `Foundation/Modern/QuantumRelativityQuotientSupportBridge.lean` | `quotientSupportVisibleKeys`、`two_route_quotient_support_visible_keys_eq` | `machineChecked` |
| support completeness | `Foundation/Modern/QuantumRelativityQuotientSupportBridge.lean` | `two_route_source_target_quotient_support_complete` | `machineChecked` |
| quotient support cancellation | `Foundation/Modern/QuantumRelativityQuotientSupportBridge.lean` | `two_route_quotient_support_amplitude_sum_cancels`、`two_route_quotient_support_born_weight_zero` | `machineChecked` |
| S5o 公开摘要 | `Foundation/Modern/QuantumRelativityQuotientSupportBridge.lean` | `quotient_support_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S5o 的主张：

```text
displayed quotient classes
-> finite quotient-support list
-> quotient-level amplitude sum
```

对 two-route toy source/target quotient support：

```text
[upper class, lower class]
-> visible keys [upper key, lower key]
-> amplitude sum 1 + (-1) = 0
-> Born-shaped weight 0
```

这不是一般 all-path enumeration，也不是 path integral；只关闭 two-route toy quotient support 的有限枚举与求和边界。

公开摘要为：

```lean
theorem quotient_support_bridge_summary :
    ...
    ∧ TwoRouteSourceTargetQuotientSupportComplete
    ∧ quotientSupportAmplitudeSum twoRouteKeyAmplitudeCandidate
      twoRouteSourceTargetQuotientEnumeration = 0
    ∧ quotientSupportBornWeight twoRouteKeyAmplitudeCandidate
      twoRouteSourceTargetQuotientEnumeration = 0
    ∧ ...
```

该 theorem 已通过 `lake build SSBX.Foundation.Modern.QuantumRelativityQuotientSupportBridge`。

---

## 〇一 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| quotient support sum | `quotientSupportAmplitudeSum` | 对 quotient class list 求有限候选振幅和 |
| quotient Born-shaped boundary | `quotientSupportBornWeight` | 对 quotient-support sum 接回 `ampProb` |
| visible-key readback | `quotientSupportVisibleKeys` | quotient support 可回读为 visible-key list |
| support representative classes | `two_route_quotient_support_representative_classes` | displayed representatives 的 classes 正是 source/target quotient support |
| support completeness | `two_route_source_target_quotient_support_complete` | 任意 toy source/target path 的 quotient class 在支撑 list 中 |
| quotient support cancellation | `two_route_quotient_support_amplitude_sum_cancels` | quotient-support 层仍有 `1 + (-1) = 0` |
| quotient support zero weight | `two_route_quotient_support_born_weight_zero` | cancelled quotient-support sum 的 Born-shaped weight 为 `0` |
| summary | `quotient_support_bridge_summary` | 合取 quotient support、readback、cancellation、representative completeness 与文构造覆盖 |

后续结构：

| 轴 | 状态 | 说明 |
|---|---|---|
| general all-path enumeration | 后续结构 | S5o 只处理 two-route toy source/target quotient support |
| general choice function | 后续结构 | S5o 复用 S5n 的 displayed reps，不为任意 quotient class 选代表 |
| quotient-level path integral | 后续结构 | 仍需要一般路径空间、测度、极限或 over-all-paths construction |
| continuous phase/action law | 后续结构 | 仍未给出连续作用量或动力学 |
| empirical closure | 后续结构 | 需要 observation ledger 与数据判准 |

本轮闭合范围：**S5o 已在 Lean 中关闭 two-route toy quotient support enumeration 与 quotient-level finite cancellation boundary。**

---

## 一 · 为什么这一步重要

S5n 给的是代表元：

```text
quotient class
-> represented by upperPath or lowerPath
```

S5o 把代表元推进成有限支撑：

```text
[upperPath, lowerPath]
-> [upper quotient class, lower quotient class]
-> finite quotient-support sum
```

这使相消不再只停留在 path list 或 key list，而可以在 quotient class support 上重写。

---

## 二 · 下一步

S5o 后可以继续：

```text
quotient support
-> quotient-support algebra
-> observable ledger boundary
```

该线已由 S5p/S5q 承接。再往后可以转向：

```text
observable ledger boundary
-> continuous phase/action law candidate
```

两条线都必须保持 machine-checked theorem 和失败记录。

---

## 三 · Validation Command

Lean 验证命令：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityQuotientSupportBridge
```
