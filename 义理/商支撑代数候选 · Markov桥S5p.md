# 商支撑代数候选 · Markov桥S5p

**前置**：[Markov因果桥 · 大统一最小验证构造](Markov因果桥%20·%20大统一最小验证构造.md) · [商支撑枚举候选 · Markov桥S5o](商支撑枚举候选%20·%20Markov桥S5o.md) · [规范代表元候选 · Markov桥S5n](规范代表元候选%20·%20Markov桥S5n.md) · [观测账本候选 · Markov桥S5q](观测账本候选%20·%20Markov桥S5q.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| quotient support algebra | `Foundation/Modern/QuantumRelativityQuotientSupportAlgebraBridge.lean` | `appendQuotientSupports`、`reverseQuotientSupport`、`duplicateQuotientSupport` | `machineChecked` |
| append / perm / reverse | `Foundation/Modern/QuantumRelativityQuotientSupportAlgebraBridge.lean` | `quotient_support_amplitude_sum_append`、`quotient_support_amplitude_sum_perm`、`quotient_support_amplitude_sum_reverse` | `machineChecked` |
| duplicate cancellation | `Foundation/Modern/QuantumRelativityQuotientSupportAlgebraBridge.lean` | `quotient_support_duplicate_cancels_of_canceling`、`quotient_support_duplicate_born_weight_zero_of_canceling` | `machineChecked` |
| two-route algebra witness | `Foundation/Modern/QuantumRelativityQuotientSupportAlgebraBridge.lean` | `two_route_reversed_quotient_support_amplitude_cancels`、`two_route_double_quotient_support_amplitude_cancels` | `machineChecked` |
| S5p 公开摘要 | `Foundation/Modern/QuantumRelativityQuotientSupportAlgebraBridge.lean` | `quotient_support_algebra_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S5p 的主张：

```text
finite quotient support
-> append / permutation / reverse / duplicate algebra
-> cancellation stability
```

对 two-route toy quotient support：

```text
[upper class, lower class]
-> reverse still cancels
-> support ++ reverse support still cancels
-> Born-shaped weight remains 0
```

这不是一般 path integral，也不是真实干涉律；只关闭 quotient-support finite list algebra。

公开摘要为：

```lean
theorem quotient_support_algebra_bridge_summary :
    ...
    ∧ quotientSupportAmplitudeSum twoRouteKeyAmplitudeCandidate
      twoRouteReversedQuotientSupport = 0
    ∧ quotientSupportBornWeight twoRouteKeyAmplitudeCandidate
      twoRouteDoubleQuotientSupport = 0
    ∧ ...
```

该 theorem 已通过 `lake build SSBX.Foundation.Modern.QuantumRelativityQuotientSupportAlgebraBridge`。

---

## 〇一 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| append algebra | `quotient_support_amplitude_sum_append` | quotient-support sum 对 append 分配 |
| permutation stability | `quotient_support_amplitude_sum_perm` | quotient-support sum 在 list permutation 下不变 |
| reverse stability | `quotient_support_amplitude_sum_reverse` | reverse 不改变 quotient-support sum |
| duplicate cancellation | `quotient_support_duplicate_cancels_of_canceling` | 零和支撑 duplicate 后仍为零 |
| two-route reversed cancellation | `two_route_reversed_quotient_support_amplitude_cancels` | two-route support 反序后仍相消 |
| two-route double cancellation | `two_route_double_quotient_support_amplitude_cancels` | support append reversed support 后仍相消 |
| summary | `quotient_support_algebra_bridge_summary` | 合取 quotient-support algebra 与文构造覆盖 |

后续结构：

| 轴 | 状态 | 说明 |
|---|---|---|
| general all-path enumeration | 后续结构 | S5p 仍只处理 finite quotient-support list algebra |
| path integral | 后续结构 | 仍需要路径空间、测度、极限或 over-all-paths construction |
| continuous phase/action law | 后续结构 | 仍未给出连续作用量或动力学 |
| unitary / CPTP law | 后续结构 | 仍未证明真实 quantum channel dynamics |
| empirical closure | 后续结构 | 需要 observation ledger 与数据判准 |

本轮闭合范围：**S5p 已在 Lean 中关闭 quotient-support finite list algebra 与 two-route cancellation stability。**

---

## 一 · 失败记录

S5p 第一次目标构建失败：

```text
命令：lake build SSBX.Foundation.Modern.QuantumRelativityQuotientSupportAlgebraBridge
失败点：twoRouteReversedQuotientSupport / twoRouteDoubleQuotientSupport 的显式类型标注
原因：显式 `twoRouteProcess` 被 Lean 解析到不同 namespace 下的同名 process
修正：移除显式返回类型，让 Lean 从 `twoRouteSourceTargetQuotientEnumeration` 推断 process
结果：目标构建通过
```

该失败被保留，因为它说明 quotient support 后续若跨 namespace 组合，显式 process 名称需要谨慎。

---

## 二 · 下一步

S5p 的直接增强已由 S5q 承接：

```text
quotient-support algebra
-> observable ledger boundary
```

S5q 后仍可继续：

```text
observable ledger boundary
-> continuous phase/action law candidate
```

两条线都必须保持 machine-checked theorem 和失败记录。

---

## 三 · Validation Command

Lean 验证命令：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityQuotientSupportAlgebraBridge
```
