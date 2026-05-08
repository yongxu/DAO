# 路径商类候选 · Markov桥S5m

**前置**：[Markov因果桥 · 大统一最小验证构造](Markov因果桥%20·%20大统一最小验证构造.md) · [有限键商候选 · Markov桥S5l](有限键商候选%20·%20Markov桥S5l.md) · [路径身份键候选 · Markov桥S5k](路径身份键候选%20·%20Markov桥S5k.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| quotient setoid | `Foundation/Modern/QuantumRelativityPathQuotientBridge.lean` | `twoStepPathKeySetoid`、`TwoStepPathKeyQuotient` | `machineChecked` |
| quotient class | `Foundation/Modern/QuantumRelativityPathQuotientBridge.lean` | `twoStepPathQuotientClass`、`same_key_implies_same_quotient_class` | `machineChecked` |
| quotient descent | `Foundation/Modern/QuantumRelativityPathQuotientBridge.lean` | `quotientVisibleKey`、`quotientKeyAmplitude`、`quotient_key_amplitude_matches_path_of_factor` | `machineChecked` |
| two-route quotient | `Foundation/Modern/QuantumRelativityPathQuotientBridge.lean` | `two_route_upper_lower_quotient_classes_distinct`、`two_route_source_target_quotient_complete` | `machineChecked` |
| S5m 公开摘要 | `Foundation/Modern/QuantumRelativityPathQuotientBridge.lean` | `path_quotient_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S5m 的主张：

```text
TwoStepPathWitness
-> quotient by visible-key equality
-> visible key and key-amplitude descend to quotient classes
```

对 two-route toy process：

```text
upper quotient class != lower quotient class
source/target two-step path quotient class is in [upper class, lower class]
```

这是真正的 Lean quotient class 构造，但不是 proof-field path equality，也不是一般路径空间或路径积分。

公开摘要为：

```lean
theorem path_quotient_bridge_summary :
    ...
    ∧ twoStepPathQuotientClass twoRouteUpperPath ≠
      twoStepPathQuotientClass twoRouteLowerPath
    ∧ TwoRouteSourceTargetQuotientComplete
    ∧ ...
```

该 theorem 已通过 `lake build SSBX.Foundation.Modern.QuantumRelativityPathQuotientBridge`。

---

## 〇一 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| quotient setoid | `twoStepPathKeySetoid` | 把 visible-key equality 包装成 `Setoid` |
| quotient class | `TwoStepPathKeyQuotient`、`twoStepPathQuotientClass` | 构造 two-step witness 的 quotient class |
| key descent | `quotientVisibleKey`、`quotient_visible_key_mk` | visible key 可从 quotient class 读回 |
| amplitude descent | `quotientKeyAmplitude`、`quotient_key_amplitude_matches_path_of_factor` | key-compatible amplitude 可在 quotient class 上读 |
| route separation | `two_route_upper_lower_quotient_classes_distinct` | upper/lower quotient classes 不同 |
| quotient completeness | `two_route_source_target_quotient_complete` | toy source/target quotient enumeration complete |
| summary | `path_quotient_bridge_summary` | 合取 quotient class construction、descent 与 two-route quotient completeness |

后续结构：

| 轴 | 状态 | 说明 |
|---|---|---|
| proof-field path equality | 后续结构 | S5m 商掉 proof fields，但不证明原 witness proof fields 相等 |
| canonical representative | 后续结构 | 尚未为每个 quotient class 选代表元 |
| general all-path enumeration | 后续结构 | S5m 仍只处理 two-step witness 与 two-route toy enumeration |
| path integral | 后续结构 | 仍需要路径空间、测度、极限或 over-all-paths construction |
| empirical closure | 后续结构 | 需要 observation ledger 与数据判准 |

本轮闭合范围：**S5m 已在 Lean 中关闭 visible-key quotient class construction、quotient descent 与 two-route quotient completeness。**

---

## 一 · 这次比 S5l 多了什么

S5l 只证明 quotient candidate relation 与 key-compatible descent 条件。S5m 增加：

```text
Setoid
-> Quot
-> quotientVisibleKey
-> quotientKeyAmplitude
```

因此“有限键商候选”现在有真正的 Lean quotient class 出口，但仍不等于一般路径空间。

---

## 二 · 下一步

S5m 后可以继续：

```text
quotient class
-> canonical representative / finite support quotient enumeration
```

或者转向：

```text
quotient class
-> observable ledger boundary
```

两条线都必须保持 machine-checked theorem 和失败记录。

---

## 三 · Validation Command

Lean 验证命令：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityPathQuotientBridge
```
