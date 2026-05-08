# 规范代表元候选 · Markov桥S5n

**前置**：[Markov因果桥 · 大统一最小验证构造](Markov因果桥%20·%20大统一最小验证构造.md) · [路径商类候选 · Markov桥S5m](路径商类候选%20·%20Markov桥S5m.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| representative predicate | `Foundation/Modern/QuantumRelativityCanonicalRepresentativeBridge.lean` | `CanonicalRepresentativeFor` | `machineChecked` |
| displayed representatives | `Foundation/Modern/QuantumRelativityCanonicalRepresentativeBridge.lean` | `two_route_upper_canonical_represents`、`two_route_lower_canonical_represents` | `machineChecked` |
| representative completeness | `Foundation/Modern/QuantumRelativityCanonicalRepresentativeBridge.lean` | `two_route_source_target_has_canonical_representative`、`two_route_source_target_canonical_representative_complete` | `machineChecked` |
| S5n 公开摘要 | `Foundation/Modern/QuantumRelativityCanonicalRepresentativeBridge.lean` | `canonical_representative_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S5n 的主张：

```text
two-route quotient class
-> represented by displayed upper or lower path
```

对任意 toy source/target two-step path：

```text
its quotient class has canonical representative upperPath or lowerPath
```

这不是一般选择函数；只关闭 two-route toy source/target quotient classes 的有限代表元边界。

公开摘要为：

```lean
theorem canonical_representative_bridge_summary :
    CanonicalRepresentativeFor
      (twoStepPathQuotientClass twoRouteUpperPath)
      twoRouteUpperPath
    ∧ ...
    ∧ TwoRouteSourceTargetCanonicalRepresentativeComplete
    ∧ ...
```

该 theorem 已通过 `lake build SSBX.Foundation.Modern.QuantumRelativityCanonicalRepresentativeBridge`。

---

## 〇一 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| representative predicate | `CanonicalRepresentativeFor` | witness 代表某个 quotient class |
| displayed upper/lower representatives | `two_route_upper_canonical_represents`、`two_route_lower_canonical_represents` | upper/lower paths 代表自身商类 |
| source/target completeness | `two_route_source_target_has_canonical_representative` | 任意 toy source/target path 的商类由 upper/lower 代表 |
| summary | `canonical_representative_bridge_summary` | 合取 displayed representatives、representative completeness 与 S5m quotient completeness |

后续结构：

| 轴 | 状态 | 说明 |
|---|---|---|
| general choice function | 后续结构 | S5n 不为任意 process 或任意 quotient class 选代表 |
| proof-field path equality | 后续结构 | S5n 不证明原 witness proof fields 相同 |
| general all-path enumeration | 后续结构 | S5n 仍只处理 two-route toy source/target two-step classes |
| path integral | 后续结构 | 仍需要路径空间、测度、极限或 over-all-paths construction |
| empirical closure | 后续结构 | 需要 observation ledger 与数据判准 |

本轮闭合范围：**S5n 已在 Lean 中关闭 two-route toy quotient classes 的 displayed canonical representative boundary。**

---

## 一 · 为什么这不是一般选择函数

S5n 只证明：

```text
source -> _ -> target in twoRouteProcess
-> quotient class is represented by upperPath or lowerPath
```

它不对任意有限过程、任意长度路径或任意商类构造选择函数。

---

## 二 · 下一步

S5n 后可以继续：

```text
displayed canonical representatives
-> finite quotient-support enumeration
-> observable ledger boundary
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
lake build SSBX.Foundation.Modern.QuantumRelativityCanonicalRepresentativeBridge
```
