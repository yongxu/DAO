# 双路径枚举候选 · Markov桥S5j

**前置**：[Markov因果桥 · 大统一最小验证构造](Markov因果桥%20·%20大统一最小验证构造.md) · [端点支撑规范化候选 · Markov桥S5i](端点支撑规范化候选%20·%20Markov桥S5i.md) · [端点索引路径族候选 · Markov桥S5h](端点索引路径族候选%20·%20Markov桥S5h.md) · [路径身份键候选 · Markov桥S5k](路径身份键候选%20·%20Markov桥S5k.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| middle list | `Foundation/Modern/QuantumRelativityTwoRouteEnumerationBridge.lean` | `endpointIndexedMiddleList`、`twoRouteSourceTargetMiddleEnumeration` | `machineChecked` |
| endpoint family middle list | `Foundation/Modern/QuantumRelativityTwoRouteEnumerationBridge.lean` | `two_route_endpoint_indexed_middle_list_eq` | `machineChecked` |
| source/target enumeration | `Foundation/Modern/QuantumRelativityTwoRouteEnumerationBridge.lean` | `two_route_source_target_middle_upper_or_lower` | `machineChecked` |
| family completeness | `Foundation/Modern/QuantumRelativityTwoRouteEnumerationBridge.lean` | `two_route_source_target_middle_mem_endpoint_family`、`two_route_source_target_middle_complete` | `machineChecked` |
| S5j 公开摘要 | `Foundation/Modern/QuantumRelativityTwoRouteEnumerationBridge.lean` | `two_route_enumeration_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S5j 的主张：

```text
twoRouteProcess source -> _ -> target two-step witness
= middle is upper or lower
```

这一步只枚举 toy process 的 source/target two-step middle state，不把它说成一般 all-path enumeration。

公开摘要为：

```lean
theorem two_route_enumeration_bridge_summary :
    endpointIndexedMiddleList twoRouteEndpointIndexedFamily =
      twoRouteSourceTargetMiddleEnumeration
    ∧ (∀ p : TwoStepPathWitness twoRouteProcess,
        p.start = TwoRouteState.source ->
          p.stop = TwoRouteState.target ->
            p.middle = TwoRouteState.upper
              ∨ p.middle = TwoRouteState.lower)
    ∧ TwoRouteSourceTargetMiddleComplete
    ∧ ...
    ∧ WenConstructiveCoverage
```

该 theorem 已通过 `lake build SSBX.Foundation.Modern.QuantumRelativityTwoRouteEnumerationBridge`。

---

## 〇一 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| displayed middle list | `twoRouteSourceTargetMiddleEnumeration` | toy source/target middle list 为 `[upper, lower]` |
| endpoint family list | `two_route_endpoint_indexed_middle_list_eq` | S5h endpoint-indexed family 的 middle list 正是 `[upper, lower]` |
| source/target exhaustion | `two_route_source_target_middle_upper_or_lower` | 任意 source/target two-step witness 的 middle 只能是 `upper` 或 `lower` |
| endpoint family completeness | `two_route_source_target_middle_mem_endpoint_family` | 任意 source/target two-step witness 的 middle 出现在 endpoint-indexed family 的 middle list 中 |
| summary | `two_route_enumeration_bridge_summary` | 合取 middle enumeration、family completeness 与 S5i cancellation boundary |

后续结构：

| 轴 | 状态 | 说明 |
|---|---|---|
| general all-path enumeration | 后续结构 | S5j 只枚举 `twoRouteProcess` 的 two-step source/target middle |
| visible path key | S5k 已关闭 | S5j 不证明 proof-field path equality；S5k 已补上 `(start,middle,stop)` key boundary |
| quotient construction | 后续结构 | S5j/S5k 仍不把 key 相同的 paths 商掉 |
| path integral | 后续结构 | 仍需要路径空间、测度、极限或 over-all-paths construction |
| continuous phase/action law | 后续结构 | 仍需连续相位、action functional 或 Hamiltonian/unitary law |
| empirical closure | 后续结构 | 需要 observation ledger 与数据判准 |

本轮闭合范围：**S5j 已在 Lean 中关闭 two-route toy process 的 source/target two-step middle enumeration。**

---

## 一 · 为什么这不是一般路径积分

S5j 的核心定理只使用四态 toy process 的 step relation：

```text
source -> upper -> target
source -> lower -> target
```

因此 theorem 的强度是：

```text
toy source/target two-step path has middle upper or lower
```

它没有生成任意长度路径，也没有定义路径空间测度。

---

## 二 · S5k 承接与下一步

S5j 的直接增强已由 S5k 承接：

```text
finite toy enumeration
-> visible path key
-> toy source/target key completeness
```

下一步可以继续尝试两条线：

```text
finite toy enumeration
-> finite quotient candidate
-> duplicate compensation theorem
```

或：

```text
finite toy enumeration
-> observed-candidate ledger
```

两条线都必须保持 machine-checked theorem 和失败记录。

---

## 三 · Validation Command

Lean 验证命令：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityTwoRouteEnumerationBridge
lake build SSBX
```

文档与格式检查：

```bash
python3 scripts/docs_next.py build --out docs-next/_generated --clean
python3 scripts/docs_next.py check --out docs-next/_generated --strict
git diff --check --
```
