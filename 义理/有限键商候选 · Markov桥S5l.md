# 有限键商候选 · Markov桥S5l

**前置**：[Markov因果桥 · 大统一最小验证构造](Markov因果桥%20·%20大统一最小验证构造.md) · [路径身份键候选 · Markov桥S5k](路径身份键候选%20·%20Markov桥S5k.md) · [双路径枚举候选 · Markov桥S5j](双路径枚举候选%20·%20Markov桥S5j.md) · [路径商类候选 · Markov桥S5m](路径商类候选%20·%20Markov桥S5m.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| key equivalence | `Foundation/Modern/QuantumRelativityFiniteKeyQuotientBridge.lean` | `TwoStepPathKeyEquivalent`、`two_step_path_key_equiv_refl`、`two_step_path_key_equiv_symm`、`two_step_path_key_equiv_trans` | `machineChecked` |
| key amplitude | `Foundation/Modern/QuantumRelativityFiniteKeyQuotientBridge.lean` | `TwoStepKeyAmplitudeCandidate`、`PathAmplitudeFactorsThroughKey`、`key_equivalent_paths_amplitude_eq` | `machineChecked` |
| key-list sum | `Foundation/Modern/QuantumRelativityFiniteKeyQuotientBridge.lean` | `endpointIndexedKeyList`、`twoStepKeyAmplitudeSum`、`endpoint_indexed_key_sum_eq_path_sum_of_factor` | `machineChecked` |
| duplicate compensation | `Foundation/Modern/QuantumRelativityFiniteKeyQuotientBridge.lean` | `two_step_key_amplitude_sum_duplicate`、`two_step_key_duplicate_born_weight_zero_of_canceling` | `machineChecked` |
| two-route key cancellation | `Foundation/Modern/QuantumRelativityFiniteKeyQuotientBridge.lean` | `two_route_key_amplitude_sum_cancels`、`two_route_key_born_weight_zero`、`two_route_duplicated_key_born_weight_zero` | `machineChecked` |
| S5l 公开摘要 | `Foundation/Modern/QuantumRelativityFiniteKeyQuotientBridge.lean` | `finite_key_quotient_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S5l 的主张：

```text
visible path key equality
-> quotient-candidate equivalence relation
-> key-compatible amplitudes are constant on that relation
-> finite key-list sums support duplicate compensation
```

对 two-route toy process：

```text
[upper key, lower key]
-> key amplitudes [1, -1]
-> key sum 0
-> Born-shaped key weight 0
```

这不是商类型构造；它只是把 S5k 的 visible key 推到“可降到 key 层”的有限候选边界。

公开摘要为：

```lean
theorem finite_key_quotient_bridge_summary :
    ...
    ∧ endpointIndexedKeyList twoRouteEndpointIndexedFamily =
      twoRouteSourceTargetKeyEnumeration
    ∧ twoStepKeyAmplitudeSum twoRouteKeyAmplitudeCandidate
      twoRouteSourceTargetKeyEnumeration = 0
    ∧ twoStepKeyBornWeight twoRouteKeyAmplitudeCandidate
      twoRouteSourceTargetKeyEnumeration = 0
    ∧ ...
```

该 theorem 已通过 `lake build SSBX.Foundation.Modern.QuantumRelativityFiniteKeyQuotientBridge`。

---

## 〇一 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| key equivalence | `TwoStepPathKeyEquivalent` | 以 visible key equality 作为 quotient candidate relation |
| equivalence laws | `two_step_path_key_equiv_refl`、`two_step_path_key_equiv_symm`、`two_step_path_key_equiv_trans` | 关系的自反、对称、传递已关闭 |
| key compatibility | `PathAmplitudeFactorsThroughKey`、`key_equivalent_paths_amplitude_eq` | 若振幅通过 key 分解，则同 key paths 振幅相同 |
| key-list sum | `endpoint_indexed_key_sum_eq_path_sum_of_factor` | key-compatible 时 endpoint path sum 等于 key-list sum |
| duplicate compensation | `two_step_key_amplitude_sum_duplicate`、`two_step_key_duplicate_born_weight_zero_of_canceling` | duplicate key list 显式给出 `sum + sum`，zero-sum duplicate 仍为零权重 |
| two-route witness | `two_route_key_amplitude_sum_cancels`、`two_route_key_born_weight_zero` | `[upper key, lower key]` 的 key-level sum 相消 |
| summary | `finite_key_quotient_bridge_summary` | 合取 quotient candidate relation、key compatibility 与 two-route key cancellation |

后续结构：

| 轴 | 状态 | 说明 |
|---|---|---|
| visible-key quotient class | S5m 已关闭 | S5l 不构造 Lean quotient class；S5m 已补上 `Setoid` / `Quot` construction |
| two-route canonical representative | S5n 已关闭 | S5n 已为 toy source/target quotient classes 给出 displayed representatives |
| finite quotient support | S5o 已关闭 | S5o 已把 displayed quotient classes 升级为 finite quotient-support list |
| quotient-support algebra | S5p 已关闭 | S5p 已证明 quotient-support append / permutation / reverse / duplicate stability |
| observable ledger boundary | S5q 已关闭 | S5q 已把 quotient-support cancellation 登记为 pending observable ledger entry |
| general choice function | 后续结构 | 仍未为任意 process 或任意 quotient class 选代表元 |
| proof-field path equality | 后续结构 | S5l 仍只看 visible `(start,middle,stop)` |
| general all-path enumeration | 后续结构 | S5l 仍只处理有限 key list 与 two-route toy witness |
| path integral | 后续结构 | 仍需要路径空间、测度、极限或 over-all-paths construction |
| empirical closure | 后续结构 | 需要 observation ledger 与数据判准 |

本轮闭合范围：**S5l 已在 Lean 中关闭 finite visible-key quotient candidate、key-compatible amplitude descent 与 two-route key-level cancellation。**

---

## 一 · 为什么这仍不是真正 quotient

S5l 证明的是：

```text
same visible key -> quotient candidate relation
factor-through-key amplitude -> same-key amplitude equality
```

它没有构造 `Quot`，也没有证明 `TwoStepPathWitness` 的 `leftStep/rightStep` proof fields 相同。这里的推进点是：若下一步要去重或压成商类，已经有可检查的兼容性条件与有限 key-sum 边界。

---

## 二 · S5m 承接与下一步

S5l 的直接增强已由 S5m 承接：

```text
finite visible-key quotient candidate
-> visible-key quotient class
-> quotient descent
```

后续已继续到：

```text
visible-key quotient class
-> displayed canonical representatives
-> finite quotient support
-> quotient-support algebra
-> observable ledger boundary
```

再往后可以转向：

```text
observable ledger boundary
-> continuous phase/action law candidate
```

两条线都必须保持 machine-checked theorem 和失败记录。

---

## 三 · Validation Command

Lean 验证命令：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityFiniteKeyQuotientBridge
```
