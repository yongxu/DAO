# 端点支撑规范化候选 · Markov桥S5i

**前置**：[Markov因果桥 · 大统一最小验证构造](Markov因果桥%20·%20大统一最小验证构造.md) · [双路径枚举候选 · Markov桥S5j](双路径枚举候选%20·%20Markov桥S5j.md) · [端点索引路径族候选 · Markov桥S5h](端点索引路径族候选%20·%20Markov桥S5h.md) · [有限路径族求和代数候选 · Markov桥S5g](有限路径族求和代数候选%20·%20Markov桥S5g.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| support filter | `Foundation/Modern/QuantumRelativityEndpointSupportNormalizationBridge.lean` | `filterEndpointIndexedTwoStepPathFamily` | `machineChecked` |
| filter completeness | `Foundation/Modern/QuantumRelativityEndpointSupportNormalizationBridge.lean` | `EndpointFamilyFilterComplete` | `machineChecked` typed skeleton |
| sum preservation | `Foundation/Modern/QuantumRelativityEndpointSupportNormalizationBridge.lean` | `endpoint_indexed_family_filter_sum_eq_of_removed_zero` | `machineChecked` |
| Born-shaped preservation | `Foundation/Modern/QuantumRelativityEndpointSupportNormalizationBridge.lean` | `endpoint_indexed_family_filter_born_weight_eq_of_removed_zero` | `machineChecked` |
| duplicate handling | `Foundation/Modern/QuantumRelativityEndpointSupportNormalizationBridge.lean` | `duplicateEndpointIndexedTwoStepPathFamily`、`endpoint_indexed_family_duplicate_sum` | `machineChecked` |
| duplicate cancellation | `Foundation/Modern/QuantumRelativityEndpointSupportNormalizationBridge.lean` | `endpoint_indexed_family_duplicate_cancels_of_canceling`、`endpoint_indexed_family_duplicate_born_weight_zero_of_canceling` | `machineChecked` |
| two-route normalized witness | `Foundation/Modern/QuantumRelativityEndpointSupportNormalizationBridge.lean` | `two_route_filtered_endpoint_family_amplitude_cancels`、`two_route_duplicated_endpoint_family_amplitude_cancels` | `machineChecked` |
| S5i 公开摘要 | `Foundation/Modern/QuantumRelativityEndpointSupportNormalizationBridge.lean` | `endpoint_support_normalization_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S5i 的主张：

```text
endpoint-indexed finite path family
+ finite Boolean support selector
+ removed paths have zero candidate amplitude
= support-filtered family with the same finite amplitude sum
```

同时，S5i 不把重复路径偷偷视为“已去重”。重复处理被显式写成：

```text
duplicate family amplitude sum = original sum + original sum
zero-sum family duplicated仍为 zero-sum
```

公开摘要为：

```lean
theorem endpoint_support_normalization_bridge_summary :
    (∀ {P : FiniteProcess} ...,
      endpointIndexedFamilyAmplitudeSum A
        (filterEndpointIndexedTwoStepPathFamily E keep) =
          endpointIndexedFamilyAmplitudeSum A E)
    ∧ ...
    ∧ (∀ {P : FiniteProcess} ...,
      endpointIndexedFamilyAmplitudeSum A
        (duplicateEndpointIndexedTwoStepPathFamily E) =
          endpointIndexedFamilyAmplitudeSum A E
            + endpointIndexedFamilyAmplitudeSum A E)
    ∧ ...
    ∧ WenConstructiveCoverage
```

该 theorem 已通过 `lake build SSBX.Foundation.Modern.QuantumRelativityEndpointSupportNormalizationBridge`。

---

## 〇一 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| finite filter | `filterEndpointIndexedTwoStepPathFamily` | 在保持 endpoint index 的前提下筛选有限路径列表 |
| filter completeness | `EndpointFamilyFilterComplete` | 被筛掉的路径候选振幅为 `0` |
| sum preservation | `endpoint_indexed_family_filter_sum_eq_of_removed_zero` | amplitude-complete filter 不改变候选振幅和 |
| Born-shaped preservation | `endpoint_indexed_family_filter_born_weight_eq_of_removed_zero` | 上述 filter 不改变 Born-shaped candidate weight |
| duplicate expansion | `endpoint_indexed_family_duplicate_sum` | 重复整个 family 会把候选振幅和变成 `sum + sum` |
| duplicate cancellation | `endpoint_indexed_family_duplicate_cancels_of_canceling` | 原 family 为零和时，重复 family 仍为零和 |
| two-route filter witness | `two_route_filtered_endpoint_family_amplitude_cancels` | two-route displayed filter 后仍相消 |
| two-route duplicate witness | `two_route_duplicated_endpoint_family_amplitude_cancels` | two-route duplicated family 仍相消 |
| 公开摘要 | `endpoint_support_normalization_bridge_summary` | 合取 filter preservation、duplicate handling 与 two-route witness |

后续结构：

| 轴 | 状态 | 说明 |
|---|---|---|
| quotient / true dedup | 后续结构 | S5i 显式计算重复贡献，不把重复路径商掉 |
| toy source/target enumeration | S5j 已关闭 | S5j 证明 twoRoute source/target two-step middle 必为 `upper` 或 `lower` |
| general all-path enumeration | 后续结构 | S5i/S5j 不生成任意过程、任意长度全部路径 |
| path integral | 后续结构 | 仍需要路径空间、测度、极限或 over-all-paths construction |
| continuous phase/action law | 后续结构 | 仍需连续相位、action functional 或 Hamiltonian/unitary law |
| Born rule derivation | 后续结构 | 仍只复用 `ampProb` boundary |
| empirical closure | 后续结构 | 需要 observation ledger 与数据判准 |

本轮闭合范围：**S5i 已在 Lean 中关闭“endpoint-indexed finite family -> amplitude-complete finite filter -> sum/weight preservation”与“duplicate expansion -> duplicate zero-sum cancellation”的候选接口。**

---

## 一 · 为什么这是规范化而不是路径积分

S5i 处理的是已经给出的有限列表：

```text
E.paths : List (EndpointTwoStepPath P E.endpoint)
```

filter theorem 的条件是：

```text
removed path -> amplitude = 0
```

因此它只证明有限支撑筛选的稳定性。它没有说所有物理路径都已经枚举，也没有给出连续路径测度。

---

## 二 · 重复项边界

重复项不是免费消失的。S5i 的 theorem 写成：

```lean
endpoint_indexed_family_duplicate_sum :
  sum (duplicate E) = sum E + sum E
```

这保证后续若要做真正去重或 quotient，必须新增路径身份、等价关系和权重补偿 theorem；不能靠文档语言把重复项抹掉。

---

## 三 · 下一步

S5i 后的直接增强 S5j 已关闭：

```text
twoRouteProcess
-> source/target two-step endpoint enumeration
-> every source-target two-step path is upper or lower
```

下一步应处理 finite path identity / quotient boundary，或转向 observation ledger。一般 all-path enumeration 或 path integral 仍不可提前写入 theorem。

---

## 四 · Validation Command

Lean 验证命令：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityEndpointSupportNormalizationBridge
lake build SSBX
```

文档与格式检查：

```bash
python3 scripts/docs_next.py build --out docs-next/_generated --clean
python3 scripts/docs_next.py check --out docs-next/_generated --strict
git diff --check --
```
