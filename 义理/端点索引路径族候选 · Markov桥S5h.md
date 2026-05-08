# 端点索引路径族候选 · Markov桥S5h

**前置**：[Markov因果桥 · 大统一最小验证构造](Markov因果桥%20·%20大统一最小验证构造.md) · [有限路径族求和代数候选 · Markov桥S5g](有限路径族求和代数候选%20·%20Markov桥S5g.md) · [有限路径族求和候选 · Markov桥S5f](有限路径族求和候选%20·%20Markov桥S5f.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| endpoint pair | `Foundation/Modern/QuantumRelativityEndpointIndexedPathFamilyBridge.lean` | `EndpointPair` | `machineChecked` typed skeleton |
| endpoint-indexed path | `Foundation/Modern/QuantumRelativityEndpointIndexedPathFamilyBridge.lean` | `EndpointTwoStepPath` | `machineChecked` typed skeleton |
| endpoint-indexed family | `Foundation/Modern/QuantumRelativityEndpointIndexedPathFamilyBridge.lean` | `EndpointIndexedTwoStepPathFamily`、`HasEndpointIndexedTwoStepPathFamily` | `machineChecked` |
| conversion | `Foundation/Modern/QuantumRelativityEndpointIndexedPathFamilyBridge.lean` | `endpointIndexedFamilyOfFinitePathFamily`、`finite_family_has_endpoint_indexed_family` | `machineChecked` |
| sum preservation | `Foundation/Modern/QuantumRelativityEndpointIndexedPathFamilyBridge.lean` | `endpoint_indexed_family_sum_of_finite_family` | `machineChecked` |
| Born-shaped preservation | `Foundation/Modern/QuantumRelativityEndpointIndexedPathFamilyBridge.lean` | `endpoint_indexed_family_born_weight_of_finite_family` | `machineChecked` |
| two-route endpoint witness | `Foundation/Modern/QuantumRelativityEndpointIndexedPathFamilyBridge.lean` | `two_route_endpoint_indexed_family_amplitude_cancels`、`two_route_endpoint_indexed_family_born_weight_zero` | `machineChecked` |
| S5h 公开摘要 | `Foundation/Modern/QuantumRelativityEndpointIndexedPathFamilyBridge.lean` | `endpoint_indexed_path_family_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S5h 的主张：

```text
S5f finite same-endpoint path family
+ S5g finite path-sum algebra
+ endpoint pair as an explicit family index
+ each path carries endpoint proofs in its endpoint-indexed type
= endpoint-indexed finite path family candidate
```

正面结论是：

```text
S5h 已把 S5f 的 same_start / same_stop ledger
收紧成 endpoint-indexed finite family。
从 S5f family 到 endpoint-indexed family 的转换
保持有限候选振幅和与 Born-shaped candidate weight；
two-route cancellation 在 endpoint-indexed 形式下仍为 0。
```

公开摘要为：

```lean
theorem endpoint_indexed_path_family_bridge_summary :
    (∀ {P : FiniteProcess} (_F : FiniteTwoStepPathFamily P),
      HasEndpointIndexedTwoStepPathFamily P)
    ∧ (∀ {P : FiniteProcess} ...,
      endpointIndexedFamilyAmplitudeSum A
        (endpointIndexedFamilyOfFinitePathFamily F) =
          finitePathFamilyAmplitudeSum A F)
    ∧ ...
    ∧ endpointIndexedFamilyAmplitudeSum
        (edgePhaseInducedTwoStepAmplitudeCandidate
          twoRouteDiscreteActionCandidate)
        twoRouteEndpointIndexedFamily = 0
    ∧ WenConstructiveCoverage
```

该 theorem 已通过 `lake build SSBX.Foundation.Modern.QuantumRelativityEndpointIndexedPathFamilyBridge`。

---

## 〇一 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| endpoint index | `EndpointPair` | 一个 finite process 中的外端点对 |
| endpoint-indexed path | `EndpointTwoStepPath` | two-step path 携带 start/stop 等于 endpoint index 的证明 |
| endpoint-indexed finite family | `EndpointIndexedTwoStepPathFamily` | family 的路径类型依赖同一个 endpoint pair |
| S5f 到 S5h 转换 | `endpointIndexedFamilyOfFinitePathFamily` | ledger-style family 可转换为 endpoint-indexed family |
| existence | `finite_family_has_endpoint_indexed_family` | 每个 S5f finite family 给出 endpoint-indexed family |
| sum preservation | `endpoint_indexed_family_sum_of_finite_family` | 转换后候选振幅和不变 |
| Born-shaped preservation | `endpoint_indexed_family_born_weight_of_finite_family` | 转换后 Born-shaped weight 不变 |
| two-route endpoint index | `two_route_endpoint_index` | two-route endpoint index 为 `source / target` |
| two-route cancellation | `two_route_endpoint_indexed_family_amplitude_cancels` | endpoint-indexed two-route family 仍相消 |
| two-route Born zero | `two_route_endpoint_indexed_family_born_weight_zero` | endpoint-indexed two-route family 仍接回 Born-shaped zero |
| 公开摘要 | `endpoint_indexed_path_family_bridge_summary` | 合取 endpoint-indexed conversion、sum preservation 与 two-route witness |

后续结构：

| 轴 | 状态 | 说明 |
|---|---|---|
| all-path enumeration | 后续结构 | S5h 只转换给定 finite family，不生成全部同端点路径 |
| filter / support normalization | 后续结构 | 尚未证明筛选、去重、支撑集或规范枚举 |
| path integral | 后续结构 | 需要路径空间、测度、极限或 over-all-paths construction |
| continuous phase/action law | 后续结构 | 仍需连续相位、action functional 或 Hamiltonian/unitary law |
| Born rule derivation | 后续结构 | 仍只复用 `ampProb` boundary |
| empirical closure | 后续结构 | 需要 observation ledger 与数据判准 |

本轮闭合范围：**S5h 已在 Lean 中关闭“same-endpoint finite family -> endpoint-indexed finite family -> sum/weight preservation -> endpoint-indexed two-route cancellation”的候选接口。**

---

## 一 · 为什么这一步比 S5g 更强

S5g 处理的是 list algebra：

```text
sum (F ++ G) = sum F + sum G
sum (reverse F) = sum F
sum (permute F) = sum F
```

S5h 处理的是路径族的索引形态：

```text
path : EndpointTwoStepPath P endpoint
```

也就是说，路径携带“属于这个端点对”的证明；后续做枚举、筛选或支撑集化时，不必反复把同端点条件作为外部 ledger 手动传递。

---

## 二 · 下一步

S5h 后最省力的增强是 S5i：

```text
endpoint-indexed finite family
-> finite support / filter normalization
-> duplicate handling boundary
```

这一步仍应保持有限结构，不提前声称 all-path enumeration、path integral 或真实干涉律。

---

## 三 · Validation Command

Lean 验证命令：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityEndpointIndexedPathFamilyBridge
lake build SSBX
```

文档与格式检查：

```bash
python3 scripts/docs_next.py build --out docs-next/_generated --clean
python3 scripts/docs_next.py check --out docs-next/_generated --strict
git diff --check --
```
