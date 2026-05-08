# 有限路径族求和候选 · Markov桥S5f

**前置**：[Markov因果桥 · 大统一最小验证构造](Markov因果桥%20·%20大统一最小验证构造.md) · [离散作用量相位候选 · Markov桥S5e](离散作用量相位候选%20·%20Markov桥S5e.md) · [离散相位标记候选 · Markov桥S5d](离散相位标记候选%20·%20Markov桥S5d.md) · [双路径相消候选 · Markov桥S5c](双路径相消候选%20·%20Markov桥S5c.md) · [非零路径振幅候选 · Markov桥S5b](非零路径振幅候选%20·%20Markov桥S5b.md) · [干涉与测量律候选 · Markov桥S5](干涉与测量律候选%20·%20Markov桥S5.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| finite path family | `Foundation/Modern/QuantumRelativityFinitePathSumBridge.lean` | `FiniteTwoStepPathFamily`、`HasFiniteTwoStepPathFamily` | `machineChecked` typed skeleton |
| finite amplitude sum | `Foundation/Modern/QuantumRelativityFinitePathSumBridge.lean` | `finitePathFamilyAmplitudeSum` | `machineChecked` |
| Born-shaped finite-family weight | `Foundation/Modern/QuantumRelativityFinitePathSumBridge.lean` | `finitePathFamilyBornWeight`、`finite_path_family_born_boundary` | `machineChecked` |
| two-route family witness | `Foundation/Modern/QuantumRelativityFinitePathSumBridge.lean` | `twoRouteUpperLowerFamily`、`two_route_family_paths_share_endpoints` | `machineChecked` |
| pair-sum compatibility | `Foundation/Modern/QuantumRelativityFinitePathSumBridge.lean` | `two_route_family_sum_eq_pair_sum` | `machineChecked` |
| finite-family cancellation | `Foundation/Modern/QuantumRelativityFinitePathSumBridge.lean` | `two_route_finite_family_amplitude_cancels`、`two_route_finite_family_born_weight_zero` | `machineChecked` |
| S5f 公开摘要 | `Foundation/Modern/QuantumRelativityFinitePathSumBridge.lean` | `finite_path_sum_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S5f 的主张：

```text
S5e edge-action-induced amplitudes
+ finite same-endpoint path family
+ finite list sum over candidate path amplitudes
+ two-route upper/lower family as length-2 instance
= finite path-family sum candidate
```

正面结论是：

```text
S5f 已把 S5c/S5e 的 two-path sum
推进为有限路径族求和接口。
two-route upper/lower pair 现在只是一个 finite family instance；
该 family sum 与原 two-path pair sum 相等，
因此仍为 0，并接回 Born-shaped zero boundary。
```

公开摘要为：

```lean
theorem finite_path_sum_bridge_summary :
    HasFiniteTwoStepPathFamily twoRouteProcess
    ∧ HasTwoStepEdgePhaseCandidate twoRouteProcess
    ∧ twoRouteUpperLowerFamily.endpointStart = TwoRouteState.source
    ∧ twoRouteUpperLowerFamily.endpointStop = TwoRouteState.target
    ∧ ...
    ∧ finitePathFamilyAmplitudeSum
        (edgePhaseInducedTwoStepAmplitudeCandidate
          twoRouteDiscreteActionCandidate)
        twoRouteUpperLowerFamily = 0
    ∧ finitePathFamilyBornWeight
        (edgePhaseInducedTwoStepAmplitudeCandidate
          twoRouteDiscreteActionCandidate)
        twoRouteUpperLowerFamily = 0
    ∧ WenConstructiveCoverage
```

该 theorem 已通过 `lake build SSBX.Foundation.Modern.QuantumRelativityFinitePathSumBridge`。

---

## 〇一 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| finite path family | `FiniteTwoStepPathFamily` | 有限 list 形式的 same-endpoint two-step path family |
| endpoint ledger | `same_start`、`same_stop` | family 中每条 path 共享外端点 |
| finite amplitude sum | `finitePathFamilyAmplitudeSum` | 对 family 的候选振幅作有限 list sum |
| Born-shaped weight | `finitePathFamilyBornWeight` | family sum 接回 `ampProb` boundary |
| two-route family | `twoRouteUpperLowerFamily` | upper/lower 两条路组成长度为 2 的 finite family |
| endpoint check | `two_route_family_paths_share_endpoints` | two-route family 中每条 path 同起点同终点 |
| pair compatibility | `two_route_family_sum_eq_pair_sum` | finite family sum 等于 S5c/S5e 的 pair sum |
| finite-family cancellation | `two_route_finite_family_amplitude_cancels` | two-route family sum 为 `0` |
| Born-shaped zero | `two_route_finite_family_born_weight_zero` | 相消后 finite-family weight 为 `0` |
| 公开摘要 | `finite_path_sum_bridge_summary` | 合取 finite family、edge-action candidate、cancellation 与 Wen coverage |

后续结构：

| 轴 | 状态 | 说明 |
|---|---|---|
| arbitrary same-endpoint path enumeration | 后续结构 | S5f 给出 finite list interface，但未生成所有路径 |
| algebraic laws of finite sums | 后续结构 | 可继续证明 append、permutation、filter 等求和性质 |
| continuous phase/action law | 后续结构 | 仍需连续相位、action functional 或 Hamiltonian/unitary law |
| path integral | 后续结构 | 需要路径空间、测度、极限或 over-all-paths construction |
| Born rule derivation | 后续结构 | 仍只复用 `ampProb` boundary |
| empirical closure | 后续结构 | 需要 observation ledger 与数据判准 |

本轮闭合范围：**S5f 已在 Lean 中关闭“finite same-endpoint path family -> finite amplitude sum -> two-route family cancellation -> Born-shaped zero weight”的候选接口。**

---

## 一 · 为什么这一步比 S5e 更强

S5e 仍然直接围绕 upper/lower 两条路径：

```text
upper amplitude + lower amplitude = 0
```

S5f 把这件事改写成一个有限族求和：

```text
family = [upper, lower]
sum family amplitudes = pair sum = 0
```

因此，下一步可以不再只写死 two-path pair，而是扩展到任意有限 list 的路径族、筛选规则、重复路径处理或端点约束。

---

## 二 · 下一步

S5f 后最省力的增强是 S5g：

```text
finite path family
-> endpoint-indexed finite family
-> append / permutation / cancellation stability
```

这仍然保持有限结构。连续 path integral 只有在有限族代数稳定后再进入。

---

## 三 · Validation Command

Lean 验证命令：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityFinitePathSumBridge
lake build SSBX
```

文档与格式检查：

```bash
python3 scripts/docs_next.py build --out docs-next/_generated --clean
python3 scripts/docs_next.py check --out docs-next/_generated --strict
git diff --check --
```
