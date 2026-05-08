# 有限路径族求和代数候选 · Markov桥S5g

**前置**：[Markov因果桥 · 大统一最小验证构造](Markov因果桥%20·%20大统一最小验证构造.md) · [端点支撑规范化候选 · Markov桥S5i](端点支撑规范化候选%20·%20Markov桥S5i.md) · [端点索引路径族候选 · Markov桥S5h](端点索引路径族候选%20·%20Markov桥S5h.md) · [有限路径族求和候选 · Markov桥S5f](有限路径族求和候选%20·%20Markov桥S5f.md) · [离散作用量相位候选 · Markov桥S5e](离散作用量相位候选%20·%20Markov桥S5e.md) · [双路径相消候选 · Markov桥S5c](双路径相消候选%20·%20Markov桥S5c.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| finite family append | `Foundation/Modern/QuantumRelativityFinitePathSumAlgebraBridge.lean` | `appendFiniteTwoStepPathFamilies` | `machineChecked` typed skeleton |
| finite family reverse | `Foundation/Modern/QuantumRelativityFinitePathSumAlgebraBridge.lean` | `reverseFiniteTwoStepPathFamily` | `machineChecked` typed skeleton |
| append sum law | `Foundation/Modern/QuantumRelativityFinitePathSumAlgebraBridge.lean` | `finite_path_family_amplitude_sum_append`、`finite_path_family_born_weight_append_boundary` | `machineChecked` |
| permutation stability | `Foundation/Modern/QuantumRelativityFinitePathSumAlgebraBridge.lean` | `finite_path_family_amplitude_sum_perm`、`finite_path_family_born_weight_perm` | `machineChecked` |
| reverse stability | `Foundation/Modern/QuantumRelativityFinitePathSumAlgebraBridge.lean` | `finite_path_family_amplitude_sum_reverse`、`finite_path_family_born_weight_reverse` | `machineChecked` |
| cancellation stability | `Foundation/Modern/QuantumRelativityFinitePathSumAlgebraBridge.lean` | `finite_path_family_append_cancels_of_canceling_summands` | `machineChecked` |
| two-route algebra witness | `Foundation/Modern/QuantumRelativityFinitePathSumAlgebraBridge.lean` | `two_route_reversed_family_amplitude_cancels`、`two_route_double_family_amplitude_cancels` | `machineChecked` |
| S5g 公开摘要 | `Foundation/Modern/QuantumRelativityFinitePathSumAlgebraBridge.lean` | `finite_path_sum_algebra_bridge_summary` | `machineChecked` |
| S5h 后续闭合 | `Foundation/Modern/QuantumRelativityEndpointIndexedPathFamilyBridge.lean` | `endpoint_indexed_path_family_bridge_summary` 关闭 endpoint-indexed conversion 与 sum preservation | `machineChecked` |
| S5i 后续闭合 | `Foundation/Modern/QuantumRelativityEndpointSupportNormalizationBridge.lean` | `endpoint_support_normalization_bridge_summary` 关闭 finite filter 与 duplicate boundary | `machineChecked` |

---

## 〇 · Claim Block

S5g 的主张：

```text
S5f finite same-endpoint path family
+ append operation with endpoint ledger
+ reverse operation
+ permutation-stable finite list sum
+ cancellation stability under append
= finite path-sum algebra candidate
```

正面结论是：

```text
S5g 已把 S5f 的 finite path-family sum
推进为有限 list 代数：
endpoint-compatible append 的振幅和等于两族振幅和之和；
路径族置换与反序不改变候选振幅和；
两个已经相消的 endpoint-compatible families 拼接后仍相消；
two-route witness 在反序与双拼接下仍接回 Born-shaped zero boundary。
```

公开摘要为：

```lean
theorem finite_path_sum_algebra_bridge_summary :
    (∀ {P : FiniteProcess} ...,
      finitePathFamilyAmplitudeSum A
        (appendFiniteTwoStepPathFamilies F G hStart hStop) =
          finitePathFamilyAmplitudeSum A F
            + finitePathFamilyAmplitudeSum A G)
    ∧ (∀ {P : FiniteProcess} ...,
      F.paths.Perm G.paths ->
        finitePathFamilyAmplitudeSum A F =
          finitePathFamilyAmplitudeSum A G)
    ∧ (∀ {P : FiniteProcess} ...,
      finitePathFamilyAmplitudeSum A (reverseFiniteTwoStepPathFamily F) =
        finitePathFamilyAmplitudeSum A F)
    ∧ ...
    ∧ finitePathFamilyAmplitudeSum
        (edgePhaseInducedTwoStepAmplitudeCandidate
          twoRouteDiscreteActionCandidate)
        twoRouteDoubleCancelingFamily = 0
    ∧ WenConstructiveCoverage
```

该 theorem 已通过 `lake build SSBX.Foundation.Modern.QuantumRelativityFinitePathSumAlgebraBridge`。

---

## 〇一 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| endpoint-compatible append | `appendFiniteTwoStepPathFamilies` | 两个同端点 ledger 的有限路径族可拼接成新路径族 |
| reverse family | `reverseFiniteTwoStepPathFamily` | 反序保留 endpoint ledger |
| append sum law | `finite_path_family_amplitude_sum_append` | 拼接族的候选振幅和等于两族振幅和之和 |
| append Born boundary | `finite_path_family_born_weight_append_boundary` | 拼接族的 Born-shaped weight 接到拼接后的有限和 |
| permutation stability | `finite_path_family_amplitude_sum_perm` | list permutation 不改变有限路径族候选振幅和 |
| permutation Born stability | `finite_path_family_born_weight_perm` | list permutation 不改变 Born-shaped candidate weight |
| reverse stability | `finite_path_family_amplitude_sum_reverse`、`finite_path_family_born_weight_reverse` | 反序不改变候选振幅和或 Born-shaped weight |
| cancellation stability | `finite_path_family_append_cancels_of_canceling_summands` | 两个已相消的 endpoint-compatible families 拼接后仍相消 |
| two-route reversed witness | `two_route_reversed_family_amplitude_cancels`、`two_route_reversed_family_born_weight_zero` | upper/lower 反序后仍相消 |
| two-route double witness | `two_route_double_family_amplitude_cancels`、`two_route_double_family_born_weight_zero` | 两个 two-route cancelled families 拼接后仍相消 |
| 公开摘要 | `finite_path_sum_algebra_bridge_summary` | 合取 append、perm、reverse 与 two-route cancellation stability |

后续结构：

| 轴 | 状态 | 说明 |
|---|---|---|
| arbitrary all-path enumeration | 后续结构 | S5g 只证明给定 finite list 的代数，不生成全部路径 |
| endpoint-indexed family construction | S5h 已关闭 | 已由 `endpoint_indexed_path_family_bridge_summary` 把同端点 ledger 推到 endpoint-indexed family |
| filter / duplicate normalization | S5i 已关闭有限候选接口 | 已由 `endpoint_support_normalization_bridge_summary` 证明 amplitude-complete filter preservation 与 duplicate expansion |
| quotient / true dedup | 后续结构 | S5i 显式计算重复贡献，尚未做路径等价商 |
| continuous phase/action law | 后续结构 | 仍需连续相位、action functional 或 Hamiltonian/unitary law |
| path integral | 后续结构 | 需要路径空间、测度、极限或 over-all-paths construction |
| Born rule derivation | 后续结构 | 仍只复用 `ampProb` boundary |
| empirical closure | 后续结构 | 需要 observation ledger 与数据判准 |

本轮闭合范围：**S5g 已在 Lean 中关闭“finite path-family sum -> append / permutation / reverse stability -> cancellation stability”的候选接口。**

---

## 一 · 为什么这一步比 S5f 更强

S5f 已经把 two-route pair 改写成 finite family：

```text
family = [upper, lower]
sum family amplitudes = 0
```

S5g 增加的是有限族自身的稳定代数：

```text
sum (F ++ G) = sum F + sum G
sum (permute F) = sum F
sum (reverse F) = sum F
sum F = 0 and sum G = 0 -> sum (F ++ G) = 0
```

因此，后续可以继续做 endpoint-indexed construction、filter、support normalization 或 all-path enumeration，而不会每次回到 two-path special case。

---

## 二 · 后续承接

S5g 后的直接增强 S5h 与 S5i 已关闭：

```text
finite path-sum algebra
-> endpoint-indexed family constructor
-> finite support filter / duplicate boundary
```

下一步应在 two-route toy process 上尝试 source/target two-step enumeration。一般 path integral、连续测度与经验可测干涉仍不应提前写入 theorem。

---

## 三 · Validation Command

Lean 验证命令：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityFinitePathSumAlgebraBridge
lake build SSBX
```

文档与格式检查：

```bash
python3 scripts/docs_next.py build --out docs-next/_generated --clean
python3 scripts/docs_next.py check --out docs-next/_generated --strict
git diff --check --
```
