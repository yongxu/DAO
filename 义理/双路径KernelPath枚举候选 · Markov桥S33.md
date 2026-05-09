# 双路径KernelPath枚举候选 · Markov桥S33

**前置**：[端点索引递归载体族候选 · Markov桥S31](端点索引递归载体族候选%20·%20Markov桥S31.md) · [双路径递归载体族完备候选 · Markov桥S32](双路径递归载体族完备候选%20·%20Markov桥S32.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

## 一 · 本轮闭合

| 层 | Lean 文件 | 入口 | 状态 |
|---|---|---|---|
| positive edge cases | `Foundation/Modern/QuantumRelativityTwoRouteKernelPathEnumerationBridge.lean` | `two_route_positive_edge_cases` | `machineChecked` |
| source-started targets | 同上 | `two_route_kernel_path_source_targets`、`two_route_kernel_path_source_upper_targets`、`two_route_kernel_path_source_lower_targets`、`two_route_kernel_path_source_target_targets_cases` | `machineChecked` |
| source/target carrier cases | 同上 | `two_route_kernel_path_source_target_points_cases` | `machineChecked` |
| source/target weight | 同上 | `two_route_kernel_path_source_target_weight_one` | `machineChecked` |
| displayed-family readback | 同上 | `two_route_kernel_path_source_target_matches_displayed_family` | `machineChecked` |
| S33 summary | 同上 | `two_route_kernel_path_enumeration_bridge_summary` | `machineChecked` |

S33 证明的是 toy `twoRouteKernel` 的 source/target `KernelPath` carrier normal form：

```lean
theorem two_route_kernel_path_source_target_points_cases
    (p : KernelPath twoRouteKernel
      TwoRouteState.source TwoRouteState.target) :
    kernelPathPoints p =
        [TwoRouteState.source, TwoRouteState.upper, TwoRouteState.target]
      ∨ kernelPathPoints p =
        [TwoRouteState.source, TwoRouteState.lower, TwoRouteState.target]
```

这一步比 S32 强：S32 只证明 displayed family 的成员是 upper/lower；S33 证明任意同端点 `KernelPath` 的递归 carrier 也只能落到 upper/lower 两条 carrier。

## 二 · 形式出口

Lean summary：

```lean
theorem two_route_kernel_path_enumeration_bridge_summary :
    TwoRouteKernelPathEnumerationComplete
    ∧ TwoRouteDisplayedRecursiveCarrierFamilyComplete
    ∧ EndpointIndexedRecursiveCarrierFamilyClosed
    ∧ TwoRouteEndpointIndexedRecursiveFamilyClosed
    ∧ (∀ p : KernelPath twoRouteKernel
          TwoRouteState.source TwoRouteState.target,
        KernelPath.weight p = 1)
    ∧ (∀ b : PendingBeyondS33, ClosedByStepwiseS33 b = false)
    ∧ WenConstructiveCoverage
```

本轮已证明：

| 项 | theorem / def | 含义 |
|---|---|---|
| edge classification | `two_route_positive_edge_cases` | 正权边只可能是 `source -> upper`、`source -> lower`、`upper -> target`、`lower -> target` |
| no incoming source | `two_route_no_positive_edge_to_source` | 没有正权边进入 `source` |
| no outgoing target | `two_route_no_positive_edge_from_target` | 没有正权边从 `target` 出发 |
| source/target carrier normal form | `two_route_kernel_path_source_target_points_cases` | 任意 `KernelPath source target` 的 `kernelPathPoints` 只能是 upper route 或 lower route |
| source/target weight | `two_route_kernel_path_source_target_weight_one` | 任意 source/target `KernelPath` 的权重为 `1` |
| displayed-family readback | `two_route_kernel_path_source_target_matches_displayed_family` | 任意 source/target recursive carrier 可读回 S32 displayed carrier family 的 carrier list |

## 三 · 边界

S33 是 toy all-`KernelPath` carrier enumeration，不是一般 all-path theorem：

| 未关闭项 | 边界 |
|---|---|
| arbitrary endpoint completeness | 只处理 `twoRouteKernel source target` |
| arbitrary finite process enumeration | 不枚举任意有限过程的所有 `KernelPath` |
| global path enumeration | 不处理全局 path space |
| arbitrary-length causal intervals | twoRoute 的高度被具体边分类限制，不推出一般任意长度区间 |
| general path integral | carrier enumeration 不是积分测度或极限过程 |
| Lorentzian geometry / metric recovery | 没有连续几何、光锥或度规恢复 |
| empirical closure | 没有实验数据、观测模型或可测预言 theorem |

## 四 · 验证

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityTwoRouteKernelPathEnumerationBridge
lake build SSBX
python3 scripts/docs_next.py build --out docs-next/_generated --clean
python3 scripts/docs_next.py check --out docs-next/_generated --strict
git diff --check --
```

自审搜索：

```bash
rg -n "general all-path enumeration|path integral|arbitrary endpoint completeness|Lorentzian geometry|metric recovery" formal/SSBX/Foundation/Modern formal/SSBX/notes 义理 docs-next/10_formal_形式/modern.md
```

失败记录：

```text
日期：2026-05-09
目标：证明 source-started KernelPath normal form
失败类型：Lean indexed-inductive proof/termination friction
失败原因：直接写递归 theorem `{b} -> KernelPath source b -> match b with ...` 时，termination checker 难以看出 `snoc` 前缀路径严格变小；直接 `induction/cases p` 在固定 index 上也触发 indexed motive 错误。
保留结论：目标可证，失败点不是数学障碍，而是 indexed-inductive 消去方式。
修正方式：改为 endpoint-specific equation proofs：先 source/source，再 source/upper 与 source/lower，最后 source/target；由 twoRoute 正权边分类逐层排除所有其他构造。
```

## 五 · 下一步

S33 支撑的下一步是 toy path-sum / support boundary：

```text
all KernelPath source target carrier enumeration
-> support contains exactly upper/lower carriers
-> path-sum over recursive carrier family agrees with displayed two-route sum
-> Born-shaped zero boundary can use all-KernelPath support, not only hand-displayed support
```

这仍然只是 twoRoute toy witness。若要从这里走向一般 theorem，需要额外证明有限无环过程的 rank/height、正权边 support finite、以及 endpoint-indexed all-path recursion 的终止性。
