# 双路径递归载体族完备候选 · Markov桥S32

## 一 · 本轮闭合

| 层 | Lean 文件 | 入口 | 状态 |
|---|---|---|---|
| displayed family | `Foundation/Modern/QuantumRelativityTwoRouteDisplayedCarrierCompletenessBridge.lean` | `twoRouteDisplayedRecursiveCarrierFamily` | `machineChecked` |
| upper/lower membership | 同上 | `two_route_upper_recursive_carrier_mem_family`、`two_route_lower_recursive_carrier_mem_family` | `machineChecked` |
| displayed member cases | 同上 | `two_route_displayed_recursive_family_member_cases` | `machineChecked` |
| carrier cases | 同上 | `two_route_displayed_recursive_family_member_carrier_cases` | `machineChecked` |
| weight cases | 同上 | `two_route_displayed_recursive_family_member_weight_one` | `machineChecked` |
| S32 summary | 同上 | `two_route_displayed_carrier_completeness_bridge_summary` | `machineChecked` |

S32 只证明 toy displayed-family completeness：

```text
two-route endpoint-indexed recursive family
-> contains upper displayed recursive carrier
-> contains lower displayed recursive carrier
-> every displayed member is upper or lower
-> every displayed member has weight 1
```

这一步把 S31 的 family 从“给出一个列表”推进到“这个 displayed list 只有 upper/lower 两个 member”。

## 二 · 形式出口

Lean summary：

```lean
theorem two_route_displayed_carrier_completeness_bridge_summary :
    TwoRouteDisplayedRecursiveCarrierFamilyComplete
    ∧ EndpointIndexedRecursiveCarrierFamilyClosed
    ∧ TwoRouteEndpointIndexedRecursiveFamilyClosed
    ∧ twoRouteDisplayedRecursiveCarrierFamily =
      [twoRouteUpperRecursiveKernelCarrier,
        twoRouteLowerRecursiveKernelCarrier]
    ∧ (∀ C : DisplayedKernelPathCarrier twoRouteKernel
          TwoRouteState.source TwoRouteState.target,
        C ∈ twoRouteDisplayedRecursiveCarrierFamily ->
          C.weight = 1)
    ∧ (∀ b : PendingBeyondS32, ClosedByStepwiseS32 b = false)
    ∧ WenConstructiveCoverage
```

本轮已证明：

| 项 | theorem / def | 含义 |
|---|---|---|
| displayed list equality | `two_route_displayed_recursive_family_eq` | displayed family 等于 `[upper, lower]` |
| membership | `two_route_upper_recursive_carrier_mem_family` / `two_route_lower_recursive_carrier_mem_family` | upper/lower 均在 family 中 |
| member case split | `two_route_displayed_recursive_family_member_cases` | 任意 displayed member 是 upper 或 lower |
| carrier case split | `two_route_displayed_recursive_family_member_carrier_cases` | 任意 displayed member 的 carrier 是 upper carrier 或 lower carrier |
| weight law | `two_route_displayed_recursive_family_member_weight_one` | 任意 displayed member 权重为 `1` |

## 三 · 边界

S32 不是一般 all-path theorem：

| 未关闭项 | 边界 |
|---|---|
| arbitrary endpoint completeness | 只处理 two-route source/target displayed family |
| all KernelPath enumeration | 不证明所有 `KernelPath twoRouteKernel source target` inhabitant 都被枚举 |
| global path enumeration | 不处理任意 finite process 的所有 paths |
| arbitrary-length causal intervals | 不推出任意长度因果区间 |
| general path integral | displayed family list 不是积分测度 |
| Lorentzian geometry / metric recovery | 没有连续几何、光锥或度规恢复 |

## 四 · 验证

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityTwoRouteDisplayedCarrierCompletenessBridge
lake build SSBX
python3 scripts/docs_next.py build --out docs-next/_generated --clean
python3 scripts/docs_next.py check --out docs-next/_generated --strict
git diff --check --
```

自审搜索：

```bash
rg -n "all KernelPath enumeration|global path enumeration|arbitrary endpoint completeness|path integral|Lorentzian geometry|metric recovery" formal/SSBX/Foundation/Modern formal/SSBX/notes 义理 docs-next/10_formal_形式/modern.md
```

失败记录：

```text
日期：2026-05-09
目标：lake build SSBX.Foundation.Modern.QuantumRelativityTwoRouteDisplayedCarrierCompletenessBridge
失败类型：Lean proof failure
失败原因：upper/lower membership 只展开 displayed family 不足以化简到底层 list；同时 `causalBefore (P := ...)` 需要打开 Markov namespace。
保留结论：two-route displayed family completeness 可行，失败点是 namespace/unfolding 细节。
下一步：显式展开 endpoint-indexed family 与 recursive family，并补 `QuantumRelativityMarkovBridge` open。
```

## 五 · 后续

S33 已承接并关闭更强的 toy source/target `KernelPath` carrier enumeration：

```text
all KernelPath twoRouteKernel source target inhabitants reduce to upper/lower
```

见《双路径KernelPath枚举候选 · Markov桥S33》。S32 自身仍只读作 displayed family completeness；S33 才把任意同端点 `KernelPath` 的递归 carrier 也归约到 upper/lower。
