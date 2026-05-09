# 递归核路径载体候选 · Markov桥S30

## 一 · 本轮闭合

| 层 | Lean 文件 | 入口 | 状态 |
|---|---|---|---|
| recursive targets | `Foundation/Modern/QuantumRelativityKernelPathRecursiveCarrierBridge.lean` | `kernelPathTargets` | `machineChecked` |
| recursive points | 同上 | `kernelPathPoints`、`kernelPath_start_mem`、`kernelPath_stop_mem` | `machineChecked` |
| append readback | 同上 | `kernelPathTargets_append`、`kernelPathPoints_append` | `machineChecked` |
| recursive carrier | 同上 | `recursiveKernelPathCarrier`、`recursive_kernel_path_carrier_closed` | `machineChecked` |
| finite carrier family | 同上 | `twoRouteRecursiveKernelCarrierFamily`、`finite_recursive_kernel_carrier_family_closed` | `machineChecked` |
| S30 summary | 同上 | `kernel_path_recursive_carrier_bridge_summary` | `machineChecked` |

S30 把 S29 的 displayed carrier 推进一步：

```text
finite KernelPath constructors
-> recursive target list
-> recursive point carrier
-> endpoints are in the carrier
-> append carrier law
-> finite two-route recursive carrier family
```

关键变化是：carrier 不再只是外加 displayed list，而是可由 `KernelPath.refl` / `KernelPath.snoc` 递归生成。

## 二 · 形式出口

Lean summary：

```lean
theorem kernel_path_recursive_carrier_bridge_summary :
    RecursiveKernelPathCarrierClosed
    ∧ KernelPathAppendCarrierClosed
    ∧ FiniteRecursiveKernelCarrierFamilyClosed
    ∧ FiniteKernelPathCarrierClosed
    ∧ KernelPathLocalIntervalSoundClosed
    ∧ concreteRecursiveKernelCarrier.carrier =
      [ConcreteState.prepared, ConcreteState.evolved, ConcreteState.measured]
    ∧ concreteRecursiveKernelCarrier.weight = 1
    ∧ twoRouteRecursiveKernelCarrierFamily.map (fun C => C.carrier) =
      [ [TwoRouteState.source, TwoRouteState.upper, TwoRouteState.target]
      , [TwoRouteState.source, TwoRouteState.lower, TwoRouteState.target]
      ]
    ∧ twoRouteRecursiveKernelCarrierFamily.map
      (fun C => DisplayedKernelPathCarrier.weight C) = [1, 1]
    ∧ (∀ b : PendingBeyondS30, ClosedByStepwiseS30 b = false)
    ∧ WenConstructiveCoverage
```

S30 已证明：

| 项 | theorem / def | 含义 |
|---|---|---|
| constructor carrier | `kernelPathTargets` / `kernelPathPoints` | finite kernel path 的点载体由构造子递归给出 |
| endpoint membership | `kernelPath_start_mem` / `kernelPath_stop_mem` | 起点和终点都在递归 carrier 中 |
| append law | `kernelPathPoints_append` | append 后的 carrier 等于左 carrier 加右 path targets |
| canonical displayed carrier | `recursiveKernelPathCarrier` | 从任何 finite `KernelPath` 自动得到 S29 displayed carrier |
| concrete witness | `concreteRecursiveKernelCarrier` | prepared/evolved/measured 三点 carrier |
| two-route family | `twoRouteRecursiveKernelCarrierFamily` | upper/lower 两条路径形成 finite recursive carrier family |

## 三 · 边界

S30 只关闭 finite constructor-level carrier：

| 未关闭项 | 边界 |
|---|---|
| global path enumeration | 没有枚举任意端点之间的所有 paths |
| arbitrary-length causal intervals | 没有证明 `{x | causalBefore a x ∧ causalBefore x b}` 的全局有限性或完备枚举 |
| full causal set local finiteness | 没有证明完整 causal set 公理 |
| general path integral | recursive carrier family 不是路径积分测度 |
| Lorentzian geometry / metric recovery | 没有连续几何、光锥或度规恢复 |
| empirical closure | 没有经验标定或可测预言闭合 |

本轮最重要的收获是：

```text
KernelPath
-> recursive finite carrier
-> displayed carrier
-> weight / causal readback
```

这让“路径上的有限载体”不再依赖任意外加列表，而是从路径构造本身读出。

## 四 · 验证

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityKernelPathRecursiveCarrierBridge
lake build SSBX
python3 scripts/docs_next.py build --out docs-next/_generated --clean
python3 scripts/docs_next.py check --out docs-next/_generated --strict
git diff --check --
```

自审搜索：

```bash
rg -n "全局 path enumeration|arbitrary-length causal interval|full causal set local finiteness|path integral|Lorentzian geometry|metric recovery" formal/SSBX/Foundation/Modern formal/SSBX/notes 义理 docs-next/10_formal_形式/modern.md
```

失败记录：

```text
日期：2026-05-09
目标：lake build SSBX.Foundation.Modern.QuantumRelativityKernelPathRecursiveCarrierBridge
失败类型：Lean proof failure
失败原因：indexed KernelPath induction 的 refl 分支不接受显式参数；若干 list equality 在 simp 后仍需 rfl 收尾。
保留结论：递归 carrier 定义可行，失败点是 proof-script 形状，不是概念阻塞。
下一步：修正 induction 分支与 list equality 收尾后重新构建。
```

## 五 · 下一步

S30 后的自然推进顺序中，第一步已由 S31 承接：

```text
recursive carrier
-> endpoint-indexed finite carrier family
-> toy all-path carrier enumeration
-> finite all-path support boundary
```

S31 已把 recursive carriers 包成 endpoint-indexed finite carrier family，并读回 two-route carrier/weight lists。下一步最省力目标不是一般 path integral，而是对 two-route source/target 证明：

```text
the recursively generated carrier family is exactly the displayed two-route family
```

也就是把 S30 的 family 从 witness 推到 toy completeness boundary。
