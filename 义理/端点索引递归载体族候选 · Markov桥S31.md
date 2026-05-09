# 端点索引递归载体族候选 · Markov桥S31

## 一 · 本轮闭合

| 层 | Lean 文件 | 入口 | 状态 |
|---|---|---|---|
| endpoint-indexed family | `Foundation/Modern/QuantumRelativityEndpointIndexedRecursiveCarrierBridge.lean` | `EndpointIndexedRecursiveKernelCarrierFamily` | `machineChecked` |
| member readback | 同上 | `member_start_mem`、`member_stop_mem`、`member_causal_before`、`member_weight_readback` | `machineChecked` |
| two-route family | 同上 | `twoRouteEndpointIndexedRecursiveCarrierFamily` | `machineChecked` |
| carrier/weight readback | 同上 | `two_route_endpoint_indexed_recursive_family_carriers`、`two_route_endpoint_indexed_recursive_family_weights` | `machineChecked` |
| total displayed weight | 同上 | `two_route_endpoint_indexed_recursive_family_weight_sum` | `machineChecked` |
| S31 summary | 同上 | `endpoint_indexed_recursive_carrier_bridge_summary` | `machineChecked` |

S31 把 S30 的 recursive carriers 包装成 endpoint-indexed finite family：

```text
recursive carriers
-> endpoint-indexed finite family
-> all members share typed endpoints
-> carrier lists / weights are readable as finite lists
-> two-route displayed total weight = 2
```

这里的“endpoint-indexed”是类型层面的：每个 member 都是同一 `K a b` 下的 `DisplayedKernelPathCarrier K a b`。

## 二 · 形式出口

Lean summary：

```lean
theorem endpoint_indexed_recursive_carrier_bridge_summary :
    EndpointIndexedRecursiveCarrierFamilyClosed
    ∧ TwoRouteEndpointIndexedRecursiveFamilyClosed
    ∧ RecursiveKernelPathCarrierClosed
    ∧ KernelPathAppendCarrierClosed
    ∧ FiniteRecursiveKernelCarrierFamilyClosed
    ∧ twoRouteEndpointIndexedRecursiveCarrierFamily.carrierLists =
      [ [TwoRouteState.source, TwoRouteState.upper, TwoRouteState.target]
      , [TwoRouteState.source, TwoRouteState.lower, TwoRouteState.target]
      ]
    ∧ twoRouteEndpointIndexedRecursiveCarrierFamily.weights = [1, 1]
    ∧ twoRouteEndpointIndexedRecursiveCarrierFamily.weightSum = 2
    ∧ (∀ b : PendingBeyondS31, ClosedByStepwiseS31 b = false)
    ∧ WenConstructiveCoverage
```

本轮已证明：

| 项 | theorem / def | 含义 |
|---|---|---|
| shared endpoints | `EndpointIndexedRecursiveKernelCarrierFamily` | family members 在类型上共享 `a / b` |
| member endpoint readback | `member_start_mem`、`member_stop_mem` | 任意 member 的 carrier 含起点和终点 |
| member causal readback | `member_causal_before` | 任意 member 可读回同端点 `causalBefore` |
| member weight readback | `member_weight_readback` | 任意 member 的 displayed weight 等于底层 kernel path weight |
| two-route carrier lists | `two_route_endpoint_indexed_recursive_family_carriers` | upper/lower carrier list 可读回 |
| two-route weights | `two_route_endpoint_indexed_recursive_family_weights` | weights 为 `[1, 1]` |
| displayed weight sum | `two_route_endpoint_indexed_recursive_family_weight_sum` | displayed total weight 为 `2` |

## 三 · 边界

S31 不证明：

| 未关闭项 | 边界 |
|---|---|
| all-path completeness | 没有证明 family 包含同端点的所有 kernel paths |
| global path enumeration | 没有枚举任意端点之间的所有 paths |
| arbitrary-length causal intervals | 没有证明全局 `{x | causalBefore a x ∧ causalBefore x b}` 枚举 |
| general path integral | finite family list 不是路径积分测度 |
| full causal set local finiteness | 没有证明完整 causal set 局部有限性 |
| Lorentzian geometry / metric recovery | 没有连续几何、光锥或度规恢复 |

本轮闭合范围可以读作：

```text
same endpoints
same recursive-carrier type
finite displayed family
readable carriers and weights
```

## 四 · 验证

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityEndpointIndexedRecursiveCarrierBridge
lake build SSBX
python3 scripts/docs_next.py build --out docs-next/_generated --clean
python3 scripts/docs_next.py check --out docs-next/_generated --strict
git diff --check --
```

自审搜索：

```bash
rg -n "all-path completeness|global path enumeration|arbitrary-length causal interval|path integral|Lorentzian geometry|metric recovery" formal/SSBX/Foundation/Modern formal/SSBX/notes 义理 docs-next/10_formal_形式/modern.md
```

## 五 · 下一步

下一步最省力目标已由 S32 承接：

```text
endpoint-indexed recursive carrier family
-> two-route toy carrier-family completeness boundary
```

S32 已只在 toy `twoRouteProcess` 上证明 source/target 的 displayed endpoint-indexed recursive family 正好覆盖 upper/lower 两条 displayed route；S33 继续证明任意 `KernelPath twoRouteKernel source target` 的 recursive carrier 也只能是 upper/lower。二者都仍不推广到任意有限过程。
