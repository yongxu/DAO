# 有限因果区间候选 · Markov桥S28

**前置**：[路径组合与因果约束 · Markov桥S3](路径组合与因果约束%20·%20Markov桥S3.md) · [有限因果局部性候选 · Markov桥S27](有限因果局部性候选%20·%20Markov桥S27.md) · [双路径相消候选 · Markov桥S5c](双路径相消候选%20·%20Markov桥S5c.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**后续**：[有限核路径载体候选 · Markov桥S29](有限核路径载体候选%20·%20Markov桥S29.md) 已把本页的 displayed interval points 接到 S19 finite `KernelPath` carrier / weight / causal readback。

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| finite two-step interval | `Foundation/Modern/QuantumRelativityFiniteCausalIntervalBridge.lean` | `FiniteTwoStepCausalIntervalCandidate`、`closedTwoStepIntervalPoints` | `machineChecked` |
| middle soundness | `Foundation/Modern/QuantumRelativityFiniteCausalIntervalBridge.lean` | `interval_middle_step_law`、`interval_middle_causal_law` | `machineChecked` |
| localFuture handoff | `Foundation/Modern/QuantumRelativityFiniteCausalIntervalBridge.lean` | `LocalTwoStepIntervalRespectsLocalFuture`、`interval_respects_local_future` | `machineChecked` |
| concrete interval | `Foundation/Modern/QuantumRelativityFiniteCausalIntervalBridge.lean` | `concretePreparedMeasuredInterval` | `machineChecked` |
| two-route interval | `Foundation/Modern/QuantumRelativityFiniteCausalIntervalBridge.lean` | `twoRouteSourceTargetInterval`、`two_route_interval_has_two_distinct_middles` | `machineChecked` |
| S28 summary | `Foundation/Modern/QuantumRelativityFiniteCausalIntervalBridge.lean` | `finite_causal_interval_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S28 关闭的是一个有限 two-step 因果区间候选：

```text
fixed endpoints a,c
-> finite middle list
-> m ∈ middle implies step a m and step m c
-> middle respects S27 localFuture on both legs
-> concrete chain has [evolved]
-> two-route source/target interval has [upper, lower]
```

公开摘要为：

```lean
theorem finite_causal_interval_bridge_summary :
    FiniteCausalIntervalClosed
    ∧ FiniteCausalLocalityClosed
    ∧ TwoRouteFiniteActionExtremumClosed
    ∧ FinitePathSpaceActionFunctionalClosed
    ∧ HasSameEndpointTwoStepPair twoRouteProcess
    ∧ (∀ b : PendingBeyondS28, ClosedByStepwiseS28 b = false)
    ∧ WenConstructiveCoverage
```

---

## 〇一 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| finite interval carrier | `FiniteTwoStepCausalIntervalCandidate` | 固定端点之间的二步中间态由 finite list 展示 |
| closed points | `closedTwoStepIntervalPoints` | endpoint + displayed middles + endpoint 的闭区间点列 |
| step soundness | `interval_middle_step_law` | list 中每个 middle 都满足左右两段 step |
| causal readback | `interval_middle_causal_law` | middle 给出两段 `causalBefore` |
| localFuture handoff | `interval_respects_local_future` | middle 和 stop 均落在对应 localFuture |
| concrete witness | `concretePreparedMeasuredInterval` | `prepared -> evolved -> measured` 的中间点为 `[evolved]` |
| two-route witness | `twoRouteSourceTargetInterval` | `source -> target` 的 displayed middle list 为 `[upper, lower]` |
| distinct middles | `two_route_interval_has_two_distinct_middles` | upper/lower 同在区间内且不同 |
| S28 summary | `finite_causal_interval_bridge_summary` | S28 接回 S27/S26/S25 与 two-route pair |

未纳入本轮：

| 项 | 原因 |
|---|---|
| full causal set axioms | 本轮只处理 displayed two-step interval，不证明反身、传递、反对称或全局偏序 |
| arbitrary-length causal intervals | 没有一般长度路径、传递闭包枚举或全路径列表 |
| global local finiteness theorem | `FiniteProcess` 目前没有全状态 `Fintype` 枚举，也不枚举 `{x | causalBefore a x ∧ causalBefore x b}` |
| light cone / Lorentzian locality / metric recovery | 没有连续时空、锥结构、Lorentzian manifold 或度规恢复 |
| relativistic field locality | 没有场、算符代数或 spacelike commutativity |
| empirical closure | 没有数据、误差模型、阈值或可测预言 theorem |

本轮闭合范围：**当前 finite typed skeleton 中的 displayed two-step causal interval candidate**。

---

## 一 · 为什么不直接证全局 causal interval

当前 `causalBefore` 仍由 `Reachable` 读取，而 `Reachable` 允许任意有效 `ProcessPath` witness：

```text
P.step a b ∨ exists p, p.start = a ∧ p.stop = b ∧ p.valid
```

这不是可枚举传递闭包。若直接定义：

```text
{x | causalBefore a x ∧ causalBefore x b}
```

就会把“任意有效 path witness”也纳入区间，当前结构没有足够信息枚举它。因此 S28 只证明更窄但可复用的版本：

```text
step a m ∧ step m c
```

即 displayed two-step interval。

---

## 二 · 与 S27 的连接

S27 给出：

```text
b ∈ localFuture a iff step a b
```

S28 利用这个接口证明：

```text
m ∈ interval.middle
-> m ∈ localFuture a
-> c ∈ localFuture m
```

所以 S28 是 S27 的局部未来邻域在二步区间上的加厚，而不是完整 causal set local finiteness。

---

## 三 · Validation Command

第一次目标模块 build：

```text
命令：lake build SSBX.Foundation.Modern.QuantumRelativityFiniteCausalIntervalBridge
失败点：concrete/twoRoute interval membership proofs
原因：singleton/list membership 的 `simp` 未关闭 impossible cases 与 direct membership cases
修正：改为显式 `cases hm`、`List.mem_singleton_self`、`List.mem_cons_self` 与 `List.mem_cons_of_mem`
结果：进入第二次 build
```

第二次目标模块 build：

```text
命令：lake build SSBX.Foundation.Modern.QuantumRelativityFiniteCausalIntervalBridge
失败点：twoRoute lower membership proofs
原因：`List.mem_cons_of_mem` 在当前 Lean 版本中需要保留 prepend element 的显式占位参数
修正：改为 `List.mem_cons_of_mem _ (List.mem_singleton_self ...)`
结果：第三次目标模块 build 通过
```

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityFiniteCausalIntervalBridge
lake build SSBX
python3 scripts/docs_next.py build --out docs-next/_generated --clean
python3 scripts/docs_next.py check --out docs-next/_generated --strict
git diff --check --
```

自审搜索：

```bash
rg -n "完整 causal set local finiteness|causalBefore.*偏序|Lorentzian locality|metric recovery|light cone|物理级因果局部性" formal/SSBX/Foundation/Modern formal/SSBX/notes 义理 docs-next/10_formal_形式/modern.md
```

---

## 四 · 下一步

S28 后续最自然的推进不是直接宣称因果集完成，而是拆成：

```text
displayed interval -> arbitrary finite path interval -> partial-order-backed interval -> causal set local finiteness
```

其中任意长度路径需要新的 path list / transitive closure / enumeration 接口。
