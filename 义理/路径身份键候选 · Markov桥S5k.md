# 路径身份键候选 · Markov桥S5k

**前置**：[Markov因果桥 · 大统一最小验证构造](Markov因果桥%20·%20大统一最小验证构造.md) · [双路径枚举候选 · Markov桥S5j](双路径枚举候选%20·%20Markov桥S5j.md) · [端点支撑规范化候选 · Markov桥S5i](端点支撑规范化候选%20·%20Markov桥S5i.md) · [有限键商候选 · Markov桥S5l](有限键商候选%20·%20Markov桥S5l.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| path key | `Foundation/Modern/QuantumRelativityPathIdentityBridge.lean` | `TwoStepPathKey`、`twoStepPathKey` | `machineChecked` |
| key equality boundary | `Foundation/Modern/QuantumRelativityPathIdentityBridge.lean` | `two_step_path_key_eq_start`、`two_step_path_key_eq_middle`、`two_step_path_key_eq_stop` | `machineChecked` |
| two-route key separation | `Foundation/Modern/QuantumRelativityPathIdentityBridge.lean` | `two_route_upper_lower_keys_distinct` | `machineChecked` |
| key enumeration | `Foundation/Modern/QuantumRelativityPathIdentityBridge.lean` | `twoRouteSourceTargetKeyEnumeration`、`two_route_source_target_key_mem_enumeration` | `machineChecked` |
| S5k 公开摘要 | `Foundation/Modern/QuantumRelativityPathIdentityBridge.lean` | `path_identity_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S5k 的主张：

```text
TwoStepPathWitness
-> visible key (start, middle, stop)
-> key equality preserves visible route data
```

对 two-route toy process：

```text
upper key != lower key
source/target two-step path key is in [upper key, lower key]
```

这不是商类本身；它只是给后续 quotient 或去重提供一个可审计身份键。S5m 已把该 key equality 承接为 visible-key quotient class。

公开摘要为：

```lean
theorem path_identity_bridge_summary :
    (∀ {P : FiniteProcess} {p q : TwoStepPathWitness P},
      twoStepPathKey p = twoStepPathKey q -> p.start = q.start)
    ∧ ...
    ∧ twoStepPathKey twoRouteUpperPath ≠
      twoStepPathKey twoRouteLowerPath
    ∧ TwoRouteSourceTargetKeyComplete
    ∧ TwoRouteSourceTargetMiddleComplete
    ∧ WenConstructiveCoverage
```

该 theorem 已通过 `lake build SSBX.Foundation.Modern.QuantumRelativityPathIdentityBridge`。

---

## 〇一 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| visible path key | `TwoStepPathKey` | 只保留 `start/middle/stop`，不含 proof fields |
| key projection | `twoStepPathKey` | 从 `TwoStepPathWitness` 抽出可比较身份数据 |
| key equality boundary | `two_step_path_key_eq_start`、`two_step_path_key_eq_middle`、`two_step_path_key_eq_stop` | key 相同推出可见路径数据相同 |
| route separation | `two_route_upper_lower_keys_distinct` | upper/lower displayed routes 的 key 不同 |
| key enumeration | `two_route_source_target_key_mem_enumeration` | toy source/target path 的 key 在 displayed key list 中 |
| key completeness | `two_route_source_target_key_complete` | key enumeration completeness predicate 已关闭 |
| summary | `path_identity_bridge_summary` | 合取 key boundary、two-route key separation 与 S5j middle completeness |

后续结构：

| 轴 | 状态 | 说明 |
|---|---|---|
| finite visible-key quotient candidate | S5l 已关闭 | S5k 不把 key 相同的 paths 商掉；S5l 已证明 key-equivalence 与 key-compatible amplitude descent |
| visible-key quotient class | S5m 已关闭 | S5k 不构造 Lean quotient class；S5m 已补上 `Setoid` / `Quot` construction |
| two-route canonical representative | S5n 已关闭 | S5n 已为 toy source/target quotient classes 给出 displayed representatives |
| finite quotient support | S5o 已关闭 | S5o 已把 displayed quotient classes 升级为 finite quotient-support list |
| quotient-support algebra | S5p 已关闭 | S5p 已证明 quotient-support append / permutation / reverse / duplicate stability |
| general choice function | 后续结构 | 仍未为任意 process 或任意 quotient class 选代表元 |
| proof-field path equality | 后续结构 | S5k 避免证明 witness proof fields 相同 |
| general all-path enumeration | 后续结构 | S5k 仍只处理 two-route toy source/target two-step keys |
| path integral | 后续结构 | 仍需要路径空间、测度、极限或 over-all-paths construction |
| empirical closure | 后续结构 | 需要 observation ledger 与数据判准 |

本轮闭合范围：**S5k 已在 Lean 中关闭 finite two-step visible path-key boundary 与 two-route toy key completeness。**

---

## 一 · 为什么这不是 quotient

`TwoStepPathWitness` 里含有 `leftStep/rightStep` proof fields。S5k 不试图证明两个 witness 完全相等，而只抽出：

```text
(start, middle, stop)
```

这足够支撑后续“按可见路径数据去重”的候选方向，但还不是 quotient theorem。

---

## 二 · S5l 承接与下一步

S5k 的直接增强已由 S5l 承接：

```text
visible path key
-> finite quotient candidate
-> duplicate compensation theorem
-> visible-key quotient class
```

下一步可以继续：

```text
finite visible-key quotient candidate
-> observable ledger boundary
```

或者转向：

```text
candidate interference
-> observable ledger boundary
```

两条线都需要单独 theorem。

---

## 三 · Validation Command

Lean 验证命令：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityPathIdentityBridge
lake build SSBX
```

文档与格式检查：

```bash
python3 scripts/docs_next.py build --out docs-next/_generated --clean
python3 scripts/docs_next.py check --out docs-next/_generated --strict
git diff --check --
```
