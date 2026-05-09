# 观测账本候选 · Markov桥S5q

**前置**：[Markov因果桥 · 大统一最小验证构造](Markov因果桥%20·%20大统一最小验证构造.md) · [商支撑代数候选 · Markov桥S5p](商支撑代数候选%20·%20Markov桥S5p.md) · [商支撑枚举候选 · Markov桥S5o](商支撑枚举候选%20·%20Markov桥S5o.md) · [作用量相位律候选 · Markov桥S5r](作用量相位律候选%20·%20Markov桥S5r.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| empirical status | `Foundation/Modern/QuantumRelativityObservableLedgerBridge.lean` | `EmpiricalClosureStatus.pendingData` / `externallyClosed` | `machineChecked` |
| observable ledger entry | `Foundation/Modern/QuantumRelativityObservableLedgerBridge.lean` | `ObservableLedgerEntry`、`ObservableLedgerPending`、`EmpiricallyClosed` | `machineChecked` |
| pending boundary | `Foundation/Modern/QuantumRelativityObservableLedgerBridge.lean` | `pending_not_empirically_closed` | `machineChecked` |
| two-route ledger entry | `Foundation/Modern/QuantumRelativityObservableLedgerBridge.lean` | `twoRouteCancellationObservableLedgerEntry` | `machineChecked` |
| two-route ledger facts | `Foundation/Modern/QuantumRelativityObservableLedgerBridge.lean` | `two_route_observable_ledger_amplitude_zero`、`two_route_observable_ledger_weight_zero`、`two_route_observable_ledger_not_empirically_closed` | `machineChecked` |
| S5q 公开摘要 | `Foundation/Modern/QuantumRelativityObservableLedgerBridge.lean` | `observable_ledger_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S5q 的主张：

```text
quotient-support cancellation
-> observable ledger entry
-> pending empirical status
```

对 two-route toy quotient support：

```text
[upper class, lower class]
-> amplitude sum = 0
-> Born-shaped candidate weight = 0
-> status = pendingData
-> not externally empirically closed
```

这不是实验闭合，也不是数据校准、可测预言 theorem、Born rule 推导或真实物理干涉律；它只关闭“候选可测差异可以怎样进入账本，并保持 pending 边界”。

公开摘要为：

```lean
theorem observable_ledger_bridge_summary :
    TwoRouteObservableLedgerBoundaryComplete
    ∧ twoRouteCancellationObservableLedgerEntry.amplitudeSum =
      quotientSupportAmplitudeSum twoRouteKeyAmplitudeCandidate
        twoRouteSourceTargetQuotientEnumeration
    ∧ twoRouteCancellationObservableLedgerEntry.candidateWeight =
      quotientSupportBornWeight twoRouteKeyAmplitudeCandidate
        twoRouteSourceTargetQuotientEnumeration
    ∧ quotientSupportAmplitudeSum twoRouteKeyAmplitudeCandidate
      twoRouteDoubleQuotientSupport = 0
    ∧ quotientSupportBornWeight twoRouteKeyAmplitudeCandidate
      twoRouteDoubleQuotientSupport = 0
    ∧ WenConstructiveCoverage
```

该 theorem 已通过 `lake build SSBX.Foundation.Modern.QuantumRelativityObservableLedgerBridge`。

---

## 〇一 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| ledger carrier | `ObservableLedgerEntry` | 记录 key-amplitude、finite quotient support、displayed amplitude sum、candidate weight 与 status |
| pending boundary | `pending_not_empirically_closed` | pending entry 与 externally closed status 不相容 |
| two-route entry | `twoRouteCancellationObservableLedgerEntry` | two-route quotient-support cancellation 可登记为 pending observable candidate |
| zero amplitude | `two_route_observable_ledger_amplitude_zero` | 账本 entry 的 displayed amplitude sum 为 `0` |
| zero weight | `two_route_observable_ledger_weight_zero` | 账本 entry 的 Born-shaped candidate weight 为 `0` |
| no empirical closure | `two_route_observable_ledger_not_empirically_closed` | two-route entry 保持 pending，不被读成实验闭合 |
| summary | `observable_ledger_bridge_summary` | 合取 observable ledger boundary、S5p double-support cancellation 与文构造覆盖 |

后续结构：

| 轴 | 状态 | 说明 |
|---|---|---|
| data calibration | 后续结构 | 需要把外部数据、误差模型或实验协议接入 ledger |
| measurable prediction theorem | 后续结构 | 需要定义观测量、判别阈值与检验定理 |
| Born rule derivation | 后续结构 | S5q 只记录 Born-shaped candidate weight，不推出 Born rule |
| continuous phase/action law | 后续结构 | 仍未给出连续相位、作用量或动力学 |
| path integral | 后续结构 | 仍需要一般路径空间、求和/积分与极限结构 |

本轮闭合范围：**S5q 已在 Lean 中关闭 observable ledger candidate boundary，并明确 pending entry 不是 empirical closure。**

---

## 一 · 失败记录

S5q 目标构建一次通过：

```text
命令：lake build SSBX.Foundation.Modern.QuantumRelativityObservableLedgerBridge
结果：Build completed successfully
备注：构建输出中有既有 Wen 模块 unused simp argument 警告；新增 S5q 模块无失败。
```

---

## 二 · 下一步

S5q 的 action-law 增强已由 S5r 承接：

```text
observable ledger boundary
-> finite action-to-phase law candidate
```

再往后可以继续：

```text
finite action-to-phase law candidate
-> continuous phase/action law candidate
```

两条线都必须保持 machine-checked theorem 和失败记录。

---

## 三 · Validation Command

Lean 验证命令：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityObservableLedgerBridge
```
