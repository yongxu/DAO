# 作用量相位律候选 · Markov桥S5r

**前置**：[Markov因果桥 · 大统一最小验证构造](Markov因果桥%20·%20大统一最小验证构造.md) · [观测账本候选 · Markov桥S5q](观测账本候选%20·%20Markov桥S5q.md) · [商支撑代数候选 · Markov桥S5p](商支撑代数候选%20·%20Markov桥S5p.md) · [离散作用量相位候选 · Markov桥S5e](离散作用量相位候选%20·%20Markov桥S5e.md) · [逐步统一候选摘要 · Markov桥S8](逐步统一候选摘要%20·%20Markov桥S8.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**后续**：[作用相位到测量权重链 · Markov桥S22](作用相位到测量权重链%20·%20Markov桥S22.md) 已把本页的 finite action branch / action index 接到 one-qubit measurement-event weights；[连续作用量泛函候选 · Markov桥S24](连续作用量泛函候选%20·%20Markov桥S24.md) 已把本页的 `0/1` action index 接到 displayed continuous action-coordinate functional 的采样值；[路径空间作用量泛函候选 · Markov桥S25](路径空间作用量泛函候选%20·%20Markov桥S25.md) 与 [有限作用量极值候选 · Markov桥S26](有限作用量极值候选%20·%20Markov桥S26.md) 已把 action values 推到 finite quotient path space 与 finite support minimum。

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| period-two action phase | `Foundation/Modern/QuantumRelativityActionPhaseLawBridge.lean` | `actionIndexPhase`、`actionIndexAmplitude` | `machineChecked` |
| action law candidate | `Foundation/Modern/QuantumRelativityActionPhaseLawBridge.lean` | `QuotientActionPhaseLawCandidate`、`quotientActionPhaseAmplitude` | `machineChecked` |
| two-route action law | `Foundation/Modern/QuantumRelativityActionPhaseLawBridge.lean` | `twoRouteQuotientActionPhaseLaw`、`two_route_upper_quotient_action_index`、`two_route_lower_quotient_action_index` | `machineChecked` |
| quotient-support cancellation | `Foundation/Modern/QuantumRelativityActionPhaseLawBridge.lean` | `two_route_action_phase_support_amplitude_cancels`、`two_route_action_phase_support_born_weight_zero` | `machineChecked` |
| ledger-compatible key law | `Foundation/Modern/QuantumRelativityActionPhaseLawBridge.lean` | `twoRouteActionPhaseKeyAmplitudeCandidate`、`twoRouteActionPhaseObservableLedgerEntry` | `machineChecked` |
| S5r 公开摘要 | `Foundation/Modern/QuantumRelativityActionPhaseLawBridge.lean` | `action_phase_law_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S5r 的主张：

```text
finite action index
-> period-two phase
-> quotient-support amplitude sum
-> pending observable ledger entry
```

对 two-route toy quotient support：

```text
upper action index = 0
lower action index = 1
actionIndexAmplitude 0 = 1
actionIndexAmplitude 1 = -1
finite quotient-support sum = 0
Born-shaped candidate weight = 0
status = pendingData
```

这不是连续作用量泛函，也不是 Hamiltonian/unitary dynamics、一般 path integral、Born rule 推导或经验闭合；它只关闭有限 period-two action-to-phase law candidate。

公开摘要为：

```lean
theorem action_phase_law_bridge_summary :
    TwoRouteActionPhaseLawBoundaryComplete
    ∧ quotientSupportAmplitudeSum twoRouteActionPhaseKeyAmplitudeCandidate
      twoRouteSourceTargetQuotientEnumeration = 0
    ∧ quotientSupportBornWeight twoRouteActionPhaseKeyAmplitudeCandidate
      twoRouteSourceTargetQuotientEnumeration = 0
    ∧ TwoRouteObservableLedgerBoundaryComplete
    ∧ WenConstructiveCoverage
```

该 theorem 已通过 `lake build SSBX.Foundation.Modern.QuantumRelativityActionPhaseLawBridge`。

---

## 〇一 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| finite action phase | `actionIndexPhase`、`actionIndexAmplitude` | action index mod 2 导出 `zero/pi` 与 `1/-1` |
| cancellation seed | `action_index_zero_one_amplitudes_cancel` | index `0` 与 `1` 的诱导振幅相消 |
| quotient action law | `QuotientActionPhaseLawCandidate` | quotient class 上的有限 action index law |
| two-route action indices | `two_route_upper_quotient_action_index`、`two_route_lower_quotient_action_index` | upper/lower quotient classes 分别携带 `0/1` |
| support cancellation | `two_route_action_phase_support_amplitude_cancels` | action-phase law 在 two-route quotient support 上相消 |
| ledger entry | `twoRouteActionPhaseObservableLedgerEntry` | action-phase law 可登记为 pending observable entry |
| summary | `action_phase_law_bridge_summary` | 合取 finite action-phase law、ledger boundary 与文构造覆盖 |

后续结构：

| 轴 | 状态 | 说明 |
|---|---|---|
| displayed continuous action functional | 已由 S24 承接 | S24 给出 `S(t)=t` 的 continuous action-coordinate functional，并在 `0/1` 采样点回到本页 action index |
| finite quotient path-space action functional | 已由 S25 承接 | S25 把本页 action index 接到 two-route quotient path classes 上的 action values |
| finite action extremum | 已由 S26 承接 | S26 证明 two-route finite quotient support 上 upper 是 action minimum，lower 不是 |
| smooth or infinite-dimensional path-space action functional | 后续结构 | 仍未处理路径流形、continuous variation 或 stationary action principle |
| Hamiltonian / unitary dynamics | 后续结构 | 仍未给出动力学生成律 |
| path integral | 后续结构 | 仍需要一般路径空间、求和/积分与极限 |
| Born rule derivation | 后续结构 | 仍只记录 Born-shaped candidate weight |
| empirical closure | 后续结构 | S5r 接回 pending ledger，不证明数据校准或实验闭合 |

本轮闭合范围：**S5r 已在 Lean 中关闭 finite action-to-phase law candidate，并把其 two-route cancellation 接回 pending observable ledger。**

---

## 一 · 失败记录

S5r 第一次目标构建失败：

```text
命令：lake build SSBX.Foundation.Modern.QuantumRelativityActionPhaseLawBridge
失败点：two_route_action_phase_support_amplitude_cancels 与 key-support cancellation proof
原因：proof 中展开了 `quotientVisibleKey`，导致 `Quot.lift` 暴露，`quotient_visible_key_mk` 不能作为 simp theorem 收缩 quotient readback
修正：不展开 `quotientVisibleKey`，保留 quotient readback 形状，让既有 `[simp]` theorem 关闭计算
结果：目标构建通过
```

---

## 二 · 下一步

S5r 的当前摘要增强已由 S8 承接：

```text
finite action-to-phase law
-> stepwise unification candidate summary
```

S22/S24/S25 已经补上三条后续链：

```text
finite action-to-phase law
-> action amplitude
-> normalized one-qubit state
-> measurement-event weights
```

```text
finite action-to-phase law
-> displayed continuous action-coordinate functional
-> sampled finite phase evolution

finite action-to-phase law
-> finite quotient path-space action functional
-> quotient-support action-induced cancellation
```

再往后可以继续 smooth/infinite-dimensional path-space action functional、Euler-Lagrange、Hamiltonian/unitary dynamics 与 path integral。每条线都必须保持 machine-checked theorem 和失败记录。

---

## 三 · Validation Command

Lean 验证命令：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityActionPhaseLawBridge
```
