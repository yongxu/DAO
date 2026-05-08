# 离散相位标记候选 · Markov桥S5d

**前置**：[Markov因果桥 · 大统一最小验证构造](Markov因果桥%20·%20大统一最小验证构造.md) · [离散作用量相位候选 · Markov桥S5e](离散作用量相位候选%20·%20Markov桥S5e.md) · [双路径相消候选 · Markov桥S5c](双路径相消候选%20·%20Markov桥S5c.md) · [非零路径振幅候选 · Markov桥S5b](非零路径振幅候选%20·%20Markov桥S5b.md) · [干涉与测量律候选 · Markov桥S5](干涉与测量律候选%20·%20Markov桥S5.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| 离散相位标签 | `Foundation/Modern/QuantumRelativityDiscretePhaseBridge.lean` | `DiscretePhase`、`discretePhaseAmplitude` | `machineChecked` typed skeleton |
| 相位相消 | `Foundation/Modern/QuantumRelativityDiscretePhaseBridge.lean` | `discrete_phase_amplitudes_cancel` | `machineChecked` |
| two-step phase candidate | `Foundation/Modern/QuantumRelativityDiscretePhaseBridge.lean` | `TwoStepPhaseCandidate`、`phaseInducedTwoStepAmplitudeCandidate` | `machineChecked` typed skeleton |
| two-route 相位标签 | `Foundation/Modern/QuantumRelativityDiscretePhaseBridge.lean` | `two_route_upper_phase`、`two_route_lower_phase` | `machineChecked` |
| 相位导出振幅 | `Foundation/Modern/QuantumRelativityDiscretePhaseBridge.lean` | `two_route_upper_phase_amplitude`、`two_route_lower_phase_amplitude` | `machineChecked` |
| 相位导出相消 | `Foundation/Modern/QuantumRelativityDiscretePhaseBridge.lean` | `two_route_phase_pair_amplitude_cancels`、`two_route_phase_cancelled_born_weight_zero` | `machineChecked` |
| S5d 公开摘要 | `Foundation/Modern/QuantumRelativityDiscretePhaseBridge.lean` | `discrete_phase_bridge_summary` | `machineChecked` |
| S5e edge-action follow-up | `Foundation/Modern/QuantumRelativityDiscreteActionBridge.lean` | `discrete_action_phase_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S5d 的主张很窄：

```text
S5c two-path finite cancellation
+ finite phase labels: zero / pi
+ phaseAmplitude zero = 1
+ phaseAmplitude pi = -1
+ upper path labelled zero
+ lower path labelled pi
= phase-labelled two-path cancellation candidate
```

它不证明 Hamiltonian，不证明作用量泛函，不证明 unitary evolution，不证明 path integral，不证明 Born rule 推导，不证明 decoherence，也不证明经验闭合。

正面结论是：

```text
S5d 已把 S5c 的两条相反候选振幅
改写为离散相位标记 `zero/pi` 的导出结果；
因此 two-path cancellation 不再只是裸数值赋值，
而有一个可检查的 phase-label candidate 来源。
S5e 进一步把这两个 path-level labels
改写为 edge-level phase increments 的有限累积结果。
```

公开摘要为：

```lean
theorem discrete_phase_bridge_summary :
    HasTwoStepPhaseCandidate twoRouteProcess
    ∧ (discretePhaseAmplitude DiscretePhase.zero
        + discretePhaseAmplitude DiscretePhase.pi = 0)
    ∧ twoRoutePhaseCandidate.phaseOf twoRouteUpperPath = DiscretePhase.zero
    ∧ twoRoutePhaseCandidate.phaseOf twoRouteLowerPath = DiscretePhase.pi
    ∧ ...
    ∧ twoStepPairAmplitudeSum
        (phaseInducedTwoStepAmplitudeCandidate twoRoutePhaseCandidate)
        twoRouteUpperLowerPair = 0
    ∧ WenConstructiveCoverage
```

该 theorem 已通过 `lake build SSBX.Foundation.Modern.QuantumRelativityDiscretePhaseBridge`。

---

## 〇一 · 边界声明

| 说法 | 本文状态 | 精确含义 |
|---|---|---|
| 离散相位标签已开口 | `machineChecked` typed skeleton | `DiscretePhase.zero` 与 `DiscretePhase.pi` 两个标签 |
| 相位到振幅映射 | `machineChecked` | `zero -> 1`，`pi -> -1` |
| primitive phase cancellation | `machineChecked` | `discrete_phase_amplitudes_cancel` 证明 `1 + (-1) = 0` |
| two-step phase candidate | `machineChecked` typed skeleton | `TwoStepPhaseCandidate` 给 two-step witness 分配 phase label |
| phase-induced amplitude candidate | `machineChecked` typed skeleton | `phaseInducedTwoStepAmplitudeCandidate` 接回 S5c 的 amplitude interface |
| upper/lower 标签 | `machineChecked` | upper 为 `zero`，lower 为 `pi` |
| phase-induced cancellation | `machineChecked` | `two_route_phase_pair_amplitude_cancels` |
| Born-shaped zero boundary | `machineChecked` | `two_route_phase_cancelled_born_weight_zero` |
| 连续相位群 | 未纳入本轮 | 没有 `U(1)`、角度加法、指数映射或连续参数 |
| action / Hamiltonian law | 未纳入本轮 | 没有从作用量或 Hamiltonian 推出相位 |
| unitary / CPTP | 未纳入本轮 | channel 仍是 candidate skeleton |
| path integral | 未纳入本轮 | 没有路径空间、测度、极限或 over-all-paths sum |
| 经验闭合 | 未纳入本轮 | 没有 observation ledger 或数据判准 |

边界句：

```text
S5d 关闭的是离散 phase-label candidate 到 two-path cancellation 的接口；
它不是物理相位动力学，也不是 path integral 或 Born rule 推导。
```

---

## 〇二 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| phase labels | `DiscretePhase` | 最小二值相位标签 |
| phase amplitude map | `discretePhaseAmplitude` | `zero/pi` 分别给出 `1/-1` |
| phase cancellation | `discrete_phase_amplitudes_cancel` | 标签层已经有相消形状 |
| two-step phase candidate | `TwoStepPhaseCandidate` | two-step path witness 可携带 phase label |
| amplitude induction | `phaseInducedTwoStepAmplitudeCandidate` | phase label 可接回 S5c amplitude candidate |
| upper/lower labels | `two_route_upper_phase`、`two_route_lower_phase` | two-route toy paths 的标签被机器检查 |
| upper/lower amplitudes | `two_route_upper_phase_amplitude`、`two_route_lower_phase_amplitude` | `zero/pi` 导出 `1/-1` |
| phase-induced cancellation | `two_route_phase_pair_amplitude_cancels` | 两路径有限和仍为 `0` |
| Born-shaped zero | `two_route_phase_cancelled_born_weight_zero` | 相消后候选权重为 `0` |
| edge-action accumulation follow-up | `discrete_action_phase_bridge_summary` | S5e 已把 path phase label 接到 edge increments |
| 公开摘要 | `discrete_phase_bridge_summary` | 合取 phase label、two-path cancellation、S5c 边界与 Wen coverage |

尚未闭合：

| 轴 | 状态 | 说明 |
|---|---|---|
| continuous phase | 未纳入本轮 | 没有连续角度、`U(1)` 或指数映射 |
| action principle | 未纳入本轮 | 没有 action functional 或 stationary phase |
| Hamiltonian / unitary evolution | 未纳入本轮 | 没有时间演化算子 |
| path integral | 未纳入本轮 | 没有路径空间和求和/积分测度 |
| Born rule derivation | 未纳入本轮 | 仍只复用 `ampProb` boundary |
| empirical closure | 未纳入本轮 | S5q 已补 pending observable ledger；仍没有外部数据或实验闭合 |

本轮闭合范围：**S5d 已在 Lean 中关闭“two-route upper/lower paths 的相反候选振幅可由离散 phase label `zero/pi` 导出，并保持 S5c 的 two-path cancellation 与 Born-shaped zero boundary”；S5e 后续关闭 edge-action phase accumulation candidate；它们不关闭连续相位、作用量动力学、unitary/CPTP、path integral、Born rule 推导或经验闭合。**

---

## 一 · 为什么这一步比 S5c 更强

S5c 已证明：

```text
upper amplitude = 1
lower amplitude = -1
```

但这两个数值仍像是直接赋值。S5d 加入最小一层来源：

```text
upper path -> phase zero -> amplitude 1
lower path -> phase pi   -> amplitude -1
```

这不是物理相位动力学。它只说明当前形式语言已经能把“相反振幅”重写为“相反离散相位标签导出的振幅”。

---

## 二 · Validation Command

Lean 验证命令：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityDiscretePhaseBridge
lake build SSBX.Foundation.Modern.QuantumRelativityDiscreteActionBridge
lake build SSBX
```

文档与格式检查：

```bash
python3 scripts/docs_next.py build --out docs-next/_generated --clean
python3 scripts/docs_next.py check --out docs-next/_generated --strict
git diff --check --
```
