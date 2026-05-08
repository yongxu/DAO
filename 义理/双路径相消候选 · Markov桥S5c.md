# 双路径相消候选 · Markov桥S5c

**前置**：[Markov因果桥 · 大统一最小验证构造](Markov因果桥%20·%20大统一最小验证构造.md) · [离散相位标记候选 · Markov桥S5d](离散相位标记候选%20·%20Markov桥S5d.md) · [离散作用量相位候选 · Markov桥S5e](离散作用量相位候选%20·%20Markov桥S5e.md) · [非零路径振幅候选 · Markov桥S5b](非零路径振幅候选%20·%20Markov桥S5b.md) · [干涉与测量律候选 · Markov桥S5](干涉与测量律候选%20·%20Markov桥S5.md) · [经典Markov与量子振幅分层 · Markov桥S4](经典Markov与量子振幅分层%20·%20Markov桥S4.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| two-step path witness | `Foundation/Modern/QuantumRelativityTwoPathInterferenceBridge.lean` | `TwoStepPathWitness`、`TwoStepPathWitness.toProcessPath` | `machineChecked` typed skeleton |
| 同端点双路径 | `Foundation/Modern/QuantumRelativityTwoPathInterferenceBridge.lean` | `SameEndpointTwoStepPair`、`two_route_paths_same_endpoints`、`two_route_paths_distinct_middle` | `machineChecked` |
| two-route toy process | `Foundation/Modern/QuantumRelativityTwoPathInterferenceBridge.lean` | `twoRouteProcess`、`twoRouteFiniteProbabilityKernel`、`twoRouteQuantumChannelSkeleton` | `machineChecked` typed witness |
| path-amplitude projection | `Foundation/Modern/QuantumRelativityTwoPathInterferenceBridge.lean` | `twoRoutePathAmplitudeSkeleton`、`TwoStepPathAmplitudeCandidate` | `machineChecked` typed skeleton |
| 双路径候选振幅 | `Foundation/Modern/QuantumRelativityTwoPathInterferenceBridge.lean` | `two_route_upper_amplitude`、`two_route_lower_amplitude` | `machineChecked` |
| 有限两路径相消 | `Foundation/Modern/QuantumRelativityTwoPathInterferenceBridge.lean` | `two_route_pair_amplitude_cancels`、`two_route_cancelled_born_weight_zero` | `machineChecked` |
| S5c 公开摘要 | `Foundation/Modern/QuantumRelativityTwoPathInterferenceBridge.lean` | `two_path_interference_bridge_summary` | `machineChecked` |
| S5d 离散相位 follow-up | `Foundation/Modern/QuantumRelativityDiscretePhaseBridge.lean` | `discrete_phase_bridge_summary` | `machineChecked` |
| S5e 离散作用量相位 follow-up | `Foundation/Modern/QuantumRelativityDiscreteActionBridge.lean` | `discrete_action_phase_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S5c 的主张很窄：

```text
S5b nonzero path-amplitude candidate
+ middle-preserving two-step path witness
+ same-endpoint / different-middle pair
+ finite two-path candidate sum: 1 + (-1) = 0
+ Born-shaped zero-boundary: ampProb 0 = 0
= two-path cancellation candidate boundary
```

它不证明路径积分，不证明真实相位动力学，不证明 Born rule 从 Markov 桥推出，不证明 unitary/CPTP channel law，不证明 decoherence，也不证明经验闭合。
S5d 后续把 `1/-1` 候选振幅改写为 `zero/pi` 离散 phase labels 导出的振幅；S5e 后续把 path phase 改写为 edge increments 的有限累积。

正面结论是：

```text
S5c 已把 S5 的抽象相消 witness
推进到同端点、不同中间态 two-step paths 上；
S5d 又把这组 `1/-1` 候选振幅
推进到 `zero/pi` 离散 phase labels 的导出读法；
S5e 继续把整条路径标签推进到 edge phase increments 的累积读法。
```

公开摘要为：

```lean
theorem two_path_interference_bridge_summary :
    HasFiniteProbabilityProjection twoRouteProcess
    ∧ HasQuantumChannelCandidate twoRouteProcess
    ∧ HasPathAmplitudeProjection twoRouteProcess
    ∧ HasTwoStepPathAmplitudeCandidate twoRouteProcess
    ∧ HasSameEndpointTwoStepPair twoRouteProcess
    ∧ ...
    ∧ twoStepPairAmplitudeSum
        twoRouteTwoStepAmplitudeCandidate
        twoRouteUpperLowerPair = 0
    ∧ (bornRuleCandidate
        (twoStepPairAmplitudeSum
          twoRouteTwoStepAmplitudeCandidate
          twoRouteUpperLowerPair)).candidateWeight = 0
    ∧ WenConstructiveCoverage
```

该 theorem 已通过 `lake build SSBX.Foundation.Modern.QuantumRelativityTwoPathInterferenceBridge`。

---

## 〇一 · 边界声明

| 说法 | 本文状态 | 精确含义 |
|---|---|---|
| `ProcessPath` 丢失中间路径身份 | `machineChecked` interface response | 新增 `TwoStepPathWitness`，保留 `start / middle / stop` |
| 两条路径同端点 | `machineChecked` | `twoRouteUpperPath` 与 `twoRouteLowerPath` 同起点 `source`、同终点 `target` |
| 两条路径中间态不同 | `machineChecked` | 上路中间态 `upper`，下路中间态 `lower` |
| two-route toy process | `machineChecked` typed witness | `source -> upper -> target` 与 `source -> lower -> target` |
| finite probability / channel candidate | `machineChecked` typed skeleton | `twoRouteFiniteProbabilityKernel` 与 `twoRouteQuantumChannelSkeleton` |
| endpoint-only path amplitude projection | `machineChecked` typed skeleton | 复用 S5b 的 `validPathIndicatorPathAmplitudeSkeleton` |
| middle-preserving amplitude candidate | `machineChecked` typed skeleton | `TwoStepPathAmplitudeCandidate` 对 two-step witness 赋候选振幅 |
| upper amplitude = `1` | `machineChecked` | `two_route_upper_amplitude` |
| lower amplitude = `-1` | `machineChecked` | `two_route_lower_amplitude` |
| finite two-path sum cancels | `machineChecked` | `two_route_pair_amplitude_cancels` 证明 `1 + (-1) = 0` |
| Born-shaped zero boundary | `machineChecked` | `two_route_cancelled_born_weight_zero` 证明取消后的候选权重为 `0` |
| 离散 phase-label 来源 | S5c 未纳入；S5d 已开单独接口 | `discrete_phase_bridge_summary` 证明 `zero/pi` 标签导出 `1/-1` |
| 离散 edge-action phase 来源 | S5c 未纳入；S5e 已开单独接口 | `discrete_action_phase_bridge_summary` 证明 edge increments 累积为 path phase |
| 一般 path integral | 未纳入本轮 | 没有 over all paths、measure、limit 或 action functional |
| 相位 / 作用量动力学 | 未纳入本轮 | 振幅符号由 toy candidate 指定，不由 Hamiltonian、action 或 unitary law 推出 |
| Born rule 推导 | 未纳入本轮 | 只证明 `ampProb 0 = 0` 的 boundary，不从 Markov 权重推出 Born rule |
| 真实可测干涉 | 未纳入本轮 | 没有 observation ledger、实验设置、数据判准或可测预测 |

边界句：

```text
S5c 关闭的是 middle-preserving two-step finite cancellation candidate；
它不是物理干涉定律，也不是 Born rule 或路径积分的推导。
```

---

## 〇二 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| 中间态保留 | `TwoStepPathWitness` | 弥补 `ProcessPath` 只保留外端点的问题 |
| 同端点双路径 | `SameEndpointTwoStepPair`、`twoRouteUpperLowerPair` | 可在 Lean 中记录“两条不同中间态的同端点路径” |
| toy process | `twoRouteProcess` | 最小四状态两路过程 |
| finite probability boundary | `twoRouteFiniteProbabilityKernel` | two-route process 仍接回 S2 有限概率核接口 |
| channel candidate | `twoRouteQuantumChannelSkeleton` | two-route process 仍接回 S4 channel candidate |
| endpoint-only path amplitude | `twoRoutePathAmplitudeSkeleton` | S5b 的 valid-path indicator projection 可用于 two-route process |
| two-step amplitude | `twoRouteTwoStepAmplitudeCandidate` | middle-preserving candidate 给 upper/lower 分配 `1/-1` |
| upper/lower 数值 | `two_route_upper_amplitude`、`two_route_lower_amplitude` | 两条候选振幅被机器检查 |
| cancellation | `two_route_pair_amplitude_cancels` | 有限两路径候选和为零 |
| Born-shaped zero | `two_route_cancelled_born_weight_zero` | 相消后接回 `bornRuleCandidate`，候选权重为 `0` |
| 离散相位标签 | S5c 未纳入；S5d 已开单独接口 | `zero/pi` 到 `1/-1` 的候选导出 |
| 离散作用量相位 | S5c 未纳入；S5e 已开单独接口 | edge increments 到 path phase 的候选导出 |
| 公开摘要 | `two_path_interference_bridge_summary` | 合取 S2/S4/S5/S5b 边界、two-route witness、finite cancellation 与 Wen coverage |

尚未闭合：

| 轴 | 状态 | 说明 |
|---|---|---|
| 一般路径族求和 | 未纳入本轮 | 本轮只有两条路径的有限和 |
| phase/action law | 未纳入本轮 | 没有从作用量或动力学推出相位 |
| path integral | 未纳入本轮 | 没有路径空间、测度或极限过程 |
| unitary/CPTP law | 未纳入本轮 | channel 仍是 candidate skeleton |
| Born rule derivation | 未纳入本轮 | 只复用 `ampProb` 形状 |
| decoherence / measurement model | 未纳入本轮 | 没有环境、密度矩阵或测量仪器模型 |
| empirical closure | 未纳入本轮 | S5q 已补 pending observable ledger；仍没有数据接口、误差模型或实验闭合 |

本轮闭合范围：**S5c 已在 Lean 中关闭“同端点、不同中间态的两条 two-step candidate paths 可携带 `1` 与 `-1`，其有限和为 `0`，并且相消后的 Born-shaped candidate weight 为 `0`”这个 typed skeleton；S5d 后续关闭 discrete phase-label candidate；S5e 后续关闭 discrete edge-action phase accumulation candidate；它们不关闭一般路径积分、连续相位/作用量动力学、Born rule 推导、unitary/CPTP channel law、decoherence 或经验闭合。**

---

## 一 · 为什么需要 `TwoStepPathWitness`

S5b 的 `ProcessPath` 只有：

```text
start / stop / valid
```

这足以证明“非零候选振幅不跑出 path / causal boundary”，但不足以区分：

```text
source -> upper -> target
source -> lower -> target
```

因为两条路径的外端点相同。S5c 因此新增 `TwoStepPathWitness`，把 `middle` 作为结构字段保留下来；再用 `SameEndpointTwoStepPair` 记录“同端点但中间态不同”。

---

## 二 · two-route toy witness

`twoRouteProcess` 是一个纯 toy witness：

```text
source
  -> upper -> target
  -> lower -> target
```

其中 `source` 行的有限分母为 `2`，`upper/lower` 行的有限分母为 `1`，`target` 为终端行。它只证明当前接口可承载两路候选结构，不声称这是物理双缝模型。

---

## 三 · 有限相消与 Born-shaped boundary

S5c 的核心数值是：

```text
upper amplitude = 1
lower amplitude = -1
finite sum = 0
candidateWeight = ampProb 0 = 0
```

这一步比 S5 的抽象 `InterferenceCandidate` 更强，因为它把相消 witness 接到了两条同端点、不同中间态的 candidate paths；但它仍不是物理干涉律，因为相位来源、路径族选择、实验读数和概率归一化都还没有进入 theorem。

---

## 四 · Validation Command

Lean 验证命令：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityTwoPathInterferenceBridge
lake build SSBX.Foundation.Modern.QuantumRelativityDiscretePhaseBridge
lake build SSBX.Foundation.Modern.QuantumRelativityDiscreteActionBridge
lake build SSBX
```

文档与格式检查：

```bash
python3 scripts/docs_next.py build --out docs-next/_generated --clean
python3 scripts/docs_next.py check --out docs-next/_generated --strict
git diff --check -- formal/SSBX/Foundation/Modern/QuantumRelativityTwoPathInterferenceBridge.lean formal/SSBX/Foundation/Modern/QuantumRelativityDiscretePhaseBridge.lean formal/SSBX/Foundation/Modern/QuantumRelativityDiscreteActionBridge.lean formal/SSBX.lean formal/SSBX/notes/unification-stepwise-plan.md formal/SSBX/notes/markov-causal-bridge-verification-plan.md formal/SSBX/notes/markov-causal-bridge-plan.md docs-next/10_formal_形式/modern.md '义理/双路径相消候选 · Markov桥S5c.md' '义理/离散相位标记候选 · Markov桥S5d.md' '义理/离散作用量相位候选 · Markov桥S5e.md' '义理/非零路径振幅候选 · Markov桥S5b.md' '义理/干涉与测量律候选 · Markov桥S5.md' '义理/Markov因果桥 · 大统一最小验证构造.md'
```
