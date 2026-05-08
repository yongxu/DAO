# Markov因果桥 · 大统一最小验证构造

**前置**：[量子与相对论整合方向 · 从桥到新理论](量子与相对论整合方向%20·%20从桥到新理论.md) · [量子与相对论直统一不可能 · 当前语言NoGo](量子与相对论直统一不可能%20·%20当前语言NoGo.md) · [`markov-causal-bridge-plan`](../formal/SSBX/notes/markov-causal-bridge-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| 直统一 no-go | `Foundation/Modern/QuantumRelativityNoGo.lean` | `no_direct_unification_by_addition` 排除当前语言直接相加 | `machineChecked` |
| 中介桥方向 | `Foundation/Modern/QuantumRelativityIntegration.lean` | `only_mediated_bridge_is_framework_route` 定位正向路线为中介桥 | `machineChecked` |
| 桥项双投影 | `Foundation/Modern/QuantumRelativityIntegration.lean` | `BridgeTerm`、`bridge_projections_same_one`、`bridge_projections_not_current_identity` | `machineChecked` |
| Markov-因果桥载体 | `Foundation/Modern/QuantumRelativityMarkovBridge.lean` | `FiniteProcess`、`state_code_within_bound`、`ProcessPath`、`path_implies_reachable` | `machineChecked` |
| Markov 读法 | `Foundation/Modern/QuantumRelativityMarkovBridge.lean` | `MarkovKernelSkeleton`、`positive_weight_implies_step`、`pathWeight` | `machineChecked` |
| 因果读法 | `Foundation/Modern/QuantumRelativityMarkovBridge.lean` | `CausalEvent`、`causalBefore`、`step_implies_causal_before` | `machineChecked` |
| 测量-事件对齐 | `Foundation/Modern/QuantumRelativityMarkovBridge.lean` | `MeasurementEventBridge`、`measurement_event_alignment` | `machineChecked` |
| 桥接边界 | `Foundation/Modern/QuantumRelativityMarkovBridge.lean` | `MeasurementEventBridge.toBridgeTerm`、`measurement_event_bridge_term_keeps_faces`、`markov_bridge_keeps_quantum_and_relativity_faces`、`markov_bridge_same_one_not_identity`、`markov_bridge_not_direct_language_addition` | `machineChecked` |
| 公开摘要 | `Foundation/Modern/QuantumRelativityMarkovBridge.lean` | `markov_causal_bridge_summary` | `machineChecked` |

> 本文回答第三个问题：
>
> **如果中介桥是正向整合方向，第一块最小可验证构造应当是什么？**
>
> 答：先不要从完整 Hilbert 空间、Lorentzian geometry 或量子引力方程开始，而从一个有限过程结构开始。这个有限过程同时允许两种投影：一侧读成 Markov / 测量过程，另一侧读成事件 / 因果结构。若终端状态在两种读法下可对齐，则“测量结果成为事件”至少获得一个可检查的 typed skeleton。

---

## 〇 · Claim Block

本文主张很窄：

```text
最小桥接尝试 =
  有限过程载体
  + Markov / 测量投影
  + 因果 / 事件投影
  + 终端状态的测量-事件对齐
  + 仍服从 current-language no-go
```

这不是量子引力理论，也不是“大统一已经完成”。它只把上一层的“中介桥方向”推进为一个候选最小构造：同一个有限过程对象可以被双读，并且终端状态可以同时被读为测量结果与事件记录。

公开摘要为：

```lean
theorem markov_causal_bridge_summary :
    HasMarkovProjection P
    ∧ HasCausalProjection P
    ∧ MeasurementEventsAlign b
    ∧ keepsQuantumFace MarkovCausalRoute = true
    ∧ keepsRelativityFace MarkovCausalRoute = true
    ∧ sameOne .quantumSpace .relativisticSpacetime
    ∧ ¬ CurrentPhysicalUnity .quantumSpace .relativisticSpacetime
    ∧ ¬ DirectUnificationByAddition
```

该 theorem 已通过 `lake build SSBX.Foundation.Modern.QuantumRelativityMarkovBridge`。

---

## 〇一 · 边界声明

本文只给 companion 文档与最小构造边界，不声称完成物理统一。

| 说法 | 本文状态 | 精确含义 |
|---|---|---|
| 当前语言直接相加不可行 | `machineChecked` | 复用 `no_direct_unification_by_addition` |
| 正向方向应为中介桥 | `machineChecked` | 复用 `only_mediated_bridge_is_framework_route` |
| Markov-因果桥是候选中介载体 | `machineChecked` typed skeleton | Lean 模块已构建通过 |
| 终端状态可读成测量结果与事件记录 | `machineChecked` typed skeleton | 由 `measurement_event_alignment` 关闭 |
| 该桥不是 direct language addition | `machineChecked` bridge target | 复用 no-go 的 `markov_bridge_not_direct_language_addition` |
| 归一化概率 / Born rule | 未纳入本轮 | 初版最多用支持集与 `Nat` 权重 |
| 复幅、干涉、量子通道 | 未纳入本轮 | 后续才从经典 Markov 结构升级 |
| Lorentzian geometry / 度规恢复 | 未纳入本轮 | 初版只保留事件与可达因果接口 |
| 反对称性、局部性、经典极限 | 未纳入本轮 | 需要更强结构与额外 theorem |
| 经验预言与实验闭合 | 未纳入本轮 | 尚无 pending ledger / 数据接口 |

边界句：

```text
Markov 因果桥只验证“测量结果作为事件”的有限过程骨架；
它不证明完整量子理论、不证明广义相对论、不证明二者的最终统一。
```

---

## 〇二 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| 直统一 no-go | `no_direct_unification_by_addition` | 现成量子语言与相对论语言的 tagged addition 不能产生直接统一项 |
| 中介桥方向 | `only_mediated_bridge_is_framework_route` | 若保留两面并新增中介，正向路线是 `mediatedBridge` |
| 桥项双投影 | `BridgeTerm`、`bridge_projections_same_one`、`bridge_projections_not_current_identity` | 中介项可双投影、同根，但不是当前 face identity |

typed skeleton / machineChecked in this branch：

| 轴 | 目标锚点 | 当前状态 |
|---|---|---|
| 有限过程载体 | `FiniteProcess`、`state_code_within_bound` | `machineChecked` typed skeleton |
| 路径接口 | `ProcessPath`、`path_implies_reachable` | `machineChecked` typed skeleton |
| 终端测量候选 | `terminal_as_measurement_candidate` | `machineChecked` typed skeleton |
| Markov 支持 / 权重 | `MarkovKernelSkeleton` | `machineChecked` typed skeleton |
| 非零权重推出一步可达 | `positive_weight_implies_step` | `machineChecked` theorem |
| 因果事件投影 | `CausalEvent`、`causalBefore` | `machineChecked` typed skeleton |
| 一步转移推出因果先后 | `step_implies_causal_before` | `machineChecked` theorem |
| 测量-事件桥 | `MeasurementEventBridge` | `machineChecked` typed skeleton |
| 测量事件对齐 | `measurement_event_alignment` | `machineChecked` theorem |
| 桥项投影 | `MeasurementEventBridge.toBridgeTerm`、`measurement_event_bridge_term_keeps_faces` | `machineChecked` theorem |
| Markov 桥保留两面 | `markov_bridge_keeps_quantum_and_relativity_faces` | `machineChecked` theorem |
| 同根非同一 | `markov_bridge_same_one_not_identity` | `machineChecked` theorem |
| 公开摘要 | `markov_causal_bridge_summary` | `machineChecked` theorem |

未纳入本轮：

| 轴 | 状态 | 说明 |
|---|---|---|
| 概率归一化 | 未纳入本轮 | 初版只需“可转移 / 权重非零”的结构事实 |
| 路径权重乘法定律 | 未纳入本轮 | `pathWeight` 可先作为接口占位 |
| Born rule | 未纳入本轮 | 不从该有限骨架直接推出物理概率律 |
| Quantum channel / amplitude | 未纳入本轮 | 需下一层从 Markov skeleton 升级 |
| 干涉 | 未纳入本轮 | 经典 Markov 加法不足以表达相位抵消 |
| 因果集公理 | 未纳入本轮 | 本轮不证明偏序、局部有限性或 manifold recovery |
| 度规与曲率 | 未纳入本轮 | 需要几何极限或额外重建结构 |
| 经验闭合 | 未纳入本轮 | 尚无可测差异与数据判准 |

本轮闭合范围：**Markov-因果桥的最小 typed skeleton 已在 Lean 中关闭；它只关闭有限过程双读、测量-事件对齐、同根非同一与 no-go 保持，不关闭概率归一化、Born rule、量子通道、干涉、度规恢复或经验闭合。**

---

## 一 · 最小载体：有限过程

第一步的中介载体不是连续时空，也不是完整态空间，而是有限过程：

```text
Finite Markov-Causal Process
├─ state：带有有界自然数编码的有限状态骨架
├─ initial：初态
├─ terminal：终态谓词
├─ step：一步转移关系
└─ path：从初态到终态的有效过程记录
```

它的优势是可先在 Lean 中证明结构事实：

| 结构事实 | 目标锚点 | 读法 |
|---|---|---|
| 状态编码落在有限界内 | `state_code_within_bound` | 本轮至少把“有限”写成有界编码见证 |
| 有效路径给出可达关系 | `path_implies_reachable` | 过程中的路径不是散点集合，而是方向性连接 |
| 终端状态可作测量候选 | `terminal_as_measurement_candidate` | 到达终端时，状态可进入“结果 / 记录”读法 |

这里的“有限”不是最终世界图像，只是第一轮验证策略：先用最少依赖关闭双读骨架，再决定哪些接口需要升级。

---

## 二 · Markov 读法

在 Markov 读法中，同一过程被看成状态转移系统：

| Markov 侧对象 | 初版读法 | 非目标 |
|---|---|---|
| 状态 | 候选测量前后的过程节点 | 不等同完整 Hilbert 态 |
| 转移 | 下一步支持集或权重 | 不要求概率归一化 |
| 路径 | 可能历史 | 不先证明路径积分 |
| 终端 | 测量结果候选 | 不先证明 Born rule |

初版使用 `Nat` 权重，只证明：

```text
权重非零 -> 存在一步转移
```

也就是本轮已关闭的 theorem：

```lean
theorem positive_weight_implies_step :
    ...
```

这只证明 Markov skeleton 与过程转移一致，不证明真实概率模型已经完成。

---

## 三 · 因果读法

在因果读法中，同一过程被看成事件结构：

| 因果侧对象 | 初版读法 | 非目标 |
|---|---|---|
| 状态投影 | 候选事件 | 不等同连续时空点 |
| 一步转移 | 直接因果边 | 不等同光锥几何 |
| 可达闭包 | 过去 / 未来方向 | 不先证明完整偏序 |
| 终端状态 | 事件记录 | 不先恢复度规 |

本轮已关闭的 theorem 是：

```lean
theorem step_implies_causal_before :
    ...
```

它只表达“过程方向可以被读成因果方向”。反过来的完备性、反对称性、局部有限性、Lorentzian geometry 与 metric recovery 都不在本轮。

---

## 四 · 测量-事件对齐

桥接的最小突破点在终端状态：

| 同一底层状态 | Markov / 测量读法 | 因果 / 事件读法 |
|---|---|---|
| `s : State` 且 `terminal s` | 测量结果候选 | 事件记录候选 |

实际结构可读成：

```lean
structure MeasurementEventBridge where
  terminalState : State
  isTerminal : terminal terminalState

def MeasurementEventBridge.measurementCandidate ...
def MeasurementEventBridge.eventRecord ...
def MeasurementEventBridge.toBridgeTerm ...
```

本轮已关闭的 theorem：

```lean
theorem measurement_event_alignment :
    ...
```

概念读法是：

```text
同一个终端状态
= 在 Markov 投影下的测量结果
= 在因果投影下的事件记录
```

这一步不把量子项和相对论项直接相加。它是在一个新中介载体中给出共享底层状态，再分别投影到两套读法。因此它必须继续带着 no-go 边界：

```lean
no_direct_unification_by_addition
```

---

## 五 · 与中介桥层对接

上一层 `QuantumRelativityIntegration` 已经证明：

```text
正向路线 = mediatedBridge
```

本层要做的是把 `mediatedBridge` 的空位具体化为一个有限过程候选：

| 上一层抽象项 | 本层候选解释 |
|---|---|
| `BridgeTerm` | 有限 Markov-因果过程的双投影 |
| `quantumProjection` | Markov / 测量侧读法 |
| `relativityProjection` | 因果 / 事件侧读法 |
| `sameOne` | 两投影共享同一底层过程 |
| `¬ CurrentPhysicalUnity` | 两投影不被偷换成旧语言对象同一 |

本轮已关闭这些桥接 theorem：

```lean
theorem measurement_event_bridge_term_keeps_faces :
    b.toBridgeTerm.quantumFace = .quantumSpace
    ∧ b.toBridgeTerm.relativityFace = .relativisticSpacetime

theorem markov_bridge_keeps_quantum_and_relativity_faces :
    keepsQuantumFace MarkovCausalRoute = true
    ∧ keepsRelativityFace MarkovCausalRoute = true

theorem markov_bridge_same_one_not_identity :
    sameOne .quantumSpace .relativisticSpacetime
    ∧ ¬ CurrentPhysicalUnity .quantumSpace .relativisticSpacetime
```

因此，“中介桥方向”现在获得了第一块可复用的有限构造。但这仍只是 typed skeleton，不是物理动力学或经验闭合。

---

## 六 · Exploration Directions

后续探索分层推进，不在本文档中提前打勾。

| 方向 | 目标 | 当前状态 |
|---|---|---|
| 概率核 | 从支持集 / `Nat` 权重升级到归一化 Markov kernel | 未纳入本轮 |
| 量子通道 | 从经典转移升级为 channel / amplitude skeleton | 未纳入本轮 |
| 干涉 | 让路径权重能表达相位与抵消 | 未纳入本轮 |
| 因果局部性 | 下一步只依赖局部过去或邻域 | 未纳入本轮 |
| 因果集接口 | 加入偏序、局部有限性与事件网络公理 | 未纳入本轮 |
| 几何极限 | 从稳定可达结构恢复粗粒度时空 / 度规 | 未纳入本轮 |
| 经典极限 | 回收普通事件记录与宏观因果结构 | 未纳入本轮 |
| 经验接口 | 把候选可测差异写入 pending ledger | 未纳入本轮 |

探索顺序建议：

```text
有限过程双读
-> 测量-事件对齐
-> Markov 权重与路径接口
-> 因果约束加强
-> 量子通道 / 干涉升级
-> 几何与经验接口
```

---

## 七 · Result Log

记录格式：成功只记录已有可检查产物；失败或未完成不打勾。

| 日期 | 项目 | 结果 | 说明 |
|---|---|---|---|
| 2026-05-08 | companion Markdown | success | 本文档创建，给出最小 Markov-因果桥构造、边界声明、审计与验证命令 |
| 2026-05-08 | Lean module | success | `QuantumRelativityMarkovBridge.lean` 创建并通过目标构建 |
| 2026-05-08 | finite carrier audit | success | 原草案只写 `State : Type`；后补 `stateCode/stateBound/stateCode_lt_bound/stateCode_injective`，把“有限”收窄为有界编码 skeleton |
| 2026-05-08 | `BridgeTerm` projection | success | 新增 `MeasurementEventBridge.toBridgeTerm` 与 `measurement_event_bridge_term_keeps_faces`，把本层桥接到上一层 tag-level `BridgeTerm` |
| 2026-05-08 | first native `lake build` | infrastructure failure / retained | 新 worktree 首次构建卡在 `mathlib4` 克隆超过十分钟，尚未进入 Lean 检查；这不是 theorem 失败 |
| 2026-05-08 | cache-assisted `lake build SSBX.Foundation.Modern.QuantumRelativityMarkovBridge` | success | 改用主 worktree 同 revision 依赖缓存后通过，输出 `Build completed successfully (6 jobs).` |
| 2026-05-08 | `markov_causal_bridge_summary` | `machineChecked` | 关闭 Markov 投影、因果投影、测量-事件对齐、两面保留、同根非同一、no-go 保持 |
| 2026-05-08 | `lake build SSBX` | success with existing warnings | 顶层 import 构建通过，输出 `Build completed successfully (2885 jobs).`；警告来自既有 Wen 模块 unused simp args，不来自本轮新增 Markov 模块 |
| 2026-05-08 | verification plan | success | 新增 `formal/SSBX/notes/markov-causal-bridge-verification-plan.md`，记录回归验证、锚点审计、边界审计、升级路线与失败模板 |

---

## 八 · Validation Command

Lean 验证命令：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
lake build SSBX
```

文档与索引格式检查：

```bash
git diff --check -- formal/SSBX/Foundation/Modern/QuantumRelativityMarkovBridge.lean formal/SSBX.lean formal/SSBX/notes/markov-causal-bridge-plan.md formal/SSBX/notes/markov-causal-bridge-verification-plan.md docs-next/10_formal_形式/modern.md '义理/Markov因果桥 · 大统一最小验证构造.md'
```

一句话总结：

> Markov 因果桥不是最终统一理论，而是把“测量结果成为事件”压成一个有限、双投影、可验证的最小 skeleton；本轮已关闭 skeleton，下一轮才升级概率核、量子通道、干涉、因果约束、几何极限与经验接口。
