# Markov-Causal Bridge Verification Plan

目标：把 Markov-因果桥从“已能构建的 typed skeleton”推进到可重复验证的研究程序。本文只定义验证流程，不新增物理 claim。

关联文件：

| 文件 | 作用 |
|---|---|
| `formal/SSBX/Foundation/Modern/QuantumRelativityNoGo.lean` | tagged 物理语言非坍缩边界 |
| `formal/SSBX/Foundation/Modern/QuantumRelativityWenBoundary.lean` | `192 × 371` 文构造覆盖与 tagged 边界相容性 |
| `formal/SSBX/Foundation/Modern/QuantumRelativityMarkovBridge.lean` | 当前 machine-checked Lean 骨架 |
| `formal/SSBX/Foundation/Modern/QuantumRelativityConcreteBridge.lean` | 三状态 concrete bridge witness |
| `formal/SSBX/Foundation/Modern/OperatorCellGridMarkovBridge.lean` | `71232` operator-cell grid bridge process |
| `formal/SSBX/Foundation/Modern/QuantumRelativityFiniteProbabilityBridge.lean` | S2 finite probability-kernel denominator interface |
| `formal/SSBX/Foundation/Modern/QuantumRelativityPathCausalBridge.lean` | S3 path composition and local causal constraints |
| `formal/SSBX/Foundation/Modern/QuantumRelativityAmplitudeChannelBridge.lean` | S4 classical Markov / quantum amplitude-channel layered interface |
| `formal/SSBX/notes/markov-causal-bridge-plan.md` | 探索计划与完成记录 |
| `formal/SSBX/notes/unification-stepwise-plan.md` | 逐步完善到候选统一的阶段路线 |
| `义理/文构造完备与直相加边界.md` | 对 `current-language no-go` 旧说法的边界修正 |
| `义理/Markov因果桥 · 大统一最小验证构造.md` | 义理边界与 theorem 锚点说明 |
| `义理/有限概率核接口 · Markov桥S2.md` | S2 有限概率核接口 companion 文档 |
| `义理/路径组合与因果约束 · Markov桥S3.md` | S3 路径组合与局部因果约束 companion 文档 |
| `义理/经典Markov与量子振幅分层 · Markov桥S4.md` | S4 经典 Markov 与量子振幅 / 通道候选分层 companion 文档 |

## 当前验证结论

- [x] `QuantumRelativityMarkovBridge.lean` 可单独构建。
- [x] `SSBX` 顶层入口可构建并导入新模块。
- [x] `markov_causal_bridge_summary` 已关闭有限过程双读、测量-事件对齐、两面保留、同根非同一、tagged physical-language noncollapse 保持。
- [x] `MeasurementEventBridge.toBridgeTerm` 已把本层桥接到上一层 tag-level `BridgeTerm`。
- [x] `wen_constructive_boundary_summary` 已确认 `192 × 371` 文构造覆盖不受 tagged-language 边界否定。
- [x] `concrete_bridge_summary` 已给出三状态 `prepared → evolved → measured` concrete bridge witness。
- [x] `operator_cell_grid_markov_causal_bridge_summary` 已把 `371 × 192 = 71232` operator-cell grid 用作 finite process 状态空间。
- [x] `finite_probability_bridge_summary` 已关闭 concrete 与 `71232` grid 的有限概率核接口：非终端行分母非零，权重受行分母约束。
- [x] `path_causal_bridge_summary` 已关闭 path witness composition、组合后 reachability / `causalBefore`、concrete 与 grid 的 code-successor/no-self-loop 约束。
- [x] `amplitude_channel_bridge_summary` 已关闭 classical Markov / quantum amplitude-channel 分层候选接口：layer separation、channel candidate 到 S2 boundary 的投影、非零振幅支持精化。
- [x] 首次新 worktree 原生构建的 `mathlib4` 克隆阻塞已记录为基础设施失败，不当作 theorem 失败。
- [ ] 尚未验证 sum-one 概率律、Born rule 从 Markov 桥的推导、干涉、unitary / CPTP quantum channel law、完整因果偏序、局部有限 causal set、度规恢复或经验闭合。

## 每次变更的最低验证门槛

任何改动触及本桥相关 Lean 或文档时，至少执行：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityWenBoundary
lake build SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
lake build SSBX.Foundation.Modern.QuantumRelativityConcreteBridge
lake build SSBX.Foundation.Modern.OperatorCellGridMarkovBridge
lake build SSBX.Foundation.Modern.QuantumRelativityFiniteProbabilityBridge
lake build SSBX.Foundation.Modern.QuantumRelativityPathCausalBridge
lake build SSBX.Foundation.Modern.QuantumRelativityAmplitudeChannelBridge
lake build SSBX
git diff --check -- formal/SSBX/Foundation/Modern/QuantumRelativityNoGo.lean formal/SSBX/Foundation/Modern/QuantumRelativityIntegration.lean formal/SSBX/Foundation/Modern/QuantumRelativityWenBoundary.lean formal/SSBX/Foundation/Modern/QuantumRelativityMarkovBridge.lean formal/SSBX/Foundation/Modern/QuantumRelativityConcreteBridge.lean formal/SSBX/Foundation/Modern/OperatorCellGridMarkovBridge.lean formal/SSBX/Foundation/Modern/QuantumRelativityFiniteProbabilityBridge.lean formal/SSBX/Foundation/Modern/QuantumRelativityPathCausalBridge.lean formal/SSBX/Foundation/Modern/QuantumRelativityAmplitudeChannelBridge.lean formal/SSBX.lean formal/SSBX/notes/markov-causal-bridge-plan.md formal/SSBX/notes/markov-causal-bridge-verification-plan.md formal/SSBX/notes/unification-stepwise-plan.md docs-next/10_formal_形式/modern.md '义理/文构造完备与直相加边界.md' '义理/Markov因果桥 · 大统一最小验证构造.md' '义理/有限概率核接口 · Markov桥S2.md' '义理/路径组合与因果约束 · Markov桥S3.md' '义理/经典Markov与量子振幅分层 · Markov桥S4.md' '义理/量子与相对论直统一不可能 · 当前语言NoGo.md' '义理/量子与相对论整合方向 · 从桥到新理论.md' '义理/量子时空互补 · 从一到测.md'
```

通过标准：

| 门槛 | 通过标准 | 失败处理 |
|---|---|---|
| 目标模块构建 | `Build completed successfully` | 修 Lean；若失败来自依赖或网络，记录为 infra failure |
| 顶层入口构建 | `lake build SSBX` 通过 | 检查 import 顺序、命名冲突、旧模块影响 |
| 格式检查 | `git diff --check` 无输出 | 修尾随空格、冲突标记、缩进问题 |
| 状态词自审 | 无 stale `unchecked/planned/build pending` | 更新文档状态或撤回对应勾选 |

状态词自审命令：

```bash
rg -n "待处理|future|deferred|部分相关|佛|唯识|analogy|unchecked|planned|build pending|not run|not edited|failure-to-close" formal/SSBX/notes/markov-causal-bridge-plan.md formal/SSBX/notes/markov-causal-bridge-verification-plan.md formal/SSBX/notes/unification-stepwise-plan.md '义理/Markov因果桥 · 大统一最小验证构造.md' '义理/有限概率核接口 · Markov桥S2.md' '义理/路径组合与因果约束 · Markov桥S3.md' '义理/经典Markov与量子振幅分层 · Markov桥S4.md'
```

## Theorem 锚点审计

每次修改后确认这些锚点仍存在：

| 层 | 锚点 | 当前状态 |
|---|---|---|
| 有限载体 | `FiniteProcess`、`state_code_within_bound` | `machineChecked` |
| 路径与可达 | `ProcessPath`、`Reachable`、`path_implies_reachable` | `machineChecked` |
| Markov 读法 | `MarkovKernelSkeleton`、`positive_weight_implies_step`、`pathWeight` | `machineChecked` |
| 因果读法 | `CausalEvent`、`causalBefore`、`step_implies_causal_before` | `machineChecked` |
| 测量-事件对齐 | `MeasurementEventBridge`、`measurement_event_alignment` | `machineChecked` |
| 上层桥项投影 | `MeasurementEventBridge.toBridgeTerm`、`measurement_event_bridge_term_keeps_faces` | `machineChecked` |
| 中介路线边界 | `MarkovCausalRoute`、`markov_causal_route_is_framework_route` | `machineChecked` |
| 文构造边界修正 | `wen_constructive_boundary_summary` | `machineChecked` |
| concrete bridge witness | `concrete_bridge_summary` | `machineChecked` |
| operator-cell grid bridge | `operator_cell_grid_markov_causal_bridge_summary` | `machineChecked` |
| finite probability-kernel interface | `finite_probability_bridge_summary` | `machineChecked` |
| path composition and local causal constraints | `path_causal_bridge_summary` | `machineChecked` |
| classical Markov / quantum amplitude-channel layering | `amplitude_channel_bridge_summary` | `machineChecked` |
| tagged-language noncollapse 保持 | `markov_bridge_not_direct_language_addition` | `machineChecked` |
| 公开摘要 | `markov_causal_bridge_summary` | `machineChecked` |

审计命令：

```bash
rg -n "theorem|structure|def" formal/SSBX/Foundation/Modern/QuantumRelativityMarkovBridge.lean formal/SSBX/Foundation/Modern/QuantumRelativityConcreteBridge.lean formal/SSBX/Foundation/Modern/OperatorCellGridMarkovBridge.lean
```

## 边界审计

本桥当前只能说：

```text
同一个有限过程骨架
  可以有 Markov / 测量读法
  可以有因果 / 事件读法
  终端状态可以对齐成测量候选与事件记录
  可以承载与 classical Markov layer 分开的 quantum amplitude/channel candidate layer
  并且不取消当前 tagged 物理语言 noncollapse 边界
```

本桥当前不能说：

| 禁止提前声称 | 原因 |
|---|---|
| 已证明量子引力 | 没有动力学、连续极限、量子场或引力方程 |
| 已推出 Born rule | 有限行分母、权重上界和 S4 layer separation 都不是 Born-rule derivation |
| 已表达干涉 | S4 有复幅候选接口，但没有路径复幅组合、相位或路径相消 theorem |
| 已证明真实 quantum channel law | S4 的 `QuantumChannelSkeleton` 是 candidate interface；没有 unitary evolution、CPTP、Kraus 或 density-matrix law |
| 已恢复完整因果集或时空度规 | S3 只排除一步自环；没有偏序全公理、Lorentzian geometry 或 metric recovery theorem |
| 已给经验预言 | 没有 pending ledger、观测量或数据判准 |

文档中若出现这些强 claim，必须降级为 `未纳入本轮` 或新增相应 formal structure 后再验证。

## 下一轮升级验证路线

每一步都必须新增 Lean 锚点、更新义理边界、记录成功或失败。

| 阶段 | 目标 | 验证出口 |
|---|---|---|
| V1 | 给出一个具体有限实例 | 已由 `concrete_bridge_summary` 与 `operator_cell_grid_markov_causal_bridge_summary` 关闭 |
| V2 | 从 `Nat` 权重升级到有限概率核 | 已由 `finite_probability_bridge_summary` 关闭 finite denominator / bounded weights interface |
| V3 | 加强路径 / 因果组合 | 已由 `path_causal_bridge_summary` 关闭 path witness composition；`pathWeight` 乘法仍 pending |
| V4 | 加强因果结构 | S3 已关闭 code-successor/no-self-loop；完整偏序、局部有限性仍 pending |
| V5 | 引入 quantum channel / amplitude skeleton | 已由 `amplitude_channel_bridge_summary` 关闭候选接口；真实 channel law、干涉和 Born-rule derivation 仍 pending |
| V6 | 经验接口 | 把候选可测差异写入 pending ledger，而不是直接宣称实验闭合 |

## 失败记录模板

失败不能删除，应写入探索计划或本文：

```text
日期：
目标：
命令 / theorem：
失败类型：Lean proof failure / build failure / infra failure / conceptual overclaim
失败原因：
保留结论：
下一步：
```

## 当前命令记录

已执行并通过：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityMarkovBridge
lake build SSBX.Foundation.Modern.QuantumRelativityWenBoundary
lake build SSBX.Foundation.Modern.QuantumRelativityConcreteBridge
lake build SSBX.Foundation.Modern.OperatorCellGridMarkovBridge
lake build SSBX.Foundation.Modern.QuantumRelativityFiniteProbabilityBridge
lake build SSBX.Foundation.Modern.QuantumRelativityPathCausalBridge
lake build SSBX.Foundation.Modern.QuantumRelativityAmplitudeChannelBridge
lake build SSBX
git diff --check -- formal/SSBX/Foundation/Modern/QuantumRelativityNoGo.lean formal/SSBX/Foundation/Modern/QuantumRelativityIntegration.lean formal/SSBX/Foundation/Modern/QuantumRelativityWenBoundary.lean formal/SSBX/Foundation/Modern/QuantumRelativityMarkovBridge.lean formal/SSBX/Foundation/Modern/QuantumRelativityConcreteBridge.lean formal/SSBX/Foundation/Modern/OperatorCellGridMarkovBridge.lean formal/SSBX/Foundation/Modern/QuantumRelativityFiniteProbabilityBridge.lean formal/SSBX/Foundation/Modern/QuantumRelativityPathCausalBridge.lean formal/SSBX/Foundation/Modern/QuantumRelativityAmplitudeChannelBridge.lean formal/SSBX.lean formal/SSBX/notes/markov-causal-bridge-plan.md formal/SSBX/notes/markov-causal-bridge-verification-plan.md formal/SSBX/notes/unification-stepwise-plan.md docs-next/10_formal_形式/modern.md '义理/文构造完备与直相加边界.md' '义理/Markov因果桥 · 大统一最小验证构造.md' '义理/有限概率核接口 · Markov桥S2.md' '义理/路径组合与因果约束 · Markov桥S3.md' '义理/经典Markov与量子振幅分层 · Markov桥S4.md' '义理/量子与相对论直统一不可能 · 当前语言NoGo.md' '义理/量子与相对论整合方向 · 从桥到新理论.md' '义理/量子时空互补 · 从一到测.md'
```

备注：`lake build SSBX` 仍会输出既有 Wen 模块的 unused simp args linter 警告；本轮新增 Markov / WenBoundary / ConcreteBridge / OperatorCellGrid / FiniteProbabilityBridge / PathCausalBridge / AmplitudeChannelBridge 模块无警告。
