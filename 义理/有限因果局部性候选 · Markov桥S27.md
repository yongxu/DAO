# 有限因果局部性候选 · Markov桥S27

**前置**：[路径组合与因果约束 · Markov桥S3](路径组合与因果约束%20·%20Markov桥S3.md) · [有限作用量极值候选 · Markov桥S26](有限作用量极值候选%20·%20Markov桥S26.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**后续**：[有限因果区间候选 · Markov桥S28](有限因果区间候选%20·%20Markov桥S28.md) 已把本页的 one-step localFuture locality 加厚为 displayed two-step causal interval candidate。

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| finite local future | `Foundation/Modern/QuantumRelativityFiniteCausalLocalityBridge.lean` | `FiniteCausalLocalFutureCandidate` | `machineChecked` |
| step/local equivalence | `Foundation/Modern/QuantumRelativityFiniteCausalLocalityBridge.lean` | `local_future_iff_step`、`step_depends_on_local_future` | `machineChecked` |
| causal readback | `Foundation/Modern/QuantumRelativityFiniteCausalLocalityBridge.lean` | `local_future_implies_causal_before`、`nonlocal_not_one_step` | `machineChecked` |
| kernel locality | `Foundation/Modern/QuantumRelativityFiniteCausalLocalityBridge.lean` | `KernelRespectsLocalFuture`、`kernel_positive_weight_implies_local_future` | `machineChecked` |
| concrete/grid witnesses | `Foundation/Modern/QuantumRelativityFiniteCausalLocalityBridge.lean` | `concreteCausalLocalFuture`、`operatorCellGridCausalLocalFuture` | `machineChecked` |
| S27 summary | `Foundation/Modern/QuantumRelativityFiniteCausalLocalityBridge.lean` | `finite_causal_locality_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S27 关闭的是一个有限 one-step 因果局部性候选：

```text
finite process state
-> finite localFuture list
-> b ∈ localFuture a iff step a b
-> nonlocal target cannot be a one-step successor
-> positive Markov kernel weight targets localFuture
-> localFuture membership gives causalBefore
```

公开摘要为：

```lean
theorem finite_causal_locality_bridge_summary :
    FiniteCausalLocalityClosed
    ∧ TwoRouteFiniteActionExtremumClosed
    ∧ FinitePathSpaceActionFunctionalClosed
    ∧ (∀ {P : FiniteProcess} (c : ComposableProcessPaths P),
        causalBefore (P := P) ⟨c.left.start⟩ ⟨c.right.stop⟩)
    ∧ CodeSuccessorStep concreteProcess
    ∧ CodeSuccessorStep operatorCellGridProcess
    ∧ (∀ b : PendingBeyondS27, ClosedByStepwiseS27 b = false)
    ∧ WenConstructiveCoverage
```

---

## 〇一 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| finite local future | `FiniteCausalLocalFutureCandidate` | 每个状态有一个有限 list 作为下一步局部未来邻域 |
| exact step support | `local_future_iff_step` | `localFuture` 精确等于 one-step transition support |
| local causal readback | `local_future_implies_causal_before` | 局部未来成员可读成 `causalBefore` |
| nonlocal exclusion | `nonlocal_not_one_step` | 不在局部未来 list 中则不能是一步 successor |
| kernel locality | `kernel_positive_weight_implies_local_future` | 正 Markov 权重目标落在局部未来 list |
| concrete local future | `concreteCausalLocalFuture` | `prepared -> [evolved]`、`evolved -> [measured]`、`measured -> []` |
| grid local future | `operatorCellGridCausalLocalFuture` | `94976` grid 的 successor index 给出局部未来 list |
| S27 summary | `finite_causal_locality_bridge_summary` | S27 接回 S26/S25、S3 path causal boundary 与 Wen coverage |

未纳入本轮：

| 项 | 原因 |
|---|---|
| local finite interval candidate | 已由 S28 承接为 displayed two-step causal interval candidate；仍非全局 causal set local finiteness |
| full causal set axioms | 本轮只处理 one-step localFuture，不证明完整反身、传递、反对称或任意长度 causal interval |
| light cone / Lorentzian locality | 没有连续时空、锥结构、度规或 Lorentzian manifold |
| metric recovery | 没有从有限可达结构恢复距离或曲率 |
| relativistic field locality | 没有场、算符代数或 spacelike commutativity |
| smooth/infinite-dimensional path-space action | 仍沿用 S25/S26 的有限 quotient support |
| stationary action / Euler-Lagrange / Hamiltonian | 没有 continuous variation、运动方程或动力学生成律 |
| general path integral / Hilbert measurement / decoherence | 没有路径测度、一般测量公设或环境模型 |
| empirical closure | 没有数据、误差模型、阈值或可测预言 theorem |

本轮闭合范围：**finite one-step localFuture list 与 Markov kernel support locality**。

---

## 一 · 为什么这一步必要

S3 已有 code-successor / no-self-loop，说明一步转移有方向性。S27 补的是局部性接口：

```text
state a
-> explicit finite localFuture a
-> all one-step targets are exactly inside that list
```

因此“下一步只依赖局部邻域”在当前 typed skeleton 中变成了可检查命题，而不是解释性文字。

---

## 二 · 边界读法

这里的“局部性”必须按窄义读：

```text
finite localFuture list
one-step support iff list membership
positive kernel weight respects that support
```

它不是完整相对论局部性。完整物理级还需要：

```text
causal set axioms
arbitrary-length finite intervals
light cones
Lorentzian metric
relativistic field locality
data-bearing predictions
```

---

## 三 · 失败记录

S27 第一次 build：

```text
命令：lake build SSBX.Foundation.Modern.QuantumRelativityFiniteCausalLocalityBridge
失败点：concrete_nonlocal_measured_not_step_to_prepared；operatorCellGrid_initial_local_future
原因：`List` membership 的 decidability 没有自动合成；`Fin` list equality 暴露不同 proof terms
修正：改用显式 empty-list nonmembership proof；grid 初态局部未来改写为 length boundary
结果：进入第二次 build
```

S27 第二次 build：

```text
命令：lake build SSBX.Foundation.Modern.QuantumRelativityFiniteCausalLocalityBridge
失败点：operatorCellGrid_initial_local_future_length
原因：`simp` 将目标化为 singleton list length，但没有自动以 definitional equality 关闭
修正：在 `simp [allOperatorCells_length]` 后补 `rfl`
结果：目标模块 build 通过
```

当前目标模块的验证命令为：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityFiniteCausalLocalityBridge
```
