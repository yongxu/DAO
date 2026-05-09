# 路径组合与因果约束 · Markov桥S3

**前置**：[Markov因果桥 · 大统一最小验证构造](Markov因果桥%20·%20大统一最小验证构造.md) · [有限概率核接口 · Markov桥S2](有限概率核接口%20·%20Markov桥S2.md) · [经典Markov与量子振幅分层 · Markov桥S4](经典Markov与量子振幅分层%20·%20Markov桥S4.md) · [干涉与测量律候选 · Markov桥S5](干涉与测量律候选%20·%20Markov桥S5.md) · [非零路径振幅候选 · Markov桥S5b](非零路径振幅候选%20·%20Markov桥S5b.md) · [路径权重乘法候选 · Markov桥S19](路径权重乘法候选%20·%20Markov桥S19.md) · [文构造完备与直相加边界](文构造完备与直相加边界.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**后续**：[有限因果局部性候选 · Markov桥S27](有限因果局部性候选%20·%20Markov桥S27.md) 已把本页的 one-step causal boundary 加厚为 finite localFuture list：`step a b ↔ b ∈ localFuture a`。[有限因果区间候选 · Markov桥S28](有限因果区间候选%20·%20Markov桥S28.md) 进一步给出 displayed two-step causal interval candidate。

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| 路径组合接口 | `Foundation/Modern/QuantumRelativityPathCausalBridge.lean` | `ComposableProcessPaths`、`composeProcessPaths` | `machineChecked` |
| 组合路径有效性 | `Foundation/Modern/QuantumRelativityPathCausalBridge.lean` | `composed_path_valid` | `machineChecked` |
| 组合路径可达 | `Foundation/Modern/QuantumRelativityPathCausalBridge.lean` | `composed_path_reachable` | `machineChecked` |
| 组合路径因果读法 | `Foundation/Modern/QuantumRelativityPathCausalBridge.lean` | `composed_path_causal_before` | `machineChecked` |
| code-successor 约束 | `Foundation/Modern/QuantumRelativityPathCausalBridge.lean` | `CodeSuccessorStep`、`CodeMonotoneStep`、`code_successor_step_monotone` | `machineChecked` |
| no-self-loop 约束 | `Foundation/Modern/QuantumRelativityPathCausalBridge.lean` | `code_monotone_step_no_self_loop`、`concrete_no_self_step`、`operatorCellGrid_no_self_step` | `machineChecked` |
| S3 公开摘要 | `Foundation/Modern/QuantumRelativityPathCausalBridge.lean` | `path_causal_bridge_summary` | `machineChecked` |
| S19 路径权重乘法 | `Foundation/Modern/QuantumRelativityPathWeightMultiplicationBridge.lean` | `KernelPath.weight_append`、`path_weight_multiplication_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S3 的主张很窄：

```text
已有有限过程桥
+ 两段有效 path witness 可组合
+ 组合后外端点可达
+ 组合后可读成 causalBefore
+ concrete/grid 一步转移满足 code-successor
+ code-monotone step 排除一步自环
= path composition and local causal constraint interface
```

这一步不证明完整 path algebra，也不证明 causal set 的全部公理。它只把 S1/S2 的有限过程继续加厚为一个可组合路径接口，并在 concrete 与 `71232` grid witness 上验证最小局部方向性。

公开摘要为：

```lean
theorem path_causal_bridge_summary :
    (∀ {P : FiniteProcess} (c : ComposableProcessPaths P),
      Reachable P c.left.start c.right.stop)
    ∧ (∀ {P : FiniteProcess} (c : ComposableProcessPaths P),
      causalBefore (P := P) ⟨c.left.start⟩ ⟨c.right.stop⟩)
    ∧ CodeSuccessorStep concreteProcess
    ∧ CodeMonotoneStep concreteProcess
    ∧ (∀ a : ConcreteState, ¬ concreteProcess.step a a)
    ∧ CodeSuccessorStep operatorCellGridProcess
    ∧ CodeMonotoneStep operatorCellGridProcess
    ∧ (∀ a : OperatorCellGridState, ¬ operatorCellGridProcess.step a a)
    ∧ HasFiniteProbabilityProjection concreteProcess
    ∧ HasFiniteProbabilityProjection operatorCellGridProcess
    ∧ allOperatorCells.length = 71232
    ∧ WenConstructiveCoverage
```

该 theorem 已通过 `lake build SSBX.Foundation.Modern.QuantumRelativityPathCausalBridge`。

---

## 〇一 · 边界声明

| 说法 | 本文状态 | 精确含义 |
|---|---|---|
| 两段 path witness 可组合 | `machineChecked` | `left.stop = right.start` 且两段有效时，可形成外端点 path witness |
| 组合 path witness 给出 reachability | `machineChecked` | 复用 `path_implies_reachable` |
| 组合 path witness 给出 causalBefore | `machineChecked` | 因果读法仍是 `Reachable` 的事件投影 |
| concrete bridge code-successor | `machineChecked` | `prepared -> evolved -> measured` 每一步 code 加一 |
| `71232` grid code-successor | `machineChecked` | successor index 每一步 code 加一 |
| 一步自环排除 | `machineChecked` | code-monotone step 不可能有 `step a a` |
| pathWeight 乘法律 | `machineChecked` theorem | S19 保留旧 `pathWeight = 1` 的 placeholder law，并新增 `KernelPath.weight_append` 关闭有限 kernel path weight multiplication |
| 振幅干涉读法 | S3 未纳入；S5/S5b 已开候选接口 | S3 path composition 不被解释为路径振幅叠加或相消；S5/S5b 只记录 candidate，不证明真实干涉律 |
| 完整可达传递闭包 | 未纳入本轮 | 本轮只组合显式 path witness |
| 完整因果偏序 / causal set | 未纳入本轮 | 尚未证明反身、传递、反对称、局部有限全公理 |
| light cone / Lorentzian metric | 未纳入本轮 | 没有连续几何、度规恢复或光锥结构 |

边界句：

```text
S3 关闭的是 path witness composition 与最小 no-self-loop 方向性；
它不是完整因果集理论，也不是时空几何恢复。
```

---

## 〇二 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| 组合输入 | `ComposableProcessPaths` | 两段 path witness 共享中间状态 |
| 组合输出 | `composeProcessPaths` | 生成外端点 path witness |
| 有效性 | `composed_path_valid` | 两段有效且中点相合，则组合有效 |
| 可达性 | `composed_path_reachable` | 组合 path witness 推出外端点 `Reachable` |
| 因果读法 | `composed_path_causal_before` | 组合 path witness 可读成外端点 `causalBefore` |
| 局部方向 | `CodeSuccessorStep`、`CodeMonotoneStep` | 一步转移推进有限 code |
| 排除自环 | `code_monotone_step_no_self_loop` | code-monotone step 排除 `step a a` |
| concrete/grid 实例 | `concrete_code_successor_step`、`operatorCellGrid_code_successor_step` | S1 witness 继续承载 S3 约束 |
| pathWeight multiplication | `KernelPath.weight_append`、`path_weight_multiplication_bridge_summary` | 已由 S19 关闭有限 kernel path 的权重乘法 |
| 公开摘要 | `path_causal_bridge_summary` | S3 合取 path composition、local causal constraint 与 S2 bridge facts |

未纳入本轮：

| 轴 | 状态 | 说明 |
|---|---|---|
| reachability 传递闭包全律 | 未纳入本轮 | 本轮只组合显式 witness，不重写 `Reachable` 定义 |
| causalBefore 偏序公理 | 未纳入本轮 | 反身、传递、反对称需下一层结构 |
| 局部有限 causal set | 未纳入本轮 | S28 只关闭 displayed two-step interval candidate；尚未证明任意 causal interval 有有限 cardinality |
| 几何恢复 | 未纳入本轮 | 没有 metric、topology、manifold 或 continuum limit |

本轮闭合范围：**S3 已在 Lean 中关闭 path witness composition 与 code-successor/no-self-loop 局部方向性；S19 已关闭有限 kernel path 的 pathWeight multiplication typed skeleton。完整因果偏序、局部有限 causal set、light cone、Lorentzian geometry、metric recovery 或经验闭合仍未关闭。**

---

## 一 · 为什么这一步足够小

已有 `ProcessPath` 只有三个字段：

```lean
structure ProcessPath (P : FiniteProcess) where
  start : P.State
  stop : P.State
  valid : Prop
```

因此 S3 不强行引入列表路径、路径乘积或完整 transitive closure，而是先定义一个中间状态相合的组合接口：

```lean
structure ComposableProcessPaths (P : FiniteProcess) where
  left : ProcessPath P
  right : ProcessPath P
  middle_eq : left.stop = right.start
  left_valid : left.valid
  right_valid : right.valid
```

这样可以证明最小组合事实：

```text
两段有效 witness
-> 一个组合 witness
-> Reachable outer endpoints
-> causalBefore outer endpoints
```

这正好满足 S3 的最低要求，而不把当前 skeleton 冒充完整路径代数。

---

## 二 · 局部因果约束

为了给 concrete 与 grid witness 增加最小方向性，S3 定义：

```lean
def CodeSuccessorStep (P : FiniteProcess) : Prop :=
  ∀ a b : P.State, P.step a b → P.stateCode b = P.stateCode a + 1

def CodeMonotoneStep (P : FiniteProcess) : Prop :=
  ∀ a b : P.State, P.step a b → P.stateCode a < P.stateCode b
```

因此有：

```text
CodeSuccessorStep -> CodeMonotoneStep -> no one-step self loop
```

concrete witness 的 `prepared -> evolved -> measured` 和 `71232` grid 的 successor index 都满足该约束。

---

## 三 · 下一步

S3 之后，最省力的推进顺序是：

| 阶段 | 目标 | 本文状态 |
|---|---|---|
| S4 | classical Markov 与 quantum amplitude 分层 | 已由《经典Markov与量子振幅分层 · Markov桥S4》关闭候选接口；S3 path composition 本身仍不表达干涉 |
| S5 | 干涉与 Born-rule-shaped candidate | 已由《干涉与测量律候选 · Markov桥S5》关闭候选接口；真实干涉律仍未纳入，Born rule typed-skeleton derivation 已由 S18 承接 |
| S5b | 非零 path-amplitude candidate witness | 已由《非零路径振幅候选 · Markov桥S5b》关闭候选接口；相位律、路径求和与可测相消仍未纳入 |
| S19 | 路径权重乘法候选 | 已由《路径权重乘法候选 · Markov桥S19》关闭 finite kernel path 的 weight append law |
| S6 | 几何与度规候选接口 | 未纳入本轮 |
| S7 | 经验 pending ledger | S5q 已关闭最小 pending observable ledger；数据接口仍未纳入本轮 |

---

## 四 · Validation Command

Lean 验证命令：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityPathCausalBridge
lake build SSBX
```

文档与格式检查：

```bash
git diff --check -- formal/SSBX/Foundation/Modern/QuantumRelativityPathCausalBridge.lean formal/SSBX/Foundation/Modern/QuantumRelativityNonzeroPathAmplitudeBridge.lean formal/SSBX.lean formal/SSBX/notes/unification-stepwise-plan.md formal/SSBX/notes/markov-causal-bridge-verification-plan.md formal/SSBX/notes/markov-causal-bridge-plan.md docs-next/10_formal_形式/modern.md '义理/路径组合与因果约束 · Markov桥S3.md' '义理/Markov因果桥 · 大统一最小验证构造.md' '义理/经典Markov与量子振幅分层 · Markov桥S4.md' '义理/干涉与测量律候选 · Markov桥S5.md' '义理/非零路径振幅候选 · Markov桥S5b.md'
```
