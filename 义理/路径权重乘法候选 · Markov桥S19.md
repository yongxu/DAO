# 路径权重乘法候选 · Markov桥S19

**前置**：[路径组合与因果约束 · Markov桥S3](路径组合与因果约束%20·%20Markov桥S3.md) · [Born rule推导候选 · Markov桥S18](Born%20rule推导候选%20·%20Markov桥S18.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| current placeholder law | `Foundation/Modern/QuantumRelativityPathWeightMultiplicationBridge.lean` | `current_pathWeight_compose_multiplicative` | `machineChecked` |
| weighted edge | `Foundation/Modern/QuantumRelativityPathWeightMultiplicationBridge.lean` | `KernelEdge`、`KernelEdge.weight`、`KernelEdge.step` | `machineChecked` |
| finite kernel path | `Foundation/Modern/QuantumRelativityPathWeightMultiplicationBridge.lean` | `KernelPath`、`KernelPath.weight`、`KernelPath.append` | `machineChecked` |
| multiplication law | `Foundation/Modern/QuantumRelativityPathWeightMultiplicationBridge.lean` | `KernelPath.weight_append` | `machineChecked` |
| concrete witness | `Foundation/Modern/QuantumRelativityPathWeightMultiplicationBridge.lean` | `concrete_two_step_path_weight_multiplicative` | `machineChecked` |
| S19 summary | `Foundation/Modern/QuantumRelativityPathWeightMultiplicationBridge.lean` | `path_weight_multiplication_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S19 的主张：

```text
positive Markov edge weights
+ endpoint-indexed finite kernel path
+ append composition of matching endpoints
= path weight of append = product of path weights
```

公开摘要为：

```lean
theorem path_weight_multiplication_bridge_summary :
    PathWeightMultiplicationBoundaryClosed
    ∧ KernelPath.weight concretePreparedMeasuredKernelPath = 1
    ∧ Reachable concreteProcess ConcreteState.prepared ConcreteState.measured
    ∧ causalBefore (P := concreteProcess)
        ⟨ConcreteState.prepared⟩ ⟨ConcreteState.measured⟩
    ∧ (∀ b : PendingBeyondS19, ClosedByStepwiseS19 b = false)
    ∧ WenConstructiveCoverage
```

---

## 〇一 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| 旧占位接口乘法 | `current_pathWeight_compose_multiplicative` | 旧 `pathWeight = 1` 在 S3 composition 下乘法闭合，但只是 placeholder law |
| 正权重边 | `KernelEdge`、`KernelEdge.step` | 正 Markov 权重推出 process step |
| 有限 kernel path | `KernelPath` | endpoint matching 写进 type，append 只能连接同中点路径 |
| 路径权重 | `KernelPath.weight` | 路径权重是有限 edge weight product |
| 乘法定律 | `KernelPath.weight_append` | append 后的 path weight 等于左右 path weight 的乘积 |
| concrete two-step witness | `concrete_two_step_path_weight_multiplicative` | `prepared -> evolved -> measured` 的二步权重乘法闭合 |
| 公开摘要 | `path_weight_multiplication_bridge_summary` | 合取 S19 law、concrete reachability / causalBefore、pending ledger 与 Wen coverage |

未纳入本轮：

| 轴 | 状态 | 说明 |
|---|---|---|
| stochastic independence semantics | required but not closed | S19 只证明有限乘积代数，不解释概率独立性 |
| general all-path enumeration | required but not closed | 不枚举任意端点之间全部路径 |
| path integral | required but not closed | 不做无限路径族、measure 或连续极限 |
| amplitude dynamics / measurement semantics | required but not closed | 不证明振幅动力学、测量公设或 decoherence |
| physical channel law / empirical closure | required but not closed | 不证明 unitary/CPTP、metric recovery 或数据闭合 |

本轮闭合范围：**有限 Markov kernel path 的 path-weight multiplication typed skeleton**。

---

## 一 · 为什么不直接改旧 pathWeight

旧 `ProcessPath` 只有起点、终点和 `valid : Prop`：

```lean
structure ProcessPath (P : FiniteProcess) where
  start : P.State
  stop : P.State
  valid : Prop
```

它没有边列表，因此无法从旧结构内部计算真实乘积。S19 保留旧 `pathWeight` 的 placeholder law，同时新增 `KernelEdge` / `KernelPath` 精化层：每条边携带正 Markov 权重，路径权重定义为这些边权重的有限乘积。

---

## 二 · Lean 证明入口

核心 theorem：

```lean
theorem KernelPath.weight_append
    (p : KernelPath K a b) (q : KernelPath K b c) :
    KernelPath.weight (KernelPath.append p q)
      = KernelPath.weight p * KernelPath.weight q
```

证明只对右路径做归纳；`refl` 分支是乘以 `1`，`snoc` 分支用 `Nat.mul_assoc` 关闭。这是纯有限乘积代数，不假设概率归一化。

---

## 三 · Validation Command

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityPathWeightMultiplicationBridge
```
