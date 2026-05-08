# 有限概率核接口 · Markov桥S2

**前置**：[Markov因果桥 · 大统一最小验证构造](Markov因果桥%20·%20大统一最小验证构造.md) · [路径组合与因果约束 · Markov桥S3](路径组合与因果约束%20·%20Markov桥S3.md) · [经典Markov与量子振幅分层 · Markov桥S4](经典Markov与量子振幅分层%20·%20Markov桥S4.md) · [干涉与测量律候选 · Markov桥S5](干涉与测量律候选%20·%20Markov桥S5.md) · [非零路径振幅候选 · Markov桥S5b](非零路径振幅候选%20·%20Markov桥S5b.md) · [文构造完备与直相加边界](文构造完备与直相加边界.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| 有限概率核接口 | `Foundation/Modern/QuantumRelativityFiniteProbabilityBridge.lean` | `FiniteProbabilityKernelSkeleton` 在 Markov skeleton 上增加有限行分母 | `machineChecked` |
| 概率投影存在性 | `Foundation/Modern/QuantumRelativityFiniteProbabilityBridge.lean` | `HasFiniteProbabilityProjection` | `machineChecked` |
| 行可规格化 | `Foundation/Modern/QuantumRelativityFiniteProbabilityBridge.lean` | `RowNormalizable` 与 `nonterminal_row_normalizable` | `machineChecked` |
| 有限质量候选 | `Foundation/Modern/QuantumRelativityFiniteProbabilityBridge.lean` | `finiteMassCandidate`、`finiteMassCandidate_denominator_positive_if_not_terminal` | `machineChecked` |
| concrete 实例 | `Foundation/Modern/QuantumRelativityFiniteProbabilityBridge.lean` | `concreteFiniteProbabilityKernel`、`concrete_prepared_row_normalizable`、`concrete_evolved_row_normalizable` | `machineChecked` |
| `71232` grid 实例 | `Foundation/Modern/QuantumRelativityFiniteProbabilityBridge.lean` | `operatorCellGridFiniteProbabilityKernel`、`operatorCellGrid_nonterminal_row_normalizable` | `machineChecked` |
| S2 公开摘要 | `Foundation/Modern/QuantumRelativityFiniteProbabilityBridge.lean` | `finite_probability_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S2 的主张很窄：

```text
已有 Markov / 因果桥
+ finite row denominator
+ non-terminal row denominator is nonzero
+ each weight is bounded by its row denominator
+ terminal rows may stop
= finite probability-kernel interface
```

这一步只把 `Nat` 权重升级成可读作有限质量候选的接口。它没有证明行权重求和等于分母，没有证明实数概率测度，没有证明 Born rule，也没有在 S2 内引入 quantum amplitude/channel、干涉、度规恢复或经验闭合。

公开摘要为：

```lean
theorem finite_probability_bridge_summary :
    HasFiniteProbabilityProjection concreteProcess
    ∧ HasFiniteProbabilityProjection operatorCellGridProcess
    ∧ ...
    ∧ allOperatorIds.length = 371
    ∧ Cell192.all.length = 192
    ∧ allOperatorCells.length = 71232
    ∧ WenConstructiveCoverage
```

该 theorem 已通过 `lake build SSBX.Foundation.Modern.QuantumRelativityFiniteProbabilityBridge`。

---

## 〇一 · 边界声明

| 说法 | 本文状态 | 精确含义 |
|---|---|---|
| concrete bridge 有有限概率核接口 | `machineChecked` | `prepared` 与 `evolved` 行分母为 `1`，终端 `measured` 行可停止 |
| `71232` grid bridge 有有限概率核接口 | `machineChecked` | 非终端 successor 行分母为 `1`，末端行可停止 |
| 非终端行可规格化 | `machineChecked` | `RowNormalizable` 只表示行分母非零 |
| 权重受分母约束 | `machineChecked` | 每个 `weight a b ≤ rowTotal a` |
| 有限质量候选 | `machineChecked` typed skeleton | `numerator / denominator` 作为候选接口 |
| sum-one 概率律 | S9/S10/S11 已后续关闭有限条件版本 | 本文件 S2 只证明分母接口；`finite_probability_normalization_bridge_summary` 已证明 concrete/grid 非终端行归一，`normalized_mass_bridge_summary` 已证明逐项 normalized mass 求和为 `1`，`born_weight_normalization_bridge_summary` 已证明 normalized amplitude support 条件下的 candidateWeight law |
| Born rule | 未纳入本轮 | 尚未从振幅范数推出测量概率 |
| quantum amplitude / channel candidate | S2 未纳入；S4 已开单独接口 | 见《经典Markov与量子振幅分层 · Markov桥S4》；S2 finite mass 不等于振幅或 Born 概率 |
| 真实 quantum channel law | 未纳入本轮 | 尚未证明 unitarity、CPTP、Kraus 或 density-matrix law |
| 干涉、度规、经验闭合 | 未纳入本轮 | S3/S4/S5/S5b 已分别处理路径、候选分层、干涉/Born-shaped candidate 与非零 witness；真实干涉律、几何和经验闭合仍需后续层 |

边界句：

```text
S2 关闭的是 finite denominator interface；
它让 Markov 权重可以进入有限质量候选读法，
但还不是物理概率律或量子测量律。
```

---

## 〇二 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| 接口层 | `FiniteProbabilityKernelSkeleton` | 在 Markov kernel skeleton 上加 `rowTotal`、非终端非零条件与权重上界 |
| 投影存在 | `HasFiniteProbabilityProjection` | 一个有限过程拥有这样的 kernel 即有 S2 投影 |
| 行条件 | `RowNormalizable`、`nonterminal_row_normalizable` | 非终端行有非零分母 |
| 质量候选 | `FiniteMassCandidate`、`finiteMassCandidate_denominator_positive_if_not_terminal` | `weight / rowTotal` 的候选分母可检查 |
| concrete 实例 | `concreteFiniteProbabilityKernel` | 三状态实例接入 S2 |
| grid 实例 | `operatorCellGridFiniteProbabilityKernel` | `371 × 192 = 71232` grid 接入 S2 |
| 公开摘要 | `finite_probability_bridge_summary` | concrete、grid、`192 × 371` 覆盖同时保留 |

未纳入本轮：

| 轴 | 状态 | 说明 |
|---|---|---|
| 权重行求和 | 未纳入本轮 | 没有证明 `sum weights = rowTotal` |
| 实数概率空间 | 未纳入本轮 | 没有把候选分数提升为 measure-theoretic probability |
| Born rule | 未纳入本轮 | S2 没有 amplitude；S4/S5 另开候选层与 Born-shaped boundary，但不提供 Born rule 推导 |
| 路径组合 | S2 未纳入；S3 已开单独接口 | 见《路径组合与因果约束 · Markov桥S3》；`pathWeight` 乘法仍未纳入 |
| 经验接口 | 未纳入本轮 | 没有 observation ledger 和数据判准 |

本轮闭合范围：**S2 已在 Lean 中关闭 finite probability-kernel denominator interface；它保守地证明非终端行分母非零和权重上界。S9 已后续关闭 concrete/grid 的 finite row sum-one normalization boundary，S10 已把逐项 normalized mass 求和证明为 `1`，S11 已在 normalized amplitude support 条件下关闭 candidateWeight 非负与 sum-one；Born rule、quantum amplitude/channel law、干涉、几何恢复或经验闭合仍不由 S2 推出。S4/S5/S5b 后续只把 amplitude/channel、path amplitude、Born-shaped boundary 与非零 path witness 作为独立候选层接上，不把 S2 finite mass 解释成 Born 概率。**

---

## 一 · 为什么这一步足够小

上一轮已有：

```text
FiniteProcess
+ MarkovKernelSkeleton
+ concrete bridge
+ 71232 operator-cell grid bridge
```

但 `MarkovKernelSkeleton.weight : State -> State -> Nat` 只说明离散权重，不说明它可以进入概率候选。S2 的最省力补强是增加一行分母：

```lean
structure FiniteProbabilityKernelSkeleton (P : FiniteProcess)
    extends MarkovKernelSkeleton P where
  rowTotal : P.State → Nat
  rowTotal_positive_if_not_terminal :
    ∀ a : P.State, ¬ P.terminal a → rowTotal a ≠ 0
  weight_le_rowTotal :
    ∀ a b : P.State, weight a b ≤ rowTotal a
```

这使每个非终端权重都能读成：

```text
finite mass candidate = numerator / denominator
```

其中 numerator 是一步权重，denominator 是该行分母。终端行允许停止，避免为了形式归一化而偷偷加入一个吸收物理转移。

---

## 二 · concrete 与 grid 的读法

三状态 concrete bridge：

| 状态 | rowTotal | 读法 |
|---|---:|---|
| `prepared` | `1` | 唯一步走向 `evolved` |
| `evolved` | `1` | 唯一步走向 `measured` |
| `measured` | `0` | 终端行停止 |

`71232` operator-cell grid bridge：

| 行 | rowTotal | 读法 |
|---|---:|---|
| 非末端 cell | `1` | successor 权重为 `1` |
| 末端 cell | `0` | terminal row 停止 |

这两个实例都不是随机物理模型。它们只证明 S1 的有限 bridge witness 可以继续承载 S2 的有限分母接口。

---

## 三 · 下一步

S2 之后，最省力的推进顺序是：

| 阶段 | 目标 | 本文状态 |
|---|---|---|
| S3 | 路径组合与局部因果约束 | 已由《路径组合与因果约束 · Markov桥S3》关闭最小接口 |
| S4 | classical Markov 与 quantum amplitude 分层 | 已由《经典Markov与量子振幅分层 · Markov桥S4》关闭候选接口；真实 channel law 仍未纳入 |
| S5 | 干涉与 Born-rule-shaped candidate | 已由《干涉与测量律候选 · Markov桥S5》关闭候选接口；真实干涉律与 Born rule 推导仍未纳入 |
| S5b | 非零 path-amplitude candidate witness | 已由《非零路径振幅候选 · Markov桥S5b》关闭候选接口；相位律、路径求和与可测相消仍未纳入 |
| S6 | 几何与度规候选接口 | 未纳入本轮 |
| S7 | 经验 pending ledger | S5q 已关闭最小 pending observable ledger；数据接口仍未纳入本轮 |

---

## 四 · Validation Command

Lean 验证命令：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityFiniteProbabilityBridge
lake build SSBX
```

文档与格式检查：

```bash
git diff --check -- formal/SSBX/Foundation/Modern/QuantumRelativityFiniteProbabilityBridge.lean formal/SSBX/Foundation/Modern/QuantumRelativityNonzeroPathAmplitudeBridge.lean formal/SSBX.lean formal/SSBX/notes/unification-stepwise-plan.md formal/SSBX/notes/markov-causal-bridge-verification-plan.md formal/SSBX/notes/markov-causal-bridge-plan.md docs-next/10_formal_形式/modern.md '义理/有限概率核接口 · Markov桥S2.md' '义理/Markov因果桥 · 大统一最小验证构造.md' '义理/经典Markov与量子振幅分层 · Markov桥S4.md' '义理/干涉与测量律候选 · Markov桥S5.md' '义理/非零路径振幅候选 · Markov桥S5b.md'
```
