# 非零路径振幅候选 · Markov桥S5b

**前置**：[Markov因果桥 · 大统一最小验证构造](Markov因果桥%20·%20大统一最小验证构造.md) · [干涉与测量律候选 · Markov桥S5](干涉与测量律候选%20·%20Markov桥S5.md) · [经典Markov与量子振幅分层 · Markov桥S4](经典Markov与量子振幅分层%20·%20Markov桥S4.md) · [路径组合与因果约束 · Markov桥S3](路径组合与因果约束%20·%20Markov桥S3.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| 非零振幅边界 | `Foundation/Modern/QuantumRelativityNonzeroPathAmplitudeBridge.lean` | `nonzero_path_amplitude_implies_valid` | `machineChecked` |
| 可达投影 | `Foundation/Modern/QuantumRelativityNonzeroPathAmplitudeBridge.lean` | `nonzero_path_amplitude_implies_reachable` | `machineChecked` |
| 因果投影 | `Foundation/Modern/QuantumRelativityNonzeroPathAmplitudeBridge.lean` | `nonzero_path_amplitude_implies_causal_before` | `machineChecked` |
| 非零候选骨架 | `Foundation/Modern/QuantumRelativityNonzeroPathAmplitudeBridge.lean` | `validPathIndicatorPathAmplitudeSkeleton`、`valid_path_indicator_nonzero` | `machineChecked` typed skeleton |
| concrete 非零 witness | `Foundation/Modern/QuantumRelativityNonzeroPathAmplitudeBridge.lean` | `concretePreparedMeasuredPath`、`concrete_prepared_measured_path_nonzero_amplitude` | `machineChecked` |
| S5b 公开摘要 | `Foundation/Modern/QuantumRelativityNonzeroPathAmplitudeBridge.lean` | `nonzero_path_amplitude_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S5b 的主张很窄：

```text
已有 S5 path amplitude skeleton
+ 非零 path amplitude 支持条件
+ valid path witness
+ Reachable / causalBefore projection
+ concrete prepared -> measured 非零候选 witness
= nonzero path-amplitude candidate boundary
```

它不证明真实相位动力学，不证明路径积分，不证明真实干涉律，不证明 Born rule 从 Markov 桥推出，不证明 unitary/CPTP channel law，不证明 decoherence 或经验闭合。

公开摘要为：

```lean
theorem nonzero_path_amplitude_bridge_summary :
    (∀ {P : FiniteProcess} (A : PathAmplitudeSkeleton P)
        (p : ProcessPath P),
        A.pathAmplitude p ≠ 0 -> p.valid)
    ∧ (∀ {P : FiniteProcess} (A : PathAmplitudeSkeleton P)
        (p : ProcessPath P),
        A.pathAmplitude p ≠ 0 -> Reachable P p.start p.stop)
    ∧ ...
    ∧ concreteNonzeroPathAmplitudeSkeleton.pathAmplitude
        concretePreparedMeasuredPath ≠ 0
    ∧ WenConstructiveCoverage
```

该 theorem 已通过 `lake build SSBX.Foundation.Modern.QuantumRelativityNonzeroPathAmplitudeBridge`。

---

## 〇一 · 边界声明

| 说法 | 本文状态 | 精确含义 |
|---|---|---|
| 非零 path amplitude 不跑出 path 边界 | `machineChecked` | `pathAmplitude p ≠ 0 -> p.valid` |
| 非零 path amplitude 给出可达 | `machineChecked` | 复用 S3/S0 的 `path_implies_reachable` |
| 非零 path amplitude 给出因果读法 | `machineChecked` | 可读成 `causalBefore` |
| concrete 非零候选 witness | `machineChecked` | `prepared -> evolved -> measured` 的 composed path 在 indicator skeleton 下振幅为 `1` |
| valid-path indicator | `machineChecked` typed skeleton | 有效 path 给 `1`，无效 path 给 `0` |
| 真实相位动力学 | 未纳入本轮 | 没有 action、phase evolution、Hamiltonian 或 unitary law |
| 真实干涉律 | 未纳入本轮 | 没有两条实际路径的振幅求和和可测相消 theorem |
| Born rule 推导 | 未纳入本轮 | 仍只保留 `ampProb` 形状，不从 Markov 权重推出测量概率律 |
| 真实 quantum channel law | 未纳入本轮 | 没有 CPTP、Kraus、density matrix 或 trace preservation |
| 经验闭合 | 未纳入本轮 | 没有观测量 ledger、数据判准或实验接口 |

边界句：

```text
S5b 关闭的是非零 path-amplitude candidate witness 与 path/causal boundary；
它不是物理相位动力学，也不是真实干涉定律。
```

---

## 〇二 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| 非零到有效路径 | `nonzero_path_amplitude_implies_valid` | S5 的 support condition 可复用为边界 theorem |
| 非零到可达 | `nonzero_path_amplitude_implies_reachable` | 非零候选振幅先给 path validity，再给 endpoint reachability |
| 非零到因果 before | `nonzero_path_amplitude_implies_causal_before` | 非零候选振幅可以投影成 causal reading |
| indicator skeleton | `validPathIndicatorPathAmplitudeSkeleton` | 用最小方式摆脱 zero placeholder，不加入物理相位律 |
| concrete 非零路径 | `concretePreparedMeasuredPath` | `prepared -> evolved -> measured` composed path |
| concrete 非零振幅 | `concrete_prepared_measured_path_nonzero_amplitude` | concrete path amplitude candidate 不再全为零 |
| concrete 可达 / 因果 | `concrete_nonzero_path_amplitude_reachable`、`concrete_nonzero_path_amplitude_causal_before` | 非零 witness 可接回 S3 path/causal boundary |
| 公开摘要 | `nonzero_path_amplitude_bridge_summary` | 合取非零边界、concrete witness、S5 interference candidate 与 Wen coverage |

未纳入本轮：

| 轴 | 状态 | 说明 |
|---|---|---|
| 相位演化 | 未纳入本轮 | indicator amplitude 只有 `0/1`，没有 phase |
| 路径求和 | 未纳入本轮 | 没有 over-paths sum 或 path integral |
| 真实干涉律 | 未纳入本轮 | 没有实际替代路径之间的相消定理 |
| Born rule 从桥推导 | 未纳入本轮 | `ampProb` boundary 仍不是 derivation |
| 经验预测 | 未纳入本轮 | 没有 observation ledger |

本轮闭合范围：**S5b 已在 Lean 中关闭“非零 path amplitude -> valid path -> Reachable / causalBefore”的候选边界，并给 concrete bridge 一个非零 path-amplitude witness；它不关闭相位动力学、路径求和、真实干涉律、Born rule 推导、unitary/CPTP channel law、decoherence 或经验闭合。**

---

## 一 · 为什么这一步是最省力推进

S5 已经有 `PathAmplitudeSkeleton`，但 concrete/grid 使用 zero placeholder。若直接谈真实干涉，会缺两个必要环节：

```text
非零 path amplitude
-> 有效 path witness
-> 可达 / 因果读法
```

S5b 先关闭这个最小环节。它不引入 Hilbert 空间动力学，也不引入路径积分，只证明非零候选振幅不会脱离当前有限过程边界。

---

## 二 · indicator skeleton 的读法

`validPathIndicatorPathAmplitudeSkeleton` 的定义很朴素：

```text
valid path -> amplitude 1
invalid path -> amplitude 0
```

这不是物理模型。它只是说明当前形式语言可以承载一个非零 path amplitude witness，并且该 witness 自动投回 path/causal boundary。

---

## 三 · 下一步

S5b 之后，真实干涉还至少需要三件事：

| 缺口 | 最小后续形式 |
|---|---|
| 相位 | 给 path amplitude 加 phase/action law |
| 路径求和 | 定义同端点路径族与有限求和 |
| 可测相消 | 把求和后的振幅接到 Born-shaped boundary 或 observation ledger |

这三件事未关闭前，不能写“真实干涉律已证”。

---

## 四 · Validation Command

Lean 验证命令：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityNonzeroPathAmplitudeBridge
lake build SSBX
```

文档与格式检查：

```bash
git diff --check -- formal/SSBX/Foundation/Modern/QuantumRelativityNonzeroPathAmplitudeBridge.lean formal/SSBX.lean formal/SSBX/notes/unification-stepwise-plan.md formal/SSBX/notes/markov-causal-bridge-verification-plan.md formal/SSBX/notes/markov-causal-bridge-plan.md docs-next/10_formal_形式/modern.md '义理/非零路径振幅候选 · Markov桥S5b.md' '义理/干涉与测量律候选 · Markov桥S5.md' '义理/Markov因果桥 · 大统一最小验证构造.md'
```
