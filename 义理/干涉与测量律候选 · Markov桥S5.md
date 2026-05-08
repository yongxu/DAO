# 干涉与测量律候选 · Markov桥S5

**前置**：[Markov因果桥 · 大统一最小验证构造](Markov因果桥%20·%20大统一最小验证构造.md) · [非零路径振幅候选 · Markov桥S5b](非零路径振幅候选%20·%20Markov桥S5b.md) · [经典Markov与量子振幅分层 · Markov桥S4](经典Markov与量子振幅分层%20·%20Markov桥S4.md) · [路径组合与因果约束 · Markov桥S3](路径组合与因果约束%20·%20Markov桥S3.md) · [有限概率核接口 · Markov桥S2](有限概率核接口%20·%20Markov桥S2.md) · [`unification-stepwise-plan`](../formal/SSBX/notes/unification-stepwise-plan.md) · [`markov-causal-bridge-verification-plan`](../formal/SSBX/notes/markov-causal-bridge-verification-plan.md)

**Lean 锚点**：

| 层 | 文件 | 内容 | 状态 |
|---|---|---|---|
| 路径振幅候选 | `Foundation/Modern/QuantumRelativityInterferenceBridge.lean` | `PathAmplitudeSkeleton`、`HasPathAmplitudeProjection` | `machineChecked` typed skeleton |
| 路径振幅组合 | `Foundation/Modern/QuantumRelativityInterferenceBridge.lean` | `amplitude_path_composition` | `machineChecked` |
| 干涉候选 | `Foundation/Modern/QuantumRelativityInterferenceBridge.lean` | `InterferenceCandidate`、`destructiveInterferenceWitness`、`interference_candidate` | `machineChecked` typed witness |
| Born-shaped boundary | `Foundation/Modern/QuantumRelativityInterferenceBridge.lean` | `BornRuleCandidateBoundary`、`bornRuleCandidate`、`born_rule_candidate_boundary`、`born_rule_candidate_nonnegative` | `machineChecked` |
| concrete/grid 候选 | `Foundation/Modern/QuantumRelativityInterferenceBridge.lean` | `concretePathAmplitudeSkeleton`、`operatorCellGridPathAmplitudeSkeleton` | `machineChecked` |
| S5 公开摘要 | `Foundation/Modern/QuantumRelativityInterferenceBridge.lean` | `interference_bridge_summary` | `machineChecked` |
| S5b 非零 follow-up | `Foundation/Modern/QuantumRelativityNonzeroPathAmplitudeBridge.lean` | `nonzero_path_amplitude_bridge_summary` | `machineChecked` |

---

## 〇 · Claim Block

S5 的主张很窄：

```text
已有 S4 amplitude/channel candidate layer
+ path amplitude skeleton
+ candidate composition equation over explicit path witnesses
+ destructive-interference typed witness
+ Born-rule-shaped boundary weight = ampProb amplitude
= interference / measurement-law candidate interface
```

它不证明真实干涉律，不证明路径积分，不证明 Born rule 从 Markov 桥推出，不证明 unitary evolution，不证明 CPTP quantum channel law，不证明 decoherence 或经验闭合。

公开摘要为：

```lean
theorem interference_bridge_summary :
    HasPathAmplitudeProjection concreteProcess
    ∧ HasPathAmplitudeProjection operatorCellGridProcess
    ∧ HasInterferenceCandidate
    ∧ (∀ {P : FiniteProcess} (A : PathAmplitudeSkeleton P)
        (c : ComposableProcessPaths P),
        A.pathAmplitude (composeProcessPaths c) =
          A.pathAmplitude c.left * A.pathAmplitude c.right)
    ∧ (∀ z : ℂ, (bornRuleCandidate z).candidateWeight = ampProb z)
    ∧ ...
    ∧ WenConstructiveCoverage
```

该 theorem 已通过 `lake build SSBX.Foundation.Modern.QuantumRelativityInterferenceBridge`。

---

## 〇一 · 边界声明

| 说法 | 本文状态 | 精确含义 |
|---|---|---|
| 路径振幅候选已开口 | `machineChecked` typed skeleton | `PathAmplitudeSkeleton` 给每个 `ProcessPath` 一个复数候选值 |
| 路径振幅组合接口 | `machineChecked` | `amplitude_path_composition` 只表达显式 path witness 上的候选等式 |
| 干涉候选存在 | `machineChecked` typed witness | `1 + (-1) = 0` 作为相消形状的 typed witness |
| Born-shaped boundary | `machineChecked` | `bornRuleCandidate z` 只记录 `candidateWeight = ampProb z` |
| concrete/grid path amplitude candidate | `machineChecked` | S5 本文件仍用 zero path-amplitude placeholder |
| 非零候选路径振幅 | S5 未纳入；S5b 已开单独接口 | 见《非零路径振幅候选 · Markov桥S5b》；该接口仍不是物理相位动力学 |
| 非零物理路径振幅 | 未纳入本轮 | 尚无 action、phase evolution、Hamiltonian 或 unitary law |
| 真实干涉律 | 未纳入本轮 | 没有把两条实际路径的振幅相加并预测观测差异 |
| Born rule 推导 | 未纳入本轮 | 只记录形状，不从 Markov 权重或 path amplitude 推出测量概率律 |
| unitary / CPTP / decoherence | 未纳入本轮 | 没有 Hilbert-space evolution law、Kraus map、density matrix 或环境模型 |
| 经验闭合 | 未纳入本轮 | 没有观测量 ledger、数据判准或实验接口 |

边界句：

```text
S5 关闭的是 interference-shaped 和 Born-rule-shaped candidate interface；
它不是物理干涉定律，也不是 Born rule 的推导。
```

---

## 〇二 · 完成度审计

已完成 / 已证 / machineChecked：

| 轴 | Lean 锚点 | 读法 |
|---|---|---|
| 路径振幅骨架 | `PathAmplitudeSkeleton` | 在 S4 channel candidate 上增加 path amplitude 字段 |
| 路径振幅投影 | `HasPathAmplitudeProjection` | 一个有限过程可承载路径振幅候选 |
| 组合等式 | `amplitude_path_composition` | 显式 composable path witness 上可读取组合候选等式 |
| 干涉候选结构 | `InterferenceCandidate` | 两个复振幅相加为零的 typed witness 形状 |
| 相消 witness | `destructiveInterferenceWitness`、`interference_candidate` | `1` 与 `-1` 给出最小相消候选 |
| Born-shaped boundary | `BornRuleCandidateBoundary`、`born_rule_candidate_boundary` | 单一复幅的候选权重等于 `ampProb` |
| 非负性 | `born_rule_candidate_nonnegative` | `ampProb` 是 norm square，候选权重非负 |
| concrete/grid 候选 | `concretePathAmplitudeSkeleton`、`operatorCellGridPathAmplitudeSkeleton` | S1-S4 witness 可继续承载 S5 candidate |
| 公开摘要 | `interference_bridge_summary` | 合取 path amplitude、interference candidate、Born-shaped boundary 与 Wen coverage |

未纳入本轮：

| 轴 | 状态 | 说明 |
|---|---|---|
| 非零候选 witness | S5 未纳入；S5b 已开单独接口 | `nonzero_path_amplitude_bridge_summary` 关闭非零候选振幅到 valid/reachable/causalBefore 的边界 |
| 非零路径动力学 | 未纳入本轮 | S5b 的 indicator witness 不是 action / phase / unitary dynamics |
| 路径振幅求和律 | 未纳入本轮 | 没有 over-paths sum、phase law 或 cancellation theorem |
| Born rule 从桥推导 | 未纳入本轮 | `ampProb` boundary 不是 Markov-to-Born theorem |
| 真实量子通道律 | 未纳入本轮 | S5 仍不证明 unitary/CPTP/Kraus/density law |
| 经验预测 | 未纳入本轮 | 没有数据接口或实验判准 |

本轮闭合范围：**S5 已在 Lean 中关闭 path-amplitude candidate、candidate composition equation、destructive-interference typed witness 与 Born-rule-shaped boundary；S5b 后续关闭非零 path-amplitude candidate witness 与 valid/reachable/causalBefore 边界；它们仍不关闭真实干涉、Born rule 推导、物理相位动力学、unitary/CPTP channel law、decoherence 或经验闭合。**

---

## 一 · 路径振幅候选

S3 已有 `ComposableProcessPaths` 与 `composeProcessPaths`，S4 已有 amplitude/channel candidate。S5 把两者接起来：

```lean
structure PathAmplitudeSkeleton (P : FiniteProcess) where
  channel : QuantumChannelSkeleton P
  pathAmplitude : ProcessPath P → ℂ
  path_support_implies_valid :
    ∀ p : ProcessPath P, pathAmplitude p ≠ 0 → p.valid
  composed_amplitude :
    ∀ c : ComposableProcessPaths P,
      pathAmplitude (composeProcessPaths c) =
        pathAmplitude c.left * pathAmplitude c.right
```

这只说明“候选振幅不能跑出 path witness 边界”。它还不是路径积分，也不是真实量子动力学。

---

## 二 · 干涉候选

S5 的干涉只做到最小 typed witness：

```text
1 + (-1) = 0
```

这表明形式语言已经能承载“相消形状”。它尚未连接到两条实际物理路径、相位演化、观测概率或实验差异。

---

## 三 · Born-shaped boundary

S5 记录：

```text
candidateWeight = ampProb amplitude
```

这与 `Quantum.lean` 中 `ampProb` 的局部定义对齐。它不是从 Markov 权重推出 Born rule，也不是测量公设的证明。

---

## 四 · Validation Command

Lean 验证命令：

```bash
lake build SSBX.Foundation.Modern.QuantumRelativityInterferenceBridge
lake build SSBX.Foundation.Modern.QuantumRelativityNonzeroPathAmplitudeBridge
lake build SSBX
```

文档与格式检查：

```bash
git diff --check -- formal/SSBX/Foundation/Modern/QuantumRelativityInterferenceBridge.lean formal/SSBX/Foundation/Modern/QuantumRelativityNonzeroPathAmplitudeBridge.lean formal/SSBX.lean formal/SSBX/notes/unification-stepwise-plan.md formal/SSBX/notes/markov-causal-bridge-verification-plan.md formal/SSBX/notes/markov-causal-bridge-plan.md docs-next/10_formal_形式/modern.md '义理/干涉与测量律候选 · Markov桥S5.md' '义理/非零路径振幅候选 · Markov桥S5b.md' '义理/Markov因果桥 · 大统一最小验证构造.md' '义理/经典Markov与量子振幅分层 · Markov桥S4.md'
```
