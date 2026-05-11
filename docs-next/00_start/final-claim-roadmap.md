# 最终 Claim Roadmap — scale-free 边界生成理论

> 状态：roadmap v0.1 (2026-05-11)
> 角色：本文区分“最终可争取之 claim”与“当前已经可 claim”。它不是新定本，不覆盖 [`final-theory.md`](final-theory.md)；它给后续证明、文档、Lean skeleton 的目标顺序。
> 形式锚：[`yi-RO-hierarchy.md`](../10_formal_形式/yi-RO-hierarchy.md) · [`r8-root-language-tree.md`](../10_formal_形式/r8-root-language-tree.md) · [`quantum-roadmap.md`](../10_formal_形式/quantum-roadmap.md) · [`roadmap-self-similarity-v1.md`](roadmap-self-similarity-v1.md) · [`文-R8投影规约.md`](../../义理/文-R8投影规约.md)

---

## 0 · 为什么写这份 roadmap

当前 v3 已经把 R₀..R₈ strict-uniform、Cell256、V₄ Shi、Cayley 元-算子融合、平方塔和文-R8投影规约分别立住。下一步需要避免两个相反错误：

| 错误 | 后果 |
|---|---|
| 过弱 | 把理论误读成只是一张 256 格静态表 |
| 过强 | 把尚未证明的物理统一、完整自然语言语义或所有真理判定提前宣布完成 |

本文给出两个层次：

1. **最终 claim**：我们认为最终可以做到、值得朝此证明。
2. **当前 claim**：基于现有 Lean / 文档，现在已经可以 defend。

---

## 1 · 最终 Claim

最终目标表述：

> **生生不息是一套 scale-free 的边界生成理论。它以 R₈ = (Z/2)⁸ 为最小语言表达闭合核，以自相似升维生成任意尺度的可描述结构；道、理、法、证据、善、量、测、数学对象、物理模型与程序语义都可作为边界角色进入同一表达-投影-审计框架。对任一可描述 claim，系统不必给出简单 yes/no，而应给出其 truth status：已证、已反、可判、独立、经验待定、投影有损、或边界外。**

这句话的关键词不是“R₈ 装下全部”，而是：

```text
R₈ 最小核
+ 自相似 scale-free extension
+ 文 / Lisp / Program 组合语法
+ 投影与损失账本
+ truth-status 审计
```

### 1.1 最终 claim 的强含义

| 方面 | 最终要证明的内容 |
|---|---|
| 语言 | 任意有限表达可经文法规约进入某个 typed semantic layer，并有 R₈ 可见投影 |
| 规则 | `quote / apply / compose / if / equal / lookup / recurse / project` 等通用语法原语可由 R₈ 原子编码、组合、执行 |
| 自相似 | R₈ 不是终点；R₈ 作为 alphabet 生成 List / Tree / Program / Stream / Measure / Hilbert 等更高尺度 |
| 道 | 道不是单个经验对象，而是 origin / no-op / identity / anchor / 归位条件在各尺度的对应角色 |
| 理 | 理是可推导规则结构；理性是把理施用于现象，并接受证据与投影审计 |
| 法 | 法是可复用、可执行、可约束的规则接口，不只是规范文本 |
| 证据 | 证据是经测量 / 记录 / 校准 / 推断接口落下的可审计投影 |
| 善 | 善不是任意偏好，而是能在多尺度边界中维持生成、互通、可归位的结构条件 |
| 科学 | 数学、量化、概率、连续测度、量子态空间、物理模型都作为 carrier / enrichment 进入同一边界生成语法 |
| 真 | 真不是单一标签；真值以 truth status 与 proof / evidence / model / boundary ledger 形式呈现 |

### 1.2 最终 claim 不能偷换成什么

| 不应声称 | 正确边界 |
|---|---|
| R₈ 单格能装下所有函数 | 所有函数需 Program / Table / List R₈ 表示；R₈ 是 alphabet 与最小语义核 |
| 已完成物理大统一 | 最终目标可包含物理统一接口；当前只有有限 bridge 与 typed skeleton |
| 已完整映射自然语言 | 当前只有 catalogue / WenSurface / R8 projection 接口；完整语义仍需解释器 |
| 系统内部判定所有真理 | 系统应给 truth status；不可判、经验待定、边界外也是合法结果 |
| 自指带来全能 | 系统能处理自指；完备性来自边界分层与可审计投影，不来自吞下自身 |

---

## 2 · 当前 Claim

当前已经可以 defend 的版本：

> **当前项目已经形式化了一套 R₀..R₈ strict-uniform 的最小代数核：R₈ = Cell256 = (Z/2)⁸，道 = origin = identity = no-op，R₈ 元与 R₈ XOR 自作用经 Cayley 双射融合。平方塔证明 R₈ 可读为 R₄ × R₄；文-R8投影规约证明：给定解释器后，任意句子都有 R₈ 可见投影、投影损失账本与归道检测接口。371 个文言算子 catalogue 与 256 个 R₈ cells 形成 94976 行覆盖网格，但该网格目前是覆盖与保守 machine denotation，不等于完整自然语言语义。**

### 2.1 当前已完成

| 层 | 当前状态 | 锚 |
|---|---|---|
| R₀..R₈ strict uniform | 已落地 | `RHierarchy.lean`, `LiftProject.lean` |
| R₈ Cell256 | 已落地 | `R8.lean`, `R8Stratify.lean` |
| 道五重身份 | 已落地于 R₈ | `R8.origin`, `way_at_origin`, `way_noop_operator` |
| Cayley 元-算子融合 | 已落地 | `R8.cayley`, `R8.cayley_inj`, `epsAtOrigin_cayley` |
| R₈ = R₄ × R₄ | 已落地 | `SelfSimilarity.r8_eq_r4_squared` |
| R₈ ≃ V₄⁴ | 已落地 | `V4Tensor.iso` |
| 文言算子 catalogue | 已覆盖 | `allOperatorIds.length = 371`, `allOperatorIds.Nodup` |
| operator-cell grid | 已覆盖 | `allOperatorCells.length = 94976` |
| 文-R8投影规约 | 已有 typed skeleton | `R8ProjectionCalculus.lean` |
| 量子接口 | 有 roadmap 与有限 bridge | `QuantumR8Bridge.lean`, `quantum-roadmap.md` |
| Markov / Born / action bridge | 有 stepwise typed skeleton | `QuantumRelativity*.lean` S-series |

### 2.2 当前可说的“完备”

当前可说：

```text
R₈ 对自身 XOR self-action 完备。
R₀..R₈ 对 strict binary algebraic closure 完备。
文-R8投影规约对“给定解释器后的可见投影 / 损失账本 / 归道检测”完备。
```

当前不可说：

```text
完整自然语言语义已完成。
完整物理大统一已完成。
所有数学真理可内部判定。
所有函数 R₈ → R₈ 都是 R₈ 的一个元素。
```

正确表述：

```text
所有函数 R₈ → R₈ 可由 R₈ 生成的表 / 程序 / Lisp-Wen 语法表示；
但函数空间不等于单个 R₈ carrier。
```

---

## 3 · 从当前到最终还缺什么

### 3.1 文法与解释器

| 缺口 | 目标 |
|---|---|
| 真实 parser | `Sentence.source → WenSurface AST / WenNormalForm` |
| 具体解释器 | `WenNormalForm → R8Semantics` 的可执行实例 |
| 例句 corpus | “道总归道”“真可假假可真”“分而可合”等固定测试 |
| 371 接入 | `OperatorId × R8 → R8Semantics` 的分层映射 |

当前进展：

| 项 | 状态 |
|---|---|
| root-rule program kernel | done: [`RootRuleKernel.lean`](../../formal/SSBX/Foundation/Wen/RootRuleKernel.lean) |
| checked example corpus | done: [`RootRuleExamples.lean`](../../formal/SSBX/Foundation/Wen/RootRuleExamples.lean) |
| demo interpreter | done as skeleton: [`RootRuleDemoInterpreter.lean`](../../formal/SSBX/Foundation/Wen/RootRuleDemoInterpreter.lean) |
| full parser / full semantics | pending |

### 3.2 通用程序规则

| 原语 | 目标 |
|---|---|
| `quote` | 程序作为数据 |
| `apply` | 元 / 算子施用 |
| `compose` | 路径与算子列组合 |
| `if` | 谓词分支 |
| `equal` | cell / syntax equality |
| `lookup` | 环境 / 表 / 史带取值 |
| `recurse` | fuel / partial eval / fixed point |
| `project` | 高维结构到 R₈ 可见投影 |

这些原语应作为 Wen/Lisp kernel 的最小通用组合层，而不是 371 catalogue 的任意罗列。

### 3.3 高维与连续层

| 层 | 目标 |
|---|---|
| List / Tree R₈ | 表、语法树、有限程序 |
| Stream / L∞ | 无界自相似展开 |
| Probability kernel | 概率转移与有限归一化 |
| Measure / interval | 连续量化与测度接口 |
| Hilbert / Qubit | 量子态空间、unitary、measurement |
| Physical model | 经验标定、预测、实验闭合 |

### 3.4 Truth-status ledger

最终系统不应把所有 claim 压成 true/false，而应给：

| 状态 | 含义 |
|---|---|
| `machineChecked` | 当前 Lean theorem 已证 |
| `modelComputed` | 模型计算得出 |
| `ledgerDependent` | 依赖 claim ledger |
| `empiricalPending` | 需要数据、校准或实验 |
| `projectionLoss` | 高维语义投影到 R₈ 时有损 |
| `independentOrUndecidable` | 当前系统内不可判或独立 |
| `outsideCurrentInterface` | 缺解释器 / 缺语义 / 缺测量接口 |

---

## 4 · Roadmap 顺序

### R1 · 例句 corpus

建立 `WenR8Examples.lean` 与 companion doc：

| 例句 | 预期语义 |
|---|---|
| 道总归道 | `returnsDao (.cell R8.origin)` |
| 真可假假可真 | 同一 axis toggle twice returns origin |
| 分而可合 | lift / project retract |
| 加元 / 加爻 | `AxisAppropriate` certificate |
| 高于八而投影于八 | `projected c ProjectionLoss.*` |

状态：typed skeleton 已落地于 [`RootRuleExamples.lean`](../../formal/SSBX/Foundation/Wen/RootRuleExamples.lean)，入口 theorem：

```lean
root_rule_examples_summary
```

已覆盖：

| 例 | 当前 theorem |
|---|---|
| 道总归道 | `dao_returns_dao_visible` |
| 真可假假可真 | `truth_toggle_twice_returns_dao` |
| 缺上下文 | `missing_context_reports_loss` |
| quote 有高阶损失 | `quote_reports_loss` |
| 加轴可审计 | `yin_axis_candidate_appropriate` |

### R2 · 通用语法核

建立 `WenR8Kernel.lean`：

```lean
inductive CoreForm
  | quote
  | apply
  | compose
  | ite
  | equal
  | lookup
  | recurse
  | project
```

目标：证明每个 kernel primitive 都有 R₈ encoding 与 `R8Semantics` 投影。

### R3 · 371 catalogue 分层接入

不要声称 371 个都已完整专义。分三层接入：

| 层 | 内容 |
|---|---|
| exact cell transform | 已有 `43 × 256 = 11008` family-backed rows |
| signature carrier | 有 arity / action-bit / structural carrier |
| domain semantics pending | 需要文义 / 领域解释 |

目标：每个 `OperatorId` 至少有 `R8Semantics.projected` 或 `slice` 的保守落点。

### R4 · Axis independence checker

建立有限 basis / span checker：

```text
newAxis ∉ span(priorAxes)
```

目标：把 `AxisAppropriate.independentFromPrior` 从外部证书推进到可计算证书。

状态：typed skeleton 已落地于 [`R8AxisIndependence.lean`](../../formal/SSBX/Foundation/Wen/R8AxisIndependence.lean)，入口 theorem：

```lean
r8_axis_independence_summary
```

### R5 · Projection kernel

定义高维投影：

```text
projectToR8 : H → R8
kernel(projectToR8)
```

目标：不仅说“有损”，还说明哪些差异被折叠。

状态：typed skeleton 已落地于 [`R8ProjectionKernel.lean`](../../formal/SSBX/Foundation/Wen/R8ProjectionKernel.lean)，入口 theorem：

```lean
r8_projection_kernel_summary
```

### R6 · Science carriers

逐步把已有 Modern 文件接入统一 carrier/enrichment 表：

| carrier | 文件方向 |
|---|---|
| Bool / Fin | R-hierarchy |
| Qubit / Hilbert | Quantum / QuantumR8Bridge |
| Probability | QuantumRelativityFiniteProbability* |
| Measure | Kolmogorov / Lebesgue |
| Program | BaguaTuring / Wen MetaInterp |

---

## 5 · 推荐公开说法

### 5.1 现在可以公开说

> We have formalized a minimal R₈ algebraic kernel for a self-auditing unification framework: R₈ = (Z/2)⁸ is complete for its XOR self-action closure, and higher expressions can be projected into R₈ with explicit loss ledgers. This is not yet a completed physical GUT; it is a formally anchored, scale-aware language for expressing, projecting, and auditing claims across mathematical, linguistic, and scientific layers.

中文：

> 我们已经形式化了一套以 R₈ 为最小核的自审计统一框架：R₈ 对自身 XOR 自作用闭合完备；高阶表达可投影入 R₈，并记录损失账本。这还不是已完成的物理大统一理论，而是一套有形式锚的、可跨尺度表达、投影、审计 claim 的语言。

### 5.2 最终希望公开说

> 生生不息是一套 scale-free 的边界生成理论：R₈ 给出最小表达闭合核，自相似升维给出任意尺度的可描述结构，文 / 程序 / 测量 / 量子 / 概率 / 连续数学都作为 carrier 或 enrichment 进入同一投影-审计框架。它对任何可描述 claim 给出 truth status，而不是把所有问题粗暴压成一个内部 yes/no。

---

## 6 · 一句话

当前：

```text
R₈ 核 + 文-R8 投影规约已经成立。
```

最终：

```text
R₈ 核 + scale-free 自相似生成 + truth-status ledger
= 一套可表达、可投影、可审计的一般统一理论。
```
