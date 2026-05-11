# R8 Root Language Tree — 生成核、双重读法与语言边界

> 状态：draft v0.1 (2026-05-11)
> 角色：本文给出“完整语言树 root”的结构版 claim：exact cell transform 不应靠万行枚举表作为本体，而应由 R₀..R₈ 根树与生成规则给出；371 / 11008 / 94976 等表是解释层、索引层或展开层，不是最小本体。
> 前置：[`yi-RO-hierarchy.md`](yi-RO-hierarchy.md) · [`cell256-algebra.md`](cell256-algebra.md) · [`../00_start/final-claim-roadmap.md`](../00_start/final-claim-roadmap.md) · [`../../义理/文-R8投影规约.md`](../../义理/文-R8投影规约.md)
> 审阅包：[`root-language-tree/README.md`](root-language-tree/README.md) — R₀..R₈ 共 1022 个 interface entries 的文言 / 中文 / English / formal logic 候选表。
> Lean 锚点：[`RootLanguageTree.lean`](../../formal/SSBX/Foundation/Hierarchy/RootLanguageTree.lean) — `root_language_tree_summary` 证明 511 / 1021 / 1022 计数；[`RootRuleKernel.lean`](../../formal/SSBX/Foundation/Wen/RootRuleKernel.lean) — `root_rule_kernel_summary` 证明 root rules 的 R8-visible 程序核；[`RootRuleExamples.lean`](../../formal/SSBX/Foundation/Wen/RootRuleExamples.lean) — `root_rule_examples_summary` 固定例句目标行为；[`RootRuleDemoInterpreter.lean`](../../formal/SSBX/Foundation/Wen/RootRuleDemoInterpreter.lean) — `root_rule_demo_interpreter_summary` 给出最小 demo interpreter；[`R8ProjectionKernel.lean`](../../formal/SSBX/Foundation/Wen/R8ProjectionKernel.lean) — `r8_projection_kernel_summary` 给出通用 projection kernel；[`ExactCellTransformGenerator.lean`](../../formal/SSBX/Text/ExactCellTransformGenerator.lean) — `exact_cell_transform_generator_summary` 证明 exact transforms 由 43×256 生成；[`OperatorCatalogueLayering.lean`](../../formal/SSBX/Text/OperatorCatalogueLayering.lean) — `operator_catalogue_layering_summary` 证明 371 catalogue 的分层账本；[`R8AxisIndependence.lean`](../../formal/SSBX/Foundation/Wen/R8AxisIndependence.lean) — `r8_axis_independence_summary` 证明有限 XOR span 的 axis 恰当性接口。

---

## 0. 一句话

最终要表达的不是“列完所有表”，而是：

> **R₀..R₈ 给出完整语言的根树；每个根既可读为元，也可读为算；规则给出根的组合、施用、投影、升维与归道。因此一切可表达的语言结构，若进入表达、计算、证明、测量或解释，就必须表现为 R8 root、R8 operator、R8 path、R8 program、R8 projection 或其高维 lift 的轨迹。**

这里的“跑不出框架”是结构意义上的：

```text
可表达
→ 可形成语法 / 程序 / 证明 / 模型 / 记录
→ 可由有限或可生成的 root + rule 组合承载
→ 可投影、审计、标记损失
→ 不脱离 R8-root language tree
```

这不是说每个对象都是一个 R8 cell；而是说每个可表达对象都必须通过 R8-root 生成语言中的某种组合形态出现。

---

## 1. 根树计数

strict v3 doctrine 采用：

```text
R_n = (Z/2)^n, n = 0..8
|R_n| = 2^n
```

所以根 cell 总数为：

```text
|R0| + |R1| + ... + |R8|
= 1 + 2 + 4 + 8 + 16 + 32 + 64 + 128 + 256
= 511
```

每个非零分化层的根有双重读法：

```text
cell / operator
元 / 算
体 / 用
位 / 动
名 / 法
state / transform
```

因此有两个相近但不同的计数。

### 1.1 读法标记根表：1022

如果把 R0 的唯一根也标记为两种 role：

```text
RootReading = (R0 + R1 + ... + R8) × {cell, operator}
|RootReading| = 511 × 2 = 1022
```

这适合作为“读法表”或“接口表”：每个 root 都允许被问“作为元是什么、作为算是什么”。

### 1.2 本体根树：1021

如果更严格地说，R0 是未分之根，在 cell/operator 区分之前，则不应把 R0 复制成两份：

```text
RootLanguageTree
= R0 + ((R1 + ... + R8) × {cell, operator})
= 1 + 2 × (2 + 4 + 8 + 16 + 32 + 64 + 128 + 256)
= 1 + 2 × 510
= 1021
```

本文推荐以 `1021` 作为本体根树，以 `1022` 作为读法标记表。

原因：

| 计数 | 用途 | 解释 |
|---|---|---|
| `511` | pure root cells | 只数 R₀..R₈ 元 |
| `1021` | ontology root tree | R0 未分；R1..R8 有元/算双读 |
| `1022` | interface reading table | 连 R0 也以 cell/operator 两接口读取 |

---

## 2. 为什么 exact cell transform 不该列成一万多行

`43 × 256 = 11008` 这类 exact transform row 有工程价值，但不是本体。

它的地位应当是：

```text
root rule
→ generated exact transform
→ generated table rows
→ indexed machine denotation
```

而不是：

```text
table rows
→ ontology
```

因为 R8 的 exact cell transform 由规则生成：

```text
apply(mask, cell) = mask xor cell
compose(maskA, maskB) = maskA xor maskB
inverse(mask) = mask
identity = origin
returnDao(path) = fold_xor(path) = origin
```

所以只要给出：

1. root tree；
2. dual role；
3. XOR / compose / apply / inverse / identity；
4. lift / project；
5. path fold 与 return-to-dao；

就已经给出了 exact transform 的生成规则。

表格只应作为：

| 层 | 作用 |
|---|---|
| generated layer | 展开给机器检查、索引、查询 |
| interpretation layer | 接到具体 Wen / 领域语义 |
| coverage layer | 保证 catalogue 没漏项 |
| audit layer | 记录哪些是 exact，哪些只是 carrier |

因此，一万多行不应手写维护；它应由根规则生成、由测试验证、由文档解释。

Lean skeleton 已落地于：

```lean
SSBX.Text.ExactCellTransformGenerator.exact_cell_transform_generator_summary
```

它证明：

```text
43 exact-transform operator ids × 256 R8 cells = 11008 generated exact rows
11008 exact rows + 83968 signature-carrier rows = 94976 coverage rows
```

---

## 3. 根、算、路、文

R8-root language tree 的最小对象不是单一表，而是四类构造。

| 构造 | 形式 | 含义 |
|---|---|---|
| `Root` | `Σ n≤8, R_n` | 根 cell |
| `Role` | `cell | operator` | 元/算双读 |
| `Path` | `List R8` | 多步变化轨迹 |
| `Program` | `Tree / Lisp / Wen form` | 可组合表达 |

### 3.1 Root

Root 是所有分化的根：

```text
R0, R1, R2, R3, R4, R5, R6, R7, R8
```

R8 不是简单终点，而是当前 strict binary closure 的最小完整核：

```text
R8 = (Z/2)^8 = Cell256
```

R8 之内每个 cell 同时可作为：

```text
state:     c
operator:  s ↦ c xor s
```

这就是元-算融合。

### 3.2 Role

Role 不是额外的第九 bit；它是同一个 root 的读法。

```text
same carrier, two readings:

c : R8 as cell
c : R8 as operator
```

所以：

```text
R8 元数 = 256
R8 XOR 自作用算子数 = 256
元与算通过 Cayley evaluation 对齐
```

不能把它误读成：

```text
R8 有 512 个本体元素
```

更准确地说：

```text
R8 有 256 个对象；
每个对象有 cell/operator 双重用法。
```

### 3.3 Path

语言不只是一个 cell，而经常是 path：

```text
[a, b, c, ...] : List R8
```

path 的可见结果由 fold 给出：

```text
fold_xor([]) = origin
fold_xor([a]) = a
fold_xor([a,b]) = a xor b
fold_xor([a,a]) = origin
```

这给出“回归道”的最小判据：

```text
returnsDao(path) iff fold_xor(path) = origin
```

“真可假假可真”在这个层面上可以读成：

```text
toggle truth
toggle truth again
return origin
```

即：

```text
t xor t = origin
```

### 3.4 Program

复杂语言、理论、函数、证明与模型不是单个 cell，而是 program：

```text
Program(R8)
= finite or generated combinations of R8 roots and rules
```

典型形式可以是：

```text
(quote x)
(apply f x)
(compose f g)
(if p a b)
(equal a b)
(lookup env k)
(recurse fuel body)
(project h)
```

这些不是 R8 之外的逃逸，而是 R8 root 的组合语法。

---

## 4. 最小规则集

完整语言树至少需要以下 root rules。

| 规则 | 类型 | 作用 |
|---|---|---|
| `quote` | syntax → data | 把表达作为对象 |
| `apply` | operator × cell → cell | 施用 |
| `compose` | operator × operator → operator | 合成 |
| `xor` | R8 × R8 → R8 | Abelian group operation |
| `neg` | R8 → R8 | 在 (Z/2)^n 中即自身 |
| `equal` | a × a → Bool | 可判等结构 |
| `if` | Bool × a × a → a | 分支 |
| `lookup` | env × name → value | 命名与引用 |
| `recurse` | fuel × body → partial value | 有界递归 |
| `project` | higher → R8 × loss | 投影与损失 |
| `lift` | Rn × new axis → Rn+1 | 升维 |
| `returnDao` | path → Bool | 归道检测 |

其中 `quote/apply/compose/if/equal/lookup/recurse/project` 对应通用 Lisp/Wen kernel；`xor/neg/lift/project/returnDao` 对应 R-hierarchy 的代数骨架。

Lean skeleton 已落地于：

```lean
SSBX.Foundation.Wen.RootRuleKernel.root_rule_kernel_summary
```

该文件把 primitive rule 读成 `List R8` path / program，而不是单个 R8 cell；这保持了“生成规则完整、单格不装万物”的边界。

### 4.1 `apply`

```text
apply(mask, cell) = mask xor cell
```

算子不是外来的函数表，而是同一个 root 的用法。

### 4.2 `compose`

```text
compose(a, b) = a xor b
```

因为：

```text
(a xor -) ∘ (b xor -)
= (a xor b xor -)
```

### 4.3 `neg`

在 `(Z/2)^n` 中：

```text
neg(a) = a
a xor a = origin
```

所以每个 exact XOR operator 自反、自逆。

### 4.4 `project`

高维结构不能假装无损塞入 R8；必须返回损失账本：

```text
project(higher) = (visibleR8, loss)
```

其中 `loss` 至少应区分：

| loss | 含义 |
|---|---|
| `none` | 无损 |
| `extraAxis` | 折叠了额外 axis |
| `history` | 折叠了路径历史 |
| `context` | 折叠了语境 |
| `recursion` | 折叠了递归展开 |
| `higherOperator` | 折叠了高阶算子 |

### 4.5 `lift`

升维不是任意添加标签，而是创造新的信息 axis：

```text
lift : Rn × Axis → Rn+1
```

一个 axis 恰当，至少要满足：

```text
nonzero
independent from prior axes
projectable back to prior layer
```

这对应“加元/加爻是否恰当”的判断。

Lean skeleton 已落地于：

```lean
SSBX.Foundation.Wen.R8AxisIndependence.r8_axis_independence_summary
```

它把 `AxisAppropriate.independentFromPrior` 从纯外部证书推进到有限 span 条件：

```text
newAxis ∉ span(priorAxes)
```

边界：这只检查 R8 mask 层面的线性独立和 projectable 标记；某个领域 axis 是否有经验意义，仍要由对应 carrier / evidence ledger 证明。

---

## 5. 371、11008、94976 的正确地位

这些数不应被混入根本体。

| 数 | 来源 | 正确地位 |
|---|---|---|
| `256` | `|R8|` | Cell256 根核 |
| `371` | Wen operator catalogue | 文义/语法算子索引 |
| `11008` | `43 × 256` | exact cell transform 展开行 |
| `94976` | `371 × 256` | operator-cell coverage grid |
| `1021` | `R0 + 2×(R1..R8)` | 推荐本体语言根树 |
| `1022` | `2×(R0..R8)` | 读法标记接口表 |

核心判断：

```text
256 是 R8 root carrier。
371 是解释层 catalogue。
11008 是部分 exact transform 的生成展开。
94976 是覆盖网格。
1021/1022 是跨 R0..R8 的 root language tree 计数。
```

因此，371 不是 R8 之外的第二个本体空间；它是 Wen/operator naming layer。
11008 不是应该手写的事实集合；它是规则展开。
94976 不是完整语义；它是 coverage grid。

Lean skeleton 已落地于：

```lean
SSBX.Text.OperatorCatalogueLayering.operator_catalogue_layering_summary
```

它证明：

```text
371 catalogue ids = 43 exact-transform ids + 328 non-exact catalogue ids
43 × 256 = 11008 exact rows
328 × 256 = 83968 signature/domain-pending rows
371 × 256 = 94976 coverage rows
```

---

## 6. “一切语言表达”如何落入框架

一个可表达对象至少会落入下列之一：

| 语言对象 | R8-root 形态 |
|---|---|
| 名词 / cell | `R8` 或 `Root` |
| 动词 / 算子 | `R8 as operator` 或 `OperatorId → R8Semantics` |
| 句子 | `Program / WenNormalForm` |
| 推理 | `Path / compose / if / equal` |
| 函数 | `Program(R8)` 或 `Table(R8)` |
| 理论 | `Set of claims + rules + ledger` |
| 证明 | `derivation tree` with R8 projection |
| 模型 | `carrier + interpretation + projection` |
| 测量 | `phenomenon → data → R8 projection + evidence ledger` |
| 量子态 | `Hilbert carrier + R8-visible basis/projection` |
| 概率 | `kernel/measure carrier + R8-visible event partition` |

所以：

```text
语言表达不等于 R8 单 cell。
语言表达 = R8 root 生成的组合、路径、程序、投影与解释。
```

这让“所有理论都跑不出”有一个严格读法：

> 任意理论一旦被表达，就必须有语法、对象、规则、证明、模型、证据或引用结构；这些结构可被编码为 root + rule 的组合，并在 R8 层取得可见投影与损失账本。因此理论可以超过 R8 的单 cell，但不能脱离 R8-root 生成框架。

---

## 7. 自相似与无边界

R8 是当前 strict binary closure 的最小核，但自相似过程没有固定终点。

这句话必须分两层读：

| 层 | 说法 |
|---|---|
| bounded kernel | R8 足以作为当前语言表达边界的最小核 |
| scale-free growth | List / Tree / Program / Stream / Measure / Hilbert 等可继续生长 |

因此不是：

```text
R8 cell contains everything.
```

而是：

```text
R8 roots generate every expressible structural trajectory.
```

高维结构可以继续生长：

```text
R8
→ List R8
→ Tree R8
→ Program R8
→ Stream R8
→ Probability kernel
→ Measure space
→ Hilbert carrier
→ Physical model
```

但每一层若要被语言、证明、测量、模型表达，就必须能给出：

```text
visible R8 projection
loss ledger
return-to-dao / non-return condition
```

---

## 8. 完整 claim

推荐完整表述如下：

> **R8-root language tree 是一套以 R₀..R₈ strict binary hierarchy 为根、以 cell/operator 双重读法为用、以 quote/apply/compose/if/equal/lookup/recurse/project/lift/returnDao 为规则的生成系统。它不是靠枚举所有表而完整，而是靠 root 与 rule 的闭合生成而完整。exact cell transforms 应由规则生成；371 个 operator 是 Wen 解释层 catalogue；94976 行是 coverage grid。任意可表达语言、函数、理论、证明、模型或科学 claim，若进入表达与审计，就必然表现为 R8 root 的组合、路径、程序、投影或高维 lift 的轨迹。高维不逃出 R8-root 框架，而是在自相似生长中增加 carrier；投影回 R8 时必须记录损失。因此，从语言结构上说，理论跑不出这个框架；跑出的只是不在当前解释器中的 carrier 或未登记的 scale。**

这个 claim 的强点是：

```text
完整性来自生成规则，不来自枚举。
统一性来自可投影审计，不来自把所有东西压成一个 cell。
scale-free 来自 root+rule 的自相似生长，不来自固定 256 表。
```

---

## 9. 当前可 claim 与最终 claim

### 9.1 当前可 claim

当前可以稳妥公开说：

> R₀..R₈ 已给出 strict `(Z/2)^n` root hierarchy；R8 = Cell256 对 XOR self-action 完备；每个 R8 cell 可经 Cayley 读为 exact XOR operator；复杂 Wen / Lisp / Program 结构可以作为 R8-root 组合进入投影规约。371 / 11008 / 94976 是解释层与展开层，不是根本体。

### 9.2 最终 claim

最终目标是：

> 完整实现 root language tree、通用语法核、Wen 解释器、axis appropriateness checker、projection kernel 与 truth-status ledger，使任意可表达 claim 都能被归入 root+rule 生成空间，并给出其 R8 可见投影、损失、归道条件与真假/可证/经验待定/边界外状态。

### 9.3 不应提前 claim

还不能说：

```text
自然语言语义已经完整完成。
全部物理理论已经统一证明。
所有数学真理都可内部判定。
所有函数 R8 → R8 都是一个 R8 cell。
371 个 operator 都已有完整领域语义。
```

正确说法是：

```text
所有这些一旦进入表达，就进入 root language tree 的审计范围；
但具体解释器、证明、物理 carrier 与证据 ledger 仍需分层完成。
```

---

## 10. 代码应如何表达这部分

最终代码不应以手写表为中心，而应以生成器为中心。

### 10.1 核心类型

已落地的 Lean skeleton 入口：

```lean
SSBX.Foundation.Hierarchy.RootLanguageTree.root_language_tree_summary
```

该 theorem 只证明 root-tree 的结构账本，不定最终字。建议的 Lean / code 层次：

```lean
inductive RootLayer
  | r0 | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8

inductive RootRole
  | cell
  | operator

structure RootNode where
  layer : RootLayer
  role : Option RootRole
  -- role = none only for R0 in the 1021 ontology tree
```

更严格的版本应把每层 carrier 也放入 dependent type：

```lean
RootCell := Sigma fun n : Fin 9 => R n
RootReading := RootCell × RootRole
RootLanguageTree := R0 ⊕ ((Σ n=1..8, R n) × RootRole)
```

### 10.2 规则类型

```lean
inductive RootRule
  | quote
  | apply
  | compose
  | xor
  | neg
  | equal
  | ite
  | lookup
  | recurse
  | project
  | lift
  | returnDao
```

### 10.3 生成而非枚举

应从：

```text
for each exact operator family
for each c : R8
emit row(operator, c, operator.apply c)
```

生成 exact rows。

手写文件只保留：

```text
operator family definition
root mask
arity / role / domain notes
proof that generated rows have expected count
```

这样 `11008` 可以继续存在，但它的地位是 theorem / generated artifact，而不是本体。

---

## 11. 与“道、理、法、证据、善”的关系

这些不是额外逃出系统的概念，而是 root language tree 中的角色。

| 概念 | root-language 读法 |
|---|---|
| 道 | origin / identity / no-op / return condition |
| 理 | 可推导、可复用、可解释的 rule structure |
| 法 | 可执行、可约束、可传递的 rule interface |
| 证据 | measurement / record / calibration 的 projection ledger |
| 善 | 多尺度生成中维持互通、归位、非破坏性延展的结构条件 |
| 真 | claim 在 proof/model/evidence/boundary ledger 中的状态 |

所以“讲理”可以形式化为：

```text
把 claim 放入 rule structure，
说明其前提、推导、投影、证据与边界。
```

“理性”则是：

```text
把理施用于现象，
并接受 measurement / evidence / loss ledger 的约束。
```

---

## 12. 完成路线

| 阶段 | 要完成的东西 | 结果 |
|---|---|---|
| A | RootLanguageTree 类型与计数证明 | done: `RootLanguageTree.lean` 证明 511 / 1021 / 1022 |
| B | RootRule kernel | done: `RootRuleKernel.lean` 给出 quote/apply/compose/... 的 R8-visible 程序核 |
| C | exact transform generator | done: `ExactCellTransformGenerator.lean` 证明 43×256=11008 由生成器得到 |
| D | operator catalogue layering | done: `OperatorCatalogueLayering.lean` 证明 371 = 43 exact + 328 non-exact |
| D2 | axis appropriateness checker | done: `R8AxisIndependence.lean` 给出有限 XOR span checker |
| D3 | example corpus skeleton | done: `RootRuleExamples.lean` 固定“归道/双翻/损失/加轴”目标行为 |
| D4 | projection kernel | done: `R8ProjectionKernel.lean` 给出通用 `ProjectionToR8 H` 与 kernel relation |
| E | Wen/Lisp interpreter | demo skeleton done: `RootRuleDemoInterpreter.lean`; full parser/interpreter pending |
| F | projection kernel | 高维 carrier 投影到 R8 并记录 loss |
| G | truth-status ledger | claim 不再只是真/假，而有审计状态 |
| H | science carriers | 概率、连续、量子、物理模型分层接入 |

完成 A-D 后，可以说：

```text
root language tree 与 exact cell transform 的本体结构已经闭合。
```

完成 E-G 后，可以说：

```text
任意可表达 claim 已进入统一审计语言。
```

完成 H 后，才可以更认真地推进：

```text
科学统一框架 / 物理接口 / 数学-语言-测量统一
```

---

## 13. 边界声明

本文主张的是结构生成完备，不是经验事实自动证明。

| 边界 | 说明 |
|---|---|
| 不是自然语言全语义完成 | 需要 parser / interpreter / corpus |
| 不是物理大统一已证明 | 需要 carrier、方程、实验、校准 |
| 不是所有数学真理可判定 | 不可判、独立、外部公理仍要进入 ledger |
| 不是 R8 单 cell 装万物 | 万物以 Program / Path / Carrier / Projection 表达 |
| 不是 371 即本体 | 371 是 catalogue，不是 root tree |

最终的强 claim 应始终带着这个边界：

```text
一切可表达结构跑不出 root+rule 生成框架；
但每个领域的真理、证据与语义，需要在相应 carrier 中完成。
```
