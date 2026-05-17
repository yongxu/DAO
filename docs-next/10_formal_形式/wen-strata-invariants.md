# Wen 语言栈之 stratum 边界 invariants

> Status: normative. Audience: future reviewers / Claude / human contributors
> evaluating "should X be folded into Y?" refactor proposals over the
> `formal/SSBX/Foundation/Wen/` surface.

## 缘起

判断「是否应当将 X 折叠为 Y 的 view」时，须先看 X 与 Y 是否处于**同一 stratum**。
本文档列举 `Foundation/Wen/` 下三个常被读者（包括最初撰写 multi-plan 之 reviewer）
混淆为「parallel AST」的类型 —— `WenDef.Tm` / `RootRuleKernel.CoreForm` /
`R8ProjectionCalculus.R8Semantics` —— 并说明它们实际上分属三个**不同 stratum**
（L1 / L3 / L1→L0 projection 见证），互不可互相 reduce。

本文不是历史性的「曾考虑过这件事」的反思 ——
它是**面向未来**的：若再有 PR 提议「Tm 立唯一 core，CoreForm 折叠为 view」，
请先读完本文，再决定是否仍要推进。结论是**不应折叠**；下方 §5 给出三条具体理由。

## §1  WenDef.Tm — L1 typed lambda

**来源**：`formal/SSBX/Foundation/Wen/WenDef.lean:91-138`
（`namespace SSBX.Foundation.Wen.WenDef`，`inductive Tm : Type`，47 个构造子，
`deriving DecidableEq, Repr`）。

**stratum**：L1（typed 用户级语言层 —— `Surface → SurfaceExpr → Tm` 之最终目的地）。

**构造子分类**：

| 类别 | 构造子 | 数量 |
| --- | --- | ---: |
| λ-calculus core | `var / abs / app` | 3 |
| 字面量 | `hexLit / boolLit / cellLit` | 3 |
| 内核 hex/bool 算子 | `jia / yi / notB / andB / orB / eqHex / forallH / uniqueH / exactly3H / majorityH / cuoH / zongH / huH / cuoZongH / flip1H..flip6H / pairH / dupH / list1H / list2H / list3H / headH` | 22 |
| Cell-级算子 | `eqCell / cuoC / zongC / huC / shiNextC / shiPrevC / flip1C..flip6C` | 12 |
| Catalogue 桥 | `catalogue1 / catalogue2 / catalogue3` (with `OperatorId`) | 3 |
| 共计 | | **43**\* |

\* WenDef.lean 顶部 doc-string 写「22 内核 + 用户 def」，对应 hex/bool 内核分组；
其余 12 cell-级算子是 V₄ Shi 迁移期间补入的（参见 file header §「Phase F.2 migration note」）；
catalogue1/2/3 是接 `Text.OperatorSignatures` 的桥点。

**责任**：
- parsing / elaboration 的目标 IR
- 用户级 eval 的 canonical term type
- 经 `WenDefEval.denoteHexFun` 之 Lean-level universal denotation
- 经 `WenDefCompile.compileHexFunCertified?` 之保守桥 → YiInstr（仅 cuo-equivariant 子集）

**不可达**：
- root-rule 之 `quote` / `recurse n` / `project` —— 这些不是 Tm 的语义层 primitives；
  Tm 的 hex/bool/cell 类型系统**不允许** meta-quotation
- 显式 `ProjectionLoss` ledger —— Tm 之 `Hex → Hex` 是确定函数，没有 loss tag

## §2  CoreForm — L3 R8-visible root program

**来源**：`formal/SSBX/Foundation/Wen/RootRuleKernel.lean:59-110`
（`namespace SSBX.Foundation.Wen.RootRuleKernel`，`inductive CoreForm : Type`，
10 个构造子）。

**stratum**：L3（root-rule visible program 层；R₈ projection 之**源头**）。

**10 构造子**（按 file 序）：

| # | 构造子 | 元数 / 载荷 | 语义意图 |
| ---: | --- | --- | --- |
| 1 | `atom` | `R8` | 单元 R₈ cell 字面量 |
| 2 | `primitive` | `RootRule` | 12 条 root rule 之注入 |
| 3 | `quote` | `CoreForm → CoreForm` | meta-quotation；强制 `higherOperator` loss |
| 4 | `apply` | `CoreForm → CoreForm → CoreForm` | Cayley-style R₈ self-action（XOR 实现） |
| 5 | `compose` | `CoreForm → CoreForm → CoreForm` | composition（XOR） |
| 6 | `ite` | `CoreForm → CoreForm → CoreForm → CoreForm` | 视情之 R₈.origin 与否分支 |
| 7 | `equal` | `CoreForm → CoreForm → CoreForm` | R₈ visible 相等性测试 |
| 8 | `lookup` | `String → CoreForm` | environment 名字解析；缺则 `context` loss |
| 9 | `recurse` | `Nat → CoreForm → CoreForm` | 显式 fuel 之递归；强制 `recursion` loss |
| 10 | `project` | `CoreForm → CoreForm` | 显式向 R₈ 投影 |

**责任**：
- RootRule 之 12-rule 的程序表达
- R₈ projection 之**载体** —— `CoreForm.eval : Env → CoreForm → R8Semantics`
  保证「每个 CoreForm 都有 visible R₈ projection」（`every_form_has_visible_projection`）
  以及「每个 CoreForm 都有 loss ledger」（`every_form_has_loss_ledger`）
- 12 条 stratum-内 theorem（`atom_visible` / `apply_atoms_visible` /
  `compose_atoms_visible` / `equal_same_atom_returns_origin` /
  `duplicated_apply_returns_origin` / `missing_lookup_has_context_loss` /
  `quote_reports_higher_operator_loss` / `recurse_reports_recursion_loss` /
  `every_form_has_visible_projection` / `every_form_has_loss_ledger` /
  `root_rule_kernel_summary` / `primitive_has_visible_projection`）

**不可达**：
- 通用 `Bool` 类型（CoreForm 把 truth 编码为「visible cell = origin or not」）
- 通用 lambda 抽象（CoreForm 没有 binder；`lookup` 仅是 environment 查表）
- Tm 之类型系统（`Ty.hex / .bool / .cell / .arr / ...`）

### CoreForm 与 Tm 不可互转的 rationale

三条**结构性**理由，每一条单独已足以否决 `Tm ≃ CoreForm` 同构：

1. **`quote` 是 meta-quotation 算子**，跨 L1/L3 边界。
   它把一个 CoreForm 表达式作为「higher-than-R8 operator」打包并强制 loss ledger
   `higherOperator`（见 RootRuleKernel.lean:81-83；`quote_reports_higher_operator_loss`
   theorem）。Tm 的 λ-calculus 不支持「将一个项当作元层引用」 —— Tm 的 binder 只跑
   capture-avoiding substitution，没有「打包 + loss tag」之概念。

2. **`recurse n e` 含显式 `Nat` fuel**，且强制 `recursion` loss
   （RootRuleKernel.lean:106-108；`recurse_reports_recursion_loss`）。
   Tm 之 λ-calculus 无 explicit fuel —— 它在 `JianSTLC` 桥上的语义是无界 β-reduction
   且保证停机（type-soundness 见 `Jian.JianSTLC.simulation`）。把 `recurse n e` 翻译进
   Tm 必须**丢掉** `n` 与 loss tag，二者皆是 R₈ projection 的 weight-bearing 数据。

3. **Tm 之 `Hex → Hex` 是确定函数**；CoreForm 之 `primitive` 携 loss ledger。
   即便仅看 closed cuo-equivariant 子集 —— Tm 经
   `compileHexFunCertified?` 编出 YiInstr 后是 deterministic 算子；
   而 CoreForm 之 `primitiveSemantics` 返回 `R8Semantics`，其值可能是
   `.path [...]` / `.projected c loss`，loss 信息无 Tm-side 对应。

**结论**：不存在 `Tm ≃ CoreForm` 同构函数。任何「折叠」尝试都要么丢 `quote / recurse / loss
ledger`（背叛 L3 stratum 的 R₈ projection 责任），要么要给 Tm 加 meta-quotation 与
fuel 的形式机制（背叛 L1 stratum 的「typed-λ 用户语言」责任）。两条路都不优于「保持两栈分立」。

## §3  R8Semantics — L1→L0 projection witness

**来源**：`formal/SSBX/Foundation/Wen/R8ProjectionCalculus.lean:66-71`
（`namespace SSBX.Foundation.Wen.R8ProjectionCalculus`，`inductive R8Semantics`，
5 个构造子）。

**stratum**：L1→L0 projection 的**见证类型** —— 不是独立 AST，而是
「Tm / CoreForm 在向 R₈（256-cell）投影时，损失了哪些 higher-than-R8 结构」
的可被审计 ledger。

**5 构造子**：

| # | 构造子 | 元数 | 含义 |
| ---: | --- | --- | --- |
| 1 | `cell` | `R8` | 单一 cell —— 无损投影 |
| 2 | `operator` | `R8 → R8` | 算子值 —— operator-shape，仍 R₈-内 |
| 3 | `path` | `List R8` | masks 折叠路径 —— Cayley-style |
| 4 | `slice` | `R8 → (R8 → Prop)` | 区域 + anchor cell —— diagnostic 用 |
| 5 | `projected` | `R8 → ProjectionLoss` | visible cell **加** loss tag —— 强制可审计 |

**配套 `ProjectionLoss`**（R8ProjectionCalculus.lean:36-43，6 类）：
`none / extraAxis / history / context / recursion / higherOperator`。
`ProjectionLoss.clear` 谓词（同文件 48-50 行）判定「无 higher-than-R8 material 被丢」
当且仅当 tag 为 `none`。

**责任**：
- 纪录 Tm / CoreForm 投影到 R₈ 时**损失了什么**
- 作为 `CoreForm.eval` 的返回类型，使 R₈-visible projection 的「每一步」都带 ledger
- 暴露 `visibleR8 : R8Semantics → R8` 之统一坐标
- 4 个核心 lemma（`foldMasks_nil / foldMasks_singleton / foldMasks_pair_self`
  以及 6 个 `ProjectionLoss.clear_*` 个案）作为 projection 算子代数的支撑

**不存活**：
- `R8Semantics → Tm` 之 lift —— 一旦 projected，higher-than-R8 信息已丢；不可还原
- `R8Semantics ≃ Tm × Loss` 不成立 —— `path` / `slice` / `operator` 三 case 携带的
  「非单点」结构在 Tm 端无对应（Tm 的 `Hex → Hex` 没有 path / region 之概念）

### loss ledger 之必要性

R₈ 是 256-cell **有限**论域。任何 Tm 之**非有限**项 ——
λ-over-无限-Nat / Kleene-递归 / meta-quotation —— 投到 R₈ 必丢信息。
R₈Semantics 用 `ProjectionLoss` 的 6 类标识「丢了什么类」：

| Loss tag | 何时产生 | 示例 source |
| --- | --- | --- |
| `none` | 完全在 R₈ 内 | `atom c` |
| `extraAxis` | 额外维度被压扁 | 高维 cell-product 投到 R₈ |
| `history` | path 之历史被折扁 | `foldMasks` 之结果 |
| `context` | 环境缺值 | `lookup name` 且 `env name = none` |
| `recursion` | 含 explicit fuel | `recurse n body` |
| `higherOperator` | meta-quote | `quote e` |

**没有** loss tag 的投影 = unsound projection。
任何想把 R8Semantics 改为「`Tm × Loss` view」的 refactor 都会破坏这个不变量
（因为 `path / slice / operator` 不能用 `Tm × Loss` 表达 —— 它们的 ledger 是
R₈-side 的几何信息，不在 Tm 端）。

## §4  Theorem 依赖分布

下表为撰文时（commit 树根 `main` 之前一次 spot-check）三个类型在 `formal/SSBX/` 树上的
直接引用 + 各自承载的 theorem / lemma 数量。粗略数字（grep -n 统计），用作
「stratum 的 weight-bearing 程度」之参考；不是精确的 theorem-dependency graph。

| stratum | 类型 | 直接 grep 引用数 | stratum 内 theorem/lemma 数 |
| --- | --- | ---: | ---: |
| L1 | `WenDef.Tm` | ~280（含 WenDef / WenDefEval / WenDefCompile / Text 几个簇） | ~40+ across eval/compile |
| L3 | `CoreForm` | 72（局限于 RootRuleKernel.lean 内 + 直接 R8 projection 用户） | 12 |
| L1→L0 | `R8Semantics` | 22（限 Foundation/Wen 内） | 4 核心 lemma + 6 `clear_*` |
| L3-meta | `RootRule / RootOperator / RootWord` triad | ~99（Foundation 全树） | ~56（含 Hierarchy 簇） |

**读数**：
- CoreForm 的 12 theorem 是「R₈ projection always-exists / always-has-ledger」的
  **直接 metatheory**；删一条都会让 §5 的「不要折叠」论证失去 Lean-机器支撑。
- R8Semantics 的 4 lemma + 6 个 `clear_*` 是 projection 代数的最小自洽集；
  数量小不代表 weight 小 —— 它是「整个 L1→L0 投影族」必经的瓶颈类型。
- RootRule triad 的 ~56 theorem 是 Path 丙 metatheory 的承重柱；
  CoreForm + R8Semantics 的「primitive」case 都把它们拉成 dependency。

## §5  推论：不要折叠

三条具体的「不」：

1. **不要尝试 `Tm ≃ CoreForm` 同构**。
   §2 末尾给的三条结构性理由（`quote` / `recurse` fuel / loss ledger）每一条
   单独已足以否决。把 CoreForm 折叠为「Tm 的 view」会强制让 Tm 长出 meta-quotation
   与显式 fuel —— 背叛 L1 stratum 的「typed-λ 用户层」契约。

2. **不要把 `R8Semantics` 改为 `Tm × ProjectionLoss`**。
   projection 之 loss 是 R₈-side 的几何信息（路径 / 区域 / operator-shape），
   不在 Tm 端。`path / slice / operator` 三 case 必死。

3. **不要废 `RootRuleKernel`**。
   它的 12 theorem 是 Path 丙 metatheory 的 weight-bearing 支柱；
   CoreForm 是 R₈ projection 之**唯一**带 loss-tracked 程序表面 ——
   没有它，「R₈-visible 根规则程序」就退化为字面 R₈ cell 集合，
   12 条 RootRule 与 R₈ 之间的算法桥消失。

这三条与「distinction monism」的 substrate 论证一致 —— 见
[`wen-substrate/03-operation-monism.md`](wen-substrate/03-operation-monism.md)
中 "Distinction monism — `o` / `x` below the operator" 一节
（v1.4 substrate 之底层 realisation-free 层）。该章节点出：
substrate 的根 primitive 不是任何具体类型 / 算法，而是 **act of distinguishing**；
每一个 stratum 是该 act 在不同 abstraction level 上的一次具体 instantiation
（chapter 01 表「Four nested abstraction levels」之 0/1/2/3 层）。
Tm（L1 typed-λ）/ CoreForm（L3 root-rule program）/ R8Semantics（L1→L0 projection 见证）
正是 substrate 在三个不同关注点上的 instantiation —— 折叠任意两个等于在
distinction-monism 框架下抹掉一对**独立的**realisation 层。

历史 note：multi-plan 第 ② 步「Tm 立唯一 core，CoreForm 折叠为 view」之误读，
源于把「parallel AST」错读为「相同 stratum 的不同书写形式」。
本文档之存在即是为防再次发生此类误读。

## §6  「Wen 语言栈」的真实层次

```
Layer L  (Surface):       String / 文言 prose
                          │
                          ▼  lex + Pratt parser
Layer L-1 (SurfaceExpr):  tree with markers/binders / 显式 binders
                          │
                          ▼  elaborate
                          │  (resolves names; uses Text.OperatorSignatures
                          │   + theoremBackedSemanticsFor? when present)
Layer L1 (Tm):            typed λ + 22 hex/bool 内核 + 12 cell 算子
                          │  + catalogue1/2/3 → OperatorId
                          │
                  ┌───────┼───────────────────────────┐
                  │       │                           │
                  ▼       ▼                           ▼
              denoteHexFun                  compileHexFunCertified?
              (Lean-level                   (保守桥, cuo-equivariant only)
               canonical eval)                          │
                  │                                     ▼
                  │                              YiInstr (ISA)
                  │                                     │
                  ▼                                     ▼
              Hexagram → Hexagram              YiState.runFuel (native eval)
                                                        │
                                                        ▼
Layer L0 (R8):            256-cell 具象 state, V₄ Shi {道,已,今,未}
                          ▲
                          │  R8Semantics (projection witness)
                          │  with ProjectionLoss ledger
                          │
Layer L3 (CoreForm):      root-rule programs (RootRule × 12 注入)
                          自 RootRuleKernel.CoreForm.eval 直射 R8Semantics
```

**关键不变量**：
- L1 ↔ L3 **不互转**（distinction monism）—— 见 §5 三条具体「不」
- L1 → L0 经 `compileHexFunCertified?` 仅覆盖 cuo-equivariant subset
  （wider 子集靠 native eval / `denoteHexFun`）
- L3 → L0 经 `CoreForm.eval` 强制 ledger（loss tag 必填）
- L0 → 任何上层**不存在 lift**（信息已丢）

## 参考

- `formal/SSBX/Foundation/Wen/WenDef.lean:91-138` — `Tm` 定义
- `formal/SSBX/Foundation/Wen/WenDefEval.lean` — `denoteHexFun`
- `formal/SSBX/Foundation/Wen/WenDefCompile.lean` — `compileHexFunCertified?`
- `formal/SSBX/Foundation/Wen/RootRuleKernel.lean:59-110` — `CoreForm` 定义；
  同文件 52-160 行为 12 个 stratum-内 theorem
- `formal/SSBX/Foundation/Wen/R8ProjectionCalculus.lean:36-43` — `ProjectionLoss`
- `formal/SSBX/Foundation/Wen/R8ProjectionCalculus.lean:66-71` — `R8Semantics`
- `docs-next/10_formal_形式/wen-substrate/03-operation-monism.md` —
  operation monism + **distinction monism**（substrate 之 realisation-free 层）
- `docs-next/10_formal_形式/wen-substrate/01-foundations.md` —
  Four nested abstraction levels（0/1/2/3）
- `docs-next/10_formal_形式/wen-native-expression-layers.md` —
  原生表达 layer 之另一面向
