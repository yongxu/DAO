# 文之 native 构造层

> 状态：v1 (2026-05-13)
> Lean anchor: `SSBX.Foundation.Wen.Native.Reader`, `SSBX.Foundation.Wen.Native.ChineseAliases`
> 作用：固定 native Wen 中「式、行、列、文、值、集」之构造口径；中文 primitive 作为 surface alias / 理论词表，文言算法 parser 降低到 native top forms 后运行。

## Decision

文构造层采用 native Wen，而不是旧 V4 Lisp spine：

```text
名 / 元 / 算子
  -> 式
  -> 行
  -> 行列
  -> 文
  -> 运行
  -> 值
  -> 值列
  -> 集
```

这条链的关键点是：`文` 是可执行行之列，不是单个表达式；`集` 是列上附加去重判准，不是塞回单个 R₈ cell 的幂集对象。

## Terms

| 中文 | Lean anchor | 说明 |
|---|---|---|
| 元 | `Cell n = Layered.Rn n` | rank-polymorphic cell；R₈ 时为 Cell256 视角 |
| 算子 | `Prim n` / `Layered.Vn n` | native primitive 或层内 action |
| 名 | `Expr.ref : Cell n -> Expr n` | surface/global name 经 cell 命名 |
| 式 | `Native.Expr n` | native core expression |
| 核式 | `RootRuleKernel.CoreForm` | root-rule kernel 之保守 R₈-visible core form |
| 行 | `TopForm n` | 可执行 top form：表达式行或定义行 |
| 行列 | `List (TopForm n)` | 多行有序列 |
| 文 | `List (TopForm n)` | 程序文本之形式锚；等同于行列 |
| 值 | `Value n` | native runtime value |
| 值列 | `List (Value n)` 或 `Value.list` | 值之有限序列；运行结果可保留顺序与重复 |
| 集 | `List α + Nodup` | 列加无重复证明；遗忘顺序/重复时才进入集合口径 |

`史` 与这里的 `集` 不同。`史` 保留次序、重复与过程痕迹；把 `史` 投成 `集` 是有损的 support 操作。

## Chinese Primitive Surface

中文 primitive 是 reader/surface 边界别名，全部落到既有 native constructor 或 `Prim`：

| 中文 | native |
|---|---|
| 函 | `lambda` / `Expr.lam` |
| 施 | `app` / `Expr.app` |
| 结 | `cons` / `Prim.cons` |
| 空 | `nil` / `Expr.nil` / `Value.nil` |
| 首 | `car` / `Prim.car` |
| 余 | `cdr` / `Prim.cdr` |
| 若 | `if` / `Expr.if0` |
| 空乎 | `null` / `Prim.null` |
| 判空 | `null` / `Prim.null` |
| 不大于 | `numLe` / `Prim.numLe` |
| 大于 | `numLt` / `Prim.numLt` |
| 引 | `quote` / `Expr.quote` |
| 解 | `eval` / `Prim.eval` |
| 定 | `define` / `TopForm.define` |

这些字在 surface 边界降低到 native core。`不大于/大于` 与递归闭包是为了让纯文言快速排序跑在 native evaluator 上加入的最小 native core 支持；它们不改变 R₀..R₈ carrier。

## Lists And Sets

列用 `空` 与 `结` 生成：

```text
列:
  空
  结 x xs
```

在 Lean core 中，表达式列用 `Expr.list` 展开为 `Expr.nil / Expr.cons`；值列用 `Value.list` 展开为 `Value.nil / Value.cons`。reader 中 `(结 a b)` 作为 surface primitive application 读入，求值后得到同一值层 cons。

集不是新的 cell carrier：

```text
集 α:
  items : List α
  nodup : items.Nodup
```

因此：

```text
值列 -> 集
```

必须显式给出去重判准。若以后需要 quotient set 或 finite set API，应作为值列上的外延视图加入，而不是把 `P(R₈)` 声称为一个 R₈ 元。

## Functor Boundary

`函` 只是映射候选。`函子` 需要再加保结构律：

```text
函子 = 函 + 保结构律
```

list-map 的理论式可以写作：

```text
映 f 空 = 空
映 f (结 x xs) = 结 (施 f x) (映 f xs)
```

这里的 `施 f x` 是 native application；若 `f` 是 core lambda，则经 `Expr.app` 运行；若 `f` 是 primitive，则经 `Prim` arity 与 `applyPrim` 运行。

## Boundaries

- 本页只固定 native Wen 的构造词表，不改 R₀..R₈ strict `(Z/2)^n` 层级。
- `R₈` 可承载有限编码、路径或投影，但不能把 `P(R₈)` 当作单个 R₈ cell 无损容纳。
- `Cell256` 是当前 R₈ carrier；不引入 `Cell192`。
- 中文 token 是 surface alias；本体层仍是 `Expr n`, `TopForm n`, `Value n`, `Prim n`。
- `核式` 指向 `RootRuleKernel.CoreForm`，与 native `Expr n` 并列为理论锚；二者不在本页合并。

## Lean Placement

- `formal/SSBX/Foundation/Wen/Native/ChineseAliases.lean`：中文 `abbrev/def` 与小定理，证明别名与 native core 同义。
- `formal/SSBX/Foundation/Wen/Native/Reader.lean`：reader 接受中文 surface token，并降低到既有 native primitive / constructor。
- `docs-next/10_formal_形式/wenyan-native-syntax-spec.md`：纯文言 algorithm parser 的规范语法；先固定结构，再扩实现。
- `formal/SSBX/Foundation/Wen/WenyanAlgorithms.lean`：不用 Lisp surface 的文言算法 parser；先把 `法曰/受/若/取/令/归/试以` 小文法读成 `Function / Stmt / Expr`，再降低到 `Native.SurfaceTopForm 8 / TopForm 8` 并用 native evaluator 运行，以 Lean 小定理验证快速排序语义。
- `WenyanAlgorithm.lean` / `wenyan-algorithm`：运行 `examples/wenyan-native/` 中的纯文言算法文件，不经 Lisp reader。
- 后续如果扩 reader，应保持同一策略：中文 token 做 parse-time lowering；只有确需表达新可计算能力时才补最小 native primitive。
