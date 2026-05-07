# Foundation/Wen

`Foundation/Wen` 是文、文言微核、自释、自举与 quine 路线的集中区域。它也包含当前唯一 opaque witness：`theOne`。

## Kernel 与 `theOne`

`Kernel.lean` 给出「一」的封装见证。`theOne` 是 opaque，不是 axiom；下游使用其投影：

- `Field`
- `dong`
- `origin`
- `origin_alive`

读法是「保留抽象见证」，不是「新增未说明公理」。当前 opaque 边界见 [../_generated/trust-boundary.md](../_generated/trust-boundary.md)。

## 文言微核

`WenDef*`、`WenEval`、`WenyanSyntax`、`WenyanParser*` 等文件组织文言表达、解析、求值与编译路线。它们的目标是让文言片段进入可检查结构，而不是宣称自然语言整体已被完全形式化。

## 自释与自举

`WenyanReflect`、`WenyanSelfHost`、`WenyanSelfInterp` 等模块处理自释、自解释与自举路线。读法应分层：

- 语法层：对象语言如何表示。
- 求值层：表达如何执行或解释。
- 反射层：系统如何谈论自身片段。
- 证明层：哪些性质已成 theorem。

## Quine 路线

`WenyanQuine*` 系列记录自指、构造、见证、搜索、历史与路线。它与 Bagua/GodelLi 的不完备边界相关，但不能被写成去公理化已经完成。

当前仍有唯一显式 axiom `kleene_recursion_axiom`。相关去公理化路线应看 `formal/SSBX/notes/zero-axiom-roadmap.md` 与 [trust-boundaries.md](./trust-boundaries.md)。

## 与 Text 的分工

Text 层维护算子、字、义位与覆盖表；Wen 层处理文言表达系统本身。查询算子总表看 [../_generated/operator-index.md](../_generated/operator-index.md)，查询 Wen 模块清单看 [../_generated/lean-index.md](../_generated/lean-index.md)。
