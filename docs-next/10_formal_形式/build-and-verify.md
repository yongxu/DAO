# 构建与核验

本页说明形式层如何读构建结果。机器事实以最新 `lake build`、Lean 源文件与 `../_generated/` 为准；人工文档只给出核验口径。

## 当前口径

- `lake build` 已恢复通过。
- 当前仍有 unused `simp` argument warnings；这些是警告，不是证明缺口本身。
- live `sorry`、`admit`、`unsafe` 不应存在。
- 唯一显式 axiom 是 `kleene_recursion_axiom`。
- 唯一 opaque 是 `theOne`。
- 唯一顶层 partial boundary 是 `YiState.run`。

以上统计应以 [../_generated/trust-boundary.md](../_generated/trust-boundary.md) 与最新构建输出复核，不从散文段落读取最终数量。

## 建议核验顺序

1. 运行 `lake build`，先确认 Lean 层能通过。
2. 查看警告是否只是 unused `simp` argument 一类维护警告。
3. 查 [../_generated/lean-index.md](../_generated/lean-index.md)，确认模块是否被索引到。
4. 查 [../_generated/trust-boundary.md](../_generated/trust-boundary.md)，确认 axiom、opaque、partial def 没有扩张。
5. 查 [../_generated/claim-index.md](../_generated/claim-index.md)，区分 machineChecked、modelComputed、ledgerDependent。

## 通过不等于全闭合

构建通过只说明当前 Lean 文件在给定依赖与信任边界下类型检查成功。它不自动说明：

- ledgerDependent claim 已由 Lean 证明。
- 经验阈值、正邪判定或 Ω 类接口已经实证闭合。
- `kleene_recursion_axiom` 已被内部化。
- `YiState.run` 的所有执行都会返回。

因此文档写法应使用「构建通过，仍有警告」「在该 axiom 下」「由 ledger 记录」「由模型计算」等口径，避免把工程状态扩大成哲学或经验结论。

## 警告处理

unused `simp` argument warnings 通常表示证明脚本里有多余的 simp 参数。处理它们可以提高可维护性，但在当前口径下不改变 theorem 的成立状态。

若新增 warning，应先判断它是否影响：

- theorem 是否仍能通过。
- 是否暴露了不可达、未使用或误命名声明。
- 是否改变生成索引中的模块覆盖。
- 是否改变信任边界扫描。

## 文档同步

构建事实写入人工文档时，只写稳定结论和路径。模块数、声明数、claim 数、算子数、pending 数等易漂移数据，引用 `../_generated/`，不要手动复刻。
