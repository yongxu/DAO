# BaguaTuring run boundary

结论：`YiState.run` 的 `partial def` 不应在当前接口中删除。

## 边界

- `runFuel : Nat -> YiState -> YiState` 是证明路径。它是结构递归的总函数，所有可机检的执行正确性、停机上界、反例与归纳不变量都应落在这里。
- `run : YiState -> YiState` 是执行边界。它表达“无界运行直到停机”；对不停止的程序，它可能不返回结果。

因此，若把 `run` 改成普通总函数 `YiState -> YiState`，就必须给每个输入返回一个 `YiState`。这会把不停止的执行伪装成某个最终状态，丢失当前 Turing/nontermination 语义。可以新增总的 bounded API，也可以定义返回 `Option`、fuel、trace 或 coinductive stream 的替代接口，但这些都不是与现有 `run` 同型同义的替代。

## 机检证据

`BaguaTuring.lean` 中的 `loopProg` 是 `[jump 0]`。新增边界定理证明：

- `step_loopProg_init`：单步后仍是初态。
- `runFuel_loopProg_init_eq`：任意 fuel 后仍是初态。
- `loopProg_has_no_fuel_witness`：不存在有限 fuel 使其停机。
- `loopProg_unbounded`：公开的 qian 输入版本，保持原摘要定理的形状。

这些定理说明：`runFuel` 足以承载证明；`run` 保留为可能发散的可执行见证，而不是 theorem-level proof object。
