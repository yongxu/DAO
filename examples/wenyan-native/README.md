# Native wenyan algorithm files

这些示例不用 Lisp / S-expression。`quicksort.wen` 已可由专用文言算法 parser 读入，
先成 `Function / Stmt / Expr` 小 AST，再降低到 native `TopForm 8`，最后由 native evaluator 运行。

当前状态：

- 规范语法见 `docs-next/10_formal_形式/wenyan-native-syntax-spec.md`。
- parser、native lowering 与语义见 `formal/SSBX/Foundation/Wen/WenyanAlgorithms.lean`，已由 Lean 小定理验证。
- `quicksort.wen` 可由 `wenyan-algorithm` 运行；它不走 Lisp reader。
- 当前输出走 native `TopForm 8 / Value 8`；后续可把同一文法并入通用 native reader。

## Inventory

| File | 内容 |
|---|---|
| `list-basics.wen` | 映、择、折、和 |
| `quicksort.wen` | 快速排序 |

## Parser Surface

当前 parser 覆盖快速排序所需的小文法：

```text
法曰名。
受列。
若列空，归空。
取列之首，名曰枢。
取列之余，名曰余。
令小者为择（不大于枢）余。
令大者为择（大于枢）余。
归并速排小者、结枢空、速排大者。
试以三、一、二、一。
```

## Run

`quicksort.wen` includes a sample line:

```text
试以三、一、二、一。
```

Run it through the native wenyan algorithm parser:

```bash
lake env lean --run WenyanAlgorithm.lean examples/wenyan-native/quicksort.wen
```

Override the sample input with command-line numbers:

```bash
lake env lean --run WenyanAlgorithm.lean examples/wenyan-native/quicksort.wen 9 4 1 4
```
