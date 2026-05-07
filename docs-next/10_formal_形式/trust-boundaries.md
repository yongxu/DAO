# 信任边界

形式层的信任边界必须明示，避免把工程事实、经验校准或文档同步误读为 Lean 已闭合证明。

## 已知边界

| 边界 | 位置 | 口径 |
|---|---|---|
| `kleene_recursion_axiom` | `formal/SSBX/Foundation/Bagua/GodelLi.lean` | 唯一显式 axiom；用于 cuo-restricted Kleene/Rice/GodelLi 结论。 |
| `opaque theOne` | `formal/SSBX/Foundation/Wen/Kernel.lean` | 唯一 opaque；封装「一」的见证，使 `Field`、`dong`、`origin` 保持抽象。 |
| `YiState.run` | `formal/SSBX/Foundation/Bagua/BaguaTuring.lean` | 唯一顶层 `partial def`；表示无界执行可能不返回。证明路径使用 `runFuel`。 |

## 非边界但常被误读的项

- `Field := theOne.state`、`dong := theOne.dong`、`origin := theOne.origin`、`origin_alive := theOne.alive` 是 `theOne` 的投影，不是新增公理。
- `runFuel` 是结构递归总函数，可用于 theorem-level 执行证明；`run` 是 executable boundary。
- 文档中的「claim」「ledger」「DAG」是审计对象；只有 Lean theorem 才是机器闭合命题。
- 经验校准、阈值、正邪判定等 pending interface 不能冒称已由 Lean 证明为真。

## 构建后的硬要求

构建修复完成后，形式层应满足：

- live `sorry` 数量为 `0`。
- live `admit` 数量为 `0`。
- live `unsafe` 数量为 `0`。
- axiom 仍只允许 `kleene_recursion_axiom`。
- opaque 仍只允许 `theOne`。
- partial boundary 仍只允许 `YiState.run`，除非维护记录明确解释新增边界。

## `kleene_recursion_axiom` 的读法

`kleene_recursion_axiom` 不应被描述成「Lean 已证明的 Church-Turing 定理」。更准确的口径是：

- 它是当前 BaguaTuring 对角化路线的单一形式假设。
- 它已经收窄到 cuo-invariant decider 相关口径。
- `formal/SSBX/Foundation/Bagua/KleeneInternal.lean` 与 `formal/SSBX/notes/zero-axiom-roadmap.md` 记录了去公理化路线。
- 在相关 witness/compiler/interfaces 未闭合前，依赖它的无条件 Godel/Rice 结论都应标注为「在此 axiom 下」。

## `theOne` 的读法

`theOne` 是 opaque witness，不是 axiom。它的作用是保留「一」的抽象性：下游可以使用 `state`、`dong`、`origin` 与 `alive`，但不能展开其内部构造。

## `YiState.run` 的读法

`YiState.run` 是 partial，因为 BaguaTuring 允许真实非停机。若强行改成普通总函数，会把非停机伪装成某个最终状态。证明和审计应优先使用：

- `runFuel`：有 fuel 的总执行。
- 有限 `native_decide` 见证：用于具体小例。
- `run-boundary.md`：说明为何保留 `partial def run`。

## 生成索引

若 `../_generated/` 已生成，应优先引用其中的 trust-boundary、declaration、module index 来核对统计。本页维护语义口径，不手写替代机器统计。
