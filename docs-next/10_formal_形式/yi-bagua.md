# Yi 与 Bagua

Yi/Bagua 层把易、八卦、Cell192、受控计算与不完备边界放到同一阅读路径。这里也是当前唯一 axiom 与唯一 partial boundary 所在区域。

## Yi

`Foundation/Yi/Yi.lean` 与 `YiCore.lean` 提供易层基础对象。它们位于八卦和更高义理桥接之前，适合先读数据结构和基本关系。

## Bagua algebra

`BaguaAlgebra.lean`、`BaguaWenSpec.lean`、`Cell192.lean` 等模块处理八卦代数、受控文规范与 192 cell 结构。读法是形式结构与索引空间，不是把每个传统解释都当作 theorem。

## BaguaTuring

`BaguaTuring.lean` 给出计算模型。这里有当前唯一顶层 partial boundary：`YiState.run`。

正确读法：

- `runFuel` 是有 fuel 的总执行，可进入 theorem 证明。
- `run` 表示真实无界执行，可能不返回。
- partial 边界不是漏洞，而是非停机语义的诚实表达。

## Kleene/Rice/GodelLi

`KleeneInternal.lean`、`CuoInvariance.lean`、`GodelLi.lean` 等模块组织不完备与对角化路线。当前唯一显式 axiom 是 `kleene_recursion_axiom`，用于 cuo-restricted 相关结论。

写法应是：

- 「在 `kleene_recursion_axiom` 下」。
- 「当前路线尚有去公理化 roadmap」。
- 「不把它说成 Lean 已内部证明的 Church-Turing 定理」。

## 核验

信任边界查 [../_generated/trust-boundary.md](../_generated/trust-boundary.md)。模块清单查 [../_generated/lean-index.md](../_generated/lean-index.md)。义理互证可看旧文 `义理/Cell192_BaguaTuring_理层全集与不完备.md`、`义理/J_理之不完备_哥德尔在192.md` 与 `义理/M_证明报告_192_理之不完备.md`，但最终强度以 Lean 和 claim ledger 为准。
