# Truth 与 Model

Truth/Model 层管理 claim、语义充分性与体系内真理口径。它的核心不是把所有 claim 一次性证明，而是明确每条 claim 的状态。

## Claim ledger

claim 状态以 [../_generated/claim-index.md](../_generated/claim-index.md) 为准。常见状态包括：

- `machineChecked`：已有 Lean 层机器核验。
- `modelComputed`：由模型或 concrete ledger 给出计算结果。
- `ledgerDependent`：依赖账本、公理映射、接口或外部校准。

写文档时必须保留状态，不应只摘 claim 名称。

## Truth 模块

`Truth.Basic` 给出基础真理结构；`Truth.Semantics` 组织语义；`Truth.ClaimLedger` 维护 claim 条目；`Truth.Adequacy` 与 `Truth.Absolute` 给出充足性和体系内绝对真理口径；`Truth.SelfDescription` 处理自描述。

这些文件的定理可以按 Lean theorem 使用，但 ledgerDependent claim 仍是 ledgerDependent。

## Model 模块

`Model.Adequacy` 与 `Model.ConcreteLedger` 提供模型层材料。模型计算能给出案例结果或充足性桥，但不会自动把经验接口变成无条件真理。

因此推荐写法是：

- 「模型计算得到某案例结果」。
- 「语义充分性 claim 已 machineChecked」。
- 「某充分性公理仍是 ledgerDependent」。

不推荐写成：

- 「Lean 已证明所有推荐系统判断正确」。
- 「体系内绝对真理已经无前提闭合」。

## 体系内真理

体系内真理应读成在当前形式系统、ledger、模型与信任边界下的陈述。若 claim 依赖 `kleene_recursion_axiom`、adequacy axiom 或 pending interface，应在句子中明示。

## 与信任边界关系

Truth/Model 层不新增当前扫描中的 axiom、opaque 或 partial def。当前 live 边界仍以 [../_generated/trust-boundary.md](../_generated/trust-boundary.md) 为准：`kleene_recursion_axiom`、`theOne`、`YiState.run`。
