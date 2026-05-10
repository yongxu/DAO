# Claim 状态读法

> 状态：v3 定本 (2026-05-11) — Cell256 / V₄ Shi / 严格 uniform R₀..R₈

`ClaimLedger` 把文本 claim、模型结果和形式证明放入同一张账本。它是审计工具，不是把所有 claim 自动升级为 theorem 的机制。

## 状态总览

最新状态以 `../_generated/claim-index.md` 为准。本页只解释读法。

| 状态 | 含义 | 文档写法 |
|---|---|---|
| `machineChecked` | Lean 已检查对应 theorem 或 registry 性质 | 可写「形式层已闭合」 |
| `modelComputed` | 由具体模型或案例计算给出 | 可写「模型案例给出」 |
| `ledgerDependent` | 由 ledger、文本来源或公理映射承接 | 应写「账本承接」 |

## Kind 与状态

| Kind | 常见状态 | 说明 |
|---|---|---|
| `definition` | `ledgerDependent` | 定义来自旧文或 ledger，未必是 theorem |
| `proved` | `machineChecked` | 已有 Lean theorem 支撑 |
| `registry` | `machineChecked` | 表或名册完备性由 Lean 检查 |
| `modelInterface` | `ledgerDependent` | 接口存在，但经验充分性未闭合 |
| `axiomBacked` | `ledgerDependent` | 依赖明示公理或 claim ledger |
| `caseResult` | `modelComputed` 或 `ledgerDependent` | 具体案例可能已算出，也可能仍依赖解释 |

## 审读规则

- 读 claim 前先看 status，不只看 label。
- label 是人读标题，不是证明强度。
- source 是来源提示，不等于完整证明。
- claim 若依赖 pending interface，必须保留 pending 口径。
- 同一主题可同时有 machineChecked 子命题和 ledgerDependent 总 claim。

## 与信任边界的关系

`axiomBacked` 不一定表示 Lean 里新增 axiom。它可能表示 claim ledger 依赖旧文、公理账本或外部充分性假设。真正的形式信任边界以 `../_generated/trust-boundary.md` 和 `../10_formal_形式/trust-boundaries.md` 为准。

当前必须特别标明：

- `kleene_recursion_axiom` 相关结论依赖该 axiom。
- `theOne` 是 opaque witness，不能当作可展开构造。
- `YiState.run` 是 partial execution boundary，证明层优先用 fuel 版本。

## Cell192 → Cell256 迁移对 claim 状态的影响 (2026-05-10/11)

V₄ Shi / Cell256 升级后，与 Cell192 cardinality 直接绑定的 claim 已被替换或重号；本页的状态分类（`machineChecked` / `modelComputed` / `ledgerDependent`）与 Kind taxonomy 不依赖具体 cardinality，因此本页本身**不需要按 cell-cardinality 改写**。需要留意的具体迁移：

- `Cell192OperatorComplete` → `Cell256OperatorComplete`（Self-description witness，仍 `machineChecked`）。
- 旧 `R6_complete` / `R7_complete` bundle → **`R8_complete`** in `Cell256Stratify.lean`，axiom audit = `{propext, native_decide}`，**0 项目自定义 axiom**。
- `wen_constructive_coverage_192_371` 等下游 cascade 引理保留旧名（避免重命名传播），但 cardinality 已升级到 `256 × 371 = 94976`（详见 `../30_crosswalk_互证/old-to-new.md` Cell192→Cell256 节）。

具体 claim 列表与状态以 `../_generated/claim-index.md` 为准。

## 更新检查

改动 `ClaimLedger.lean` 或相关 theorem 后，应重新生成 `../_generated/claim-index.md`。人工页只改解释口径，不手写替代统计。
