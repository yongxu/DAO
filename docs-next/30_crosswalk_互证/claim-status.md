> 状态：v3 (2026-05-11) — claim 状态读法 + v3 当前 live claim 摘录。完整状态以 `../_generated/claim-index.md` 为准。

# Claim 状态读法

`ClaimLedger` 把文本 claim、模型结果和形式证明放入同一张账本。它是审计工具，不是把所有 claim 自动升级为 theorem 的机制。

## 状态总览

最新状态以 `../_generated/claim-index.md` 为准。本页只解释读法 + 列出 v3 当前关键 live claim。

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

## v3 当前关键 live claim（精选 7 条）

| # | claim | kind | status | 锚 |
|---|---|---|---|---|
| 1 | **Cell256 R₈ closure 收口**：基数 256 + R₀..R₈ strict-uniform + P/T/Y closure + (Z/2)⁸ 群作用 simply-transitive on `(qian, dao)` + BenZheng 投影 + 位置-算子树双射 + xuGua256 (序卦 256 cell 扩展) | `proved` (bundle) | `machineChecked` | `Cell256Stratify.lean § 7` `R8_complete` |
| 2 | **R8_complete axiom audit**：`#print axioms R8_complete` 仅含 Lean 核心 axioms `propext` 与 `native_decide`（无项目自定义 axiom 介入） | `proved` | `machineChecked`（审计已审） | `Cell256Stratify.lean § Axiom audit` |
| 3 | **Cell256 = (Z/2)⁸ Abelian 群** + **Cayley fusion 严格成立**（`ε ∘ ι = id`，`ι` 单射，`ι` 群同态） | `proved` | `machineChecked` | `Cell256.lean § 7` `cell256_phaseA_summary` + § 7.6 |
| 4 | **R₀..R₈ 8 对 lift/project 全 retract**（`proj ∘ lift = id`，faithful Rₙ ↪ R_{n+1}） | `proved` | `machineChecked` | `LiftProject.lean § 9` `liftProject_summary` |
| 5 | **印 / 投 = XOR-with-mask atomic 算子**：each involution；commute；`yin_mask ⊕ tou_mask = (qian, jin)` (V₄ central) | `proved` | `machineChecked` | `Cell256.lean § 8` + `Operators/Atomic.lean` `atomic_all_involutive` |
| 6 | **{id, cuo, zong, cuoZong} on Hexagram = V₄ Klein**（每元 involution、abelian、composite 关系全成立）；`hu` 不在 V₄，但其唯一不动点 = `{乾, 坤}` | `proved` | `machineChecked` | `Operators/V4Outer.lean § 7` `v4_outer_summary` |
| 7 | **0 sorry 跨已迁文件**（V₄ Shi 迁移过程中未引入 sorry；commits `7de5064`, `0003224`, `8e4406e` 之 lake build 全 3648/3648） | `registry` | `machineChecked`（构建侧） | `git log` + `lake build`；摘要见 `../_generated/lean-index.md` |

## v3 当前 live claim — pending（精选 1 条）

| # | claim | status | 备注 |
|---|---|---|---|
| 8 | **WenyanSelfInterp.lean base-256 dispatch program 完整 re-derivation** | `pending` | atomic encoding 已迁 Cell256（Phase F.1，commit `7de5064`），但 12-tag dispatch program 之 base-256 重导（hex 0..2 × 4 shi states）尚未完成。`metaInterpStepPc_branchShiEq_notTaken_*` 之 `Shi.dao` 新 ctor 覆盖完成；下游 quine 路线之 base-256 重写**未完成**。详 `WenyanSelfInterp.lean` 头部注释 + Phase F.1 注释。 |

## 审读规则

- 读 claim 前先看 status，不只看 label。
- label 是人读标题，不是证明强度。
- source 是来源提示，不等于完整证明。
- claim 若依赖 pending interface，必须保留 pending 口径。
- 同一主题可同时有 machineChecked 子命题和 ledgerDependent 总 claim。
- v3 之新 atomic / V₄ outer / R-hierarchy 算子 / 印 / 投 之 machineChecked 状态见上表 #1–#7；引用时以这些锚为准。

## 与信任边界的关系

`axiomBacked` 不一定表示 Lean 里新增 axiom。它可能表示 claim ledger 依赖旧文、公理账本或外部充分性假设。真正的形式信任边界以 `../_generated/trust-boundary.md` 和 `../10_formal_形式/trust-boundaries.md` 为准。

当前必须特别标明：

- `kleene_recursion_axiom` 相关结论依赖该 axiom（已拆为 4 件具名原子；详 `KleeneCarrier.lean`）。
- `theOne` 是 opaque witness，不能当作可展开构造。
- `YiState.run` 是 partial execution boundary，证明层优先用 fuel 版本。
- `R8_complete` 之依赖只含 Lean 核心 `propext + native_decide`，不引入项目 axiom — 这是 v3 算子系统之主基线。

## 更新检查

改动 `ClaimLedger.lean` 或相关 theorem 后，应重新生成 `../_generated/claim-index.md`。人工页只改解释口径，不手写替代统计。

## 形式锚

- [`formal/SSBX/Foundation/Bagua/Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) — `R8_complete` + axiom audit
- [`formal/SSBX/Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) — `cell256_phaseA_summary`
- [`formal/SSBX/Foundation/Bagua/Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) — `cell128_phaseA_summary`
- [`formal/SSBX/Foundation/Hierarchy/LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) — `liftProject_summary`
- [`formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) — `atomic_all_involutive`
- [`formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) — `v4_outer_summary`
- [`formal/SSBX/Foundation/Wen/WenyanSelfInterp.lean`](../../formal/SSBX/Foundation/Wen/WenyanSelfInterp.lean) — pending base-256 dispatch
