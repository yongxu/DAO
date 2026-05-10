# 义理到 Lean

本页说明如何从义理叙述寻找形式层对应。目标是降低误读：不是每个义理句子都应有 theorem，也不是每个 theorem 都能承载完整旧文论证。

## 三步定位

1. 先看义理页所属类别：核心框架、形式与证明、传统、现代对齐或八衍专题。
2. 再查 `../_generated/crossrefs.md`，寻找文档中已有 Lean path mention 与 symbol hit。
3. 最后查 `../_generated/lean-index.md` 和 `../_generated/claim-index.md`，确认对应模块与 claim 状态。

## 类别对应

| 义理类别 | 首查位置 | 读法 |
|---|---|---|
| 四级生成、根源、开闭 | `Foundation/Core`、`Roster` | 看构造与名册登记，不直接推断价值结论 |
| 六征、实虚史真、256 格 | `Foundation/Bagua`、`Foundation/Hierarchy`、`Text` | 看有限表、算子空间与 Cell128/Cell256 相关模块 (v3：原 Cell192 已删，由 Cell256 = Hexagram × V₄ Klein Shi 取代) |
| 算子代数 | `Foundation/Bagua`、`Text/WenyanOperators` | 区分 algebra 证明与文字算子登记 |
| 文道一也、自释 | `Foundation/Wen` | 区分解释器、parser、quine 路线和自然语言主张 |
| 对齐、共同体、失败模式 | `Foundation/Core`、`Foundation/Wen`、`Truth` | 多数是 formal interface 或案例层，不宜扩成经验定律 |
| 传统义理 | `Foundation/Wen/Kernel.lean` 及 notes | 多为映射与解释，需保留文献口径 |

## 可形式化与不可直接形式化

可优先形式化的对象：

- 明确的枚举、表格、算子签名、状态转移。
- 有固定输入输出的 parser、evaluator、ledger。
- 可写成 theorem 的闭合性质，例如完备性、保守性、可达性。

应留在解释层的对象：

- 历史来源的长段阐释。
- 价值判断的应用语境。
- 经验校准、阈值选择和现实政策判断。
- 仍在 pending interface 中的协议。

## 写法约束

义理页映射到 Lean 时，建议使用以下句式：

- 「形式层登记为……」用于名册、算子、字形。
- 「Lean 已检查……」只用于 theorem 或 machineChecked claim。
- 「当前由 ledger 承接……」用于 axiomBacked 或 ledgerDependent claim。
- 「该部分仍是 pending interface……」用于经验、阈值、校准与外部数据。

避免使用「已经证明全部」「彻底解决」「无条件推出」等口径，除非生成索引和 Lean 文件都能支持。

## 维护入口

- 义理导航：`../20_theory_义理/README.md`
- 生成索引：`../_generated/`
- claim 状态：`claim-status.md`
- 旧文迁移：`old-to-new.md`
