# 模块地图

模块地图用于把读者从主题带到 Lean 文件。完整列表见 [../_generated/lean-index.md](../_generated/lean-index.md)；本页只描述模块簇的职责。

## 顶层入口

- `formal/SSBX.lean` 是聚合入口。
- `formal/SSBX/Core.lean` 给出基础枚举、三值、开闭与若干共用结构。
- `formal/SSBX/Roster.lean` 维护字根、生成项、primitive、recursive 与 pending 名册。

这些文件是阅读全局结构的入口，但不应把「被导入」误读成「所有 claim 已证明」。

## 主要簇

| 簇 | 职责 | 读法 |
|---|---|---|
| `Foundation/Core` | 单根、构造、价值、注意、人对齐 | 看结构性 theorem 与 DAG 口径。 |
| `Foundation/Wen` | 文、文言微核、自释、自举、quine 路线 | 看语法、求值、封装 witness 与路线层次。 |
| `Foundation/Jian` | 间、本体、模式核、STLC、易桥 | 看「关系间隔」如何进入形式对象。 |
| `Foundation/Yi` | 易核心与易数据结构 | 看八卦/卦象之前的易层基础。 |
| `Foundation/Bagua` | 八卦代数、Cell192、BaguaTuring、不完备 | 看计算边界与 `kleene_recursion_axiom`。 |
| `Foundation/Eight` | 八衍：动理、逻辑、数算、统计等 | 看专题中层接口，不读作经验充分性。 |
| `Foundation/Modern` | 现代数学、概率、逻辑、物理、神经 | 看形式桥接与局部定理。 |
| `Text` | glyph、义位、算子、覆盖性 | 看文字账本与算子表完备性。 |
| `Truth` | claim ledger、语义、体系内真理 | 看 claim status，而不是只看名称。 |
| `Model` | adequacy 与 concrete ledger | 看模型充分性如何被表述。 |
| `Pending` | 经验接口与示例 | 看未闭合边界。 |

## 索引优先

人工模块图会过期。核对时优先使用：

- [../_generated/lean-index.md](../_generated/lean-index.md)：模块、导入、声明、行数。
- [../_generated/crossrefs.md](../_generated/crossrefs.md)：文档与 Lean 路径/符号互证。
- [../_generated/registry-index.md](../_generated/registry-index.md)：名册 kind 与 pending/recursive 项。
- [../_generated/claim-index.md](../_generated/claim-index.md)：claim 状态。

## 阅读原则

先从模块簇判断「这页在证明什么」，再看 theorem 名称和依赖。不要只凭文件名推断强度：例如 truth 相关文件可以记录 ledgerDependent claim，Bagua 不完备路线仍依赖唯一 axiom，Pending 文件明确是接口边界。
