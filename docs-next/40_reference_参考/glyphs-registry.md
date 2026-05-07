# 字元与名册

本页说明字元、名册和 pending interface 的读法。完整统计和当前项以 `../_generated/registry-index.md` 为准。

## 来源

| 来源 | 用途 |
|---|---|
| `formal/SSBX/Roster.lean` | 概念名册与 kind |
| `formal/SSBX/Text/Glyph.lean` | 字形与 glyph 结构 |
| `formal/SSBX/Foundation/Core/AtomDerivation.lean` | atom derivation 说明 |
| `formal/SSBX/Foundation/Core/MissingGlyphs.lean` | 缺字补入与归根 |
| `formal/SSBX/notes/atom-naming.md` | 单字命名说明 |
| `formal/SSBX/notes/MissingGlyphRootReport.md` | 缺字归根记录 |
| `../_generated/registry-index.md` | 当前名册分类和 pending 列表 |

## Kind 读法

| Kind | 读法 |
|---|---|
| `primitive` | 基础项，作为下游生成的起点 |
| `atom` | 字元或核心登记项 |
| `generated` | 由根或构造路径生成的项 |
| `recursive` | 具有递归语义或自指结构的项 |
| `pending` | 名册预留接口，尚未闭合为形式事实 |

## Pending interface

pending 项是有名的待落地接口，不是错误，也不是已证明结论。文档中出现 pending 时，应写清：

- 它解决哪个外部或经验问题。
- 当前是否有模型、ledger 或旧文来源。
- 缺少的是数据、协议、证明、实现还是校准。
- 它不应被图示或摘要升级为 machineChecked。

## 字形与语义

glyph 层解决「如何登记一个字」和「它如何归入名册」。语义层解决「这个字在体系中怎样被使用」。同一个汉字可能在不同表、不同读法、不同算子组中出现，不能仅凭字面合并。

## 与生成索引的关系

`../_generated/registry-index.md` 给出当前分类和 pending/recursive 摘要。本页不重复数量。若人工叙述与生成索引冲突，先查 `Roster.lean` 和 `Glyph.lean`，再改人工文档。
