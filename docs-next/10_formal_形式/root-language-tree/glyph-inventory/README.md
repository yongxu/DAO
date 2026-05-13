# Glyph Inventory — R5..R8 审名字表

> 状态：审名 v0.1 (2026-05-13)。
> 作用：把 `layers/R5.md`..`layers/R8.md` 中的公开字词单独摊开，审的是“字”，不是只审生成 grammar。
> 边界：这些仍是 surface / reader names；formal truth 仍在 `(Z/2)^n` carrier、OX mask 与 Lean theorem 中。
> 可读性审计见 [readability-audit.md](readability-audit.md)。
> R5 operator 逐项审名见 [R5-operator-audit.md](R5-operator-audit.md)。

| layer | inventory | interface rows | 口径 |
|---|---:|---:|---|
| [R5](R5.md) | 64 | 32 cell + 32 operator | 32 个古字/文法 alias 作 cell 默认入口；operator 用 mask translation，能准确成词者收为 reader alias |
| [R6](R6.md) | 128 | 64 cell + 64 operator | 64 个六十四卦名；operator 为 6 位 XOR mask 字组 |
| [R7](R7.md) | 256 | 128 cell + 128 operator | 64 卦 × `無跡/有跡`；operator 加 `印` |
| [R8](R8.md) | 512 | 256 cell + 256 operator | `道/未/已/今 · 64卦`；operator 加 `印/投` |

读表原则：

- `推荐字词` 是当前公开入口；古字/古文语法可读者优先。`无歧义读法` 给 parser / reader fallback。
- `字源状态` 明确区分既有卦名、实字 alias、透明组合、Shi 位字组合、XOR 算子字组。
- 多原子 operator 默认用 `+` 分隔；若有准确汉语成词且不混淆 mask，可收为 reader alias，如 R5 `變化`、`改變`。
- 没有把透明组合伪装成古已有定名；后续若找到更准确单字，可替换 `推荐字词`，formal 列不变。
