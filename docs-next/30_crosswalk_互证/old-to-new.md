# 旧文到新版

本页给旧 `义理/`、`史料/` 与新版 docs-next 的迁移读法。旧文保留为来源和历史论证，新版负责入口、状态和互证。

## 总原则

- 旧文不在 docs-next 中重写成长篇合订。
- 新版优先说明「去哪里读」「当前强度如何」「是否有 Lean 或生成索引支撑」。
- 旧文中的宏大论断进入新版时，必须降到可审计状态：theorem、claim、model、registry、pending 或 archive。
- 路径存在性和统计以 `../_generated/markdown-index.md`、`../_generated/crossrefs.md` 为准。

## 旧义理入口

| 旧文范围 | 新版入口 | 备注 |
|---|---|---|
| `义理/A`–`G` | `../20_theory_义理/core-framework.md` | 核心框架与算子骨架 |
| `义理/H`–`M` | `../20_theory_义理/formal-and-proof.md` | 证明报告、Cell192、自释路线 |
| `义理/N`、`P`、`Q`、`S`、`E` | `../20_theory_义理/traditions.md` | 传统映射，不改写为史学定论 |
| `义理/O`、`R`、`U`–`Z` | `../20_theory_义理/modern-and-alignment.md` | 对齐、政治、经济、失败模式 |
| 八衍专题文 | `../20_theory_义理/extensions.md` | 数、推、测、形、类、动、识、象等专题 |
| `义理/算子别名总表.md` | `../40_reference_参考/operators.md` | 人工别名表须对照生成算子索引 |

## 旧史料入口

| 史料范围 | 新版入口 | 备注 |
|---|---|---|
| `史料/生生不息论_三本文完整版/` | `../40_reference_参考/historical-sources.md` | frozen snapshot |
| `史料/真理/daoli-v12-*.md` | `../40_reference_参考/historical-sources.md` | 早期 truth framework |
| v11/v12 单体稿 | `../40_reference_参考/historical-sources.md` | 版本追踪 |
| v14 骨架稿 | `../50_maintenance/archive-policy.md` | 归档与后续维护口径 |

## 迁移时的降级规则

| 旧文表述 | 新版处理 |
|---|---|
| 「证明」 | 查 Lean；无 theorem 时写「论证」或「ledger 承接」 |
| 「模型验证」 | 查是否 modelComputed；否则写「模型接口」 |
| 「完备」 | 区分 registry 完备、表完备、语义完备和哲学完备 |
| 「必然」 | 查是否 theorem；否则写「在该框架内主张」 |
| 「对应」 | 写清是文本映射、算子映射、claim 映射还是形式同构 |

## 不迁移内容

- 旧文的修辞段落不搬入新版。
- 史料目录不做现代化改写。
- 未落地的经验接口不写成 Lean 事实。
- 生成文件内容不复制到人工页；只引用 `../_generated/`。
