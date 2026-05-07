# 归档指针

本页记录 docs-next 对旧目录的处理方式：义理重索引，史料冻结，参考区只给入口。

## 目录关系

| 旧目录 | 新位置 | 处理方式 |
|---|---|---|
| `义理/` | `20_theory_义理/` | 按类别重建索引与阅读路径，不复制长文 |
| `史料/` | `40_reference_参考/historical-sources.md` | frozen，仅保留指针 |
| `六表_实虚史真/` | 参考区与核心框架页引用 | 作为表格资料，不并入义理正文 |
| 自动生成资料 | `_generated/` | 作为文件、术语、Lean 声明的核对来源 |

## 史料状态

`史料/` 是历史快照。它记录早期版本、迁移过程和被取代的表达，不承担当前规范叙述。当前叙述应落在 docs-next、formal 与生成索引中。

## 查找路径

1. 查义理主题：先看 [20_theory_义理/README.md](20_theory_义理/README.md)。
2. 查史料原文：看 [40_reference_参考/historical-sources.md](40_reference_参考/historical-sources.md)，再回根目录 `史料/`。
3. 查机器事实：看 `_generated/` 中的文件索引、术语索引、Lean 声明索引。

## 维护约束

- 不把旧史料复制进 docs-next。
- 不把未验证的义理解释写成 Lean 已证事实。
- 不在归档指针页追求完备引用；完备性由 `_generated/` 承担。
