# 覆盖清单

本页说明 `docs-next/` 计划覆盖哪些旧文档区，以及当前对应位置。它不是生成索引；生成索引见 `_generated/markdown-index.md` 与 `_generated/sources.json`。

## 当前覆盖区

| 旧区 | 新区 | 状态 |
|---|---|---|
| 根 README / formal README / English README | `README.md`、`overview.en.md`、`10_formal_形式/` | 已建立 staging 入口 |
| `formal/SSBX/**/*.lean` | `_generated/lean-index.*`、`10_formal_形式/` | 已索引，专题页继续扩充 |
| `formal/SSBX/Truth/ClaimLedger.lean` | `_generated/claim-index.*`、`30_crosswalk_互证/claim-status.md` | claim 状态集中化 |
| `formal/SSBX/Roster.lean` | `_generated/registry-index.*`、`40_reference_参考/glyphs-registry.md` | 名册集中化 |
| `formal/SSBX/Text/WenyanOperators.lean`、`wenyan-operators.md` | `_generated/operator-index.*`、`40_reference_参考/operators.md` | 算子集中化 |
| `formal/SSBX/diagrams/` | `_generated/diagram-index.*`、`30_crosswalk_互证/diagrams.md` | 图谱集中化 |
| `义理/` | `20_theory_义理/` | 按主题重索引，不复制长文 |
| `六表_实虚史真/` | `40_reference_参考/six-tables.md` | 作为参考资料 |
| `史料/` | `archive-pointers.md`、`40_reference_参考/historical-sources.md` | frozen archive |
| `ziwen-spec.md` | `40_reference_参考/ziwen-language.md` | 语言规范入口 |
| `web/build-data.mjs` | 暂不替换；后续可消费 `_generated/web-data.js` | 本阶段不切换 |

## 判断完成的标准

- 读者能从 `00_start/` 选择路径。
- 形式读者能定位模块、claim、trust boundary。
- 义理读者能从旧 A-Z 与八衍进入新分类。
- 维护者能运行生成与检查命令。
- 史料只作为来源和去向，不再混入当前规范。
