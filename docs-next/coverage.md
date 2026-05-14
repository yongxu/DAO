# 覆盖清单

> 状态：v3 定本 (2026-05-11) — Cell256 / V₄ Shi / 严格 uniform R₀..R₈

本页说明 `docs-next/` 计划覆盖哪些旧文档区，以及当前对应位置。它不是生成索引；生成索引见 `_generated/markdown-index.md` 与 `_generated/sources.json`。

## 当前覆盖区

| 旧区 | 新区 | 状态 |
|---|---|---|
| 根 README / formal README / English README | `README.md`、`overview.en.md`、`10_formal_形式/` | 已建立 staging 入口（v3 升级） |
| `formal/SSBX/**/*.lean` | `_generated/lean-index.*`、`10_formal_形式/` | 已索引，专题页继续扩充 |
| `formal/SSBX/Truth/ClaimLedger.lean` | `_generated/claim-index.*`、`30_crosswalk_互证/claim-status.md` | claim 状态集中化 |
| `formal/SSBX/Roster.lean` | `_generated/registry-index.*`、`40_reference_参考/glyphs-registry.md` | 名册集中化 |
| `formal/SSBX/Text/WenyanOperators.lean`、`wenyan-operators.md` | `_generated/operator-index.*`、`40_reference_参考/operators.md` | 算子集中化 |
| `formal/SSBX/diagrams/` | `_generated/diagram-index.*`、`30_crosswalk_互证/diagrams.md` | 图谱集中化 |
| `义理/` | `20_theory_义理/` | 按主题重索引（v3: core-framework.md 升级至 R₀..R₈） |
| `六表_实虚史真/` | `40_reference_参考/six-tables.md` | 作为参考资料 |
| `史料/` | `archive-pointers.md`、`40_reference_参考/historical-sources.md` | frozen archive |
| `史/docs-next-v2/` | `archive-pointers.md` | v2 (Cell192 / 旧 R₁..R₆ 编号) frozen 副本 |
| `ziwen-spec.md` | `40_reference_参考/ziwen-language.md` | 语言规范入口 |
| `web/build-data.mjs` | 暂不替换；后续可消费 `_generated/web-data.js` | 本阶段不切换 |

## v2 → v3 路由变更 (2026-05-10/11)

| 旧路径 | 新路径 / 状态 |
|---|---|
| `docs-next/10_formal_形式/cell192-grid.md` | **moved** → [`史/docs-next-v2/cell192-grid_Z3-Shi_旧版.md`](../史/docs-next-v2/cell192-grid_Z3-Shi_旧版.md) — 替代为 `docs-next/10_formal_形式/cell256-grid.md`（创建中，64 × 4 + 因/果 标注） |
| `docs-next/10_formal_形式/yi-RO-hierarchy.md` (v1, 旧 R₁..R₆ 编号) | **moved** → [`史/docs-next-v2/yi-RO-hierarchy_v1_旧R1-R6编号.md`](../史/docs-next-v2/yi-RO-hierarchy_v1_旧R1-R6编号.md) — 替代为 [`yi-RO-hierarchy.md`](10_formal_形式/yi-RO-hierarchy.md)（原 -v2.md 提为正本，R₀..R₈ uniform） |
| `表六_192格全表.md` | **renamed** → `表六_256格全表.md` (64 × 4 + 因/果 标注) |
| `formal/SSBX/Foundation/Atlas/Yi/Classical/Bagua-cluster/Cell192.lean` | **deleted** (commit `8e4406e`) — 替代为 `Cell256.lean` + `Cell128.lean` |
| `formal/SSBX/Foundation/Atlas/Yi/Classical/Bagua-cluster/Cell192Stratify.lean` | **replaced** by `Cell256Stratify.lean` (R₀..R₈ + R8_complete) |
| (无) → `Foundation/Hierarchy/RHierarchy.lean` 与 `R0_Taiji.lean` .. `R8_GuoHex.lean` | **new** (commit `1c76a55`, Phase C) |
| (无) → `Foundation/Hierarchy/R5_Wuyao.lean`、`LiftProject.lean`、`Operators/Atomic.lean`、`Operators/V4Outer.lean` | **new** (commit `7de5064`, Phase A–F) |
| (无) → `Foundation/Notation/OXNotation.lean` | **new** (`OX["xxxxxxxx"]` 8-char macro) |

详见 [`30_crosswalk_互证/old-to-new.md`](30_crosswalk_互证/old-to-new.md) 之 **Cell192 → Cell256 transition (2026-05-10/11)** 节。

## 判断完成的标准

- 读者能从 `00_start/` 选择路径（含 [`final-theory.md`](00_start/final-theory.md) v3 速览）。
- 形式读者能定位模块、claim、trust boundary（[`yi-RO-hierarchy.md`](10_formal_形式/yi-RO-hierarchy.md) 是 v3 canonical）。
- 义理读者能从旧 A-Z 与八衍进入新分类（[`core-framework.md`](20_theory_义理/core-framework.md) 已升级 R₀..R₈）。
- 维护者能运行生成与检查命令。
- 史料只作为来源和去向，不再混入当前规范；`史/docs-next-v2/` 同步 frozen。
