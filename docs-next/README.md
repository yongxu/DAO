# 生生不息新文档集 — v3 (2026-05-11) — Cell256 / V₄ Shi / 严格-uniform R₀..R₈

> 状态：v3 定本 (2026-05-11)

本目录是新的文档集暂存区。旧文档暂不删除；待本目录稳定后，再整体替换根 README、`formal/SSBX/README.md`、`义理/README.md` 与 web 索引入口。

## v3 速览入口

- [**v3 最终理论速览**](00_start/final-theory.md) — Cell256 / V₄ Klein Shi / 严格 uniform R₀..R₈ 一页地图（推荐第一读）。
- [**形式定本: yi-RO-hierarchy.md**](10_formal_形式/yi-RO-hierarchy.md) — R₀..R₈ definitive doctrine（v3 canonical theory）。
- [Theorems A–K (yi-calculus-theorem.md)](10_formal_形式/yi-calculus-theorem.md) — R₁..R₈ Lean-anchored 定理链。
- [meta-framework (yi-as-meta-framework.md)](10_formal_形式/yi-as-meta-framework.md) — self-description GUT 哲学层。

## 三条阅读路径

- [起步](00_start/README.md)：快速选择形式、义理或维护路径。
- [形式层](10_formal_形式/README.md)：从 Lean 代码、构建、信任边界、模块索引与 claim ledger 进入。
- [义理层](20_theory_义理/README.md)：从 R₀..R₈ 阶梯、六征体系、传统/现代论证与对齐主题进入。

英文读者先看 [overview.en.md](overview.en.md)。英文只维护总览，不作为第二套规范。

## 当前机器口径

- `lake build SSBX` 通过：**3656 jobs**（v3 定本，commit `1c76a55`），0 sorry, 0 warning。
- `R8_complete` axiom audit = `{propext, native_decide}`；**0 项目自定义 axiom**（`kleene_recursion_axiom` 仍存在但不在 R-hierarchy 闭合所依赖）。
- live trust boundary 以 [trust-boundary](./_generated/trust-boundary.md) 为准。
- claim 状态以 [claim-index](./_generated/claim-index.md) 为准。
- 模块与声明索引以 [lean-index](./_generated/lean-index.md) 为准。

## 最近变更 (Latest)

| 日期 | Commit | 内容 |
|---|---|---|
| 2026-05-11 | `1c76a55` | **Phase C**: 9 个 R-index 命名 alias 文件 + `RHierarchy.lean` umbrella；3656 jobs build 干净 |
| 2026-05-10 | `8e4406e` | **Phase F.6 + G + B.1**: 删 `Cell192.lean`（legacy 3-state Shi 完全删除）；4 份文档与 Lean 路径 sync；YinBit dedup |
| 2026-05-10 | `0003224` | **Phase F.x.5**: 完成 Modern/* 级联升级 (~80 文件 case-split 全 4 例) |
| 2026-05-10 | `7de5064` | **Phase A–F 教义对齐**: Cell192 → Cell256；V₄ Klein Shi 取代 Z/3 cyclic Shi；Algebraic spine on Cell128/Cell256；Cayley `ι/ε`；XOR-mask 印/投 |

详见 [`30_crosswalk_互证/old-to-new.md`](30_crosswalk_互证/old-to-new.md) 之 **Cell192 → Cell256 transition** 节。

## 读法

1. 先看 [v3 最终理论速览](00_start/final-theory.md) 拿到全局地图。
2. 然后看 [形式层信任边界](10_formal_形式/trust-boundaries.md)，确认哪些是 Lean theorem、ledger claim、模型计算或外推。
3. 再看 [义理索引](20_theory_义理/README.md)，按主题进入旧 `义理/` 的重排版本。
4. 查证时回到 [_generated](./_generated/)，不要从散文段落读取数量、状态或构建事实。
5. 需要追溯旧稿时，看 [archive-pointers.md](archive-pointers.md)；`史料/` 与 `史/docs-next-v2/`（v2 frozen 副本）保持 frozen。

## 覆盖面

本目录不是四个顶层文件；主体在各分区内：

- `00_start/`：读者路径与范围。**[final-theory.md](00_start/final-theory.md)** 是 v3 一页速览。
- `10_formal_形式/`：形式化、模块簇、信任边界、构建。**[yi-RO-hierarchy.md](10_formal_形式/yi-RO-hierarchy.md)** 是 v3 canonical theory。
- `20_theory_义理/`：旧义理文档的分类重排（**[core-framework.md](20_theory_义理/core-framework.md)** 已升级至 R₀..R₈）。
- `30_crosswalk_互证/`：Lean 与义理互证；**[old-to-new.md](30_crosswalk_互证/old-to-new.md)** 含 Cell192→Cell256 完整迁移记录。
- `40_reference_参考/`：算子、字根、六表、字文与术语。
- `50_maintenance/`：生成、检查、发布与归档策略。
- `_generated/`：脚本生成的事实索引。

## 维护原则

- 一个事实只保留一个权威来源：Lean/ledger 为形式事实，生成索引为可定位目录，人工文档只做解释和路径。
- 不在 README 里堆长表；长表进入 `_generated` 或 `40_reference_参考/`。
- 不把 `史料/` 改写成现规范；只记录它们被哪里取代。
- v3 之 ontology（Cell256 / V₄ Shi / R₀..R₈ uniform）以 [`yi-RO-hierarchy.md`](10_formal_形式/yi-RO-hierarchy.md) 为唯一定本；其它文档应链接而非复述其结构定义。
