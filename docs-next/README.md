# 生生不息新文档集 — v0.6 (2026-05-15) — R-Family Tower Algebra

> 状态：v0.6 定本 (2026-05-15) — R-Family `R_N := F_2^N` tower; R₀..R₈ root layers; R₄ + R₈ dual centers; semantic naming (Yi / Pauli / Boolean / GF(256)) demoted to **Atlas** application layer.

本目录是新的文档集暂存区。旧文档暂不删除；待本目录稳定后，再整体替换根 README、`formal/SSBX/README.md`、`义理/README.md` 与 web 索引入口。

## v0.6 canonical doctrine (必读)

- [**wen-algebra.md**](10_formal_形式/wen-algebra.md) v0.6 — Tower-level algebra + Lean compiler/interpreter foundation. R-Family closure, Hom representation as `Mat(R_4)`, three bilinear layers (dot / σ / q+Arf), 7 phantom modes, judgment layers (Information / Attractor / Behavior).
- [**v4-foundation.md**](10_formal_形式/v4-foundation.md) v0.5 — R₀–R₈ root-layer specs (each layer's structure, Aut, subgroups, bilinear). Language-independent: 「字符语义全部冻结，只看结构」.
- [**r4.md**](10_formal_形式/r4.md) — R₄ minimum complete unit专题 (rank stratification, GL(2,F₂) embedding, Aut = A_8, End(R_2) = R_4, Hom representation cell type).
- [**r8.md**](10_formal_形式/r8.md) — R₈ ceiling 专题 (spacetime, causality, information/attractor/behavior judgment, squaring tower beyond R_8, GF(256)).

## v3.0 historical (superseded)

- [final-theory.md](00_start/final-theory.md) — v3.0 one-page map (Cell256-centered, Yi-named atoms)
- [yi-RO-hierarchy.md](10_formal_形式/yi-RO-hierarchy.md) — v3.0 R-uniform strict (Z/2)ⁿ R₀..R₈ doctrine
- [yi-calculus-theorem.md](10_formal_形式/yi-calculus-theorem.md) — Theorems A–K (survive intact; positioned as Yi-Atlas theorems now)
- [yi-as-meta-framework.md](10_formal_形式/yi-as-meta-framework.md) — meta-categorical framework (Yi reframed as one Atlas binding among many)

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

| 日期 | 内容 |
|---|---|
| 2026-05-15 | **v0.6 canonical doctrine**: `wen-algebra.md` v0.6 + `v4-foundation.md` v0.5 + `r4.md` + `r8.md` 入档. 弃 𝕏/𝕐/矩/象/Frame 等历史层名; 改用 R-Family `R_N := F_2^N` parametric tower. R₄/R₈ 双中心. 语义命名（Yi/Pauli/Boolean）下放至 Atlas application layer. Lean 4 为唯一形式语言 (Clojure 弃用). |
| 2026-05-14 | v0.4 Xiang module shipped (`762a618`); since superseded by v0.6 R-Family. |
| 2026-05-11 | v3.0 `1c76a55`: 9 个 R-index 命名 alias 文件 + `RHierarchy.lean` umbrella；3656 jobs build 干净. (v3.0 superseded by v0.6.) |
| 2026-05-10 | v3.0 `7de5064`/`0003224`/`8e4406e`: Cell192 → Cell256 migration, V₄ Klein Shi, Modern/* upgrade, Cell192.lean deletion. (v3.0 superseded by v0.6.) |

详见 [`30_crosswalk_互证/old-to-new.md`](30_crosswalk_互证/old-to-new.md) 之 **Cell192 → Cell256 transition** 节。

## 读法

1. 先看 [v3 最终理论速览](00_start/final-theory.md) 拿到全局地图。
2. 然后看 [形式层信任边界](10_formal_形式/trust-boundaries.md)，确认哪些是 Lean theorem、ledger claim、模型计算或外推。
3. 再看 [义理索引](20_theory_义理/README.md)，按主题进入旧 `义理/` 的重排版本。
4. 查证时回到 [_generated](./_generated/)，不要从散文段落读取数量、状态或构建事实。
5. 需要追溯旧稿时，看 [archive-pointers.md](archive-pointers.md)；`史料/` 与 `史/docs-next-v2/`（v2 frozen 副本）保持 frozen。

## 覆盖面

本目录不是四个顶层文件；主体在各分区内：

- `00_start/`：读者路径与范围。[final-theory.md](00_start/final-theory.md) 是 v3.0 superseded 一页速览; v0.6 canonical 之一页速览在 [`wen-algebra.md`](10_formal_形式/wen-algebra.md) §0 + [`v4-foundation.md`](10_formal_形式/v4-foundation.md) §0–§1.
- `10_formal_形式/`：形式化、模块簇、信任边界、构建。**[`wen-algebra.md`](10_formal_形式/wen-algebra.md) v0.6** 是 canonical doctrine. 三 companion: `v4-foundation.md`, `r4.md`, `r8.md`.
- `20_theory_义理/`：旧义理文档的分类重排（**[core-framework.md](20_theory_义理/core-framework.md)** 已升级至 R₀..R₈）。
- `30_crosswalk_互证/`：Lean 与义理互证；**[old-to-new.md](30_crosswalk_互证/old-to-new.md)** 含 Cell192→Cell256 完整迁移记录。
- `40_reference_参考/`：算子、字根、六表、字文与术语。
- `50_maintenance/`：生成、检查、发布与归档策略。
- `_generated/`：脚本生成的事实索引。

## 维护原则

- 一个事实只保留一个权威来源：Lean/ledger 为形式事实，生成索引为可定位目录，人工文档只做解释和路径。
- 不在 README 里堆长表；长表进入 `_generated` 或 `40_reference_参考/`。
- 不把 `史料/` 改写成现规范；只记录它们被哪里取代。
- v0.6 之 ontology (R-Family `R_N := F_2^N`, R₀–R₈ root layers, R₄/R₈ 双中心, semantic naming demoted to Atlas) 以 [`wen-algebra.md`](10_formal_形式/wen-algebra.md) v0.6 + [`v4-foundation.md`](10_formal_形式/v4-foundation.md) v0.5 为唯一定本; 其它文档应链接而非复述其结构定义。
