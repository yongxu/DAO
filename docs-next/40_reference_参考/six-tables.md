> 状态：v3 (2026-05-11) — 六表参考。表六已在 v3 由 192 格旧版（Z/3 Shi）替换为 256 格新版（V₄ Shi）；旧 192 表移入 `史/义理-pre-v3/`。新表 `表六_256格全表.md` 由并行 agent 在 `六表_实虚史真/` 中产出。

# 六表参考

六表位于根目录 `六表_实虚史真/`，是实、虚、史、真和（v3）256 格的人工表格入口。docs-next 只提供读法和指针。

## 表格入口

| 表 | 路径 | 读法 |
|---|---|---|
| 表一 | `六表_实虚史真/表一_六征本表.md` | 六征基础表 |
| 表二 | `六表_实虚史真/表二_史维三态.md` | 史维三态 |
| 表三 | `六表_实虚史真/表三_实虚modal三态.md` | 实虚 modal 三态 |
| 表四 | `六表_实虚史真/表四_真假认识三态.md` | 真假认识三态 |
| 表五 | `六表_实虚史真/表五_三轴27格.md` | 三轴 27 格 |
| **表六（v3）** | `六表_实虚史真/表六_256格全表.md`（forthcoming，并行 agent 产出） | **64 卦 × 4 时态 = 256 格全表**（V₄ Shi = `{道, 已, 今, 未}`） |
| 表六（旧 v2） | [`史/义理-pre-v3/表六_192格全表_旧Z3版.md`](../../史/义理-pre-v3/表六_192格全表_旧Z3版.md) | **已归档**（Z/3 Shi 是 v2 期之结构错误；不再作为读者入口） |

## 表六之 v3 重构（v2 → v3 迁移说明）

| 项目 | v2 旧表（已归档） | v3 新表（forthcoming） |
|---|---|---|
| 总格数 | 192 = 64 × 3 | **256 = 64 × 4** |
| Shi 维 | Z/3 cyclic（dao / cur / fin） | **V₄ Klein（道 / 已 / 今 / 未）** |
| Shi 之代数性质 | cyclic 群 ℤ/3 | abelian Klein-four V₄ = (Z/2)² |
| 中点 cell | `cur` | `今` = `Shi.jin` = (因=1, 果=1) = V₄ central element = PT |
| 终点 cell | `fin` | 拆为 `已` (1,0) 与 `未` (0,1) 二独立 axis |
| 道之地位 | 仅哲学 anchor | **first-class V₄ identity = R₈ origin = OX["oooooooo"]** |
| Lean 锚 | 旧 `Cell192.lean`（已删） | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) `Cell256.all`, `xuGua256` |

## 与形式层的关系

六表不是 Lean 生成文件。需要形式核对时，优先查：

- `../_generated/lean-index.md` 中的 `Foundation/Bagua` cluster。
- [`formal/SSBX/Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean)（256-cell carrier，`xuGua` 64-序列，`xuGua256` 待在 Cell256Stratify 中）。
- [`formal/SSBX/Foundation/Bagua/Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean)（`xuGua256` 256-cell 序列）。
- [`formal/SSBX/Foundation/Bagua/Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean)（中间层 R₇ Cell128）。
- [`formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean)。
- `formal/SSBX/notes/zhouyi-position-operator-report.md`。
- `../_generated/diagram-index.md` 中 Position Operator Graph（**v3 之 256 模式**）。

## 读法边界

- 表格可作为义理分类和审计导航。
- 表格本身不等于 Lean theorem。
- 256 格的覆盖口径要区分**表格覆盖**、**算子空间覆盖**和**证明覆盖**：
  - 表格覆盖：256 个 cell 全列出（`Cell256.all_length = 256`）。
  - 算子空间覆盖：8 个 atomic XOR generators + V₄ outer perm 之全 closure。
  - 证明覆盖：`R8_complete` bundle（`Cell256Stratify.lean`）—— 含基数、R-hierarchy、P/T/Y、群作用 simply-transitive、BenZheng 投影、位置-算子树双射、xuGua256 length + Nodup。
- 涉及不完备、可判定、对角化时，应回到 BaguaTuring 和 GodelLi 相关模块（已迁 Cell256）。

## 更新规则

若六表变动，应重新生成 docs-next 索引并检查：

- `../_generated/markdown-index.md` 是否收录新路径。
- `../_generated/crossrefs.md` 是否出现新的 Lean path mention 或 symbol hit。
- `../20_theory_义理/core-framework.md` 和 `../20_theory_义理/formal-and-proof.md` 是否需要调整摘要。
- 表六之 192 → 256 重写是否同步反映在 v3 doctrine 文档（[`yi-RO-hierarchy.md`](../10_formal_形式/yi-RO-hierarchy.md)、[`cell256-grid.md`](../10_formal_形式/cell256-grid.md)）。

## 形式锚

- [`formal/SSBX/Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) — `Cell256.all`, `xuGua` (64)
- [`formal/SSBX/Foundation/Bagua/Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) — `xuGua256` (256), `R8_complete`
- [`formal/SSBX/Foundation/Bagua/Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean)
- [`docs-next/30_crosswalk_互证/old-to-new.md`](../30_crosswalk_互证/old-to-new.md) — 192 → 256 术语迁移表 (#8)
- [`docs-next/30_crosswalk_互证/cell192-to-cell256-migration.md`](../30_crosswalk_互证/cell192-to-cell256-migration.md) — 详细迁移操作
- [`史/义理-pre-v3/表六_192格全表_旧Z3版.md`](../../史/义理-pre-v3/表六_192格全表_旧Z3版.md) — 旧 192 表归档
