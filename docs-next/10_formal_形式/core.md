# 形式层入口

> 状态：v3 (2026-05-11) — 与 main @ 1c76a55 对齐。R₀..R₈ strict (Z/2)ⁿ uniform + Cell128 / Cell256 + Hierarchy/ 目录是当前形式层 spine。

形式层（`formal/SSBX/`）以 **R₀..R₈ strict (Z/2)ⁿ uniform** 为骨架，Cell128 (R₇) 与 Cell256 (R₈) 为最高两层，[`Foundation/Hierarchy/`](../../formal/SSBX/Foundation/Hierarchy/) 提供 R-index 命名 + uniform Lift/Project + inner/outer 算子拆分。本页是入口；按主题给出全局指引并链接到分页。

## 1. 什么是道源 / 什么是 R-O 双层级

「易」之 algebraic 核 = (Z/2)⁸ Abelian 群在自身上的 Cayley 自作用 + 道作为 origin choice + V₄ 外对称接口。9 层 strict uniform R₀..R₈（每 Rₙ = (Z/2)ⁿ）完整闭合：元 ≅ 算子之 fusion 是「自描述」之 algebraic 本质；道之 anchoring 是「立心」之 ontological 必要。

definitive 文本是 [yi-RO-hierarchy.md](yi-RO-hierarchy.md)（v2.1）。

## 2. 模块簇

`formal/SSBX/` 自上而下：

| 簇 | 路径 | 职责 |
|---|---|---|
| 顶层入口 | [`SSBX.lean`](../../formal/SSBX.lean) | 一处导入，build 全树 |
| Core 共用 | [`SSBX/Core.lean`](../../formal/SSBX/Core.lean) | 三值口径、开闭、共用 enum 与接口 |
| Roster 名册 | [`SSBX/Roster.lean`](../../formal/SSBX/Roster.lean) | atom / generated / primitive / recursive / pending 名册 |
| Pending | [`SSBX/Pending/`](../../formal/SSBX/Pending/) | 经验接口与示例（不进入 trust core） |
| Foundation/Core | [`SSBX/Foundation/Core/`](../../formal/SSBX/Foundation/Core/) | Yuan, Li, Monism, MonadRoot, Renlei, ShengshengBuxi, EvolutionDao, Sincerity, Attention, Alignment, ... |
| Foundation/Wen | [`SSBX/Foundation/Wen/`](../../formal/SSBX/Foundation/Wen/) | 文 / 文言微核 / 自释 / quine / WenSurface / DaoSource |
| Foundation/Jian | [`SSBX/Foundation/Jian/`](../../formal/SSBX/Foundation/Jian/) | 间之核（14 字粒子） + JianSTLC + JianYiBridge |
| Foundation/Yi | [`SSBX/Foundation/Yi/`](../../formal/SSBX/Foundation/Yi/) | Yao / Trigram / Hexagram / 易代数最小单 |
| Foundation/Bagua | [`SSBX/Foundation/Bagua/`](../../formal/SSBX/Foundation/Bagua/) | BaguaAlgebra / BenZheng / **Cell128 / Cell256** / Cell256Stratify / BaguaTuring / KleeneInternal / GodelLi / ChunkedDecide / CuoInvariance / FuelDiscipline / Newman |
| **Foundation/Hierarchy** | [`SSBX/Foundation/Hierarchy/`](../../formal/SSBX/Foundation/Hierarchy/) | **R₀..R₈ alias + RHierarchy umbrella + LiftProject + Operators/{Atomic, V4Outer}** |
| **Foundation/Notation** | [`SSBX/Foundation/Notation/`](../../formal/SSBX/Foundation/Notation/) | **`OX["xxxxxxxx"]` 8-char Cell256 字面 macro** |
| Foundation/Eight | [`SSBX/Foundation/Eight/`](../../formal/SSBX/Foundation/Eight/) | 八衍：动理 / 逻辑 / 数算 / 统计 / ... |
| Foundation/Modern | [`SSBX/Foundation/Modern/`](../../formal/SSBX/Foundation/Modern/) | 现代数学 / 概率 / 逻辑 / 物理 / 神经科学 桥接 |
| Text | [`SSBX/Text/`](../../formal/SSBX/Text/) | glyph / legacy operator inventory / 覆盖性 / OperatorAnchors / OperatorCellMap |
| Truth | [`SSBX/Truth/`](../../formal/SSBX/Truth/) | claim ledger / semantic adequacy / SelfDescription |
| Model | [`SSBX/Model/`](../../formal/SSBX/Model/) | 模型 adequacy / concrete ledger |

## 3. 「一处导入即得 R₀..R₈」

```lean
import SSBX.Foundation.Hierarchy.RHierarchy
-- 现在 R0..R8、liftR{n}toR{n+1}/projR{n+1}toR{n}、
-- atomic XOR ops 与 V₄ outer 都在 namespace 内可用
```

[`RHierarchy.lean`](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean) umbrella 一处导入下面 12 个文件：

```
R0_Taiji  R1_Yao  R2_SiXiang  R3_Trigram  R4_Mian
R5_Wuyao  R6_Hexagram  R7_YinHex  R8_GuoHex
LiftProject  Operators/Atomic  Operators/V4Outer
```

## 4. 文档导航（同目录 sibling docs）

主 doctrine：

- [yi-RO-hierarchy.md](yi-RO-hierarchy.md) — **v2.1 definitive doctrine**：R₀..R₈ + V₄ Shi + Cayley fusion + 道 origin
- [yi-calculus-theorem.md](yi-calculus-theorem.md) — Theorems A–K 易代数定理
- [yi-as-meta-framework.md](yi-as-meta-framework.md) — 易作为 self-description GUT 解读

R₈ / Cell256 spine（v3 sibling docs，本轮并行写入）：

- [cell256-grid.md](cell256-grid.md) — 256 cell × Shi V₄ 全表
- [v4-shi.md](v4-shi.md) — V₄ Klein Shi 之代数（4 元 vs 旧 3 元 Z/3）
- [cell256-algebra.md](cell256-algebra.md) — Cayley ι/ε / abelian spine
- [yin-tou-operators.md](yin-tou-operators.md) — 印/投 XOR mask 详解
- [ox-notation.md](ox-notation.md) — `OX["..."]` 8-char 字面 macro
- [operator-split.md](operator-split.md) — atomic inner/outer 算子拆分
- [lift-project.md](lift-project.md) — R₀..R₈ Lift / Project pairs
- [r8-root-language-tree.md](r8-root-language-tree.md) — R₀..R₈ root language tree、1021/1022/1023 口径、root-rule roadmap
- [root-native-operators.md](root-native-operators.md) — 根算子四类来源：mask / program / projection / alias；legacy catalogue quarantine
- [root-language-tree/README.md](root-language-tree/README.md) — 1023-entry 文言 / 中文 / English / formal logic 审阅包

R-line 与字根：

- [layer-character-map.md](layer-character-map.md) — R0–L0 字根映射推荐表
- [root-layer-map.md](root-layer-map.md) — 三轴结构定义
- [layer-axis-graph.md](layer-axis-graph.md) — 三轴汇聚 Mermaid
- [sanben-sijieduan-grid.md](sanben-sijieduan-grid.md) — 12 格内容映射 (3 本 × 4 阶段)
- [64-hexagram-grid.md](64-hexagram-grid.md) — 64 卦 4-quadrant + 算子 invariant + Cell256 扩展
- [position-operator-tree.md](position-operator-tree.md) — 算子树 R₀..R₈ 全程

模块与代码索引：

- [foundation-core.md](foundation-core.md) — Foundation/{Core, Bagua} 模块簇
- [modern.md](modern.md) — Foundation/Modern 桥接
- [wen.md](wen.md) — Foundation/Wen
- [jian.md](jian.md) — Foundation/Jian
- [eight.md](eight.md) — Foundation/Eight
- [text.md](text.md) — Text 字与算子
- [truth-model.md](truth-model.md) — Truth + Model claim 状态
- [build-and-verify.md](build-and-verify.md) — `lake build` 与验证
- [module-map.md](module-map.md) — 模块簇地图
- [trust-boundaries.md](trust-boundaries.md) — 信任边界
- [pending.md](pending.md) — 未闭合接口

## 5. SSBX.Core / SSBX.Roster 速读

**SSBX.Core**：跨模块共用定义（三值口径、开闭、共用 inductive、共用 abbrev）。它是底层词汇表，不是所有义理结论的最终证明页。其中的 theorem 可直接按 Lean theorem 使用。

**SSBX.Roster**：名册中心。生成索引 [../_generated/registry-index.md](../_generated/registry-index.md) 从这里导出统计与清单。重点：生成项是否有根 / 递归项是否有语义 / 文字覆盖是否与 Text 层同步 / pending 项是否被显式标出。

**SSBX 顶层**：[`formal/SSBX.lean`](../../formal/SSBX.lean) 聚合各模块。**注意**：顶层 import 成功只说明模块能一起类型检查；不等于所有文档 claim 都已 machine-checked。

## 6. 边界提醒

形式层不扩张当前信任边界。若读到从 Core 推到全体系的陈述，应回查具体 theorem 与 [../_generated/claim-index.md](../_generated/claim-index.md)，确认它是 machineChecked、modelComputed 还是 ledgerDependent。

R₈ 完整性陈述（[yi-RO-hierarchy.md §6](yi-RO-hierarchy.md#第六部分完整性定理-completeness-theorem)）只在「abelian closure 内」成立 —— GL(8, F₂) non-XOR 线性映射、S₂₅₆ 任意 permutation、连续扩展、概率扩展、动力扩展（halting）都按设计在边界外。

## 形式锚

- [`formal/SSBX.lean`](../../formal/SSBX.lean)
- [`formal/SSBX/Core.lean`](../../formal/SSBX/Core.lean)
- [`formal/SSBX/Roster.lean`](../../formal/SSBX/Roster.lean)
- [`formal/SSBX/Foundation/Hierarchy/RHierarchy.lean`](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean)
- [`formal/SSBX/Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean)
- [`formal/SSBX/Foundation/Bagua/Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean)
- [`formal/SSBX/Foundation/Notation/OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean)
