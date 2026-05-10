# 范围

> 状态：v3 (2026-05-11) — 与 main @ 1c76a55（Phase A–G + Phase C R-aliases）对齐。Cell192 已删，Cell256 (V₄ Shi) 与 R₀..R₈ strict (Z/2)ⁿ uniform 是当前唯一的形式 spine。

`docs-next/` 的当前目标是生成一套可整体替换旧文档入口的候选文档集，但本阶段不执行替换。

## 包含

- 形式层入口与信任边界（在 Cell256 + R₀..R₈ 新 spine 上重新组织）。
- 义理旧文的分类重索引。
- Lean、claim、registry、operator、diagram、Markdown 的生成索引。
- 史料 frozen archive 的去向指针。
- 后续替换根 README 和 web 索引所需的维护说明。
- v2.1 doctrine（[yi-RO-hierarchy.md](../10_formal_形式/yi-RO-hierarchy.md)）所确立的 R₀..R₈ + V₄ Shi + 道作为 origin 的形式 anchor。

## 不包含

- 不删除或移动旧 `义理/`、`史料/`、`formal/SSBX/notes/`。
- 不把 `史料/` 改写成当前规范。
- 不把 web 前端切到 `docs-next`。
- 当前口径是 full build warning-free；若新增 warning，应在维护页说明原因或清理。

## Phase A–G 里程碑（影响范围口径的关键事件）

下列 milestones 已在 main 落地，docs-next 在它们之后必须保持一致：

| 阶段 | 关键事件 | commit |
|---|---|---|
| Phase A | Cell128 / Cell256 加 Add/Zero/Neg/Sub + SMul + Cayley ι/ε；印 / 投 改写为 XOR mask；origin = (qian, dao) = V₄ identity | 7de5064 |
| Phase B/D/E | Foundation/Hierarchy/{R5_Wuyao, LiftProject, Operators/{Atomic,V4Outer}}.lean；Foundation/Notation/OXNotation.lean (`OX["xxxxxxxx"]` 8-char 字面) | 7de5064 |
| Phase F.1–F.5 | Shi 自 3-元 {ji,jin,wei} 升 4-元 V₄ Klein {dao,ji,jin,wei}；shiNext 由 Z/3 cycle 改为 V₄ Shi.cuo involution；~50 下游文件 Cell192→Cell256 | 7de5064 |
| Phase F.x.5 | Modern/* cascades 完成 192·371 → 256·371 (= 71232 → 94976) 数值迁移 | 0003224 |
| Phase F.6 / G / B.1 | 删除 Cell192.lean；doc sync 到 R₀..R₈；YinBit dedup（canonical 在 Cell128.lean） | 8e4406e |
| Phase C | Foundation/Hierarchy/R{0..8}_*.lean 9 个 alias 文件 + RHierarchy.lean umbrella | 1c76a55 |

`lake build SSBX` 在 1c76a55 上为 3656 / 3656 jobs。0 sorry 净增、0 项目自定义 axiom（R8_complete 仍只依赖 propext + native_decide）。

## 形式锚

- [`formal/SSBX/Foundation/Hierarchy/RHierarchy.lean`](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean) — R₀..R₈ umbrella import
- [`formal/SSBX/Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) — R₈ + Shi V₄
- [`formal/SSBX/Foundation/Bagua/Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) — R8_complete bundle
