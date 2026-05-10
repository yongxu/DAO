# Agent Instructions

> 状态：v3 (2026-05-11) — 项目 R₀..R₈ strict (Z/2)ⁿ uniform, V₄ Klein Shi, Cell256, 道 = (qian, dao) = `OX["oooooooo"]`. 旧 Cell192 / Z/3 Shi / 旧 R-编号 已归档至 `史/`，不再被入口索引。

本文件约束所有在本仓库工作的 agents。进入任务前先读本文件，并把这些规则传给后续开启的 subagents。

## v3 Doctrine and Archive Pointers

- **Canonical doctrine**: [`docs-next/10_formal_形式/yi-RO-hierarchy.md`](./docs-next/10_formal_形式/yi-RO-hierarchy.md). 任何关于 R-hierarchy / V₄ Shi / Cell256 / 道 anchor 之结构主张必须以此为准, 不要援引旧 v1 / v2 文件。
- **Pre-v3 archive**: [`史/`](./史/README.md). 仅当确实需要 v2 (Cell192 / Z/3 Shi / R₁..R₆) 之具体形式时才进入; 否则不读、不引、不更新; **不要把 `史/` 之内容作为新文档之依据**。
- **Citable historical**: [`史料/`](./史料/) 是 v9–v14 各代手稿之研究档案 (与 `史/` 不同, 仍可援引)。
- 涉及 Cell-carrier 的代码改动: 必为 `Cell256` (不是 `Cell192`); 若发现遗留 `Cell192` 命名, 在该次任务范围内一并迁移 (或报告给主线程)。

## Goal: Elegance

当任务目标提到“优雅”时，按以下标准理解：在不牺牲正确性和可维护性的前提下，用尽量少的结构承载尽量清楚的意图。

- 概念少而准：不引入多余层级、术语、helper 或框架；必要边界必须明确。
- 顺着已有系统生长：命名、文件位置、证明风格、文档语气、代码形状都贴合当前仓库。
- 局部改动能解释全局意图：读者能从改动看出为什么这样做，不需要额外猜。
- 边界干净：文档与形式化、定义与定理、生成物与手写物、主线程与 subagent 责任不混。
- 可验证但不滥验证：该证明的证明，该检查的检查；避免因为焦虑反复跑昂贵 build。
- 失败方式清楚：如果以后坏了，容易定位是哪条假设、哪个接口、哪个定义出了问题。
- 不炫技：能直写就直写；只有当抽象真的减少复杂度时才抽象。
- 在本仓库中还要保证：中文义理表达不松散，Lean 骨架不伪装成已完成证明，文档和形式系统之间的映射可审计、可追踪、不过度声称。

## Build And Verification

- 跑 build 或其他高成本验证前，先把基线更新到最新状态：根据当前分支和上游关系执行合适的 merge 或 rebase，再开始 build。
- 尽可能少跑 build。本仓库 build 很慢，也会明显消耗 MacBook 电池。
- subagents 不跑 build。subagents 只做实现、分析、文件级检查或轻量命令，并在返回时说明改了哪些文件、做了哪些非 build 验证。
- 等所有 subagents 的结果回到主线程并完成集成后，再由主线程统一决定是否跑一次 build。
- 如果改动只涉及文档、注释、计划或其他不影响构建产物的内容，默认不跑 build，除非任务明确要求。
- 每次工作结束merge回local main

## Parallel Work

- 能合理拆分并行时，尽可能多开 agents 并行推进。
- 并行任务必须有清晰边界，避免多个 agents 修改同一文件或同一模块造成冲突。
- 给 subagent 的任务说明中必须明确：不要跑 build；不要回滚他人改动；返回变更文件、关键判断和轻量验证结果。
- 主线程负责最终整合、冲突处理、必要验证和最终汇报。
