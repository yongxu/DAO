# Agent Instructions

本文件约束所有在本仓库工作的 agents。进入任务前先读本文件，并把这些规则传给后续开启的 subagents。

## Codebase Layout (v3, 2026-05-11)

- 本体已收口于 **Cell256 / V₄ Klein Shi {道, 已, 今, 未} / strict-uniform R₀..R₈**。
- 旧 `Foundation/Bagua/Cell192.lean` 已删除；替换为 `Cell128.lean` (R₇) + `Cell256.lean` (R₈)。
- 新 `Foundation/Hierarchy/`（R₀..R₈ alias files + `LiftProject.lean` + `Operators/{Atomic,V4Outer}.lean`，由 `RHierarchy.lean` umbrella 入口聚合）是 R-阶梯 uniform 基础设施。
- 新 `Foundation/Notation/OXNotation.lean` 提供 `OX["xxxxxxxx"]` 8-char Cell256 字面量 macro。
- 闭合 bundle 是 `R8_complete`（在 `Cell256Stratify.lean`），axes 仅依赖 `propext + native_decide`，不增加 project-level axiom。
- 当前 build：3656 jobs · 0 sorry · 1 axiom (`kleene_recursion_axiom`, cuo-restricted) · 1 opaque (`theOne`) · 1 partial def (`BaguaTuring.run`).
- 定本 doctrine 文档：`docs-next/00_start/final-theory.md` + `docs-next/10_formal_形式/yi-RO-hierarchy.md`。
- 三 README 同步：`README.md` (中) / `README.en.md` (英) / `README.formal.md` (Lean 规约)。

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
