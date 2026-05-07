# Core 总览

Core 是形式层的共用骨架：基础类型、三值口径、开闭、递归项、名册与顶层导入。完整声明列表看 [../_generated/lean-index.md](../_generated/lean-index.md)。

## `SSBX.Core`

`formal/SSBX/Core.lean` 承担跨模块共用定义。它提供许多后续模块使用的基本对象，例如三值口径、开闭相关结构、基础判定与接口类型。

读法：

- 它是底层词汇表，不是所有义理结论的最终证明页。
- 其中的 theorem 可以直接按 Lean theorem 使用。
- 与经验相关的判定若只是接口或参数，不应写成已实证结论。

## `SSBX.Roster`

`formal/SSBX/Roster.lean` 是名册中心。生成索引 [../_generated/registry-index.md](../_generated/registry-index.md) 从这里导出 atom、generated、primitive、recursive、pending 的统计与清单。

名册证明的重点是：

- 生成项是否有根。
- 递归项是否有语义。
- 文字覆盖是否与 Text 层同步。
- pending 项是否被显式标出，而不是混入已证明项。

## 顶层导入

`formal/SSBX.lean` 聚合各模块，让构建覆盖整套形式层。顶层导入成功说明模块能一起类型检查；它不等于所有文档 claim 都已 machineChecked。

## 与其他页关系

- 单根、构造、注意、人对齐见 [foundation-core.md](./foundation-core.md)。
- 字与算子见 [text.md](./text.md)。
- claim 状态见 [truth-model.md](./truth-model.md)。
- pending 接口见 [pending.md](./pending.md)。

## 边界提醒

Core 层本身不扩张当前信任边界。若读到从 Core 推到全体系的陈述，应回查具体 theorem 与 [../_generated/claim-index.md](../_generated/claim-index.md)，确认它是 machineChecked、modelComputed 还是 ledgerDependent。
