# 形式层总览

本节说明 Lean 形式化目前已经承担什么、仍把什么留在信任边界之外。源代码入口为 `formal/SSBX.lean` 与 `formal/SSBX/`，机器索引优先看 `../_generated/` 下的导出表；若索引尚未生成，以 Lean 源文件与 `formal/SSBX/notes/` 为准。

## 形式层承担的内容

- `Foundation/Wen/Kernel.lean` 给出「一」的封装见证，并投影出 `Field`、`dong`、`origin`、`origin_alive`。
- `Foundation/Core/` 承担单根、构造主干、价值递归、注意、人对齐等核心结构。
- `Foundation/Bagua/` 承担八卦、Cell256 / R₀..R₈ strict spine、BaguaTuring、Kleene/Rice/GodelLi 边界。
- `Text/` 承担字、legacy operator catalogue、义位与覆盖性账本；目录层只作 inventory / audit input，不作 root ontology。
- `Truth/` 与 `Model/` 承担 claim ledger、语义、充足模型原则与体系内真理口径。

## 机器口径

当前形式层按以下口径阅读：

- 已修复构建后，不允许存在 live `sorry`、`admit`、`unsafe`。
- 显式公理只有一个：`kleene_recursion_axiom`。
- 不透明封装只有一个：`opaque theOne`。
- 顶层 `partial def` 边界只有一个：`YiState.run`。
- 文档、图、名册、互证表是同步与审计对象；它们不自动等同于 Lean theorem。

## 读者路径

1. 先读 [trust-boundaries.md](./trust-boundaries.md)，确认可依赖内容与信任边界。
2. 再读 [build-and-verify.md](./build-and-verify.md)，理解构建、警告与审计口径。
3. 读 [module-map.md](./module-map.md)，按模块簇进入代码。
4. 再读 [concepts.md](./concepts.md)，理解单根、构造 DAG、概念 DAG 的区别。
5. 对图和互证关系，读 [../30_crosswalk_互证/diagrams.md](../30_crosswalk_互证/diagrams.md)。
6. 对维护流程，读 [../50_maintenance/README.md](../50_maintenance/README.md)。

## 分页索引

- [core.md](./core.md)：`Foundation/Core` 与顶层核心结构。
- [text.md](./text.md)：字、义位、算子与文本完备账本。
- [truth-model.md](./truth-model.md)：truth、claim ledger 与 model adequacy。
- [foundation-core.md](./foundation-core.md)：核心 foundation 各文件的读法。
- [root-layer-map.md](./root-layer-map.md)：底层 root 几层的生成线、名册线、内容线、关系与算子总图。
- [r8-root-language-tree.md](./r8-root-language-tree.md)：R₀..R₈ root language tree、1021/1022/1023 口径、root-rule roadmap。
- [root-native-operators.md](./root-native-operators.md)：root-native operator 四类来源与 legacy catalogue quarantine 形式锚。
- [v4-foundation.md](./v4-foundation.md)：V4 作为 Wen 的 two-axis Klein-four kernel、跨域读法与 preservation atlas。
- [v4-kernel-interpreter-architecture.md](./v4-kernel-interpreter-architecture.md)：V4-native interpreter kernel 与后续 R-space backend contract。
- [root-language-tree/README.md](./root-language-tree/README.md)：1023-entry 文言 / 中文 / English / formal logic 审阅包。
- [wen.md](./wen.md)：`Foundation/Wen`、文言微核、自释与 quine 路线。
- [jian.md](./jian.md)：`Foundation/Jian` 的间、本体与 STLC 桥。
- [yi-bagua.md](./yi-bagua.md)：易、八卦、Cell256、BaguaTuring 与不完备边界。
- [eight.md](./eight.md)：八衍模块与现代专题之间的中层接口。
- [modern.md](./modern.md)：现代数学、概率、逻辑、物理与神经接口。
- [pending.md](./pending.md)：pending interface 的经验边界。

## 与生成索引的关系

建议由生成流程维护 `../_generated/` 下的索引，例如模块清单、声明清单、图节点清单、信任边界统计。本文只描述阅读口径；数量统计应以生成索引或最新 `lake build` 后的审计输出为准。
