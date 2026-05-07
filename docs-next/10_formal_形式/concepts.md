# 形式概念图谱

形式层有三种容易混淆的图：单根图、构造图、概念依赖图。它们都服务于审计，但证明目标不同。

## 单根图 Monad DAG

单根图说明登记项如何回到「一」。它的证明主轴在 `Foundation/Core/MonadRoot.lean`，图与说明在 `formal/SSBX/diagrams/MonadDAG.*`、`formal/SSBX/notes/MonadDAG.md`。

读法：

- 根是「一元」。
- 中层是文、物、生、理、心、人、模、审校、价值、证明、注意、真理等面向。
- 下层包含字根、生成项、递归项、primitive、pending interface 与 claim。
- 它回答「是否有共同根」；不回答「每个经验 claim 是否为真」。

## 构造图 Construction DAG

构造图说明内容如何从当前论域 Γ 出发，经三本、三显、三征、开闭、价值、行动、注意、人对齐、模型与真理，构造到「生生不息论」。对应 Lean 主轴为 `Foundation/Core/Monism.lean`。

读法：

- 起点是 Γ，而不是把所有内容直接从 metaphysical root 推出。
- 边表示构造依赖，rank 严格推进，用于无环审计。
- 它证明的是构造充分性与依赖形状，不是无前提宇宙真理。

## 概念依赖图 Concept DAG

概念 DAG 是名册依赖图，方向为「字根/依赖项 -> 生成项/递归项」。完整图来自 `formal/SSBX/diagrams/ConceptDAG.*` 与 `formal/SSBX/notes/ConceptDAG.md`。

读法：

- `atom`：单字根。
- `generated`：由字根或其他生成项合成。
- `primitive`：模型、度量或算子接口。
- `recursive`：价值与真理类递归谓词。
- `pending`：经验或模型项，必须等待校准。

## 三图关系

| 图 | 核心问题 | 主要来源 | 边界 |
|---|---|---|---|
| Monad DAG | 登记项是否回到「一」 | `MonadRoot.lean`、`MonadDAG.*` | 单根关系不是经验真值。 |
| Construction DAG | 内容如何构造到全论 | `Monism.lean`、`ConstructionDAG.*` | 构造充分性不等于无前提真理。 |
| Concept DAG | 名册依赖是否覆盖且无环 | `Roster.lean`、`ConceptDAG.*` | 名册同步不是 theorem 本身。 |

## 与生成索引的关系

当 `../_generated/` 存在时，图节点、边、孤立项、pending 项应以生成索引为准。人工文档只保留解释性口径，避免把旧数量写死。
