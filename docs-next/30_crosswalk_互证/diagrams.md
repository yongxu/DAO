# 图与互证

本页是图文件、Lean 证明、说明文档之间的互证索引。图用于审计与阅读，不替代 Lean theorem。若 `../_generated/` 中已有 diagram index、module index 或 declaration index，应优先使用生成索引核对文件存在性与数量。

## 图文件来源

| 图 | 生成/维护源 | 人读说明 | 证明或登记主轴 |
|---|---|---|---|
| Monad DAG | `formal/SSBX/diagrams/MonadDAG.mmd` | `formal/SSBX/notes/MonadDAG.md` | `Foundation/Core/MonadRoot.lean` |
| Construction DAG | `formal/SSBX/diagrams/ConstructionDAG.mmd` | `formal/SSBX/notes/ConstructionDAG.md` | `Foundation/Core/Monism.lean` |
| Concept DAG | `formal/SSBX/diagrams/ConceptDAG.*.mmd` | `formal/SSBX/notes/ConceptDAG.md` | `Roster.lean` 与概念依赖登记 |
| Attention DAG | `formal/SSBX/diagrams/AttentionDAG.mmd` | `formal/SSBX/notes/Attention.md` | `Foundation/Core/Attention.lean` |
| Human Alignment DAG | `formal/SSBX/diagrams/HumanAlignmentDAG.mmd` | `formal/SSBX/notes/HumanAlignment.md` | `Foundation/Core/HumanAlignment.lean` |
| Position Operator Graph | `formal/SSBX/diagrams/PositionOperatorGraph.*.mmd` | `formal/SSBX/notes/PositionOperatorGraph.md` | `Foundation/Bagua/` 与算子登记 |

## 互证规则

- 图的节点必须能追溯到 Lean 名称、名册项或明确标注的外部说明项。
- 图的边必须能追溯到依赖、构造前驱、算子作用或说明性 crosswalk。
- `.svg` 是渲染产物；审计以 `.mmd` 与 Lean/notes 为准。
- 生成索引存在时，不手工维护节点总数与边总数。
- pending interface 必须在图中保持 pending，不得通过图示改写成已证明结论。

## 常见误读

- Concept DAG 的「无环」只说明名册依赖可作为 DAG 阅读；不证明所有 claim 为真。
- Construction DAG 的「构造到生生不息论」依赖显式原则与模型口径；不等于把 Γ 之外的一切都形式化完毕。
- Monad DAG 的「单根」是根源登记口径；不消除 `kleene_recursion_axiom`、`theOne`、`YiState.run` 三个信任边界。

## 更新流程

1. 修改 Lean 名册、构造关系或图源后，重新生成对应 `.mmd`。
2. 渲染 `.svg`，但不要把 `.svg` 当作唯一审计来源。
3. 更新或检查 `../_generated/` 下的图索引。
4. 核对本页表格是否需要新增图类别；不要在本页写入易过期的节点数量。
