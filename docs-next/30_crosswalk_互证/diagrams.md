> 状态：v3 (2026-05-11) — 图与互证读法。已更新到 Cell256 + V₄ Klein Shi + R₀..R₈；R-hierarchy 与 Position-Operator-Tree 之 256 模式说明纳入。

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
| Position Operator Graph | `formal/SSBX/diagrams/PositionOperatorGraph.*.mmd` | `formal/SSBX/notes/PositionOperatorGraph.md` | `Foundation/Bagua/` 与算子登记（**v3：256-cell 模式**，不再 192） |
| R-Hierarchy 阶梯（如生成） | `formal/SSBX/diagrams/RHierarchy.mmd`（若生成） | `Foundation/Hierarchy/RHierarchy.lean` 头注 | R₀..R₈ strict (Z/2)ⁿ uniform；**256 节点 at R₈** |

## 互证规则

- 图的节点必须能追溯到 Lean 名称、名册项或明确标注的外部说明项。
- 图的边必须能追溯到依赖、构造前驱、算子作用或说明性 crosswalk。
- `.svg` 是渲染产物；审计以 `.mmd` 与 Lean/notes 为准。
- 生成索引存在时，不手工维护节点总数与边总数。
- pending interface 必须在图中保持 pending，不得通过图示改写成已证明结论。
- v3 之 R-hierarchy 视图（如有）以 R₀..R₈ strict-uniform 为准；旧 R₁..R₆ chong-jump 视图归 `史/`。

## 常见误读

- Concept DAG 的「无环」只说明名册依赖可作为 DAG 阅读；不证明所有 claim 为真。
- Construction DAG 的「构造到生生不息论」依赖显式原则与模型口径；不等于把 Γ 之外的一切都形式化完毕。
- Monad DAG 的「单根」是根源登记口径；不消除 `kleene_recursion_axiom`、`theOne`、`YiState.run` 三个信任边界。
- Position Operator Graph 在 v3 下应理解为 **R₈ 256 个 cell + 算子边**（不再是旧 192 cell 视图）；旧 192 视图归 `史/义理-pre-v3/`。

## v2 → v3 图示迁移要点

| 旧图概念 | v3 替代 | 注 |
|---|---|---|
| 192-cell Position Operator Graph | 256-cell（v3） | Shi 由 Z/3 cyclic 改为 V₄ Klein，节点数 192 → 256 |
| R₁..R₆ R-hierarchy 阶梯（含 R₃→R₄ chong jump） | R₀..R₈ strict (Z/2)ⁿ uniform | 显式 R₀ 太极 + R₄ Mian + R₅ 五爻；无跳跃 |
| Shi 三态环 (Z/3) | Shi V₄ Klein 群 = `{道, 已, 今, 未}` | 中心元 `今` 是 PT；`道` 是 V₄ identity = R₈ origin |
| 旧「Mian 是顶层」图示 | Mian = R₄；R-hierarchy 顶为 R₈ Cell256 | BenZheng 仍是 R₄ 之具体落地，但不再是 hierarchy 终点 |

## 更新流程

1. 修改 Lean 名册、构造关系或图源后，重新生成对应 `.mmd`。
2. 渲染 `.svg`，但不要把 `.svg` 当作唯一审计来源。
3. 更新或检查 `../_generated/` 下的图索引。
4. 核对本页表格是否需要新增图类别；不要在本页写入易过期的节点数量。
5. 涉及 R-hierarchy 或 Cell256 之图，必须与 [`Foundation/Hierarchy/RHierarchy.lean`](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean) 头注一致；与 Cell256/Cell128 carrier 之矛盾以 Lean 为准。

## 形式锚

- [`formal/SSBX/Foundation/Hierarchy/RHierarchy.lean`](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean) — R₀..R₈ umbrella
- [`formal/SSBX/Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) — 256-cell carrier
- [`formal/SSBX/Foundation/Bagua/Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) — 128-cell middle layer
- [`formal/SSBX/Foundation/Bagua/Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) — 位置-算子树双射 + xuGua256
