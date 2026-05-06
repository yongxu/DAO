# Construction DAG / 构造证明图

这张图和 `ConceptDAG.*` 不同：

- `ConceptDAG` 是名册依赖图，证明登记项覆盖和无环。
- `ConstructionDAG` 是内容构造图，表达“从 Γ 当前论域出发，经三本、三显、三征、開閉与拓扑合成，构造生生不息论”。

对应 Lean 模块：[`Foundation/Core/Monism.lean`](../Foundation/Core/Monism.lean)。

```mermaid
%% Proof-construction DAG. Direction: predecessor --> constructed stage.
%% This is not the roster dependency graph. It is the intended constructive proof spine.
flowchart TB
  gamma["Γ / territory 当前论域\nrank 0"]:::root
  jian["三本 / 物-動-間\nrank 1"]:::root
  aspects["三显 / 位-場-際\nrank 2"]:::stage
  yuan["三征 / 幾-勢-機\nrank 3"]:::stage
  dynamics["開閉闸口与網體流合成\nrank 4"]:::stage
  universal["普遍证明理\nrank 1"]:::principle
  openclose["开闭核心\nrank 5"]:::recursive
  audit["审校核心\nrank 3"]:::audit
  value["价值核心\n正/义/善/仁/道\nrank 6"]:::recursive
  action["行核心\n行改后续之间\nrank 6"]:::action
  attention["注意 / 聚焦机制核心\nattention as mechanism\nrank 6"]:::attention
  human["做人 / 对齐核心\n人 -> 意图向齐生\nrank 7"]:::human
  model["模型充分性核心\n科学模原则\nrank 4"]:::model
  truth["真理核心\nrank 7"]:::truth
  cic["CIC 作为形式模\n归纳构造演算\nrank 5"]:::external
  ssbx["生生不息论\nrank 8"]:::theory

  gamma --> jian
  gamma --> aspects
  jian --> aspects
  aspects --> yuan
  jian --> dynamics
  yuan --> dynamics
  gamma --> universal
  dynamics --> openclose
  universal --> audit
  aspects --> audit
  openclose --> value
  audit --> value
  yuan --> action
  dynamics --> action
  openclose --> action
  aspects --> attention
  openclose --> attention
  audit --> attention
  action --> human
  attention --> human
  openclose --> human
  audit --> human
  gamma --> model
  universal --> model
  audit --> model
  value --> truth
  model --> truth
  audit --> truth
  universal --> cic
  model --> cic
  truth --> ssbx
  value --> ssbx
  action --> ssbx
  attention --> ssbx
  human --> ssbx
  model --> ssbx
  cic --> ssbx

  classDef root fill:#fefce8,stroke:#ca8a04,color:#422006,stroke-width:2px;
  classDef principle fill:#eef2ff,stroke:#4f46e5,color:#312e81,stroke-width:2px;
  classDef stage fill:#f8fafc,stroke:#64748b,color:#0f172a;
  classDef recursive fill:#fff7ed,stroke:#ea580c,color:#7c2d12;
  classDef audit fill:#ecfeff,stroke:#0891b2,color:#164e63;
  classDef action fill:#f0fdf4,stroke:#16a34a,color:#14532d,stroke-width:2px;
  classDef attention fill:#fefce8,stroke:#ca8a04,color:#422006,stroke-width:2px;
  classDef human fill:#fff1f2,stroke:#e11d48,color:#881337,stroke-width:2px;
  classDef model fill:#f0fdf4,stroke:#16a34a,color:#14532d;
  classDef truth fill:#fdf2f8,stroke:#db2777,color:#831843,stroke-width:2px;
  classDef external fill:#f5f3ff,stroke:#7c3aed,color:#3b0764;
  classDef theory fill:#fef2f2,stroke:#dc2626,color:#7f1d1d,stroke-width:3px;
```

Lean 中已经证明的形状：

- `construction_ledger_complete`：每个构造阶段都登记在构造账本中。
- `predecessor_rank_lt`：每条构造边都严格降低/升高 rank，因此构造依赖无环。
- `ssbx_constructed_from_monism` / `ssbx_constructed_from_content`：给定显式 `UniversalProvePrinciple`，可构造到 `生生不息论`。
- `gammaFieldRoot`：内容构造从 Γ 当前论域开始，而非从“一元论根”开始。
- `jianRoot`、`aspectTriad`、`yuanTriad`、`systemDynamics`：把“三本（物/動/間）→ 三显（位/場/際）→ 三征（幾/勢/機）→ 開閉与網/體/流”接入构造主干。
- `actionCore`：把“行会改变后续之间”接入价值、做人和全论构造。
- `attentionCore`：把 `注意 / 聚焦机制` 接入构造主干。
- `humanAlignmentCore`：把 `做人 / 意图向齐生` 接入内容构造主干。

注意：这里证明的是“构造充分性/依赖形状”，不是无前提宇宙真理。真理仍由 `Truth` 与 `Model` 层承担。
