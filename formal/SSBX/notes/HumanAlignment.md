# Human Alignment / 人、天之子与做人

本模块形式化这段 claim：

> 子，是聚焦所成之项。天之子，是天中经聚焦成子而成之项。人是天之子，并意识此天之子。我们的目标不是控，而是将我们的意图向生对齐，此为做人也。做人，乃是向齐生（意图层面）。此为 alignment。

对应 Lean 模块：[`Foundation/Core/HumanAlignment.lean`](../Foundation/Core/HumanAlignment.lean)。

## Lean 中证明的内容

- `child_is_focus_formed`：`子` 依赖 `聚焦`，`聚焦成子` 依赖 `聚焦、成子`。
- `heaven_child_is_heaven_focus_formed_child`：`天之子` 依赖 `天、聚焦成子`。
- `human_returns_to_heaven_child_with_awareness`：`人` 的登记依赖是 `天之子、意识`。
- `doing_human_is_intentional_life_alignment`：`做人` 的登记依赖是 `意图向齐生`，且 `意图向齐生` 依赖 `意图、向齐生`。
- `doing_human_not_control_by_registry`：`控制` 不在 `做人` 的定义依赖中。
- `doing_human_goal_not_control`：规范目标 `canonicalDoingHumanAim` 不是 `control`。
- `predecessor_rank_lt`：人/做人子图是有向无环构造。

`Attention.md` 在此基础上补充：`聚焦` 是成子过程，`注意` 是调配聚焦的机制；`注意向齐生` 可以作为 `做人注意` 支持 `做人`，但 `控制` 仍只允许作为局部注意机制，不是 `做人` 的目标。

## 图

```mermaid
%% Human alignment construction DAG. Direction: predecessor --> constructed stage.
flowchart TB
  heaven["天\n一元之总显"]:::heaven
  world["世界"]:::world
  self["自身"]:::world
  focus["聚焦\n成子过程"]:::focus
  child["子\n聚焦所成之项"]:::child
  formedChild["聚焦成子"]:::child
  heavenChild["天之子\n天中经聚焦成子而成"]:::heavenChild
  awareness["意识\n意识此天之子"]:::focus
  human["人\n天之子，并意识此天之子"]:::human
  intention["意图\n意图层面"]:::intention
  align["向齐生\nalignment"]:::align
  doing["做人\n意图向齐生"]:::doing
  control["控制 / control\n非做人目标"]:::control

  world --> focus
  self --> focus
  focus --> child
  focus --> formedChild
  child --> formedChild
  heaven --> heavenChild
  formedChild --> heavenChild
  heavenChild --> awareness
  heavenChild --> human
  awareness --> human
  human --> intention
  intention --> align
  intention --> doing
  align --> doing
  control -.->|排除| doing

  classDef heaven fill:#111827,stroke:#111827,color:#ffffff,stroke-width:2px;
  classDef world fill:#f8fafc,stroke:#64748b,color:#0f172a;
  classDef focus fill:#ecfeff,stroke:#0891b2,color:#164e63;
  classDef child fill:#eef2ff,stroke:#4f46e5,color:#312e81,stroke-width:2px;
  classDef heavenChild fill:#f0fdf4,stroke:#16a34a,color:#14532d,stroke-width:3px;
  classDef human fill:#fefce8,stroke:#ca8a04,color:#422006,stroke-width:2px;
  classDef intention fill:#eef2ff,stroke:#4f46e5,color:#312e81;
  classDef align fill:#f0fdf4,stroke:#16a34a,color:#14532d,stroke-width:2px;
  classDef doing fill:#fdf2f8,stroke:#db2777,color:#831843,stroke-width:3px;
  classDef control fill:#fef2f2,stroke:#dc2626,color:#7f1d1d,stroke-dasharray: 5 5;
```

## 边界

这不是经验心理学证明。它证明的是体系内定义：当我们使用 `人/做人/alignment` 这些项时，它们的正式依赖关系如上；控制被排除在 `做人` 的目标定义之外。
