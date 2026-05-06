# 单根回归：一元生成完备工程计划

## 概念解释

当前体系有三种不同的图，不能混用：

- `ConceptDAG` 是名册依赖图，方向是“字根/依赖项 -> 生成项”。它用于检查所有登记项是否有根、有型、有依赖，因此天然会有很多字根入口。
- `ConstructionDAG` 是内容构造主干，说明如何从 Γ 当前论域、三本（物/動/間）、三显（位/場/際）、三征（幾/勢/機）、開閉闸口、拓扑合成、行动等环节构造到生生不息论。
- `MonadDAG` 是单根生成图，目标是证明所有正式项都能回到唯一根 `一元`。

`一元` 不是 `一`，也不是 `元`，也不是 `一元论`。

- `一` 和 `元` 是登记单字。
- `一元论` 是关于根的理论表达。
- `一元` 是唯一根节点，是所有面、字、概念、模型、证明、claim 的生成源。

“面”不是多个本体根，而是一元的不同投影。首版采用十二面：

```text
文面、物面、生面、理面、心面、人面、模面、审校面、价值面、证明面、注意面、真理面
```

单根结构如下：

```text
一元
  -> 面
    -> 核心单字
      -> 派生单字 / 登记单字
        -> 复合概念 / 原始算子 / 递归项 / 待校项 / 构造阶段
          -> claim / 模型判准 / 案例结论
```

因此，完整性 claim 改为：

> 凡进入生生不息论 Lean 正式体系者，必须有一条有限路径回到唯一根 `一元`。

这不是哲学真理的无前提证明，而是形式生成秩序的完备性证明。

## 本轮补入：天、子、天之子、人

本轮把“人”的定义从早期的“世界对自身的聚焦”改成更严格的生成链：

```text
天
  -> 聚焦
    -> 子
      -> 聚焦成子
        -> 天之子
          -> 人
```

其中：

- `天`：先作为已登记生成项，字根为单字 `天`，并归入单根体系。
- `子`：不是孤立实体，而是 `聚焦` 所成之项。
- `聚焦成子`：明确登记为 `聚焦 + 成子` 的复合生成项。
- `天之子`：登记为 `天 + 聚焦成子`，表示“天中经聚焦成子而成之项”。
- `人`：登记依赖从 `世界 + 自身 + 聚焦 + 意识` 收紧为 `天之子 + 意识`。

因此，人的形式回归路径不是停在复词：

```text
人 -> 天之子 -> 聚焦成子 -> 子 -> 聚焦 -> 单字/面 -> 一元
人 -> 意识 -> 单字/面 -> 一元
```

Lean 中对应证明在 `formal/SSBX/Foundation/HumanAlignment.lean`：

```lean
child_is_focus_formed
heaven_child_is_heaven_focus_formed_child
human_returns_to_heaven_child_with_awareness
```

## 工程实现

新增模块：

```text
formal/SSBX/Foundation/MonadRoot.lean
```

该模块定义：

- `Face`：十二个一元之面。
- `CoreAtom`：压缩后的核心单字层，当前把 221 个登记单字收束到 43 个核心单字。
- `MonadNode`：单根 DAG 的节点类型，包括 root、face、core、atom、formal、claim。
- `atomPrimaryFace`：每个 `AtomName` 的主归面，使用全模式匹配；新增单字但未归面时 Lean 会失败。
- `atomExtraFaces`：多义字或跨面字的额外归面，如 `生`、`开`、`正`、`真`、`道`。
- `atomCore`：每个 `AtomName` 到一个 `CoreAtom` 的全映射；新增单字未接入核心层时 Lean 会失败。
- `FormalNode`：非单字正式项，包括 generated、primitive、recursive、pending。
- `formalAtoms`：每个正式项的单字锚点；若某正式项没有单字锚点，`formal_primary_atom_mem` 会失败。
- `constructionPrimaryAtom`：每个高层构造阶段的单字锚点，例如 `普遍证明理` 回 `证`，模型充分性回 `模`，真理核心回 `真`。
- `claimPrimaryFormal`：每个 `ClaimId` 对应的正式项；新增 claim 未接入时 Lean 会失败。
- `claimPrimaryAtom`：每个 claim 通过其正式项再返回一个单字锚点。
- `StructureNode`：统一表示 formal、construction、claim 三类结构节点，并证明所有结构先回单字，再回 `一元`。
- `DirectEdge` 与 `Reachable`：定义单根路径。

核心证明：

```lean
unique_root
all_faces_from_root
all_core_atoms_reachable_from_root
all_atoms_have_face
all_atoms_reachable_from_root
all_atoms_return_through_core
all_symbols_reachable_from_root
all_claims_reachable_from_root
all_construction_nodes_reachable_from_root
no_unrooted_symbol
ssbx_reachable_from_root
near_root_constraint
monad_dag_acyclic
structures_return_single_atom
structures_return_atom_and_root
```

其中：

- `unique_root` 证明 `一元` 是 `MonadDAG` 中唯一没有入边的节点。
- `all_symbols_reachable_from_root` 证明所有 `Symbol` 都能回根。
- `all_atoms_return_through_core` 证明所有登记单字都先通过核心单字，再回 `一元`。
- `all_claims_reachable_from_root` 证明所有核心 claim 都能回根。
- `structures_return_single_atom` 证明每个 formal、construction、claim 结构都有单字返回点。
- `structures_return_atom_and_root` 证明每个结构都先返回单字，且该单字已经可回 `一元`。
- `near_root_constraint` 证明距离根不超过 2 的节点只能是根、面或核心单字。
- `monad_dag_acyclic` 用距离严格递增证明无环。

## 生成图

新增脚本：

```text
scripts/generate_monad_dag.py
scripts/render_monad_dag.sh
```

输出：

```text
formal/SSBX/MonadDAG.md
formal/SSBX/MonadDAG.mmd
formal/SSBX/MonadDAG.svg
```

图的视觉结构必须满足：

- 只有一个入度为 0 的节点：`一元`。
- 第一层只能是 `Face`。
- 第二层是 `CoreAtom` 核心单字。
- 第三层是 `AtomName` 登记单字。
- 第四层是 `GenName`、`PrimName`、`RecName`、`PendingName`。
- 第四层同时包括高层 `ConstructionId`，例如 Γ 当前论域、三本、三显、三征、開閉闸口、普遍证明理、审校核心、模型充分性核心。
- 第五层是 `ClaimId`，并有直接“回字”边返回单字锚点。

`ConceptDAG` 继续保留，但它只说明名册依赖完整性，不再承担单根证明。

## 验证命令

```bash
cd /Users/ren/repos/生生不息
lake env lean formal/SSBX/Foundation/MonadRoot.lean
lake build
python3 scripts/generate_monad_dag.py
scripts/render_monad_dag.sh
```

## 验收标准

- `lake build` 通过。
- 新增 `AtomName` 如果没有补 `atomPrimaryFace`，构建失败。
- 新增 `AtomName` 如果没有补 `atomCore`，构建失败。
- 新增 `PrimName`、`RecName`、`PendingName` 如果没有补单字锚点，构建失败。
- 新增 `ConstructionId` 如果没有补 `constructionPrimaryAtom`，构建失败。
- 新增 `ClaimId` 如果没有补 `claimPrimaryFormal`，构建失败。
- `MonadDAG.svg` 视觉上是 `一元 -> 面 -> 核心单字 -> 派生单字 -> 正式项/构造阶段 -> claim`。
- `生生不息论` 有定理 `ssbx_reachable_from_root` 证明可回到 `一元`。
