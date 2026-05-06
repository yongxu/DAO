# 間/Jian 本体三联架构

对应 Lean 模块：[`Foundation/Jian/JianOntology.lean`](../Foundation/Jian/JianOntology.lean)。

本节把 Tier 1 本体词汇压缩为 14 字：

```text
三本：物 動 間
三显：位 場 際
三征：幾 勢 機
闸口：開 閉
合成：網 體 流
```

Lean 层保持既有名册的规范化原则：已经登记为简体 canonical atom 的概念继续使用既有 `AtomName`，繁体写法由 glyph 层覆盖。因此 `動/間/場/幾/勢/機/開/閉` 等作为文本面写法进入 `Tier1Term`，但不会被拆成与 `动/间/场/几/势/机/开/闭` 竞争的第二套本体节点。`際/網/體` 当前作为 glyph-only Tier 1 术语保留，尚不冒充已有 canonical atom。

## 三本

`OnticRoot` 给出不可再分的三本：

| 本 | Lean 构造 | 含义 | 维度征 |
|---|---|---|---|
| 物 | `.wu` | 离散个体性 | 0 维倾向 |
| 動 | `.dong` | 连续过程性 | n 维倾向 |
| 間 | `.jian` | 关系结构性 | 拓扑倾向，无内在度量 |

三本不是三类事物，而是同一现象被观察时显出的三个不可还原面向。

## 三显

`Manifestation.visibleRoots` 与 `Manifestation.bracketedRoot` 形式化三显：

| 显 | 相交 | 括除 | Lean 定理 |
|---|---|---|---|
| 位 | 物 ∩ 間 | 動 | `wei_is_wu_jian_with_dong_bracketed` |
| 場 | 動 ∩ 物 | 間 | `chang_is_dong_wu_with_jian_bracketed` |
| 際 | 間 ∩ 動 | 物 | `ji_is_jian_dong_with_wu_bracketed` |

核心约束：

```lean
every_manifestation_brackets_absent_root
```

即每一显只显出两本，第三本被括除但不缺席。

### 散文读法（自 史料/间本体论_元三相与场修订稿.md §二）

- **位** 是物在間中获得指认——没有关系背景，物不显为位。
- **場** 是動在物中获得载体——没有可被作用者，動无所铺陈。
- **際** 是間在動中获得现身——没有过程，間不被经验，只是抽象拓扑。

「相交」与「括除」是同一显化的两面：相交者被显出，括除者不缺席而是结构性地不可见。Lean 之 `bracketedRoot` 字段刻画后者。

## 三征与開閉

`DynamicMark.ofManifestation` 规定：

```text
位 -> 幾
場 -> 勢
際 -> 機
```

`Gate.result` 规定二值闸口：

```text
幾開 -> 生    幾閉 -> 灭
勢開 -> 成    勢閉 -> 反
機開 -> 转    機閉 -> 守
```

Lean 中的 `gate_is_only_open_or_closed` 说明 `開/閉` 是此层唯一二值算子；`gate_results` 给出三征经闸口落到事件的完整表。

### 0 维坍缩说明（自 史料/间本体论_元三相与场修订稿.md §三）

位的静面不是「缺数据」，而是结构声明：位是二分结构的递归终点。0 维不容许「持存的」与「变迁的」两端拉开，所以由幾直接承担——

```text
勢 = 幾 沿连续介质铺开
機 = 幾 沿拓扑路由汇聚
```

於是 `開/閉` 不是另加之原语，而是 0 维坍缩后唯一活下来的算子；它即是幾抵达极限的那一刻。

## 合成与回授

`CompositeForm.parts` 给出三种拓扑合成：

| 合成 | 由何组装 | 形态 |
|---|---|---|
| 網 | 位 + 際 | 关系图 |
| 體 | 位 + 場 | 实体 |
| 流 | 場 + 際 | 过程 |

`CompositeForm.feedbackTarget` 给出回授：

```text
網 -> 位
體 -> 場
流 -> 際
```

`network_composition_arrangement_not_unique` 明确合成不是可逆还原：同样的 `位 + 際` 可以有不同 arrangement，因此从显化原子到合成层会增加结构信息。

### 合成是涌现的，不是给定的（自 史料/间本体论_元三相与场修订稿.md §五）

三显不能合并为一个更底层原语，但可以组装出更高层结构。任何具体现象都是 `網/體/流` 这三种合成在不同尺度上的叠加。「不可逆」的具体含义是：给定位与際，不唯一决定一个網——连接方式（arrangement）本身带来新增信息，故不可由合成结果回推合成方式。这是 `network_composition_arrangement_not_unique` 之散文动机。

## 四条通路

```mermaid
flowchart TB
  wu["物"]:::root
  dong["動"]:::root
  jian["間"]:::root

  wei["位 = 物 ∩ 間\n括除 動"]:::manifest
  chang["場 = 動 ∩ 物\n括除 間"]:::manifest
  ji["際 = 間 ∩ 動\n括除 物"]:::manifest

  small["幾"]:::dynamic
  trend["勢"]:::dynamic
  pivot["機"]:::dynamic
  gate["開 / 閉"]:::gate

  network["網"]:::composite
  body["體"]:::composite
  flow["流"]:::composite

  wu --> wei
  jian --> wei
  dong --> chang
  wu --> chang
  jian --> ji
  dong --> ji

  wei <--> ji

  wei --> small
  chang --> trend
  ji --> pivot
  small --> gate
  trend --> gate
  pivot --> gate

  wei --> network
  ji --> network
  wei --> body
  chang --> body
  chang --> flow
  ji --> flow

  network -.回授.-> wei
  body -.回授.-> chang
  flow -.回授.-> ji

  classDef root fill:#fefce8,stroke:#ca8a04,color:#422006,stroke-width:2px;
  classDef manifest fill:#ecfeff,stroke:#0891b2,color:#164e63,stroke-width:2px;
  classDef dynamic fill:#fff7ed,stroke:#ea580c,color:#7c2d12;
  classDef gate fill:#fef2f2,stroke:#dc2626,color:#7f1d1d,stroke-width:2px;
  classDef composite fill:#eef2ff,stroke:#4f46e5,color:#312e81,stroke-width:2px;
```

四条通路在 Lean 中分别对应：

- 显化互生：`mutuallyManifest`、`wei_ji_mutually_manifest`
- 显化合成：`Composes`、`composition_table`
- 动征驱动：`Drives`、`dynamic_drive_table`
- 合成回授：`feedback_table`

## 自指性

`SelfReferenceWitness` 把本架构本身登记为自身描述结构的一个实例：

```text
它是 間 结构；
被运用时为 動；
落在 場 中；
生成 位；
经由 際 连接；
织成 網。
```

对应定理：

```lean
ontology_is_instance_of_its_own_shape
```

这就是此处的 homoiconicity：理论不是站在外部描述现象，而是所描述结构的一个实例。
