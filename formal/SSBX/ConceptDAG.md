# Concept DAG / 概念有向无环图

方向约定：`字根 / 依赖项 --> 生成项 / 递归项`。

边界声明：`ConceptDAG` 是名册依赖图，不是单根生成证明；单根证明以 `MonadDAG` 和 `Foundation/MonadRoot.lean` 为准。

## 完整性口径

这次的“完整图”不是摘要图，而是覆盖 Lean 名册中全部登记项：

- `AtomName`：333 个
- `GenName`：134 个
- `PrimName`：5 个
- `RecName`：13 个
- `PendingName`：6 个
- 总节点：491 个
- 依赖边：458 条
- 环检测：无环，可作为 DAG 阅读

## 核心摘要图

这张只用于说明主干，不声称完整。

```mermaid
%% Reading-oriented summary. Not complete; use ConceptDAG.complete.mmd for full registry coverage.
flowchart TB
  subgraph W["物面 / 格物"]
    物["物｜字根"]:::atom
    面["面｜字根"]:::atom
    格["格｜字根"]:::atom
    域["域｜字根"]:::atom
    验["验｜字根"]:::atom
    格物["格物｜生成"]:::generated
    经验校准["经验校准｜待校"]:::pending
  end

  subgraph M["模 / 科学评价"]
    模["模｜字根"]:::atom
    评["评｜字根"]:::atom
    价["价｜字根"]:::atom
    科["科｜字根"]:::atom
    学["学｜字根"]:::atom
    可校["可校｜生成"]:::generated
    互证["互证｜生成"]:::generated
    审校不败["审校不败｜生成"]:::generated
  end

  subgraph F["形式证明 / CIC 位置"]
    逻["逻｜字根"]:::atom
    辑["辑｜字根"]:::atom
    构["构｜字根"]:::atom
    造["造｜字根"]:::atom
    纳["纳｜字根"]:::atom
    证["证｜字根"]:::atom
    明["明｜字根"]:::atom
    算["算｜字根"]:::atom
    理["理｜字根"]:::atom
    CIC模["CIC / 归纳构造演算｜外部模"]:::external
  end

  subgraph C["核心价值递归"]
    开["开｜递归"]:::recursive
    闭["闭｜递归"]:::recursive
    正["正｜递归"]:::recursive
    邪["邪｜递归"]:::recursive
    共开["共开｜递归"]:::recursive
    坏["坏｜递归"]:::recursive
    义["义｜递归"]:::recursive
    善["善｜递归"]:::recursive
    仁["仁｜递归"]:::recursive
    道["道｜递归"]:::recursive
    真["真｜递归"]:::recursive
    真道["真道｜生成"]:::generated
  end

  物 --> 格物
  格 --> 格物
  格物 --> 经验校准
  域 --> 经验校准
  验 --> 经验校准

  模 --> 可校
  评 --> 可校
  价 --> 可校
  科 --> 可校
  学 --> 可校
  审["审｜字根"]:::atom --> 审校不败
  校["校｜字根"]:::atom --> 审校不败
  败["败｜字根"]:::atom --> 审校不败
  可校 --> 审校不败
  互证 --> 审校不败

  逻 --> CIC模
  辑 --> CIC模
  构 --> CIC模
  造 --> CIC模
  纳 --> CIC模
  证 --> CIC模
  明 --> CIC模
  算 --> CIC模
  理 --> CIC模
  CIC模 --> 可校

  经验校准 --> 开
  审校不败 --> 正
  开 --> 正
  闭 --> 邪
  开 --> 共开
  闭 --> 坏
  正 --> 义
  义 --> 善
  共开 --> 道
  坏 --> 道
  审校不败 --> 真
  真 --> 真道
  道 --> 真道

  可校 --> 真

  classDef atom fill:#f8fafc,stroke:#64748b,color:#0f172a;
  classDef generated fill:#ecfeff,stroke:#0891b2,color:#164e63;
  classDef recursive fill:#fff7ed,stroke:#ea580c,color:#7c2d12;
  classDef pending fill:#fef2f2,stroke:#dc2626,color:#7f1d1d;
  classDef external fill:#f5f3ff,stroke:#7c3aed,color:#3b0764;
```

## 完整图文件

- [ConceptDAG.complete.mmd](./ConceptDAG.complete.mmd)：完整登记图，所有名册节点都显示，包括孤立字根、原始算子、待校项。
- [ConceptDAG.layered.mmd](./ConceptDAG.layered.mmd)：完整分层图，按字根、生成项、递归项、原始算子项、待校项分组。
- [ConceptDAG.full.mmd](./ConceptDAG.full.mmd)：同完整登记图，保留旧文件名用于兼容。

## 读法

- `atom`：单字根，不再向下拆。
- `generated`：由字根或其他生成项合成。
- `primitive`：模型/度量/算子接口，不由字元生成。
- `recursive`：价值/真理类递归谓词，需要三值、不动点或外部审校语义。
- `pending`：经验或模型项，不能冒称已真。
- `external`：说明性外部对象，例如 CIC；它参与摘要说明，但不是当前名册中的生成项。

## 注意

这张图证明的是“名册依赖形状可作为 DAG 展示”。它不是额外哲学证明；哲学真理仍由 `Truth` 和 `Model` 层的公理账本与模型充分性承载。
