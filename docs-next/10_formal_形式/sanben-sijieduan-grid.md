# 三本 × 四阶段：12 格内容映射

> 状态：v3 (2026-05-11) — 与 main @ 1c76a55 对齐。本文是 R₃ trigram-level 的 12 格内容映射；它**正交于** v2.1 R-hierarchy 之 R₄ Mian = Ben × Zheng (16) — 后者是 (Z/2)⁴ algebraic spine 的 first-class 层，详 [yi-RO-hierarchy.md §3.4](yi-RO-hierarchy.md#34-r₄--面-mian-) 与 [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean)。
> 作用：替代旧"12 面"读法。"面"只是这 12 个的**集合名** —— 12 个格子本身已经有更准确的名字（物 / 注意 / 模 / 文 / 生 / 心 / 理 / 价值 / 人 / 审校 / 证明 / 真理）。本文写出 (1) 三本 各自意涵 + (2) 四阶段 各自意涵 + (3) 12 个格子的四语对照 + (4) 行/列/对角等所有内部关系。
> 配套：[layer-character-map.md](layer-character-map.md) / [layer-axis-graph.md](layer-axis-graph.md) / [`LayerCharacterMap.lean`](../../formal/SSBX/Text/LayerCharacterMap.lean) / [yi-RO-hierarchy.md](yi-RO-hierarchy.md) (R₀..R₈ doctrine)。
> 形式锚：[`JianOntology.lean`](../../formal/SSBX/Foundation/Jian/JianOntology.lean)（三本）+ [root-layer-map.md §0](root-layer-map.md)（四阶段）+ [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean)（R₄ Mian = (Z/2)⁴ next-up enrichment）。

## 0a. 与 R₄ Mian 的关系（v3 加注）

12 = 3 × 4（三本 × 四阶段）是 R₃ trigram-level 之内容映射；它**不是** R₃ algebraic 群 8 = (Z/2)³ 的 group quotient，而是 trigram 之**含义投影**。

下一阶 algebraic spine 是 R₄ Mian = Ben × Zheng = (Z/2)² × (Z/2)² = (Z/2)⁴ = 16，由 [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) 形式落地。Mian 之 16 命：
- Ben (4 substrate) = zong-fixed trigrams = (Z/2)² (本 = 物 / 動 / 間 / 事，与本文三本 + "事" 一致)
- Zheng (4 mark) = zong-mobile trigrams = (Z/2)² (征 = 幾 / 勢 / 機 / 時)

所以本文 12 格是 R₃ trigram 之 内容投影; R₄ Mian 16 命是 R₃ trigram 之 zong-orbit 4+4 算子拆分; 二者在 trigram 上**正交但相容** —— 详 [position-operator-tree.md §3](position-operator-tree.md) 与 [yi-RO-hierarchy.md §3.4](yi-RO-hierarchy.md#34-r₄--面-mian-)。

---

## 0. 全局生成式

```
                          一元 (root)
                              │
                              ▼
        ┌─────────────────────┴─────────────────────┐
        │                                           │
   ─三本投射─→                              ─四阶段投射─→
        │                                           │
        ▼                                           ▼
  {物, 動, 間}                            {差, 识, 间, 事}
        │                                           │
        └────────────── × (笛卡尔积) ──────────────┘
                              │
                              ▼
                ┌──────────┬──────────┬──────────┬──────────┐
                │  (物,差) │  (物,识) │  (物,间) │  (物,事) │
                │   = 物    │  = 注意  │   = 模    │   = 文    │
                ├──────────┼──────────┼──────────┼──────────┤
                │  (動,差) │  (動,识) │  (動,间) │  (動,事) │
                │   = 生    │   = 心    │   = 理    │  = 价值  │
                ├──────────┼──────────┼──────────┼──────────┤
                │  (間,差) │  (間,识) │  (間,间) │  (間,事) │
                │   = 人    │  = 审校  │  = 证明  │  = 真理  │
                └──────────┴──────────┴──────────┴──────────┘
                              │
                          12 = 3 × 4
                          (可证 cardinality, not 设计常数)
```

---

# 第一部分：三本（内容根）

三本是从 一元 投射出的**三个内容范畴**——回答"我们在谈什么样的东西"。形式来自 [`JianOntology.lean`](../../formal/SSBX/Foundation/Jian/JianOntology.lean) 的 `JianRoot` inductive。

## 1.1 物 (wu) — 实在的承载者

**核心定义**：可被定位、承载状态、可作为变化所栖之物的项。

| 系统 | 名 |
|---|---|
| 古文 | 物 / 体 / 实 / 形 |
| 当代汉语 | 实体 / 物体 / 客体 |
| 英文 | substantive / entity / individual |
| 形式逻辑 | term / individual / domain element |
| 经典出处 | 《周易·乾》"万物资始"；《老子》"实其腹"；Aristotle *substantia* |

**判别试金石**：能问"它在哪/它是什么"的就是 物。
- 一块石头 ✓ — 在某处的承载者
- "运动" ✗ — 不是承载者，是过程（属 動）
- "之间" ✗ — 不是承载者，是关系（属 間）

**形式上**：在 [first-order logic](https://en.wikipedia.org/wiki/First-order_logic) 中是论域 \|M\| 的一个元素；在 [type theory](https://en.wikipedia.org/wiki/Type_theory) 中是某个 sort 的 inhabitant。

## 1.2 動 (dong) — 连续的过程

**核心定义**：变化、推进、生成、流转本身——不依赖某物存在而存在的"过程性"。

| 系统 | 名 |
|---|---|
| 古文 | 動 / 行 / 化 / 流 |
| 当代汉语 | 过程 / 变化 / 运动 |
| 英文 | processual / process / becoming |
| 形式逻辑 | reduction / transition / derivation step |
| 经典出处 | 《周易·系辞》"生生之谓易"；《老子》"道生一"；Heraclitus *panta rhei* |

**判别试金石**：能问"它怎么发生 / 多长时间"的就是 動。
- "燃烧" ✓ — 是过程
- "火焰" ✗ — 是物（承载燃烧的实体）
- "燃烧之间的关联" ✗ — 是 間

**形式上**：在 [operational semantics](https://en.wikipedia.org/wiki/Operational_semantics) 中是状态转移 σ → σ′；在 [proof theory](https://en.wikipedia.org/wiki/Proof_theory) 中是推理步骤；在 [rewriting system](https://en.wikipedia.org/wiki/Rewriting) 中是 rewrite step →ᵦ。

## 1.3 間 (jian) — 关系的空间

**核心定义**：项与项之间的 interval / gap / coupling / dependency；既不是项也不是过程，是**项之相关性**本身。

| 系统 | 名 |
|---|---|
| 古文 | 間 / 际 / 关 / 緣 |
| 当代汉语 | 关系 / 关联 / 间隔 |
| 英文 | relational / inter-being / between-ness |
| 形式逻辑 | relation R ⊆ A × B / morphism |
| 经典出处 | 《周易·系辞》"乾坤其易之缊邪"；Buber *I-Thou*；relational ontology (Whitehead) |

**判别试金石**：能问"它把谁和谁连/分开"的就是 間。
- "父子之伦" ✓ — 把父和子连接
- "父" 或 "子" ✗ — 是物
- "教育的过程" ✗ — 是動

**形式上**：在 [relational algebra](https://en.wikipedia.org/wiki/Relational_algebra) 中是 binary relation；在 [graph theory](https://en.wikipedia.org/wiki/Graph_theory) 中是 edge；在 [category theory](https://en.wikipedia.org/wiki/Category_theory) 中是 morphism。

## 1.4 三本之间的关系

三本不是平行无关的并列，而是有内在张力：

```
       物 ──────依赖──────→ 動
       ↑                     ↓
       │                     │
       │    間 ←─构成 / 桥接─┘
       │
       └──── 間 也建构物的"是其所是"
```

### 1.4.1 物 与 動

- **物之所以稳定**：靠 動 的反复（重复某模式才"是同一物"）
- **動之所以可定位**：靠 物 的承载（某事必发生在某物身上）
- **形式上**：在 process algebra 里是 (state, transition) 的对偶；在 category theory 里是 (object, morphism) 的双重性

### 1.4.2 動 与 間

- **動需要 間**：变化必发生在某关系之中（A 变到 B 已预设 A 与 B 之间有"可变换"关系）
- **間刻画 動**：哪些过程可发生由哪些关系预设决定
- **形式上**：transition system = (states, transitions, relation between transitions)；动力系统的"轨道"是 動 在 間 上的展开

### 1.4.3 物 与 間

- **間需要 物**：关系总是某些物之间的（empty relation 是退化情形）
- **物被 間 个体化**：A 之所以是 A 而不是 B，靠它的关系网与众不同（Leibniz' principle of identity of indiscernibles）
- **形式上**：graph = (V, E)，V 物 与 E 間 互为前提

### 1.4.4 三本不可还原性

虽然三者互为前提，但**任何一个不能完全还原为其它二者**：
- 把 物 还原为关系（structuralism 的极端立场）→ 失去"承载者"，所有关系飘空
- 把 動 还原为物的状态序列 → 失去"流"，连续性变成离散点
- 把 間 还原为物的属性 → 失去"之间"的本体性，回到唯名论

所以 [`JianOntology.lean`](../../formal/SSBX/Foundation/Jian/JianOntology.lean) 把 `JianRoot` 设为 3 构造子的 inductive，是**三足鼎立**的形式承诺。

---

# 第二部分：四阶段（本体读法）

四阶段是"差异如何成为可说之物"的四级提升。来自 [root-layer-map.md §0](root-layer-map.md) 的本体读法。

## 2.1 差 (cha) — raw distinction

**核心定义**：尚未被分辨、尚未被命名的最原始的"差"——"这与那"的最纯粹的对待。

| 系统 | 名 |
|---|---|
| 古文 | 差 / 异 / 别 / 分 |
| 当代汉语 | 差异 / 区别 / 分别 |
| 英文 | distinction / differentiation / différance |
| 形式逻辑 | bit / atomic difference / Yao polarity |
| 经典出处 | 《周易》"太极生两仪"；Saussure 之 *différence*；Spencer-Brown *Laws of Form* "draw a distinction" |

**形式锚**：在 [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) 中是 `Yao = {yang, yin}` 的最原始 bit。差 是 R1 之事。

**关键性质**：差 还没"被识"——只是"在那里"。还没有命名、还没有指称、还没有判断。是 ontology 的零点。

## 2.2 识 (shi) — marked / nameable

**核心定义**：差 被指认、可标记、可命名——"这一差异是这个差异，那一差异是那个差异"。开始有了 reference。

| 系统 | 名 |
|---|---|
| 古文 | 识 / 名 / 指 / 标 |
| 当代汉语 | 标识 / 命名 / 识别 / 指称 |
| 英文 | marking / nameable / addressed / individuated |
| 形式逻辑 | reference / variable binding / name introduction |
| 经典出处 | 《老子》"无名天地之始，有名万物之母"；Frege 之 *Sinn/Bedeutung*；Saul Kripke *naming and necessity* |

**形式锚**：[`AtomName`](../../formal/SSBX/Roster.lean) inductive 的每一个登记字——是"已被识"的具体实现。识 是 M-line 之事。

**关键性质**：识 把"无差别的差"变成"有指称的差"。这是从纯 ontology 到 epistemology 的桥。

## 2.3 间 (jian) — structured

**核心定义**：已被识的差**互相之间**有了结构、相依、相接、相对——开始构成"系统"或"模型"。

| 系统 | 名 |
|---|---|
| 古文 | 間 / 联 / 结 / 配 |
| 当代汉语 | 结构 / 关系 / 相干 / 系统 |
| 英文 | structured / inter-related / systematic |
| 形式逻辑 | structure / interpretation / system |
| 经典出处 | 《周易》"方以类聚，物以群分"；Aristotle 的 *taxis*；structuralism (Lévi-Strauss) |

**形式锚**：[`JianOntology.lean`](../../formal/SSBX/Foundation/Jian/JianOntology.lean) 的 三本 / 三显 / 三征 整体——是已被识的差进入"关系空间"。间 是 内容线 之事。

**关键性质**：间 把"孤立可识的差"组织成"互联的系统"。这是从语词到语法的桥。

**注意**：阶段名"间"与本体名"間"用同一字（间）——这不是巧合：本体的 間 在自身阶段（识→间）下达到自我表达。

## 2.4 事 (shi-event) — enacted / actualized

**核心定义**：已结构的关系**在某一时态、位点、变换中真正发生**——不只是抽象有效，而是 ledger 上有一笔。

| 系统 | 名 |
|---|---|
| 古文 | 事 / 行 / 历 / 用 |
| 当代汉语 | 事件 / 发生 / 实现 / 落地 |
| 英文 | enacted / actualized / instantiated / event |
| 形式逻辑 | trace / execution / event / commitment |
| 经典出处 | 《周易》"显诸仁，藏诸用"；Whitehead 的 *actual occasion*；event-driven semantics |

**形式锚**：[`Cell256`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) 之间的 transition —— 是"事之发生"的最小可审计形态。事 是 R₈ 之事（v2.1 重号；旧 v1 称 R5；Cell192 已删，由 Cell256 = Hexagram × Shi V₄ 替代）。

**关键性质**：事 把"系统层面有效的关系"变成"时空中真实发生的事件"。这是从结构到历史的桥。

## 2.5 四阶段之关系

四阶段不是平起平坐的列举——是一条**单调上升**的认识链：

```
差 ──识─→ 识  ──结构化─→ 间  ──落地─→ 事
 │                                       │
 │    pre-conceptual    ↑↑↑     post-conceptual
 │
 └ ontological zero    fully-actualized ┘
```

### 2.5.1 单调升级

每一阶段**严格包含**前一阶段的所有内容：

- `识 ⊃ 差`：被识的必先有差
- `间 ⊃ 识`：被结构的必先被识
- `事 ⊃ 间`：被落地的必先被结构

反过来不行——许多差永远不被识，许多识永远不进入结构，许多结构永远不落地为事。

### 2.5.2 算子化

阶段间的提升对应**特定算子**：
- `差 → 识`：命名算子 (naming) — 形式上是 binding 操作
- `识 → 间`：模型化算子 (modeling) — 形式上是 product / pairing
- `间 → 事`：实例化算子 (instantiation) — 形式上是 evaluation / commitment

### 2.5.3 反向降级

也存在**降级算子**（每级降一阶）：
- `事 → 间`：抽象 (abstraction)
- `间 → 识`：解结构 (forgetting structure)
- `识 → 差`：去名 (un-naming, unmark)

每对升降算子大致互逆——但有信息损失方向（升级一般保 information，降级一般丢）。

### 2.5.4 与本体读法的对应

本体读法 ([root-layer-map.md §0](root-layer-map.md)) 的四阶段对应到 [`MonadDAG`](../../formal/SSBX/notes/MonadDAG.md) 的层次：

| 阶段 | 本体义 | DAG 锚 | 系统层 |
|---|---|---|---|
| 差 | 一处差异 | (R1) `Yao` | bit |
| 识 | 可命名 | (M3) `AtomName` | lexicon |
| 间 | 可结构化 | (内容线) 三本/三显/三征 | system |
| 事 | 可发生 | (R₈) `Cell256` transition | history |

---

# 第三部分：12 格名册（四语对照）

## 3.1 全表

| 坐标 | 名 | 古文 | 当代 | 英文 | 形式逻辑 |
|---|---|---|---|---|---|
| (物, 差) | **物** | 体 / 形 / 实 | 实体 / 物体 | entity / individual | term / individual constant |
| (物, 识) | **注意** | 注 / 凝 / 主 | 注意 / 聚焦 | attention / reference | variable binding / valuation |
| (物, 间) | **模** | 象 / 模 / 范 | 模型 / 结构 | model / schema | structure ⟨M, I⟩ / interpretation |
| (物, 事) | **文** | 文 / 辞 / 录 | 文本 / 文献 | text / corpus | wff / sequent / proof term |
| (動, 差) | **生** | 生 / 始 / 萌 | 生成 / 萌发 | genesis / emergence | production rule / rewrite step |
| (動, 识) | **心** | 心 / 感 / 知 | 感知 / 心智 | perception / cognition | judgment Γ⊢A / observable |
| (動, 间) | **理** | 理 / 法 / 致 | 推理 / 逻辑 | reasoning / inference | inference rule / deduction |
| (動, 事) | **价值** | 善 / 义 / 利 | 价值 / 评价 | value / utility | utility function / preference |
| (間, 差) | **人** | 人 / 伦 / 仁 | 人际 / 伦理 | inter-being / dyad | binary relation R(x,y) |
| (間, 识) | **审校** | 审 / 校 / 验 | 审查 / 校验 | verification / audit | type-check / model-check |
| (間, 间) | **证明** | 证 / 据 / 立 | 证明 / 论证 | proof / demonstration | derivation / proof term |
| (間, 事) | **真理** | 真 / 道 / 是 | 真理 / 实在 | truth / validity | M ⊨ φ / soundness |

## 3.2 四语 3×4 网格速览

### 古文（最简一字）

|  | 差 | 识 | 间 | 事 |
|---|---|---|---|---|
| 物 | 体 | 注 | 象 | 文 |
| 動 | 生 | 心 | 理 | 善 |
| 間 | 人 | 审 | 证 | 真 |

### 当代汉语（标准双字）

|  | 差 | 识 | 间 | 事 |
|---|---|---|---|---|
| 物 | 实体 | 注意 | 模型 | 文本 |
| 動 | 生成 | 感知 | 推理 | 价值 |
| 間 | 人际 | 校验 | 证明 | 真理 |

### 英文（canonical noun）

|  | raw | marked | structured | enacted |
|---|---|---|---|---|
| substantive | entity | reference | model | text |
| processual | genesis | perception | inference | value |
| relational | relation | verification | proof | truth |

### 形式逻辑（最近形式锚）

|  | raw distinction | nameable | structured | enacted |
|---|---|---|---|---|
| substantive | individual / term | reference / valuation | structure 𝓜 = ⟨M, I⟩ | wff / proof term |
| processual | derivation step / →ᵦ | judgment Γ⊢A | inference rule | utility function |
| relational | binary predicate R(x,y) | type-check / decide | proof tree | ⊨ / soundness |

---

# 第四部分：三行（每个 本 的演化）

每行展示一个 本 在四阶段下的完整演化曲线。

## 4.1 物 行：物 → 注意 → 模 → 文

**主题**：实体如何从生硬给出走到永久记录。

```
       (差)              (识)               (间)              (事)
       物 ───注意操作───→ 注意 ───模型化───→ 模 ───实例化───→ 文
   bare entity     attended-to     entity-in-relation   recorded entity
```

### 4.1.1 物 → 注意：从存在到被注意

- **算子**：注意算子（pick out / refer to）
- **古文**：物 → 凝（凝其神于此物）
- **形式上**：从 universe 元素 e ∈ \|M\| 提升到 reference v(x) = e
- **关键**：物本身不需要任何主体存在——但"注意到这个物"必有主体

**例**：
- 房间里有一把椅子（物，即使无人也存在）
- 我注意到那把椅子（注意，需主体）

### 4.1.2 注意 → 模：从被注意到结构化

- **算子**：建模算子（modeling / structuring）
- **古文**：凝 → 象（凝注于象，象则成模）
- **形式上**：从单点 reference 上升到 structure ⟨M, I⟩——多个 reference 互相关联
- **关键**：单独被注意的物还没结构；要有"关系网"才是模

**例**：
- 椅子（被注意）+ 桌子（被注意）+ "椅围桌"（关系）= 餐厅模型
- 几个变量 + 它们之间的方程 = 数学模型

### 4.1.3 模 → 文：从结构化到永久记录

- **算子**：实例化 / 文字化算子（commit to text）
- **古文**：象 → 文（成象在天，垂文于地）
- **形式上**：从 abstract structure 实例化为 well-formed expression
- **关键**：模可以是抽象的、未写下的；文是 commit 到 ledger 的具体记号

**例**：
- 牛顿力学（模）→ 《自然哲学的数学原理》（文）
- 数据 schema（模）→ JSON 文档（文）

### 4.1.4 物 行的整体走向

物 行 是**实体的物化路径**——从"存在"到"被注意"到"被理解"到"被记录"。这是西方 ontology 主流（substance ontology）的标准发展曲线：从 *ousia* 到 *eidos* 到 *logos*。

---

## 4.2 動 行：生 → 心 → 理 → 价值

**主题**：变化如何从原始萌动走到伦理判断。

```
       (差)              (识)               (间)              (事)
       生 ───感知操作───→ 心 ───规律化───→ 理 ───落地评判───→ 价值
   raw genesis    sensed change    logic of process     judged event
```

### 4.2.1 生 → 心：从涌动到被感

- **算子**：感受算子（sense / perceive）
- **古文**：生 → 感（生有感，感在心）
- **形式上**：从 derivation step 提升到 judgment Γ ⊢ A——变化变成可宣告的事态
- **关键**：变化本身不需要被感受；但要进入认识就必须先被某主体感

**例**：
- 沼气在自燃（生，无感）
- 我感到温度上升（心，有感）
- 程序状态从 σ 转到 σ′（生）→ 我观察到栈 +1（心，observable）

### 4.2.2 心 → 理：从感到规律

- **算子**：归纳/演绎算子（reason about）
- **古文**：感 → 理（感而通之，则有理）
- **形式上**：从 single judgment 上升到 inference rule —— 多个 judgment 间的连接
- **关键**：单次感知还不是理；多次感知中找出可重复的关联才是理

**例**：
- 多次观察到太阳东升（多个 心 / 感知）→ 万有引力定律（理）
- 多次执行某算法（动作 sequence）→ 算法的 invariant（推理）

### 4.2.3 理 → 价值：从规律到伦理

- **算子**：评价算子（valuate / judge）
- **古文**：理 → 善（理而后能别善恶；《大学》"格物致知诚意正心"链）
- **形式上**：从 inference rule 转为 utility/preference function——客观规律加上主体偏好
- **关键**：理本身是 value-free 的（"事实如何"）；价值是把理对接到"应当如何"

**例**：
- 经济学规律（理）→ 政策评价（价值）
- 算法可行性（理）→ 算法是否伦理（价值，比如歧视性 ML 模型）

### 4.2.4 動 行的整体走向

動 行是**过程的伦理化路径**——从"发生"到"被感"到"被律"到"被判"。这是道德哲学主流（特别是儒家与德性伦理）的发展曲线：《大学》的 "格物→致知→诚意→正心" 大致就是 生→心→理→价值 的升华。

---

## 4.3 間 行：人 → 审校 → 证明 → 真理

**主题**：关系如何从具体人际走到永恒真理。

```
       (差)              (识)               (间)              (事)
       人 ───互校操作───→ 审校 ───形证操作───→ 证明 ───立真操作───→ 真理
   raw relation     audited relation    proven meta-relation    eternal truth
```

### 4.3.1 人 → 审校：从人际到互审

- **算子**：互审算子（cross-check / audit）
- **古文**：人 → 审（人各有所见，必互审而后定）
- **形式上**：从 binary relation R(a, b) 提升到 type-check 或 model-check
- **关键**：单条人际关系是直接的；要它"被识"就必须经互审/确认

**例**：
- A 信任 B（人，未审）
- A 审查 B 是否真值得信（审校）
- 程序 e 与类型 A 的潜在关联（人）→ type-check Γ ⊢ e : A（审校）

### 4.3.2 审校 → 证明：从互审到形证

- **算子**：证明算子（formal demonstration）
- **古文**：审 → 证（审其真伪而后证之以辞）
- **形式上**：从 single check / decision 上升到 derivation tree——多次 type-check 串成完整 proof
- **关键**：单次 check 只能"过/不过"；证明把 check 串成完整论证

**例**：
- 单条数学验证（审校）→ 完整数学证明（证明）
- 单元测试通过（审校）→ Hoare logic proof of correctness（证明）

### 4.3.3 证明 → 真理：从形证到立真

- **算子**：立真算子（establish as truth）
- **古文**：证 → 真（证之以辞，立之以名，定之以体）
- **形式上**：从 single derivation 上升到 universal soundness 或 model satisfaction across all worlds
- **关键**：单个证明只立此一断言；真理是在所有相关场景中皆立

**例**：
- 一个特定证明 → 数学定理（在所有解释中皆真）
- Coq 的具体 proof term → soundness theorem of the calculus

### 4.3.4 間 行的整体走向

間 行是**关系的真理化路径**——从"具体接触"到"互验"到"形证"到"立真"。这是逻辑学主流（特别是 proof theory + model theory 双轨）的发展曲线：从 dyadic relation 到 verified consistency 到 derived theorem 到 universal validity。

---

# 第五部分：四列（每个阶段的横向意义）

每列展示三个本在同一阶段下的并行投影。

## 5.1 差 列：物 / 生 / 人

**主题**：raw distinction 在三个本上的最直接表达——pre-conceptual 的"给定"。

| 本 | 差 列 | 含义 |
|---|---|---|
| 物 | **物** | 实体本身被给出，但尚未被命名 |
| 動 | **生** | 变化本身在发生，但尚未被察觉 |
| 間 | **人** | 关系本身在那里，但尚未被审视 |

### 横向共性

差 列的三格都是**未中介的 ontological zero**：
- 都是直接对待
- 都不需要主体承担
- 都最近根（in MonadDAG terms, closest to root）

### 形式实测

实际登记字数（[atom-naming.md](../../formal/SSBX/notes/atom-naming.md)）：
- 物 行 物：43
- 動 行 生：31
- 間 行 人：11

总 85 个 atom 在 差 列——是字根最密集的层之一。这印证了"差"是 ontology 的真起点。

## 5.2 识 列：注意 / 心 / 审校

**主题**：marked / addressed —— 主体活动让差变成"可指可名"。

| 本 | 识 列 | 含义 |
|---|---|---|
| 物 | **注意** | 主体把对象 picks out |
| 動 | **心** | 主体 feels 变化 |
| 間 | **审校** | 主体 cross-checks 关系 |

### 横向共性

识 列的三格都是**主体动作**：
- 都需要主体存在
- 都把"在那里"提升到"对我在那里"
- 都是 epistemology 的入口

注意 / 心 / 审校 在 [atom-naming.md](../../formal/SSBX/notes/atom-naming.md) 里被原作者归为同一群"心智 / 注意"——这种自发归类正反映了它们处于同一列。

### 形式上

这一列对应到 [`AtomName`](../../formal/SSBX/Roster.lean) inductive 的整个 lexical 层——每个登记字本质上是一个 (本, 差) 被 (主体, 识) 操作后的产物。M-line 之所以叫"名册线"，正因为它就是 识 列的形式化。

## 5.3 间 列：模 / 理 / 证明

**主题**：structured —— 形式系统建立内部秩序。

| 本 | 间 列 | 含义 |
|---|---|---|
| 物 | **模** | 实体被建模 |
| 動 | **理** | 过程被规律化 |
| 間 | **证明** | 关系被形证 |

### 横向共性

间 列的三格都是**形式机制**：
- 都需要至少两项以上才有意义（单一项不能"被结构"）
- 都引入"系统性"
- 都是 formal logic 的真正栖身处

### 形式上

这是整个 SSBX 系统**最重的工作量**所在——所有的 [`FormalNode`](../../formal/SSBX/Foundation/Core/MonadRoot.lean)、`ConstructionId`、`ClaimId` 都在这一列工作。

| 间 列 | 主要文件 |
|---|---|
| 模 (物-间) | [`Monism.lean`](../../formal/SSBX/Foundation/Core/Monism.lean) 之 ConstructionId 阶段 / [`MetaInterp.lean`](../../formal/SSBX/Foundation/Wen/MetaInterp.lean) |
| 理 (動-间) | [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) / [`BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) 的算子代数 |
| 证明 (間-间) | 所有 `theorem` 命题 + Lean 的 proof term 系统 |

## 5.4 事 列：文 / 价值 / 真理

**主题**：enacted / final —— commit 到 ledger 的永久产物。

| 本 | 事 列 | 含义 |
|---|---|---|
| 物 | **文** | 实体在事件中被永久记录 |
| 動 | **价值** | 过程在事件中被永久评判 |
| 間 | **真理** | 关系在事件中被永久立证 |

### 横向共性

事 列的三格都是**最终 commit**：
- 都是"被定下来"的产物
- 都跨越特定时刻而 persist
- 都对应 [`ClaimId`](../../formal/SSBX/Truth/Basic.lean) 系统的某个面向

### 形式上

这一列对应到系统的"持久化"机制：
- 文 → [`Roster.lean`](../../formal/SSBX/Roster.lean) 的 GenName / RecName / PendingName 三类持久符号
- 价值 → 价值评价 claims 在 [`Truth/Basic.lean`](../../formal/SSBX/Truth/Basic.lean) 的部分
- 真理 → `Truth.SemanticAdequacy` + `every_registered_claim_has_semantics` 定理

事 列总和一定程度上**= ClaimId 集合**——这是为什么 `Truth.ClaimLedger` 叫 "ledger"。

---

# 第六部分：12 格之间的关系

## 6.1 行邻接（同 本 相邻阶段）

每行的 4 格构成一条**单调升级链**：

| 本 | 升级链 | 关键算子 |
|---|---|---|
| 物 | 物 →(注意算子)→ 注意 →(建模算子)→ 模 →(文字化算子)→ 文 | naming, modeling, inscription |
| 動 | 生 →(感知算子)→ 心 →(归纳算子)→ 理 →(评价算子)→ 价值 | perception, induction, valuation |
| 間 | 人 →(互审算子)→ 审校 →(证明算子)→ 证明 →(立真算子)→ 真理 | audit, formalize, validate |

**性质**：每条链上每对相邻格之间存在**升降算子对**，大致 left-adjoint / right-adjoint 关系（升级保信息，降级损失结构）。

## 6.2 列邻接（同 阶段 相邻 本）

每列的 3 格在同一阶段下并存，**三个 本 互相牵连**：

```
差 列：    物 ─┬─ 生 ─┬─ 人
              │       │
              ↑承载   ↑参与
              │       │
              └───間构成───┘

识 列：    注意 ─┬─ 心 ─┬─ 审校
                │       │
                注意一般针对物
                心一般感受动
                审校一般针对关系
                但三者可以指同一对象 (物有动有间)
```

**性质**：同一对象（如一个人际事件）可以同时被三本捕捉——比如某人际冲突 = 人（间-差）+ 心（动-识）+ 审校（间-识）。

## 6.3 主对角线：物 → 心 → 证明 → ?

主对角线 (差,差) → (识,识) → (间,间) → (事,事) 在 3×4 网格上不是闭合的（行数 ≠ 列数），但取最对角的 3 格：

| 坐标 | 名 | 主义 |
|---|---|---|
| (物, 差) | **物** | 实体之最具实体性 |
| (動, 识) | **心** | 过程之最被觉察 |
| (間, 间) | **证明** | 关系之最被结构化 |

这是**每个本的"主义之处"** —— 物 在差时最 物，動 在识时最 動（"動 之被识"是 動 的核心 — 没被识的 動 几乎不算 動），間 在间时最 間（"關係之关系"是 間 之 essence）。

## 6.4 反对角线：文 → 理 → 人

反对角 (物,事) → (動,间) → (間,差) 的三格：

| 坐标 | 名 | 反义读 |
|---|---|---|
| (物, 事) | **文** | 实体被永久记录到事件层 |
| (動, 间) | **理** | 过程被结构化到形式层 |
| (間, 差) | **人** | 关系下降到最具体的"人际" |

这是 **"本之溢出"** —— 每个本被推到非自身的最远阶段。物 被推到 事（最远离物的"活"层）、動 被推到 间（最远离動的"静"层）、間 被推到 差（最远离間的"原始"层）。

## 6.5 cuo / 对待：本-阶段全反

如果定义 cuo 类型对待：
- 本 取反: 物 ↔ 間（或 物 ↔ 動 — 二选一）
- 阶段 取反: 差 ↔ 事，识 ↔ 间

最显著的对待对：

| 对 | 名对 | 关系 |
|---|---|---|
| (物, 差) ↔ (間, 事) | **物 ↔ 真理** | 实体之 raw vs 关系之 终极 |
| (動, 差) ↔ (間, 事) | **生 ↔ 真理** | 萌动 vs 永真 |
| (物, 事) ↔ (間, 差) | **文 ↔ 人** | 死文 vs 活人 |
| (動, 识) ↔ (間, 间) | **心 ↔ 证明** | 主观感受 vs 客观证立 |

最后一对 **心 ↔ 证明** 是哲学传统里最长寿的对待——主观 vs 客观、内在 vs 外在、phenomenology vs formalism。

## 6.6 跨网格 cross-references

同一字根可同时出现在多个格：

### 案例：「真」字
- (間, 事) = **真理**——主位
- 但 真 也是 [`CoreAtom`](../../formal/SSBX/Foundation/Core/MonadRoot.lean) 之一，可派生 实 / 伪 等
- 在 文 格 里 真 也作为登记字之一（"真"作为名字出现，不是作为 cell 名）

### 案例：「间」字
- 阶段名 = 第三阶段（间 stage）
- 本名 = 第三本（間 root）
- 两个字相同——是有意的：間 在 间 阶段达到自我表达 (間, 间) = **证明**

### 案例：「事」字
- 阶段名 = 第四阶段（事 stage）
- 但目前 没有名为「事」的格——因为 (X, 事) 已是 文 / 价值 / 真理
- 「事」可能是未登记的 conceptual anchor（[layer-character-map.md §F](layer-character-map.md) 有讨论）

---

# 第七部分：与其它系统的接合

## 7.1 与生成线 (R-line)

| 12 格 | R-line 锚 |
|---|---|
| 物 (物-差) | R₀–R₈ 任一层的元素都"是物" |
| 注意 (物-识) | M3 [AtomName](../../formal/SSBX/Roster.lean) lookup |
| 模 (物-间) | [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) / [`BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) 的代数结构 |
| 文 (物-事) | 原始 [`Roster`](../../formal/SSBX/Roster.lean) 全体 + 文档 |
| 生 (動-差) | [`Sheng.step`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) 算子 |
| 心 (動-识) | observable / 状态 trace |
| 理 (動-间) | R₃ 横向算子（dong/hua/bian/cuo/zong）+ R₈ 时态算子（V₄ Shi cuo / 印 / 投）|
| 价值 (動-事) | 评价 claims，未独立形式化 |
| 人 (間-差) | edges between AtomNames（DirectEdge）|
| 审校 (間-识) | [`MissingGlyphs`](../../formal/SSBX/Foundation/Core/MissingGlyphs.lean) 类型校验 |
| 证明 (間-间) | Lean theorem / proof term |
| 真理 (間-事) | [`Truth.ClaimLedger`](../../formal/SSBX/Truth/ClaimLedger.lean) ⊨ |

## 7.2 与名册线 (M-line)

整个名册线 (M0 → M4) **就是 识 列在四阶段进一步细分**——M-line 的 5 层是 识 阶段内部的层级（root → face → core → atom → formal）。

把名册线放进 12 格里，它**位于 注意 / 心 / 审校 三格的合集**——再加 形式化 后产物（formal/construction/claim）属于 模 / 理 / 证明 三格。

## 7.3 与内容线

内容线 = 三本 → 三显 → 三征。三本 已经是 12 格的行轴；三显 / 三征 是**三本进入 间 列后的细分**：

| 本 | 三显 (间-列细分) | 三征 (间-列再细分) |
|---|---|---|
| 物 | 位 (position) | 幾 (contingency) |
| 動 | 場 (field) | 勢 (tendency) |
| 間 | 際 (interface) | 機 (occasion) |

所以 內容线 主要工作在 间 列 (模/理/证明) 内部展开。

## 7.4 与本体读法

本体读法 = 差 / 识 / 间 / 事 四阶段 —— **就是 12 格的列轴**。本体读法不是一条独立的线，而是 12 格的横轴本身。

---

# 第八部分：Code refactor 路径

## 8.1 当前状态

[`MonadRoot.lean:20-23`](../../formal/SSBX/Foundation/Core/MonadRoot.lean) 当前定义：

```lean
inductive Face where
  | «文面» | «物面» | «生面» | «理面» | «心面» | «人面»
  | «模面» | «审校面» | «价值面» | «证明面» | «注意面» | «真理面»
```

这是 12 个枚举构造子，**没有内部结构**——12 是个 magic number。

## 8.2 建议重构

```lean
/-- 三本：内容线 root，物/動/間 -/
inductive SanBen where
  | «物» | «動» | «間»
  deriving DecidableEq, Repr, BEq

/-- 四阶段：本体读法，差/识/间/事 -/
inductive SiJieduan where
  | «差» | «识» | «间» | «事»
  deriving DecidableEq, Repr, BEq

/-- 12 格：三本 × 四阶段。"面" 这个集合名作为 abbrev 保留，
    但每格的 label 用其原本的好名字，不带"面"后缀。 -/
abbrev Mian : Type := SanBen × SiJieduan

namespace Mian

/-- 12 格各自的标准名（不带"面"）。 -/
def label : Mian → String
  | (.«物», .«差») => "物"
  | (.«物», .«识») => "注意"
  | (.«物», .«间») => "模"
  | (.«物», .«事») => "文"
  | (.«動», .«差») => "生"
  | (.«動», .«识») => "心"
  | (.«動», .«间») => "理"
  | (.«動», .«事») => "价值"
  | (.«間», .«差») => "人"
  | (.«間», .«识») => "审校"
  | (.«間», .«间») => "证明"
  | (.«間», .«事») => "真理"

end Mian

/-- Cardinality 是可证的，不是设计常数。 -/
theorem mian_cardinality : (SanBen.all ×ˢ SiJieduan.all).length = 12 := by
  native_decide
```

## 8.3 迁移成本

- **Face inductive 改写**：1 处类型定义
- **Face.label 改写**：12 处 label
- **allFaces / all_faces_complete**：保持不变（用 `(SanBen.all ×ˢ SiJieduan.all)`）
- **atomPrimaryFace**：~333 处需要从单 face 改为 (本, 阶段) 双坐标——**这是真正的成本**
- **atomExtraFaces**：约 24 处类似改造

总共约 369 处机械改动 + 333 处人类决策审视。建议**分两阶段**：

### 阶段 1（自动可迁移）

把现有的 12 个 face 名直接映射到 12 格坐标：
```
«文面» → (.«物», .«事»)
«物面» → (.«物», .«差»)
«生面» → (.«動», .«差»)
... etc
```

这一步纯机械替换，编译还能通过。

### 阶段 2（人类审视）

逐个看 ~333 字，判断**它是否还属于原坐标**——比如发现某字归 `物面` 但其实更适合 `(動, 差) = 生`，则改坐标。这是审视，不是机械。

## 8.4 编译影响

`Face` 改成 `abbrev` of `SanBen × SiJieduan` 后，所有 `Face.casesOn` 自动展开到 12 个 product cases——`atomPrimaryFace` 和 `atomFaces` 函数仍是 total pattern match，覆盖性自动检查。

`DirectEdge` 的 `face → core` 边也自动改为 `(本, 阶段) → core`——含义不变，只是实现层多一层 product 投影。

---

# 第九部分：开放问题

1. **「事」字本身**：四阶段名"事"目前是 conceptual anchor，未登记 [`AtomName`](../../formal/SSBX/Roster.lean)。是否应该 register？

2. **「缘」之归位**：[layer-character-map.md §G](layer-character-map.md) 讨论的"缘"目前不属任何已 register 层。在 12 格里它最像 (間, 差) — 但 (間, 差) 已经是「人」。是否将 缘 作为 (間, 差) 的 alias？还是需要新增一个 (間, ?) 阶段？

3. **三显 / 三征 与 12 格的精确对应**：上文 §7.3 把它们都放在 间 列，但每本 在 间 列只占 1 格——三显 / 三征 各 3 项怎么塞进 1 格？建议是：三显 = (本, 间) 的内部展开，三征 = (本, 间) 进一步细分。需要更精确的形式接合。

4. **价值 与 真理 的差异**：(動, 事) = 价值 与 (間, 事) = 真理 都是"事"列。前者是过程的最终评判，后者是关系的最终立证。但 utility function 与 model satisfaction 在 deontic logic 里是一回事——价值/真理这条边可能比看起来更模糊。

5. **是否只有 4 个阶段**：差 / 识 / 间 / 事 是当前选择。是否还有更早或更晚的阶段？比如"无"（pre-差）或"忘"（post-事）？目前看不到必需，但保留作为开放问题。

6. **本可否扩展到 4 或 5**：三本是当前选择。古文里有 "天 / 地 / 人" 三才（也是 3）、"金 / 木 / 水 / 火 / 土" 五行（5）等多种 base 划分。如果系统某天发现 物/動/間 不够，可能要扩。

---

# 附录：与其它文件的关系

| 文件 | 关系 |
|---|---|
| [root-layer-map.md](root-layer-map.md) | 本文是 §0 本体读法 + §4 内容线的细化展开 |
| [layer-character-map.md](layer-character-map.md) | 本文是 §三轴并存（§A-§I）的体系化整理 |
| [layer-axis-graph.md](layer-axis-graph.md) | 本文是 §6 三轴汇聚的 12 格 instance |
| [yi-RO-hierarchy.md](yi-RO-hierarchy.md) | v2.1 R₀..R₈ doctrine — 把 R₄ Mian = Ben × Zheng = (Z/2)⁴ 显式纳入 R-spine |
| [`JianOntology.lean`](../../formal/SSBX/Foundation/Jian/JianOntology.lean) | 三本（物/動/間）的 ground truth |
| [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) | R₄ Mian = Ben × Zheng 的 ground truth — 是本文 12 格在 R-line 上的 next-up enrichment |
| [`MonadRoot.lean`](../../formal/SSBX/Foundation/Core/MonadRoot.lean) | 当前 12 face 的 ground truth (待重构为 SanBen × SiJieduan) |
| [`Roster.lean`](../../formal/SSBX/Roster.lean) | ~333 atomName，每个需要在 12 格中找位置 |
| [atom-naming.md](../../formal/SSBX/notes/atom-naming.md) | 工作稿中的 atom 归类，自发地用了 12 格的近似结构 |

---

## 形式锚

- [`formal/SSBX/Foundation/Jian/JianOntology.lean`](../../formal/SSBX/Foundation/Jian/JianOntology.lean) — `JianRoot` (3 ctors: 物/動/間)
- [`formal/SSBX/Foundation/Core/MonadRoot.lean`](../../formal/SSBX/Foundation/Core/MonadRoot.lean) — `Face` 12 inductive (待重构为 SanBen × SiJieduan)
- [`formal/SSBX/Foundation/Bagua/BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) — R₄ Mian = (Z/2)⁴ next-up enrichment
- [`formal/SSBX/Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) — R₈ 闭合层；transition 是"事之发生"的最小可审计形态
- [`formal/SSBX/Roster.lean`](../../formal/SSBX/Roster.lean) — ~333 AtomName 之 register
