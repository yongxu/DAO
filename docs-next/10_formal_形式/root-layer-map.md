# 底层根系图：关系与算子

> **状态（2026-05-10 重大重构）**：新本体核心已落 Lean。
>
> - **新核心**：[`formal/SSBX/Foundation/Bagua/BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) — 4 本 (物動間事) + 4 征 (幾勢機時) + Mian = Ben×Zheng = 16 + Quadrant + 全部 invariants (cuo/zong/hu 在 4 象限上的行为)
> - **字根表**：[`formal/SSBX/Text/LayerCharacterMap.lean`](../../formal/SSBX/Text/LayerCharacterMap.lean) — R1-L0 + Rh 全部 66 字 ground truth
> - **JianMode → Virtue**：[`formal/SSBX/Foundation/Yi/Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) Virtue.displayChar 给出 健/顺/起/入/险/显/止/悦
> - **MonadRoot.atomPrimaryMian**：每 atom 现在有 16-cell 主归 (derived from Face via Face.toMian projection)
> - **Kernel.kernelDanZiMian**：27 KernelDanZi 字也有 Mian 映射
>
> **删除的 legacy**：
> - `inductive Face` 12-枚举 — 仍存在作 backward-compat label，未来 P5b 完全删除
> - `JianMode` → 重命名为 `Virtue`
> - `formal/SSBX/Foundation/Jian/JianOntology.lean` — 整个文件已删
> - `formal/SSBX/Core.lean` 中 GammaProcess 的 3-元 placeholder 类型（OnticRoot/Manifestation/DynamicMark/StaticFace/Gate/EventResult/CompositeForm）— 已删
>
> **本文 §2.4–§2.6 / §4 中关于"3 本 / 3 显 / 3 征 / 12 face / JianMode"的旧叙述已 stale**——以 [BenZheng.lean](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) 为新真理来源。

本文先把根下三到四层的关系和算子摊平。它不是替代 `MonadRoot.lean`、`Yuan.lean`、`Yi.lean` 或 `BaguaAlgebra.lean`，而是给这些文件之间的底层读法一个统一坐标。


## 0. 本体读法：差、识、间、事

若先不管现有文档分层，最底层应先按“差异如何成为可说之物”来读：

```text
太极 / 一元
  -- 生 / 判 -->  两仪 / 爻 / 差异 difference
  -- 识 / 见 -->  可被标记、可被指认的差异
  -- 缘 / 间 -->  差异之间的关系、相接、距离、依赖
  -- 成 / 行 -->  在时态和变换中落地的事
```

这里有四个边界：

| 阶段 | 说法 | 不是 | 在当前形式系统中最接近的锚点 |
|---|---|---|---|
| 差 | 太极生两仪；一处差异开出阳/阴两端 | 两个实体先已存在 | `Yao = {yang, yin}` 与 `Yao.neg` |
| 识 | 这个差异可以被分辨、标记、命名 | 另造一个本体根 | `AtomName`/读法登记，以及可枚举结构中的字段位 |
| 间 / 缘 | 已被识的差异可以相对、相接、相依 | 简单的物对物连线 | `物-動-間` 的内容线、`DirectEdge`/transition edge 的关系读法 |
| 事 | 关系在某一时态、位点或变换中发生并可记 | 静态名词 | `Cell192` 位点、transition、一条可审计记录 |

所以“物”不是最先的原子；更底层的是“差”。“物”是差异被识、被稳定、可进入关系之后的一个承载项。“缘”也不宜先当作第三个根；它更像“被识之差之间能够相接/相依”的边。若要形式化成新字，再决定它是 `AtomName`、`CoreAtom`，还是某类 relation label。

## 1. 先分清三条线

底层有三条容易混在一起的线：

| 线 | 问题 | 近根形状 | 机器锚点 |
|---|---|---|---|
| 生成线 | 一个根如何展开为可变结构 | `太极 / 一元 -> 爻 -> 四象 -> 八卦 -> 六十四卦 -> 192格` | `Yuan.lean`、`Yi.lean`、`BaguaAlgebra.lean`、`Cell192.lean` |
| 名册线 | 一个正式名字如何回根 | `一元 -> Face -> CoreAtom -> AtomName -> FormalNode / ClaimId` | `MonadRoot.lean`、`MonadDAG.md` |
| 内容线 | 理论内容如何构造 | `Γ -> 三本(物/動/間) -> 三显 -> 三征 -> 开闭/合成 -> 生生不息论` | `Monism.lean` |

三条线不可互相代替：

- `爻 / 阴阳` 是生成线的第一分化。
- `Face / CoreAtom / AtomName` 是名册线的回根秩序。
- `物 / 動 / 間` 是内容线的三本，不是名册线的 L1/L2。
- `缘` 可以作为“关系边 / 依赖 / 相接”的义理读法，但当前底层 Lean 主干没有把 `缘`登记为核心单字；写作时应先说清它是解释名，还是要新增登记项。

## 2. 生成线：root 往下四层

生成线回答：从唯一根怎样长出可计算的易结构。

```text
R0  太极 / 一元 / Unit
    |  分 fen：引入一个爻
    v
R1  爻 / 两仪 / Yao = {阳, 阴}
    |  分 fen：再引入一爻
    v
R2  四象 / SiXiang = Yao²
    |  分 fen：再引入一爻
    v
R3  八卦 / Trigram = Yao³
    |  重 chong：内卦 + 外卦
    v
R4  六十四卦 / Hexagram = Yao⁶
    |  配时：卦 × 已今未
    v
R5  192格 / Cell192 = Hexagram × Shi
```

### 2.1 R0：太极 / 一元

| 名 | 形式 | 作用 | 主要算子 |
|---|---|---|---|
| 太极 / 一元 | `Unit` 或单根 `一元` | 生成线的唯一未分化点 | `fenToYi`、`guiyi`、`grandCycle` |

读法：

- 在生成线里，`TaiJi` 是 `Unit`，只表示未分化的一点。
- 在名册线里，`一元`是唯一根节点，所有正式登记项都要能回到它。
- 二者可以同读为“唯一根”，但形式对象不同：一个是易生成层的 `Unit`，一个是 Monad DAG 的 root。

### 2.2 R1：爻 / 两仪 / 差

| 名 | 形式 | 元素 | 基本关系 | 主要算子 |
|---|---|---|---|---|
| 爻 / 两仪 / 差 | `Yao` | `yang`、`yin` | 一处差异的两端；阴阳互反，不是 true/false | `Yao.neg`、`yi` |

关系：

```text
阳 --neg/易--> 阴
阴 --neg/易--> 阳
neg ∘ neg = id
```

这里的 `易`不是外加动作，而是爻自身的可变性：`Yuan := Yao`，`yi := Yao.neg`。义理上，这一层先读作 `difference`：不是先有两个物，而是先有一条可翻转的差。

### 2.3 R2：四象

| 名 | 形式 | 元素数 | 来路 | 去路 |
|---|---|---:|---|---|
| 四象 | `SiXiang` | 4 | `fenToSiXiang : LiangYi -> Yao -> SiXiang` | `heToYi : SiXiang -> LiangYi` |

关系：

```text
两仪 + 新爻 --fen--> 四象
四象 --heToYi/遗忘一位--> 两仪
heToYi (fenToSiXiang y1 y2) = y1
```

四象层主要承担纵向展开/收束，不是当前横向算子最密的层。

### 2.4 R3：八卦

| 名 | 形式 | 元素数 | 横向算子 | 纵向算子 |
|---|---|---:|---|---|
| 八卦 | `Trigram` | 8 | `dong`、`hua`、`bian`、`cuo`、`zong` | `heShang`、`heZhong`、`heXia`、`guiyi` |

三爻位：

| 位 | Lean field | 单爻翻转 | 义理短名 |
|---|---|---|---|
| 初 / 下 | `y1` | `dong` | 动 |
| 中 | `y2` | `hua` | 化 |
| 上 | `y3` | `bian` | 变 |

横向关系：

```text
八卦 = Yao³
动 / 化 / 变：分别翻 y1 / y2 / y3
每个翻转二次为恒等
三者两两交换，生成 (Z/2)³
错 = 动 ∘ 化 ∘ 变
任意两卦相距至多 3 次单爻翻转
```

纵向关系：

```text
八卦 --heShang/heZhong/heXia--> 四象
四象 --heToYi--> 两仪
两仪 --heToTaiji--> 太极
八卦 --guiyi--> 太极
```

最小算子包在这一层可读成：

```text
{ 动, 化, 变, 合, 生 }
```

其中 `动/化/变`管横向互通，`合`管向根收束，`生`管按深度继续展开。

### 2.5 R4：六十四卦

| 名 | 形式 | 元素数 | 生成 | 主要算子 |
|---|---|---:|---|---|
| 六十四卦 | `Hexagram` | 64 | `chong inner outer` 或六个 `Yao` | `cuo`、`zong`、`cuoZong`、`hu`、六个单爻翻转 |

结构：

```text
y1 y2 y3 = 内卦 / 下卦
y4 y5 y6 = 外卦 / 上卦
Hexagram = inner ⊕ outer
```

算子分两类：

| 类 | 算子 | 作用 | 性质 |
|---|---|---|---|
| 整卦横向 | `cuo` | 六爻全反 | 二次为恒等 |
| 整卦横向 | `zong` | 六爻反序 | 二次为恒等 |
| 整卦横向 | `cuoZong` | 错后综 | 二次为恒等，且错综交换形成 V4 |
| 内取 | `hu` | 取中四爻成互卦 | 乾、坤为互固定点 |
| 单爻翻转 | `dongInner`、`huaInner`、`bianInner` | 翻 y1/y2/y3 | 各二次为恒等 |
| 单爻翻转 | `dongOuter`、`huaOuter`、`bianOuter` | 翻 y4/y5/y6 | 各二次为恒等 |

六十四卦层要注意：

- `chong` / `oplus` 有内外次序，通常不可交换。
- 六个单爻翻转生成 `(Z/2)^6`；任意两卦可在至多 6 次翻转内互达。
- `错/综/互`是整卦结构算子，不等同于单个爻位的 `动/化/变`。

### 2.6 R5：192格 / 事的格位

| 名 | 形式 | 元素数 | 生成 | 横向/时态算子 |
|---|---|---:|---|---|
| 192格 | `Cell192 = Hexagram × Shi` | 192 | 64卦 × 已/今/未 | `shiNext`、`shiPrev`、`hexCuo`、`hexZong`、`hexHu`、`flip1..flip6` |

关系：

```text
Shi = {已, 今, 未}
已 --next--> 今 --next--> 未 --next--> 已
Cell192 = Hexagram × Shi
```

Cell 层算子只是把卦层算子和时态算子提升到 `(Hexagram × Shi)`：

| 算子 | 作用 | 保持不变的坐标 |
|---|---|---|
| `shiNext` / `shiPrev` | 改时态 | 卦不变 |
| `hexCuo` / `hexZong` / `hexHu` | 改卦 | 时态不变 |
| `flip1..flip6` | 翻对应爻 | 时态不变 |

若要把“事”放进底层图，`Cell192` 是当前最合适的形式近似：它不是单独一个名，而是“某卦在某时态的一个格位”。一条 transition 则是“事之发生”的最小可审计形态。

## 3. 名册线：root 往下四层

名册线回答：一个正式名字或 claim 是否有回根路径。

```text
M0  一元 / root
    |
M1  Face / 一元之面
    |
M2  CoreAtom / 核心单字
    |
M3  AtomName / 登记单字 / 名
    |
M4  FormalNode / ConstructionId / ClaimId
```

### 3.1 M1：Face

`Face` 是一元的投影面，不是多个本体根。当前十二面为：

```text
文面、物面、生面、理面、心面、人面、模面、审校面、价值面、证明面、注意面、真理面
```

### 3.2 M2：CoreAtom

`CoreAtom` 是核心单字层，压缩登记单字，使“名”不是直接散落到根上。

读法：

```text
Face 给领域
CoreAtom 给字根
AtomName 给登记名
FormalNode / ClaimId 给结构与断言
```

因此“名”若要在近根层出现，应放在 M3 `AtomName`，不是 M1 或 M2。

### 3.3 M3：AtomName / 名

`AtomName` 是登记单字层。它承担两件事：

1. 每个登记字有主归面 `atomPrimaryFace`，必要时有额外归面 `atomExtraFaces`。
2. 每个登记字有核心字根 `atomCore`。

所以一个登记名的标准回根路径是：

```text
AtomName -> CoreAtom -> Face -> 一元
```

## 4. 内容线：物、动、间与“缘”

内容线不是名册近根层，而是理论构造主干。

当前机器主干写作：

```text
Γ 当前论域
  -> 三本 / 物-動-間
    -> 三显 / 位-場-際
      -> 三征 / 幾-勢-機
        -> 開閉闸口与網體流合成
          -> 生生不息论
```

若要把用户语境中的“物间缘”纳入底层图，建议先作如下区分：

| 字 | 建议读法 | 当前位置 |
|---|---|---|
| 物 | 可被定位、承载状态的项 | 内容线三本之一；名册线已有核心单字 `物` |
| 动 | 变化 / 翻转 / 推进 | 内容线三本之一；生成线也有 `动`作为下爻翻转名 |
| 间 | 项与项之间的 interval / gap / relation-space | 内容线三本之一；名册线登记为单字，但归属和核心映射按 `MonadRoot.lean` 为准 |
| 缘 | 关系边、相接条件、依赖或 coupling 的解释名 | 当前不宜当作已登记核心层；若要正式化，应新增 `AtomName`/`CoreAtom` 或作为某类 `DirectEdge` / relation label |

一句话：

```text
爻阴阳 = 生成最小差异
识 = 差异被标记、可指认，不是另一个根
物动间 = 内容构造三本：物是被稳定的承载项，动是变化，间是关系场
缘 = 被识之差之间的相接/相依，需另定形式位置
事 = 关系在时态和变换中落地，可近似读作 Cell192 位点或 transition
名 = AtomName 登记层
```

## 5. 算子总表

| 算子族 | 层 | 算子 | 类型形状 | 说明 |
|---|---|---|---|---|
| 原子反转 | R1 | `neg` / `yi` | `Yao -> Yao` | 阴阳互反，二次为恒等 |
| 纵向展开 | R0-R3 | `fenToYi`、`fenToSiXiang`、`fenToTrigram` | 加一爻 | 从未分化逐步生成两仪、四象、八卦 |
| 纵向收束 | R3-R0 | `heShang`、`heZhong`、`heXia`、`heToYi`、`heToTaiji`、`guiyi` | 遗忘/投影 | 从八卦逐步回太极 |
| 八卦横向 | R3 | `dong`、`hua`、`bian` | `Trigram -> Trigram` | 三个单爻翻转，生成 `(Z/2)^3` |
| 八卦整反 | R3 | `Trigram.cuo`、`Trigram.zong` | `Trigram -> Trigram` | 错为三翻合成，综为反序 |
| 合成重卦 | R3→R4 | `chong` / `oplus` | `Trigram -> Trigram -> Hexagram` | 内外卦有序合成，通常不可交换 |
| 重卦横向 | R4 | `Hexagram.cuo`、`zong`、`cuoZong`、`hu` | `Hexagram -> Hexagram` | 错、综、错综、互 |
| 六爻翻转 | R4 | `dongInner`、`huaInner`、`bianInner`、`dongOuter`、`huaOuter`、`bianOuter` | `Hexagram -> Hexagram` | 六个单爻位翻转，生成 `(Z/2)^6` |
| 时态循环 | R5 | `Shi.next`、`Shi.prev` | `Shi -> Shi` | 已今未三循环 |
| Cell 提升 | R5 | `shiNext`、`shiPrev`、`hexCuo`、`hexZong`、`hexHu`、`flip1..flip6` | `Cell192 -> Cell192` | 在 192 格上移动一跳 |
| 名册回根 | M0-M4 | `DirectEdge`、`Reachable` | DAG relation | 证明登记项、结构、claim 可回一元 |

## 6. 推荐命名

为了后续文档不再摇摆，建议底层统一用两套层号：

### 生成层号 R

```text
R0 根 / 太极 / 一元
R1 爻 / 两仪 / 阴阳 / 差
R1a 识 / 可标记差异（义理读法；不单列 Lean 层）
R2 四象
R3 八卦
R4 六十四卦
R5 192格
```

### 名册层号 M

```text
M0 一元
M1 面 / Face
M2 核心单字 / CoreAtom
M3 名 / 登记单字 / AtomName
M4 正式项与 claim
```

这样可以同时保留两种直觉：

- 说“底层生成”时，第一层就是 `爻 / 阴阳`。
- 说“单根名册”时，第一层是 `Face`，第二层是 `CoreAtom`，第三层才是“名”。
- 说“内容本体”时，进入的是 `物 / 動 / 間`，而不是把它误放成 root 的直属层。
