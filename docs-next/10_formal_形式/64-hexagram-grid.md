# 64 卦四语对照表 + 4 象限分类 + 算子全 invariant

> 状态：定本（2026-05-10）。
> 作用：把 64 卦按 (本本 / 本征 / 征本 / 征征) 4 象限分类，每卦给出 古文 / 现代汉语 / 形式逻辑 单字读法，并列出 cuo / zong / hu / single-yao flip 在 4 象限上的 invariant。
> 配套：
> - [sanben-sijieduan-grid.md](sanben-sijieduan-grid.md) — 12 格底层 (3 本 × 4 阶段)
> - [layer-axis-graph.md](layer-axis-graph.md) — 三轴汇聚图
> - [layer-character-map.md](layer-character-map.md) — R0–L0 字根映射
> - [`BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) / [`Cell192.lean`](../../formal/SSBX/Foundation/Bagua/Cell192.lean) — 形式锚

---

## 0. trigram-本/征 assignment

| trigram | 本/征 | 本/征 名 | 单字 | 现代义 | 形式义 |
|---|---|---|---|---|---|
| 乾 | 本 | 物 | 物 | 实在性 | ⊤ / 𝟙 / unit / id_⊤ |
| 坤 | 本 | 事 | 事 | 已成性 | ⊥ / 𝟘 / void / id_⊥ |
| 离 | 本 | 動 | 動 | 转化性 | rewrite ⟶ |
| 坎 | 本 | 間 | 間 | 关系性 | composition ∘ |
| 震 | 征 | 勢 | 勢 | 推动 | momentum / arousal |
| 艮 | 征 | 時 | 時 | 定时 | halt / fixpoint |
| 巽 | 征 | 幾 | 幾 | 微入 | limit / penetration |
| 兑 | 征 | 機 | 機 | 时机 | event / occasion |

cuo 对：
- 乾(物) ↔ 坤(事)
- 离(動) ↔ 坎(間)
- 震(勢) ↔ 巽(幾)
- 艮(時) ↔ 兑(機)

zong-fixed (本组)：{乾, 坤, 离, 坎}
zong-mobile (征组)：{震↔艮, 巽↔兑}

表头说明：
- **#** = King Wen 序号
- **古字** = 单字简化（多取本卦"卦德"原字）
- **现代** = 当代汉语
- **形式** = formal logic / category theory / type theory 术语
- **卦象** = inner ⊕ outer 用 物動間事 / 幾勢機時 命名
- **错** = cuo 对应 #
- **综** = zong 对应 #（"自" = self-zong）
- **互** = hu 对应 #

---

## 1. 本本 16（内外皆 zong-fixed substrate；最静态）

| # | 古字 | 现代 | 形式 | 卦象 (inner⊕outer) | 错 | 综 | 互 |
|---|---|---|---|---|---|---|---|
| **1** 乾 | 健 | 实在 | ⊤ / unit / id_⊤ | 物·物 | 2 | 自 | 自 |
| **2** 坤 | 顺 | 受成 | ⊥ / void / id_⊥ | 事·事 | 1 | 自 | 自 |
| **5** 需 | 待 | 等待 | promise / await / Future T | 物·間 | 35 | 6 | 38 |
| **6** 讼 | 争 | 争辩 | inconsistency / type mismatch | 間·物 | 36 | 5 | 37 |
| **7** 师 | 众 | 群聚 | quotient / equiv class | 間·事 | 13 | 8 | 24 |
| **8** 比 | 亲 | 比邻 | binary relation R(x,y) | 事·間 | 14 | 7 | 23 |
| **11** 泰 | 通 | 通畅 | composition succeeds: g∘f | 物·事 | 12 | 12 | 54 |
| **12** 否 | 塞 | 否塞 | composition blocked / disjoint | 事·物 | 11 | 11 | 53 |
| **13** 同人 | 同 | 共识 | congruence / Equiv / quotient elim | 動·物 | 7 | 14 | 44 |
| **14** 大有 | 富 | 富有 | total / saturation / coproduct exhaust | 物·動 | 8 | 13 | 43 |
| **29** 坎 | 险 | 重险 | nested ∘∘ / list / stack | 間·間 | 30 | 自 | 27 |
| **30** 离 | 丽 | 重明 | iter ⟶⟶ / fold | 動·動 | 29 | 自 | 28 |
| **35** 晋 | 进 | 晋升 | lift / promote (functor map) | 事·動 | 5 | 36 | 39 |
| **36** 明夷 | 隐 | 蔽明 | occultation / private / hidden | 動·事 | 6 | 35 | 40 |
| **63** 既济 | 成 | 已决 | ⊨ / decided / committed | 動·間 | 64 | 64 | 64 |
| **64** 未济 | 未 | 未决 | ⊭ / undecided / hole | 間·動 | 63 | 63 | 63 |

**特征**：包含 **4 自反纯卦** (1乾, 2坤, 29坎, 30离) + **2 双 self-zong cuo 对** (1↔2, 29↔30) + **泰否、既济未济、晋明夷、师比、同人大有** 等最经典对待。这 16 是 64 卦中"最 ontological"的，对应 type-theory 里的 **value semantic kernel**。

---

## 2. 本征 16（内本-外征，"底盘稳，上面动"）

| # | 古字 | 现代 | 形式 | 卦象 (inner⊕outer) | 错 | 综 | 互 |
|---|---|---|---|---|---|---|---|
| **4** 蒙 | 启 | 蒙昧 | opaque / abstract type | 間·時 | 49 | 3 | 24 |
| **9** 小畜 | 畜 | 小蓄 | small accumulation / increment | 物·幾 | 16 | 10 | 38 |
| **16** 豫 | 备 | 预备 | thunk / lazy preparation | 事·勢 | 9 | 15 | 39 |
| **20** 观 | 观 | 观察 | observation / introspection | 事·幾 | 34 | 19 | 23 |
| **22** 贲 | 饰 | 文饰 | annotation / metadata layer | 動·時 | 47 | 21 | 40 |
| **23** 剥 | 剥 | 剥落 | erosion / GC / pruning | 事·時 | 43 | 24 | 2 |
| **26** 大畜 | 畜 | 大蓄 | bulk accumulate / fold | 物·時 | 45 | 25 | 54 |
| **34** 大壮 | 壮 | 强盛 | force / strict eval | 物·勢 | 20 | 33 | 43 |
| **37** 家人 | 家 | 家族 | scope / lexical closure | 動·幾 | 40 | 38 | 64 |
| **40** 解 | 解 | 解开 | release / decoupling | 間·勢 | 37 | 39 | 63 |
| **43** 夬 | 决 | 决断 | commit / decision | 物·機 | 23 | 44 | 1 |
| **45** 萃 | 聚 | 聚集 | aggregate / merge / fold | 事·機 | 26 | 46 | 53 |
| **47** 困 | 困 | 困境 | bottleneck / livelock | 間·機 | 22 | 48 | 37 |
| **49** 革 | 革 | 变革 | total rewrite / fixpoint update | 動·機 | 4 | 50 | 44 |
| **55** 丰 | 盛 | 丰盈 | saturation / fixpoint reached | 動·勢 | 59 | 56 | 28 |
| **59** 涣 | 散 | 涣散 | scatter / broadcast / diffuse | 間·幾 | 55 | 60 | 27 |

**特征**：底盘是稳定 substrate，外卦是动态 mark——substrate 受到 mark 的"作用"。这一象限对应 type-theory 里的 **modification operations**：take a value, apply some effect/transformation.

---

## 3. 征本 16（内征-外本，"底盘动，上面稳"）

| # | 古字 | 现代 | 形式 | 卦象 (inner⊕outer) | 错 | 综 | 互 |
|---|---|---|---|---|---|---|---|
| **3** 屯 | 难 | 屯难 | initialization / bootstrap | 勢·間 | 50 | 4 | 23 |
| **10** 履 | 履 | 行履 | step / one-step trace | 機·物 | 15 | 9 | 37 |
| **15** 谦 | 谦 | 谦逊 | underspecify / kenosis / Subtype | 時·事 | 10 | 16 | 40 |
| **19** 临 | 临 | 临察 | observer / monitor / supervisor | 機·事 | 33 | 20 | 24 |
| **21** 噬嗑 | 噬 | 咬合 | unification / structural match | 勢·動 | 48 | 22 | 39 |
| **24** 复 | 复 | 复归 | recursion / fix / iterate | 勢·事 | 44 | 23 | 2 |
| **25** 无妄 | 妄 | 无妄 | pure function / referentially transparent | 勢·物 | 46 | 26 | 53 |
| **33** 遁 | 遁 | 退避 | termination / weakening / retreat | 時·物 | 19 | 34 | 44 |
| **38** 睽 | 离 | 乖离 | divergence / parametricity | 機·動 | 39 | 37 | 63 |
| **39** 蹇 | 阻 | 蹇难 | blocking / synchronization wait | 時·間 | 38 | 40 | 64 |
| **44** 姤 | 遇 | 遭遇 | handshake / sync protocol | 幾·物 | 24 | 43 | 1 |
| **46** 升 | 升 | 上升 | type lift (Maybe T from T) | 幾·事 | 25 | 45 | 54 |
| **48** 井 | 井 | 井泉 | generator / iterator / stream | 幾·間 | 21 | 47 | 38 |
| **50** 鼎/器 | 器 | 鼎器 | container / functor / vessel | 幾·動 | 3 | 49 | 43 |
| **56** 旅 | 旅 | 旅行 | traversal / itinerant | 時·動 | 60 | 55 | 28 |
| **60** 节 | 节 | 节制 | constraint / typeclass / discipline | 機·間 | 56 | 59 | 27 |

**特征**：底盘是 mark（动态），外卦是 substrate（稳定）——mark 被 substrate 框定。这一象限对应 type-theory 里的 **construction operations**：take dynamics, embed into stable form.

---

## 4. 征征 16（内外皆 mark；最动态）

| # | 古字 | 现代 | 形式 | 卦象 (inner⊕outer) | 错 | 综 | 互 |
|---|---|---|---|---|---|---|---|
| **17** 随 | 随 | 跟随 | sequential composition >>= | 勢·機 | 18 | 18 | 53 |
| **18** 蛊 | 治 | 蛊乱 | corruption / debug / fault | 幾·時 | 17 | 17 | 54 |
| **27** 颐 | 养 | 养给 | producer-consumer / supply | 勢·時 | 28 | 自 | 2 |
| **28** 大过 | 过 | 过盛 | stack overflow / overshoot | 幾·機 | 27 | 自 | 1 |
| **31** 咸 | 感 | 感应 | synchronization (concurrent) | 時·機 | 41 | 32 | 44 |
| **32** 恒 | 恒 | 恒久 | loop / while-true / persistent | 幾·勢 | 42 | 31 | 43 |
| **41** 损 | 损 | 减损 | decrement | 機·時 | 31 | 42 | 24 |
| **42** 益 | 益 | 增益 | increment | 勢·幾 | 32 | 41 | 23 |
| **51** 震 | 起 | 震起 | event / trigger | 勢·勢 | 57 | 52 | 39 |
| **52** 艮 | 止 | 止息 | halt / fixpoint reached | 時·時 | 58 | 51 | 40 |
| **53** 渐 | 渐 | 渐进 | monotone / gradual | 時·幾 | 54 | 54 | 64 |
| **54** 归妹 | 归 | 归妹 | adjoint / inverse pairing | 機·勢 | 53 | 53 | 63 |
| **57** 巽 | 入 | 渗入 | injection / right-to-left composition | 幾·幾 | 51 | 58 | 38 |
| **58** 兑 | 悦 | 悦合 | choice / alternation | 機·機 | 52 | 57 | 37 |
| **61** 中孚 | 信 | 中诚 | bisimulation / consistency | 機·幾 | 62 | 自 | 27 |
| **62** 小过 | 微 | 小过 | drift / minor change | 時·勢 | 61 | 自 | 28 |

**特征**：包含 **另 4 自反纯卦** (51震, 52艮, 57巽, 58兑) + **2 双 self-zong cuo 对** (27↔28, 61↔62)。这 16 是 64 卦中"最 dynamical"的，对应 process algebra / operational semantics 的 **dynamical kernel**。

---

## 5. 算子在 4 象限上的全表 invariant

### 5.1 cuo（六爻全反）— 32 对，全部象限内换

```
本本 (16) ──cuo──> 本本: 8 对
  (1, 2)   (5, 35)  (6, 36)   (7, 13)
  (8, 14)  (11, 12) (29, 30)  (63, 64)

本征 (16) ──cuo──> 本征: 8 对
  (4, 49)  (9, 16)  (20, 34)  (22, 47)
  (23, 43) (26, 45) (37, 40)  (55, 59)

征本 (16) ──cuo──> 征本: 8 对
  (3, 50)  (10, 15) (19, 33)  (21, 48)
  (24, 44) (25, 46) (38, 39)  (56, 60)

征征 (16) ──cuo──> 征征: 8 对
  (17, 18) (27, 28) (31, 41)  (32, 42)
  (51, 57) (52, 58) (53, 54)  (61, 62)
```

✅ **cuo 永远在象限内** — 这是 (Z/2)³ 群结构的强 invariant。

### 5.2 zong（六爻反序）— 28 对 + 8 self

```
本本: 4 self-zong + 6 zong-pair
  self: 1乾, 2坤, 29坎, 30离 (palindromic 6-yao)
  pair: (5, 6) (7, 8) (11, 12) (13, 14) (35, 36) (63, 64)

本征 ↔ 征本 (16+16): 16 对（跨象限交换）⭐
  (3,4) (9,10) (15,16) (19,20) (21,22) (23,24) (25,26)
  (33,34) (37,38) (39,40) (43,44) (45,46) (47,48) (49,50)
  (55,56) (59,60)

征征: 4 self-zong + 6 zong-pair
  self: 27颐, 28大过, 61中孚, 62小过
  pair: (17, 18) (31, 32) (41, 42) (51, 52) (53, 54) (57, 58)
```

✅ **zong 把 本征 ↔ 征本 完全交换** — 这是 zong 在 4-象限网格上的 Z/2 行动（本本/征征 自闭，本征/征本 互通）。

### 5.3 hu（取中四爻）— hu-orbit 收敛到 4 个 attractor

hu 不是简单的对换，而是一个**收缩映射**——多次迭代 hu 后，多数卦最终落入 4 个 attractor 之一：

```
hu attractors (h such that hu(h) = h or hu²(h) = h):
  {1乾}              真 fixed point
  {2坤}              真 fixed point
  {63既济, 64未济}    2-cycle
```

iteration 路径例：
```
30离 → 28大过 → 1乾  (终归 1)
29坎 → 27颐  → 2坤  (终归 2)
61中孚 → 27颐 → 2坤  (终归 2)
62小过 → 28大过 → 1乾  (终归 1)
11泰 → 54归妹 → 63既济 ↔ 64未济  (落入 63-64 cycle)
12否 → 53渐  → 64未济 ↔ 63既济  (同样落入 cycle)
```

这 4 个 attractor 都在 **本本** 象限——意味着无论 64 卦从哪起步，hu 迭代都会把它带回到 substrate-substrate 的"原型层"。

形式层面：hu 是 64 卦上的 **不动点提取算子**——它把任何 hex 抽象到其"内核 substrate 结构"。这正是 Y combinator / 不动点定理 在 64 卦上的具体形态。

### 5.4 单爻 flip（改 / 化 / 变 / 临 / 主 / 极）

爻位 1-6 对应 6 个 single-yao flip：

| flip | 爻位 | 象限行为 |
|---|---|---|
| **改** (flip y1, 初爻) | 1 | 跨象限（本↔征）|
| **化** (flip y2, 二爻) | 2 | **保象限** ⭐ |
| **变** (flip y3, 三爻) | 3 | 跨象限（本↔征）|
| **临** (flip y4, 四爻) | 4 | 跨象限（本↔征）|
| **主** (flip y5, 五爻) | 5 | **保象限** ⭐ |
| **极** (flip y6, 上爻) | 6 | 跨象限（本↔征）|

**化 / 主（中爻系列）保 partition**：因为 flip y2 / y5 是 trigram 内部的中位翻转，不破坏 trigram palindrome 性质，所以 hex 的 (inner本/征, outer本/征) 都不变。

例：
- 1乾 (本本) →改→ 44姤 (征本)：本→征
- 1乾 (本本) →化→ 13同人 (本本)：本→本 ✓
- 1乾 (本本) →变→ 10履 (征本)：本→征
- 1乾 (本本) →临→ 9小畜 (本征)：跨象限内的 outer
- 1乾 (本本) →主→ 14大有 (本本)：本→本 ✓
- 1乾 (本本) →极→ 43夬 (本征)：跨象限内的 outer

这是 6 个 flip 中**中爻 (化/主) 的特殊地位**的代数解释——它们是仅有的两个保 4-象限分类的位置爻。

---

## 6. 4 象限作为形式逻辑的"四相"

这是本文最核心的洞察：4 象限对应于一个**完整 type-theoretic / category-theoretic 系统的 4 个 phase**。

### 6.1 总览

```
本本 (16) — value semantic kernel        — 类型与命题  (denotational)
本征 (16) — modification operations       — 效用与变换  (effectual)
征本 (16) — construction operations       — 构造与合成  (constructive)
征征 (16) — dynamical kernel              — 运行与求值  (operational)
```

这 4 phase 对应到任何完整计算/证明系统的 4 个层次：
1. 你**有什么** （types, propositions, values）
2. 你能**改变什么** （effects, modifications, refinements）
3. 你能**造什么** （constructions, abstractions, generalizations）
4. 你怎么**运行** （reductions, executions, dynamics）

### 6.2 本本 = value semantic kernel（类型与命题）

**主题**：denotational semantics 的核心——"什么是有的"。

**type-theory primitives 全部在这里**：

| # | 卦 | type-theory 对应 | 何种 type / proposition |
|---|---|---|---|
| 1乾 | 健 | `Unit` / `𝟙` / terminal object | top type / true proposition |
| 2坤 | 顺 | `Void` / `𝟘` / initial object | bottom type / false proposition |
| 5需 | 待 | `Future T` / `IO action` | not-yet-evaluated value |
| 6讼 | 争 | type mismatch / inconsistency | undecidable / contradictory |
| 7师 | 众 | `T / ~` quotient | equivalence class |
| 8比 | 亲 | `A → B → Prop` | binary relation |
| 11泰 | 通 | `(B→C) ∘ (A→B)` | function composition succeeds |
| 12否 | 塞 | `Empty` morphism | composition blocked |
| 13同人 | 同 | `Equiv A B` / `A ≃ B` | type equivalence / equality |
| 14大有 | 富 | `Sigma A` / `Σ x:A. P x` | dependent sum / total |
| 29坎 | 险 | `List T` / `Stream T` / nesting | recursive container |
| 30离 | 丽 | `T →* T` / repeated reduction | iteration / Kleene star |
| 35晋 | 进 | `Functor.map : (A→B)→(F A → F B)` | functorial lift |
| 36明夷 | 隐 | private / opaque type | hidden information |
| 63既济 | 成 | proof complete / well-typed | ⊨ / fully decided |
| 64未济 | 未 | hole / metavariable / `?_` | ⊭ / hole in proof |

**关键观察**：
- **二极**：1乾 (⊤) ↔ 2坤 (⊥) 是任何 type system 的两个极端 type（unit 和 void）
- **关系-实体对偶**：7师 / 8比 (relation 视角) 与 5需 / 6讼 (entity-relation 张力) 形成 dual axis
- **完成度对偶**：63既济 ↔ 64未济 = decided ↔ undecided = complete ↔ partial
- **可见度对偶**：35晋 ↔ 36明夷 = lift ↔ hide = covariant ↔ contravariant

### 6.3 本征 = modification operations（效用与变换）

**主题**：effects on values——"怎么改它"。

**effect-system 操作全部在这里**：

| # | 卦 | 形式对应 | 何种 effect / modification |
|---|---|---|---|
| 9小畜 | 畜 | small accumulation / `T → State T` 微步 | local state increment |
| 26大畜 | 畜 | bulk fold `[T] → T` | aggregate / fold-left |
| 49革 | 革 | total rewrite / `λ_. e'` | replace whole subterm |
| 22贲 | 饰 | annotation `T ⟨meta⟩` | add metadata layer |
| 23剥 | 剥 | GC / `prune : T → T` | erosion / removal |
| 43夬 | 决 | commit / `decide : T → Bool` | resolve to definite |
| 45萃 | 聚 | reduce `[T] → T` via merge | aggregation |
| 47困 | 困 | livelock / stuck-at | bottleneck |
| 55丰 | 盛 | fixpoint reached `f x = x` | saturation |
| 59涣 | 散 | broadcast / `T → [T]` | diffusion |
| 4蒙 | 启 | abstract type / opaque | epistemic obscurity |
| 16豫 | 备 | `Lazy T` / thunk | suspended computation |
| 20观 | 观 | reflection / introspection | meta-level inspection |
| 34大壮 | 壮 | force / strict eval | maximize evaluation |
| 37家人 | 家 | lexical scope / closure | enclose value |
| 40解 | 解 | unfold / `Lazy T → T` | force release |

**关键观察**：
- **加减一对**：9小畜 / 26大畜 (累积) 与 23剥 (移除) 是 inverse-ish ops
- **强制懒惰对**：34大壮 (strict) ↔ 16豫 (lazy)
- **打开关闭对**：37家人 (close) ↔ 40解 (open)
- **45萃 / 55丰 是 fold 之"过程"vs"结果"**

这 16 个全是 "已有 value，做什么"的操作。

### 6.4 征本 = construction operations（构造与合成）

**主题**：constructions from dynamics——"怎么造一个新的"。

**type-construction primitives 全部在这里**：

| # | 卦 | 形式对应 | 何种 construction |
|---|---|---|---|
| 3屯 | 难 | `bootstrap : Init → State` | initialization |
| 10履 | 履 | `step : S → S` (single step trace) | one-step semantics |
| 15谦 | 谦 | `Subtype P` / `restrict` | refinement type |
| 19临 | 临 | `observe : Process → Trace` | supervisor / observer |
| 21噬嗑 | 噬 | `unify : T₁ ⊓ T₂ → T` | structural unification |
| 24复 | 复 | `fix : (T → T) → T` | recursive definition |
| 25无妄 | 妄 | `pure : T → M T` (referentially transparent) | pure function |
| 33遁 | 遁 | `weaken : Γ ⊢ A → Γ, x:B ⊢ A` | weakening rule |
| 38睽 | 离 | `forall α. T α` parametricity | parametric polymorphism |
| 39蹇 | 阻 | `wait : Synced → Synced` | synchronization barrier |
| 44姤 | 遇 | handshake / `pair : A × B → ...` | encounter / communication |
| 46升 | 升 | `Just : T → Maybe T` | type-level lift |
| 48井 | 井 | `iterate : (S → S) → Stream S` | generator / source |
| 50鼎 | 器 | `Functor F` / container | parameterized container |
| 56旅 | 旅 | `traverse : F (G T) → G (F T)` | applicative traversal |
| 60节 | 节 | `class C` / typeclass / interface | discipline / contract |

**关键观察**：
- **3屯 = init**, **24复 = fix**, **48井 = iterate** 是 recursion theory 三大支柱
- **44姤 = encounter** + **39蹇 = block** = π-calculus 的 sync primitives
- **15谦 = refine**, **38睽 = parametric**, **60节 = typeclass** = type system 的 abstraction primitives
- **46升 = lift**, **50鼎 = Functor** = monadic / categorical lifting

这 16 个全是"用动态做什么新结构"——construction 的核心算子集。

### 6.5 征征 = dynamical kernel（运行与求值）

**主题**：pure dynamics——"怎么运行".

**operational-semantics primitives 全部在这里**：

| # | 卦 | 形式对应 | 何种 dynamics |
|---|---|---|---|
| 17随 | 随 | `>>=` / sequential composition | bind / sequence |
| 18蛊 | 治 | corruption / fault recovery | bug / debug |
| 27颐 | 养 | producer-consumer / channel | data flow |
| 28大过 | 过 | stack overflow / non-termination | overrun |
| 31咸 | 感 | sync (rendezvous) | concurrent meeting |
| 32恒 | 恒 | `while true` / persistence | infinite loop |
| 41损 | 损 | `n - 1` / decrement | resource decrement |
| 42益 | 益 | `n + 1` / increment | resource increment |
| 51震 | 起 | event trigger | signal / interrupt |
| 52艮 | 止 | halt / fixed point | normal termination |
| 53渐 | 渐 | monotone increase | progressive convergence |
| 54归妹 | 归 | adjoint / inverse | adjoint pair |
| 57巽 | 入 | composition `∘` (right-to-left) | injection |
| 58兑 | 悦 | `+` / choice / alternation | non-deterministic choice |
| 61中孚 | 信 | bisimulation `≅` | observational equivalence |
| 62小过 | 微 | drift / minor deviation | epsilon perturbation |

**关键观察**：
- **51震 (start) ↔ 52艮 (stop)** = process 之 start/stop = 完整 lifecycle
- **17随 (>>=) ↔ 18蛊 (debug/recover)** = 顺序执行与异常处理
- **41损 / 42益** = resource 计量（decrement/increment 是 Petri net 的核心）
- **57巽 (compose) / 58兑 (choice)** = process algebra 的 sequential / non-det
- **27颐 (producer-consumer) / 28大过 (overflow)** = stream processing 的 happy path / bad path
- **53渐 (monotone) / 54归妹 (adjoint)** = order theory + Galois connection
- **61中孚 (bisimulation) / 62小过 (drift)** = equivalence vs near-equivalence

这 16 个全是"运行时发生什么"——dynamics 的核心算子集。

### 6.6 4 象限恰好对应 Curry-Howard-Lambek 三角

| 象限 | 角色 | Curry-Howard-Lambek 对应 |
|---|---|---|
| 本本 | "what is" | propositions / types / objects |
| 本征 | "what's done to it" | proofs of P→Q / function applications / morphisms (modifying) |
| 征本 | "what's made of it" | proof construction tactics / type construction / functorial structures |
| 征征 | "how it runs" | proof normalization / lambda reduction / rewriting |

这意味着**每个完整的形式系统（Type Theory / Logic / Category Theory / Process Algebra）都在 64 卦上有 4-象限自然分布**——绝非偶然。

### 6.7 算子如何在四相之间移动

cuo / zong / hu / single-yao flip 不只是"把卦变成另一卦"，它们是**在 4 phase 之间的移动**：

| 算子 | 四相行为 | 解读 |
|---|---|---|
| **cuo** | 永远象限内 | "对偶但同相位"——本本的对偶仍是本本（如 1乾 ↔ 2坤 都是 ⊤/⊥ pair）|
| **zong** | 本本 / 征征 自闭，本征 ↔ 征本 跨换 | "顺序反转"——构造 ↔ 修改互换 |
| **hu** | 多步收敛到 4 attractor (全在本本) | "深层抽象"——任何东西最终归到 value-kernel |
| **化 / 主** | 永远象限内 | "中爻动 不变 phase"——内部细节修改 |
| **改 / 变 / 临 / 极** | 跨象限 | "外部条件改变" 切换 phase |

这给出**完整的 phase-transition 代数**：
- 在 type theory 内部精炼：cuo + 化 + 主
- 从 type 到 effect：改 / 变 / 临 / 极
- 从 effect 到 construction：zong (本征 ↔ 征本)
- 从任何位置回 value-kernel：hu 多步迭代

### 6.8 Lean 端的 type-class 化

把 4 象限直接做成 Lean type class：

```lean
inductive HexQuadrant
  | benBen   -- 本本: value semantic kernel
  | benZheng -- 本征: modification ops
  | zhengBen -- 征本: construction ops
  | zhengZheng -- 征征: dynamical kernel
  deriving DecidableEq, Repr

def Hexagram.quadrant (h : Hexagram) : HexQuadrant :=
  let innerIsBen := Trigram.isBen h.inner
  let outerIsBen := Trigram.isBen h.outer
  match innerIsBen, outerIsBen with
  | true,  true  => .benBen
  | true,  false => .benZheng
  | false, true  => .zhengBen
  | false, false => .zhengZheng

theorem cuo_preserves_quadrant (h : Hexagram) :
    h.cuo.quadrant = h.quadrant := by ...

theorem zong_swap_zheng (h : Hexagram) :
    h.quadrant = .benZheng → h.zong.quadrant = .zhengBen := by ...
theorem zong_swap_ben_self (h : Hexagram) :
    h.quadrant = .benBen → h.zong.quadrant = .benBen := by ...
-- (and similar for zhengZheng self, zhengBen → benZheng)

theorem hu_attractors :
    ∀ h, ∃ n, (Hexagram.hu^[n] h) ∈ [Hexagram.qian, Hexagram.kun, Hexagram.jiJi, Hexagram.weiJi] := by ...
```

这些 theorem 把"4 phase 是 (Z/2)³ 群结构强制的"从论证升级为 native_decide 可证。

---

## 7. 序卦传 / 杂卦传 在 4 象限上的分布

### 7.1 序卦传上下经分布

序卦传分上下经：
- 上经：1-30（30 卦）
- 下经：31-64（34 卦）

按 4 象限分类：

| 象限 | 上经 # | 下经 # | 总 |
|---|---|---|---|
| 本本 | 1, 2, 5, 6, 7, 8, 11, 12, 13, 14, 29, 30 (12) | 35, 36, 63, 64 (4) | 16 |
| 本征 | 4, 9, 16, 20, 22, 23, 26 (7) | 34, 37, 40, 43, 45, 47, 49, 55, 59 (9) | 16 |
| 征本 | 3, 10, 15, 19, 21, 24, 25 (7) | 33, 38, 39, 44, 46, 48, 50, 56, 60 (9) | 16 |
| 征征 | 17, 18, 27, 28 (4) | 31, 32, 41, 42, 51, 52, 53, 54, 57, 58, 61, 62 (12) | 16 |

**关键观察**：
- 上经偏 **本本** (12/30 = 40%)，下经偏 **征征** (12/34 = 35%)
- 上经讲"乾坤天地之道"——以 substrate-substrate 为主
- 下经讲"咸恒夫妇之道"——以 mark-mark 为主
- 这印证了序卦传的"由静而动"宇宙发展观

### 7.2 杂卦传配对全在 cuo / zong 关系内

杂卦传把 64 卦排成 32 对，每对都是**主题对偶**：
- 大部分对是 zong-pair（28 对）
- 少数特殊对是 cuo-pair（4 对：1↔2、27↔28、29↔30、61↔62 = 4 双 self-zong）

这正好对应我们 §5.1 + §5.2 的算子分析——杂卦传的 32 对就是我们 zong-pair (28) + 双 self-zong cuo-pair (4) 的并集。

---

## 8. hu attractor 的特殊地位

§5.3 已说 hu 的 4 attractors {1, 2, 63, 64} 都在本本象限。这 4 个有进一步的特殊地位：

| 卦 | 特性 |
|---|---|
| **1乾** | hu-self + cuo→2 + zong-self |
| **2坤** | hu-self + cuo→1 + zong-self |
| **63既济** | hu(63) = 64 + cuo→64 + zong→64 |
| **64未济** | hu(64) = 63 + cuo→63 + zong→63 |

观察：
- **1 与 2 是同时 hu/cuo/zong 的 fixed-pair**（在 cuo 下交换，但在 hu/zong 各自不动）
- **63 与 64 在所有三个算子下都互换**（最强的对偶强度）

这 4 个是 64 卦中**对称性最强的 4 个**——它们是 "(Z/2)³ × 反序 × 中四爻" 三种代数运算下的 group-theoretic kernel。

形式逻辑层面：
- 1乾 = ⊤
- 2坤 = ⊥
- 63既济 = ⊨ (full satisfaction)
- 64未济 = ⊭ (no satisfaction)

这 4 个就是任何形式系统的**4 个最基本 truth value**：top, bottom, validated, invalidated。

---

## 9. 总结：64 卦 是完整形式系统的 64 个 primitive

每一卦都是一个具体的 formal-logic 算子或 type，4 象限给它们一个 phase 分类，cuo / zong / hu 给它们对偶 / 反序 / 抽象 三种关系。

**这不是 64 个无关概念，是一个 (Z/2)³ × ... 的代数结构**：
- 8 trigram = 4 substrate + 4 mark = (Z/2)³ 的 Z/2-quotient
- 64 hexagram = 8 × 8 = (4+4) × (4+4) = 4 quadrants × 16
- 算子 invariants 都是从 (Z/2)³ 群结构强制的

这是为什么《周易》能成为中文形式思想的种子——它的代数结构本身就是完整的 4-phase formal system 的最小生成集。

---

## 10. 与现有 Lean 锚点的对接

| 概念 | Lean 锚 |
|---|---|
| 8 trigram | [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) `Trigram` 8 个 def |
| 64 hex | [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) `Hexagram` + [`Cell192.lean`](../../formal/SSBX/Foundation/Bagua/Cell192.lean) `xuGua` |
| cuo / zong / hu | [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) + [`BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) |
| 6 flip 字（改化变临主极）| [`LayerCharacterMap.lean`](../../formal/SSBX/Text/LayerCharacterMap.lean) `flipPositionChar` |
| 4 象限分类（待加） | TODO: `Hexagram.quadrant : Hexagram → HexQuadrant` |
| 算子 invariant theorems | TODO: cuo_preserves_quadrant 等 |

**待办**：
- [ ] 在 [`BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) 添加 `Trigram.isBen` 谓词及 4 个 invariant theorem (§5.4 已草拟)
- [ ] 在 [`Cell192.lean`](../../formal/SSBX/Foundation/Bagua/Cell192.lean) 添加 `Hexagram.quadrant` 函数及 cuo / zong / hu 在 quadrant 上的 invariant theorems
- [ ] 把 64 卦的 古文 / 现代 / 形式 三语 label 加进 [`LayerCharacterMap.lean`](../../formal/SSBX/Text/LayerCharacterMap.lean) 作为新 dimension

---

## 附：序卦传完整 64 卦索引（按 King Wen 序）

```
上经 30 卦：
1乾  2坤  3屯  4蒙  5需  6讼  7师  8比  9小畜 10履
11泰 12否 13同人 14大有 15谦 16豫 17随 18蛊 19临 20观
21噬嗑 22贲 23剥 24复 25无妄 26大畜 27颐 28大过 29坎 30离

下经 34 卦：
31咸 32恒 33遁 34大壮 35晋 36明夷 37家人 38睽 39蹇 40解
41损 42益 43夬 44姤 45萃 46升 47困 48井 49革 50鼎
51震 52艮 53渐 54归妹 55丰 56旅 57巽 58兑 59涣 60节
61中孚 62小过 63既济 64未济
```
