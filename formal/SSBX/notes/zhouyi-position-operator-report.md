# 周易位与算子对照报告

本报告回答三个问题：

1. 《周易》/易学传统里大量描述的“位”和“算子”大致有哪些。
2. 当前项目已经形式化并证明了哪些。
3. 这些证明能不能说明“完整算子集”，以及还缺什么。

这里的“算子”按项目语义使用：凡是能改变卦爻状态、投影/合成状态、抽取结构、分类位置、推进时态的规则，都视为算子。严格说，《周易》经传原文并不以现代数学方式列出“算子全集”，后世常说的“错、综、互、变、之卦”等也有不同流派用法。因此本报告把“经传核心”和“传统易学常用术语”分层处理。

## 一、周易中的位

### 1. 爻位

最基本的位是六爻：

| 位 | 传统称呼 | 项目语义 |
|---|---|---|
| 1 | 初 | 下爻、初位 |
| 2 | 二 | 下卦中位 |
| 3 | 三 | 下卦上位 |
| 4 | 四 | 上卦下位 |
| 5 | 五 | 上卦中位、尊位 |
| 6 | 上 | 上爻、终位 |

当前 Lean 锚点：

- `Hexagram.atPos` 给出六位投影。
- `HexagramPosition` 中用 `Fin 6` 统一处理六位。
- `SelfDescription.BitPositionVerified` 已把“一至六位”接到实际投影命题。

结论：六位不是停留在文字表，而是已经连接到 `Hexagram` 的六个字段和 `atPos` 定理。

### 2. 阴阳位与当位

传统位法：

| 位法 | 规则 |
|---|---|
| 阳位 | 初、三、五 |
| 阴位 | 二、四、上 |
| 当位 | 阳爻居阳位，阴爻居阴位 |
| 不当位 | 阳爻居阴位，阴爻居阳位 |

当前 Lean 锚点：

- `isYangPos`
- `isYinPos`
- `wellPos`
- `wellPosCount`
- `wellPosCount_jiji = 6`
- `wellPosCount_weiji = 0`
- `wellPosCountAt_total`
- `wellPosCount_cuo_complement`

结论：当位/不当位已经是可计数、可分类、可在 64 卦上求分布的定理对象。

### 3. 中位

传统位法：

| 位 | 意义 |
|---|---|
| 二 | 下卦之中 |
| 五 | 上卦之中 |

当前 Lean 锚点：

- `centralYaos`
- `centralYaos_jiji`
- `centralYaos_weiji`
- `centralYaos_qian`
- `centralYaos_kun`
- `centralYaos_partition_total`
- `centralYaos_each_16_yy`
- `centralYaos_each_16_yYin`
- `centralYaos_each_16_YinY`
- `centralYaos_each_16_YinYin`

结论：中位已经从“二五为中”的词汇规则，接到 64 卦中四种二五组合各 16 卦的分类定理。

### 4. 应位

传统位法：

| 下卦位 | 上卦应位 |
|---|---|
| 初 | 四 |
| 二 | 五 |
| 三 | 上 |

通常以阴阳相反为“相应”。

当前 Lean 锚点：

- `yingResponds`
- `respondsCount`
- `respondsCount_jiji = 3`
- `respondsCount_weiji = 3`
- `respondsCount_qian = 0`
- `respondsCount_kun = 0`
- `respondsCountAt_0 = 8`
- `respondsCountAt_1 = 24`
- `respondsCountAt_2 = 24`
- `respondsCountAt_3 = 8`
- `respondsCountAt_total`
- `respondsCount_cuo_invariant`
- `respondsCount_zong_invariant`

结论：应位已经有三对应位、全卦计数、64 卦分布、错/综不变量。

### 5. 比位、承、乘

传统位法：

| 位法 | 规则 |
|---|---|
| 比 | 相邻两爻关系 |
| 承 | 下承上，多看相邻下位对上位 |
| 乘 | 上乘下，多看相邻上位对下位 |

当前 Lean 锚点：

- `biAdj`
- `biCount`
- `biCount_qian = 5`
- `biCount_kun = 5`
- `biCount_jiji = 0`
- `biCount_weiji = 0`
- `biCountAt_total`
- `biCount_cuo_invariant`
- `biCount_zong_invariant`
- `chenLi`
- `chengLi`
- `chenCount`
- `chengCount`
- `chen_cuo_eq_cheng`
- `cheng_cuo_eq_chen`

结论：比、承、乘已经进入可计算的相邻关系系统，并且有错卦交换承乘的定理。

### 6. 内外、上下、重卦位

传统结构：

| 结构 | 说明 |
|---|---|
| 下卦/内卦 | 初、二、三 |
| 上卦/外卦 | 四、五、上 |
| 重卦 | 八卦相重为六十四卦 |

当前 Lean 锚点：

- `Hexagram.innerTrigram`
- `Hexagram.outerTrigram`
- `Hexagram.oplus`
- `chong`
- `hex_algebra_complete`

结论：内外卦和重卦结构已经是 `Trigram × Trigram -> Hexagram` 与投影定理的一部分。

### 7. 序位与 192 格

传统里有序卦、杂卦、卦序、时义等层次。项目当前把 64 卦再乘以三态时位，得到 192 格。

当前 Lean 锚点：

- `Shi.ji`
- `Shi.jin`
- `Shi.wei`
- `Shi.next`
- `Shi.prev`
- `Cell192 := Hexagram × Shi`
- `Cell192.all_length = 192`
- `Cell192.shiNext`
- `Cell192.shiPrev`
- `xuGua`
- `xuGua_length = 64`
- `xuGuaNext`

结论：192 格是项目内的形式扩展，不是《周易》原文术语；但它已经被证明为 `64 × 3 = 192` 的格点系统，并有时间边。

## 二、周易中的算子

### 1. 爻变算子

传统语义：

| 算子 | 作用 |
|---|---|
| 动 | 一爻动 |
| 变 | 动而成变 |
| 化 | 变化、转化 |
| 之卦/变卦 | 一个或多个动爻翻转后所得之卦 |

当前 Lean 锚点：

- `YaoStar`
- `YaoStar.isOld`
- `YaoStar.isYoung`
- `HexagramStar.benGua`
- `HexagramStar.bianGua`
- 八卦层：`dong`, `hua`, `bian`
- 六十四卦层：`dongInner`, `huaInner`, `bianInner`, `dongOuter`, `huaOuter`, `bianOuter`
- 192 格层：`flip1`, `flip2`, `flip3`, `flip4`, `flip5`, `flip6`
- 完备性：`bagua_intercommunication`, `bagua_intercommunication_bounded`, `hexHammingDist_le_6`, `hex_algebra_complete`

结论：单爻翻转算子已经完备。任意 64 卦状态之间，最多六次单爻翻转可达。

待补强点：项目已经有 `HexagramStar.bianGua` 表达“老爻变为变卦”，也有六个单爻翻转表达任意选定位翻转；但还缺一个中间桥梁：具名的 `MovingLines` / `zhiGua` 集合算子，以及定理 `HexagramStar.bianGua = zhiGua oldPositions benGua`。

### 2. 错、综、互

传统语义：

| 算子 | 作用 |
|---|---|
| 错 | 六爻阴阳全反 |
| 综 | 六爻上下反序 |
| 互 | 取二三四、三四五成互卦 |

当前 Lean 锚点：

- `Trigram.cuo`
- `Trigram.zong`
- `Hexagram.cuo`
- `Hexagram.zong`
- `Hexagram.hu`
- `cuo_eq_compose`
- `hex_cuo_eq_compose`
- `zong_outside_flip_group`
- `hu_fixed_point`

结论：

- `错` 是六个单爻翻转的复合，因此对可达性不是新自由度。
- `综` 是位置置换，不由单爻翻转生成；它不是状态值翻转，而是位序重排。
- `互` 是抽取/重组中间四爻的有向算子，不是可逆群作用。

这说明“完整算子集”要先问目标：若目标是 64 卦状态可达，错/综/互都不是必需生成元；若目标是覆盖传统易学语义，它们必须保留为具名算子。

### 3. 合、分、重、生生

经传核心：

| 经典语义 | 项目算子 |
|---|---|
| 易有太极 | `Unit` / 太极 |
| 是生两仪 | `fen` / `Sheng` |
| 两仪生四象 | 迭代分 |
| 四象生八卦 | 迭代分 |
| 因而重之 | `chong` / `Hexagram.oplus` |
| 生生之谓易 | `Sheng` / 自指生成结构 |

当前 Lean 锚点：

- `he`
- `fen`
- `chong`
- `Sheng`
- `grandCycle`
- `bagua_algebra_complete`

结论：纵向生成和归一算子已经形式化。横向互通与纵向归一共同构成项目的“八卦互通 + 归一”完备代数。

### 4. 时间/序列算子

传统语义：

| 算子/结构 | 说明 |
|---|---|
| 序卦 | 64 卦次序 |
| 杂卦 | 常以对举方式说明卦义 |
| 时 | 卦有时义、爻有时位 |

当前 Lean 锚点：

- `Shi.next`
- `Shi.prev`
- `Cell192.shiNext`
- `Cell192.shiPrev`
- `xuGua`
- `xuGuaNext`

结论：项目已经有 192 格时间边和序卦列表；但“序卦传为什么如此排列”的义理证明、杂卦对举图，还没有完整形式化。

## 三、我们已有的证明层

### 1. 位已经接到实际定理

当前最强的连接在 `SelfDescription.lean`：

- `BitPositionObject` 列出阴阳、六位、八卦位、六十四卦位、192 格、既今未、当中应比承乘等位对象。
- `BitPositionVerified` 把这些名字接到实际 Lean 命题。
- `position_semantics_complete` 说明这些位对象都有证明锚点。

这正是“把位从词汇描述接到实际定理”的层。

### 2. 算子已经接到完整性声明

当前已证明或登记的完备性锚点：

| 层 | 锚点 | 意义 |
|---|---|---|
| 八卦 | `bagua_algebra_complete` | 八卦层任意互通 + 归一 |
| 六十四卦 | `hex_algebra_complete` | 六爻翻转覆盖 T6，错为复合，综为外部置换 |
| 192 格 | `cell192_operator_complete` | `Cell192` 上有六个卦爻边和时间边 |
| 自描述 | `CompleteSelfDescription` | 主体、位、算子、边界均有自描述锚点 |
| 总结 | `position_aware_complete_operator_set` | 位感知的算子集完备声明 |

### 3. 图审计已经给出可达性结论

`PositionOperatorGraph` 的结论：

- 六个单爻翻转从任一卦出发可达 `64/64`。
- 六十四卦图连通。
- `错` 是复合边，不是缺失边。
- `综` 是位序反转，不属于单爻翻转群。
- `互` 是有向、非可逆、语义抽取边。
- `Cell192 = Hexagram × Shi` 若只用卦爻边，会分成三个时间连通分量；加入 `shiNext` / `shiPrev` 后 192 格连通。

结论：以“状态可达性”为目标，当前不缺横向卦爻算子；以“192 格全连通”为目标，必须保留时间算子。

## 四、缺口清单

### A. 不影响可达性，但影响传统语义覆盖

| 缺口 | 当前情况 | 建议 |
|---|---|---|
| 之卦/变卦桥梁 | 已有 `HexagramStar.bianGua`，也可由 `flip1..flip6` 复合表达，但两者尚未由集合算子统一 | 加 `zhiGua : Finset (Fin 6) -> Hexagram -> Hexagram` |
| 动爻集合定理 | 单爻完备已证明，多动爻作为集合未单列 | 证明 `zhiGua` 等于对应翻转复合 |
| 卦名/卦辞/爻辞语义 | 有结构和若干命名卦，但没有完整文本语义证明 | 建文本索引和语义边界，不强行声称真值完备 |
| 序卦传义理 | 有 `xuGua` 列表和 next | 补 `XuGuaGraph` 和序卦关系说明 |
| 杂卦传 | 未见完整对举图 | 加 `ZaGuaPair` 数据和对偶/综错关系审计 |
| 老少阴阳/六七八九与图审计 | Lean 已有 `YaoStar` 与 `HexagramStar.bianGua`，但图审计仍以裸 `flip1..flip6` 为边 | 把老爻集合接到 `zhiGua` 和 PositionOperatorGraph |

### B. 只有在目标扩大时才算缺口

| 扩大目标 | 当前情况 | 是否影响现有完备性 |
|---|---|---|
| 任意六位置换 `S6` | 目前有 `综`，无 adjacent swap/rotation 生成元 | 不影响 64 卦状态可达；影响“全位序置换代数” |
| 完整后天/先天/纳甲/世应系统 | 当前核心是卦爻位和 192 格 | 不影响周易核心可达性；影响术数系统覆盖 |
| 文本真理全集 | 当前证明的是形式对象和算子关系 | 不可能由有限算子证明全部文本诠释真理，只能建立边界与审计 |

## 五、是否已经到“证明的极限”

不是。当前已经到达的是一个明确边界：

> 对 `Hexagram = Bool^6` 的状态可达性，六个单爻翻转是完备生成元；对 `Cell192 = Hexagram × Shi`，再加时间边即可覆盖 192 格。

这不是《周易》全部意义的极限，而是“选定状态空间 + 选定算子语义”下的可证明完备性。

还能进一步推进的方向有三类：

1. **命名完备**：把“之卦、杂卦、序卦义理、老少阴阳”等传统术语变成 Lean 中的具名节点和边。
2. **图完备**：把每一个位作为 node，每一个算子作为 edge，增加 `Cell192` 图和传统关系图，做缺边审计。
3. **边界完备**：明确哪些属于可证明状态关系，哪些只是文本解释、历史流派或价值判断，不能混称为定理。

## 六、结论

我们的现状可以概括为：

| 问题 | 答案 |
|---|---|
| 六位、当位、中位、应位、比位、承乘是否已接到实际定理 | 是 |
| 64 卦状态可达性是否缺算子 | 不缺，六个单爻翻转已完备 |
| `错` 是否是新生成元 | 不是，是六翻转复合 |
| `综` 是否由翻爻生成 | 不是，它是位置置换 |
| `互` 是否是可逆变换 | 不是，它是有向抽取/重组 |
| 192 格是否完整 | 加时间算子后完整；无时间算子则分成三个时态分量 |
| 周易解释性术语是否全部形式化 | 还没有 |
| 下一步最有价值的补强 | `zhiGua` 动爻集合算子、`ZaGua` 对举图、`XuGua` 语义图、`Cell192` 全图审计 |

因此，“我们有没有完整算子集”的答案是分层的：

- **若问形式状态可达性**：已有完整算子集。
- **若问周易传统术语覆盖**：核心已覆盖，仍需补命名语义层。
- **若问全部真理**：不能用一个有限算子集直接宣称文本真理全集；可以证明的是边界内完备、边界外不冒称。
