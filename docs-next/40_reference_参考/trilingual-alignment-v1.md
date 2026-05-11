> 状态：v1 (2026-05-11) — Wen / English / Chinese 三向对齐表。覆盖 Phase R cutover 之后所有 codebase identifier。
> 标准来源：[`Foundation/Lang/Lexicon.lean`](../../formal/SSBX/Foundation/Lang/Lexicon.lean) (162 entries) + 实际 Lean 代码。

# Trilingual Alignment — Wen ↔ English ↔ Chinese

## 0 · 三向之 meaning

| 轴 | 含义 | 在 codebase 之表现 |
|---|---|---|
| **Wen** (文) | 文言 / pinyin form — 项目历史用法（旧）+ Sexp/Wenyan surface（保留）| Lexicon `aka` field、Wenyan layer keywords、史 history |
| **English** | Canonical English identifier — Phase R 之后 codebase 主用 | Lexicon `english` field、Lean def/theorem names |
| **Chinese** | 汉字 — docstring / comment / Sexp atom / 现 doctrine references | Lexicon `chinese` field、docstrings、Sexp |

## 1 · R-hierarchy 层之命名 (R₀..R₈)

### R₀ — 太极

| Wen | English | Chinese | 锚 |
|---|---|---|---|
| taiji | taiji (proper noun) | 太极 | `Foundation/Hierarchy/R0_Taiji.lean` |
| (unit) | `Unit` (Lean stdlib) | — | 类型 |

### R₁ — 两仪 / 爻

| Wen | English | Chinese | bits | 锚 |
|---|---|---|---|---|
| Yao | Yao (proper noun) | 爻 | — | `Foundation/Yi/Yi.Yao` |
| yang | yang | 阳 | `o` | `Yao.yang` |
| yin | yin | 阴 | `x` | `Yao.yin` |

### R₂ — 四象 (SiXiang)

| Wen | English | Chinese | bits | 锚 |
|---|---|---|---|---|
| SiXiang | SiXiang (proper noun) | 四象 | — | `Foundation/Bagua/BaguaAlgebra.SiXiang` |
| taiYang | greaterYang | 太阳 | `oo` | `SiXiang.greaterYang` |
| shaoYin | lesserYin | 少阴 | `ox` | `SiXiang.lesserYin` |
| shaoYang | lesserYang | 少阳 | `xo` | `SiXiang.lesserYang` |
| taiYin | greaterYin | 太阴 | `xx` | `SiXiang.greaterYin` |

### R₃ — 八卦 (Trigram)

| Wen | English | Chinese | bits | 锚 |
|---|---|---|---|---|
| Trigram | Trigram (proper noun) | 卦 (3-yao) | — | `Foundation/Yi/Yi.Trigram` |
| qian | heaven | 乾 | `ooo` | `Trigram.heaven` |
| dui  | lake    | 兑 | `oox` | `Trigram.lake` |
| li   | fire    | 离 | `oxo` | `Trigram.fire` |
| zhen | thunder | 震 | `oxx` | `Trigram.thunder` |
| xun  | wind    | 巽 | `xoo` | `Trigram.wind` |
| kan  | water   | 坎 | `xox` | `Trigram.water` |
| gen  | mountain| 艮 | `xxo` | `Trigram.mountain` |
| kun  | earth   | 坤 | `xxx` | `Trigram.earth` |

### R₄ — 命 / 面 (Mian) = Ben × Zheng

**Ben (本) 4 atoms**:

| Wen | English | Chinese | bits | 锚 |
|---|---|---|---|---|
| Ben | Ben (proper noun) | 本 | — | `Foundation/Bagua/BenZheng.Ben` |
| wu     | thing    | 物 | `oo` | `Ben.thing` |
| dong   | motion   | 动 | `xo` | `Ben.motion` |
| jian   | interval | 间 | `ox` | `Ben.interval` |
| shi    | event    | 事 | `xx` | `Ben.event` |

**Zheng (征) 4 atoms**:

| Wen | English | Chinese | bits | 锚 |
|---|---|---|---|---|
| Zheng | Zheng (proper noun) | 征 | — | `Foundation/Bagua/BenZheng.Zheng` |
| jiFaint    | trace    | 几 | `oo` | `Zheng.trace` |
| shiForce   | momentum | 势 | `xo` | `Zheng.momentum` |
| jiOccasion | pivot    | 机 | `ox` | `Zheng.pivot` |
| shiTime    | occasion | 时 | `xx` | `Zheng.occasion` |

**Mian** = Ben × Zheng = 16-cell carrier，每 cell 名 `<Ben>·<Zheng>` (e.g., 物·几 = `(thing, trace)`).

### R₅ — 五爻 (Wuyao, provisional)

| Wen | English | Chinese | 锚 |
|---|---|---|---|
| Wuyao | Wuyao (proper noun, no canonical Yi name) | 五爻 (provisional) | `Foundation/Hierarchy/R5_Wuyao` |
| flipBenLo  | flipBenLo  | — | `L5.flipBenLo` |
| flipBenHi  | flipBenHi  | — | `L5.flipBenHi` |
| flipZhengLo| flipZhengLo| — | `L5.flipZhengLo` |
| flipZhengHi| flipZhengHi| — | `L5.flipZhengHi` |
| flipFifth  | flipFifth  | 五爻 显/隐 bit | `L5.flipFifth` |

R₅ 用 Mian × Bool 之 product 结构表示；命名按 `<Mian>·<显|隐>` (`Foundation/Lang/Names.lean § 5`).

### R₆ — 六十四卦 (Hexagram)

Hexagram = Yao⁶ = 64 cells. 完整 64 entries in [`Foundation/Lang/Lexicon.lean § 5`](../../formal/SSBX/Foundation/Lang/Lexicon.lean).

完整 64 表 (Wen pinyin alias → English → Chinese → bits)：

| # | Wen | English | Chinese | bits | Wilhelm 注 |
|---:|---|---|---|---|---|
| 01 | qian       | heaven           | 乾   | `oooooo` | The Creative |
| 02 | kun        | earth            | 坤   | `xxxxxx` | The Receptive |
| 03 | zhun       | sprout           | 屯   | `oxxxox` | Difficulty at Beginning |
| 04 | meng       | naive            | 蒙   | `xoxxxo` | Youthful Folly |
| 05 | xu         | waiting          | 需   | `oooxox` | Waiting |
| 06 | song       | dispute          | 讼   | `xoxooo` | Conflict |
| 07 | shiArmy    | army             | 师   | `xoxxxx` | The Army |
| 08 | biUnion    | uniting          | 比   | `xxxxox` | Holding Together |
| 09 | xiaoXu     | smallRestraint   | 小畜 | `oooxoo` | Small Taming |
| 10 | lvTread    | treading         | 履   | `ooxooo` | Treading |
| 11 | tai        | peace            | 泰   | `oooxxx` | Peace |
| 12 | pi         | blocking         | 否   | `xxxooo` | Standstill |
| 13 | tongRen    | fellowship       | 同人 | `oxoooo` | Fellowship |
| 14 | daYou      | greatPossession  | 大有 | `ooooxo` | Great Possession |
| 15 | qianModesty| modesty          | 谦   | `xxoxxx` | Modesty |
| 16 | yu         | enthusiasm       | 豫   | `xxxoxx` | Enthusiasm |
| 17 | sui        | following        | 随   | `oxxoox` | Following |
| 18 | gu         | decay            | 蛊   | `xooxxo` | Work on the Decayed |
| 19 | lin        | approach         | 临   | `ooxxxx` | Approach |
| 20 | guan       | contemplation    | 观   | `xxxxoo` | Contemplation |
| 21 | shiHe      | biteThrough      | 噬嗑 | `oxxoxo` | Biting Through |
| 22 | bi         | adornment        | 贲   | `oxoxox` | Grace / Adornment |
| 23 | bo         | stripping        | 剥   | `xxxxxo` | Splitting Apart |
| 24 | fu         | returning        | 复   | `oxxxxx` | Return |
| 25 | wuWang     | innocence        | 无妄 | `oxxooo` | Innocence |
| 26 | daXu       | greatRestraint   | 大畜 | `oooxxo` | Great Taming |
| 27 | yiNourish  | nourishing       | 颐   | `oxxxxo` | Mouth Corners |
| 28 | daGuo      | greatExceeding   | 大过 | `xoooox` | Preponderance of Great |
| 29 | kanHex     | abyss            | 坎   | `xoxxox` | The Abysmal (Water) |
| 30 | liHex      | brightness       | 离   | `oxooxo` | The Clinging (Fire) |
| 31 | xian       | influence        | 咸   | `xxooox` | Influence |
| 32 | heng       | duration         | 恒   | `xoooxx` | Duration |
| 33 | dun        | retreat          | 遁   | `xxoooo` | Retreat |
| 34 | daZhuang   | greatPower       | 大壮 | `ooooxx` | Great Power |
| 35 | jin        | progress         | 晋   | `xxxoxo` | Progress |
| 36 | mingYi     | darkening        | 明夷 | `oxoxxx` | Darkening of the Light |
| 37 | jiaRen     | family           | 家人 | `oxoxoo` | The Family |
| 38 | kui        | opposition       | 睽   | `ooxoxo` | Opposition |
| 39 | jianObst   | obstruction      | 蹇   | `xxoxox` | Obstruction |
| 40 | xie        | deliverance      | 解   | `xoxoxx` | Deliverance |
| 41 | sun        | decrease         | 损   | `ooxxxo` | Decrease |
| 42 | yiIncr     | increase         | 益   | `oxxxoo` | Increase |
| 43 | guai       | resolution       | 夬   | `ooooox` | Breakthrough |
| 44 | gou        | encounter        | 姤   | `xooooo` | Coming to Meet |
| 45 | cui        | gathering        | 萃   | `xxxoox` | Gathering Together |
| 46 | sheng      | ascending        | 升   | `xooxxx` | Pushing Upward |
| 47 | kunImp     | impasse          | 困   | `xoxoox` | Oppression |
| 48 | jing       | well             | 井   | `xooxox` | The Well |
| 49 | ge         | revolution       | 革   | `oxooox` | Revolution |
| 50 | ding       | cauldron         | 鼎   | `xoooxo` | The Cauldron |
| 51 | zhenHex    | arousing         | 震   | `oxxoxx` | The Arousing (Thunder) |
| 52 | genHex     | keepingStill     | 艮   | `xxoxxo` | Keeping Still (Mountain) |
| 53 | jianGrad   | gradualProgress  | 渐   | `xxoxoo` | Development / Gradual |
| 54 | guiMei     | marryingMaiden   | 归妹 | `ooxoxx` | The Marrying Maiden |
| 55 | feng       | abundance        | 丰   | `oxooxx` | Abundance / Fullness |
| 56 | lvTrav     | wanderer         | 旅   | `xxooxo` | The Wanderer |
| 57 | xunHex     | gentle           | 巽   | `xooxoo` | The Gentle (Wind) |
| 58 | duiHex     | joyous           | 兑   | `ooxoox` | The Joyous (Lake) |
| 59 | huan       | dispersion       | 涣   | `xoxxoo` | Dispersion |
| 60 | jie        | limitation       | 节   | `ooxxox` | Limitation |
| 61 | zhongFu    | innerTruth       | 中孚 | `ooxxoo` | Inner Truth |
| 62 | xiaoGuo    | smallExceeding   | 小过 | `xxooxx` | Preponderance of the Small |
| 63 | jiJi       | complete         | 既济 | `oxoxox` | After Completion |
| 64 | weiJi      | incomplete       | 未济 | `xoxoxo` | Before Completion |

### R₇ — Cell128 (历史名) = R7 (现) = Hexagram × YinBit

| Wen | English | Chinese | 锚 |
|---|---|---|---|
| Cell128 (旧) → R7 (现) | R7 | 因卦 (= Hexagram × YinBit) | `Foundation/Bagua/R7.lean` |
| 因 / YinBit | YinBit | 因 | `R7.YinBit` |

R₇ 命名 (per Names.lean § 7)：`<卦名>·<因>` where 因 ∈ {无 (false), 有 (true)}.
e.g., `(heaven, false)` = `乾·无`, `(complete, true)` = `既济·有`.

### R₈ — Cell256 (历史名) = R8 (现) = Hexagram × Shi (V₄)

| Wen | English | Chinese | 锚 |
|---|---|---|---|
| Cell256 (旧) → R8 (现) | R8 | 果卦 (= Hexagram × Shi) | `Foundation/Bagua/R8.lean` |
| GuoBit | GuoBit | 果 | `R8.GuoBit` |
| Shi | Shi (V₄ Klein) | 时 | `R8.Shi` |

**Shi V₄ 四态**：

| Wen | English | Chinese | V₄ | 锚 |
|---|---|---|---|---|
| dao | dao (preserved proper noun) | 道 | (false, false) = identity | `Shi.dao` |
| ji  | ji  (preserved proper noun) | 已 | (true,  false) = P-like   | `Shi.ji` |
| jin | jin (preserved proper noun) | 今 | (true,  true)  = PT central | `Shi.jin` |
| wei | wei (preserved proper noun) | 未 | (false, true)  = T-like   | `Shi.wei` |

> **Note**: Shi 四态 之 Wen/English 同名 (pinyin = English) — these are **preserved proper nouns** representing V₄ Klein-four elements. They're doctrinal anchors, not translatable concepts.

R₈ 命名 (per Names.lean § 8)：`<卦名>·<时>` where 时 ∈ {道, 已, 今, 未}.
e.g., `R8.origin` = `(Hexagram.heaven, Shi.dao)` = `乾·道`.

## 2 · 算子 (Operators)

### Cayley operators (R₃/R₆/R₇/R₈ all)

| Wen | English | Chinese | 语义 | 锚 |
|---|---|---|---|---|
| cuo     | complement       | 错   | XOR with all-yang (bitwise NOT) | `Yi.complement`, `R7.hexCuo`, `R8.shiCuo` |
| zong    | reverse          | 综   | Yao-order reversal | `Yi.reverse`, `R7.hexZong`, `R8.shiZong` |
| hu      | interlace        | 互   | Inner-yao extraction (Hexagram) | `Yi.interlace`, `R7.hexHu` |
| cuoZong | complementReverse| 错综 | P ∘ T = V₄ central element | `Yi.complementReverse` |

### Yao position flips

| Wen | English | Chinese | 锚 |
|---|---|---|---|
| dong (旧, conflict) → motion | motion | 動 (operator) / 动 (Ben atom) | `Trigram.motion`, `R7.flip1`, `R8.flip1` |
| hua | middleFlip | 化 | `BaguaAlgebra.middleFlip` |
| bian | topFlip | 变 | `BaguaAlgebra.topFlip` |
| flip1..6 | flip1..6 | — | `R7.flipᵢ`, `R8.flipᵢ` |

### R₇ / R₈ atomic ops (印 / 投)

| Wen | English | Chinese | 语义 | 锚 |
|---|---|---|---|---|
| yin (旧, conflict with Yao.yin) → imprint | imprint | 印 | XOR with imprint_mask = (heaven, 因) — flips YinBit | `R7.imprint`, `R8.imprint` |
| tou | project | 投 | XOR with project_mask — flips GuoBit (via V₄ in R₈) | `R8.project` |

### Predicates (state-level)

| Wen | English | Chinese | 锚 |
|---|---|---|---|
| middle  | center  | 中 | `Wen.Kernel.center`  |
| extreme | terminus | 极 | `Wen.Kernel.terminus` |
| ji (predicate)  | trace (predicate)  | 几 | `Wen.Kernel.trace` |
| shi (Kernel)    | momentumDirection | 势 (Kernel orbit direction) | `Wen.Kernel.momentumDirection` |
| jiTurning  | pivotMoment | 机 (Kernel pivot event) | `Wen.Kernel.pivotMoment` |
| ji (五行 .ji)   | trace (DynamicMark) | 几 | `Core.DynamicMark.trace` |
| shi (五行 .shi) | momentum (DynamicMark) | 势 | `Core.DynamicMark.momentum` |
| jiMoment (五行) | pivot (DynamicMark) | 机 | `Core.DynamicMark.pivot` |

### Orbit / heart / virtue

| Wen | English | Chinese | 锚 |
|---|---|---|---|
| qing  | feeling   | 情 | `Wen.Kernel.feeling` |
| de (alias hasDe) | hasVirtue | 德 | `Wen.Kernel.hasVirtue` |
| li (Kernel) | principle | 理 | `Wen.Kernel.principle` |
| xin (alias xinTrust) | integrityTrust | 信 | `Wen.Kernel.integrityTrust` |
| xi  | rest | 息 | `Wen.Kernel.rest` |
| shan | good | 善 | `Wen.Kernel.good` |
| eVice | evil | 恶 | `Wen.Kernel.evil` |
| isShengRen | isSage | 圣人 | `Wen.Kernel.isSage` |
| liProfit | profit | 利 (Kernel state predicate) | `Wen.Kernel.profit` |
| guo | fault | 过 | `Wen.Kernel.fault` |
| ku  | suffering | 苦 | `Wen.Kernel.suffering` |
| xingNature | naturalDisposition | 性 | `Wen.Kernel.naturalDisposition` |

### Compound predicates (Confucian/Daoist)

| Wen | English | Chinese | 锚 |
|---|---|---|---|
| jiSuoBuYu | selfNotDesire | 己所不欲 | `Wen.Kernel.selfNotDesire` |
| jiSuoYu | selfDesire | 己所欲 | `Wen.Kernel.selfDesire` |
| shiYuRen | applyToOther | 施于人 | `Wen.Kernel.applyToOther` |
| jiYuRen | giveToOther | 己于人 | `Wen.Kernel.giveToOther` |
| tongGen | sameRoot | 同根 | `Wen.Kernel.sameRoot` |
| tongGenMiddle | sameRootCentered | 同根中 | `Wen.Kernel.sameRootCentered` |
| ziRan | naturalness | 自然 | `Wen.Kernel.naturalness` |
| wuWei | nonAction | 无为 | `Wen.Kernel.nonAction` |
| wuBuWei | omniAction | 无不为 | `Wen.Kernel.omniAction` |
| qiJia | familyOrder | 齐家 | `Wen.Kernel.familyOrder` |
| deQiYi | fulfilledExpectation | 得其意 | `Wen.Kernel.fulfilledExpectation` |
| buDeYi | unfulfilledExpectation | 不得意 | `Wen.Kernel.unfulfilledExpectation` |
| yiHan | implicitExpectation | 意涵 | `Wen.Kernel.implicitExpectation` |
| chunYi | pureExpectation | 纯意 | `Wen.Kernel.pureExpectation` |
| qing_de_zheng | feelingWellDirected | 情得正 | `Wen.Kernel.feelingWellDirected` |

### 五行 (WuXing) verbs

| Wen | English | Chinese | 锚 |
|---|---|---|---|
| sheng (五行 cyclic) | engenders | 相生 | `Wen.Kernel.WuXing.engenders` |
| ke   (五行 cyclic) | conquers  | 相克 | `Wen.Kernel.WuXing.conquers` |

### 易 primitive ops (Yuan / Jian layer)

| Wen | English | Chinese | 锚 |
|---|---|---|---|
| yi (Yuan)        | change | 易 (Yao negation as primitive) | `Foundation/Core/Yuan.change` |
| yi (Jian/STLC)   | yi (preserved — λ rename) | 易 (atomic name transform) | `Foundation/Jian/Jian.yi`, `JianSTLC.yi` |

> **Note**: `Yuan.change` 是 R₁ 之 negation; `Jian.yi` 是 lambda calculus 之 rename — different concepts, both 易 in Chinese. Lean 中分开命名 (change vs yi).

### Generation / motion aliases (Kernel)

| Wen | English | Chinese | 锚 |
|---|---|---|---|
| sheng (Kernel state) | engenders (alias for motion) | 生 (生成 face of 動) | `Wen.Kernel.engenders` |
| xing (Kernel state) | act (alias for motion) | 行 (actor face of 動) | `Wen.Kernel.act` |

### ShuSuan (数算) arithmetic atoms

| Wen | English | Chinese | 锚 |
|---|---|---|---|
| kong  | zero      | 空 (= 0) | `Eight.ShuSuan.zero` |
| yi    | one       | 一 (= 1) | `Eight.ShuSuan.one` |
| sheng | successor | 升 (= Nat.succ) | `Eight.ShuSuan.successor` |
| he    | combine   | 合 (= +) | `Eight.ShuSuan.combine` |
| sun   | decrement | 损 (= - truncated) | `Eight.ShuSuan.decrement` |
| chong | multiply  | 重 (= ×) | `Eight.ShuSuan.multiply` |
| fan   | negate    | 反 (= Int neg) | `Eight.ShuSuan.negate` |

## 3 · Confucian doctrinal vocabulary

### 五常 (Wuchang) — at R₇ Cell128

| Wen | English | Chinese | bits | 五行 | 锚 |
|---|---|---|---|---|---|
| ren  | benevolence  | 仁 | `xoooooo` | 木 | `Wuchang.benevolence` |
| yi   | righteousness | 义 | `oxooooo` | 金 | `Wuchang.righteousness` |
| li   | propriety    | 礼 | `ooxoooo` | 火 | `Wuchang.propriety` |
| zhi  | wisdom       | 智 | `oooxooo` | 水 | `Wuchang.wisdom` |
| xin  | integrity    | 信 | `xxxxooo` | 土 | `Wuchang.integrity` |

> 信 = 仁 ⊕ 义 ⊕ 礼 ⊕ 智 (synthesis); 仁 ⊕ 义 ⊕ 礼 ⊕ 智 ⊕ 信 = origin (五常归道).

### 四端 (SiDuan) — at R₃ Trigram

| Wen | English | Chinese | trigram | 锚 |
|---|---|---|---|---|
| ceYin   | compassion   | 恻隐 | 离 ☲ | `Confucian.SiDuan.compassion` |
| xiuWu   | shame        | 羞恶 | 坎 ☵ | `Confucian.SiDuan.shame` |
| ciRang  | yielding     | 辞让 | 震 ☳ | `Confucian.SiDuan.yielding` |
| shiFei  | discernment  | 是非 | 兑 ☱ | `Confucian.SiDuan.discernment` |

### 大学八目 (BaMu) — at R₃ Trigram (proposed mapping)

| Wen | English | Chinese | trigram | 锚 |
|---|---|---|---|---|
| geWu        | investigateThings | 格物    | 巽 ☴ | `Confucian.BaMu.investigateThings` |
| zhiZhi      | extendKnowledge   | 致知    | 离 ☲ | `Confucian.BaMu.extendKnowledge` |
| chengYi     | sincereIntention  | 诚意    | 兑 ☱ | `Confucian.BaMu.sincereIntention` |
| zhengXin    | rectifyHeart      | 正心    | 艮 ☶ | `Confucian.BaMu.rectifyHeart` |
| xiuShen     | cultivateSelf     | 修身    | 震 ☳ | `Confucian.BaMu.cultivateSelf` |
| qiJia       | regulateFamily    | 齐家    | 坎 ☵ | `Confucian.BaMu.regulateFamily` |
| zhiGuo      | governState       | 治国    | 坤 ☷ | `Confucian.BaMu.governState` |
| pingTianXia | pacifyWorld       | 平天下  | 乾 ☰ | `Confucian.BaMu.pacifyWorld` |

### 五伦 (WuLun) — at R₅ Wuyao (L5 generators)

| Wen | English | Chinese | generator | 锚 |
|---|---|---|---|---|
| fuZi   | fatherSon    | 父子 | flipBenLo  | `Confucian.WuLun.fatherSon` |
| junChen| rulerSubject | 君臣 | flipBenHi  | `Confucian.WuLun.rulerSubject` |
| fuFu   | husbandWife  | 夫妇 | flipZhengLo| `Confucian.WuLun.husbandWife` |
| xiongDi| brothers     | 兄弟 | flipZhengHi| `Confucian.WuLun.brothers` |
| pengYou| friends      | 朋友 | flipFifth  | `Confucian.WuLun.friends` |

### 善恶 (ShanE) — at R₁ Yao

| Wen | English | Chinese | yao | 锚 |
|---|---|---|---|---|
| shan  | good | 善 | yang | `Confucian.ShanE.good` |
| eVice | evil | 恶 | yin  | `Confucian.ShanE.evil` |

### 喜怒哀乐 (XiNuAiLe) — at R₂ SiXiang

| Wen | English | Chinese | sixiang | 锚 |
|---|---|---|---|---|
| xi | joy     | 喜 | greaterYang | `Confucian.XiNuAiLe.joy` |
| nu | anger   | 怒 | lesserYin   | `Confucian.XiNuAiLe.anger` |
| ai | sorrow  | 哀 | lesserYang  | `Confucian.XiNuAiLe.sorrow` |
| le | delight | 乐 | greaterYin  | `Confucian.XiNuAiLe.delight` |

### 元亨利贞 (YuanHengLiZhen) — at R₂ SiXiang

| Wen | English | Chinese | sixiang | 锚 |
|---|---|---|---|---|
| yuan | originVirtue  | 元 | greaterYang | `Confucian.YuanHengLiZhen.originVirtue` |
| heng | smoothVirtue  | 亨 | lesserYang  | `Confucian.YuanHengLiZhen.smoothVirtue` |
| li   | benefitVirtue | 利 | lesserYin   | `Confucian.YuanHengLiZhen.benefitVirtue` |
| zhen | correctVirtue | 贞 | greaterYin  | `Confucian.YuanHengLiZhen.correctVirtue` |

> Virtue suffix to disambiguate from common math vocab (origin/benefit/correct).

### 大学三纲 (SanGang) — at R₃ Trigram

| Wen | English | Chinese | trigram | 锚 |
|---|---|---|---|---|
| mingMingDe   | illuminateVirtue | 明明德    | 离 ☲ | `Confucian.SanGang.illuminateVirtue` |
| qinMin       | engagePeople     | 亲民      | 兑 ☱ | `Confucian.SanGang.engagePeople` |
| zhiYuZhiShan | restInGood       | 止于至善  | 艮 ☶ | `Confucian.SanGang.restInGood` |

### 三才 (SanCai) — at R₃ Trigram

| Wen | English | Chinese | trigram | 锚 |
|---|---|---|---|---|
| tianSky    | sky    | 天 | 乾 ☰ | `Confucian.SanCai.sky` |
| diGround   | ground | 地 | 坤 ☷ | `Confucian.SanCai.ground` |
| renHuman   | human  | 人 | 艮 ☶ | `Confucian.SanCai.human` |

### 大同 (DaTong) — R₆ universal

| Wen | English | Chinese | 锚 |
|---|---|---|---|
| daTong | greatHarmony / universalHexagram | 大同 | `Confucian.DaTong.all_hexagrams_in_dao` |

`heaven_in_dao`, `earth_in_dao`, `complete_in_dao`, `incomplete_in_dao` 之 4 anchors.

### 高级 doctrinal 词

| Wen | English | Chinese | 类型 | 锚 |
|---|---|---|---|---|
| dao        | dao        | 道       | proper noun | `Lexicon.confucian` |
| shengRen   | sage       | 圣人     | predicate | `Wen.Kernel.isSage` |
| neiSheng   | innerSage  | 内圣     | predicate | `Wen.Kernel.sage_innerSage` |
| waiWang    | outerKing  | 外王     | predicate | `Wen.Kernel.sage_outerKing` |
| shu        | reciprocity| 恕       | predicate | `Lexicon.confucian` |
| zhongYong  | middleWay  | 中庸     | proper noun | `Lexicon.confucian` |
| daXue      | greatLearning | 大学  | proper noun | `Lexicon.confucian` |
| lunYu      | analects   | 论语     | proper noun | `Lexicon.confucian` |
| mengZi     | mencius    | 孟子     | proper noun | `Lexicon.confucian` |
| yiBook     | yiBook     | 易       | proper noun (= 易经) | `Lexicon.confucian` |
| taiJi      | taiji      | 太极     | proper noun | `Lexicon.confucian` |

## 4 · 命题 / 经典语句 (Kernel theorems)

约 60 theorems with renamed English names. Key examples:

| Wen (旧) | English (现) | Chinese 原句 |
|---|---|---|
| shengsheng_buxi | unceasing_generation | 生生不息 |
| ren_zhe_ai_ren | benevolent_loves_others | 仁者爱人 |
| jun_zi_he_er_bu_tong | noble_harmonizes_not_uniform | 君子和而不同 |
| jun_jun_chen_chen_fu_fu_zi_zi | roles_proper | 君君臣臣父父子子 |
| ji_suo_bu_yu__wu_shi_yu_ren | golden_rule_negative | 己所不欲勿施于人 |
| ke_ji_fu_li_wei_ren | conquer_self_restore_propriety | 克己复礼为仁 |
| zhao_wen_dao_xi_si_ke_yi | morning_dao_evening_die_acceptable | 朝闻道夕死可矣 |
| tian_di_bu_ren | heaven_earth_unkind | 天地不仁 |
| zi_qiang_bu_xi | self_strengthen_no_rest | 自强不息 |
| wu_wei_er_wu_bu_wei | nonaction_yet_no_undone | 无为而无不为 |
| zhong_yong_bu_pian_bu_yi | mean_neither_partial_nor_biased | 中庸不偏不倚 |
| xue_er_shi_xi_zhi | learn_then_practice | 学而时习之 |
| san_ren_xing_bi_you_wo_shi | three_walk_must_have_teacher | 三人行必有我师 |
| dao_fa_zi_ran | dao_follows_naturalness | 道法自然 |
| ren_zhe_bu_you | benevolent_not_worry | 仁者不忧 |
| jun_zi_tan_dang_dang | noble_at_ease | 君子坦荡荡 |
| li_zhi_yong_he_wei_gui | propriety_use_harmony_valued | 礼之用和为贵 |
| wan_wu_jie_bei_yu_wo | all_things_in_me | 万物皆备于我 |
| fan_shen_er_cheng | reflect_self_sincerity | 反身而诚 |
| wen_gu_zhi_xin | review_old_know_new | 温故知新 |
| si_hai_zhi_nei_jie_xiong_di | within_four_seas_all_brothers | 四海之内皆兄弟 |
| min_gui_jun_qing | people_noble_ruler_light | 民贵君轻 |
| hou_de_zai_wu | thick_virtue_carries | 厚德载物 |
| fan_zhe_dao_zhi_dong | return_is_dao_motion | 反者道之动 |
| shang_shan_ruo_shui | highest_good_like_water | 上善若水 |
| zhi_xu_shou_jing | reach_empty_keep_calm | 致虚守静 |
| da_cheng_ruo_que | great_completion_seems_flawed | 大成若缺 |
| jian_ai | universal_love | 兼爱 (Mozi) |
| zhuangzi_qi_state | zhuangzi_equal_state | (Zhuangzi 齐物) |
| zhuangzi_you_state | zhuangzi_wander_state | (Zhuangzi 逍遥游) |
| sunzi_xushi_blocks_naive_read | sunzi_emptyfull_blocks_naive | (Sunzi 虚实) |
| sunzi_qizheng_yuzhi | sunzi_oddregular_advance | (Sunzi 奇正) |
| renlei_「人类命运共同体_合立」 | community_holds | (Renlei.lean) |
| renlei_「人类命运共同体_有反」 | community_has_counter | (Renlei.lean) |
| renlei_「人类命运共同体_aligned_iff」 | community_aligned_iff | (Renlei.lean) |

> 完整 list (≈100 theorems) 见 [`Foundation/Wen/Kernel.lean`](../../formal/SSBX/Foundation/Wen/Kernel.lean) + [`Wuchang.lean`](../../formal/SSBX/Foundation/Lang/Wuchang.lean) + [`Confucian.lean`](../../formal/SSBX/Foundation/Lang/Confucian.lean) + [`Renlei.lean`](../../formal/SSBX/Foundation/Core/Renlei.lean).

## 5 · 保留 CJK 之 layer (architectural)

下列 layer 之 identifier 保留 CJK，因为它们是 Chinese-language substrate。

### YiCore (易之微核)

[`Foundation/Yi/YiCore.lean`](../../formal/SSBX/Foundation/Yi/YiCore.lean):

| Identifier | Chinese | 语义 |
|---|---|---|
| `«加»` | 加 | Hexagram mod-64 加 |
| `«一»` | 一 | hexagram of index 1 |
| `«生»` | 生 | = `«加» «一»` (succ 之 hexagram 化) |
| `«生生»` | 生生 | recursive `«生»` n 次 |
| `«道法自然»` | 道法自然 | theorem |
| `«周而复始»` | 周而复始 | theorem (cycle of 64) |
| `«生生不息»` | 生生不息 | theorem (reachability) |
| `«道生一也»` | 道生一也 | theorem |

### Roster (Chinese-character registry)

[`Roster.lean`](../../formal/SSBX/Roster.lean):
- `AtomName` inductive — ~300 CJK 构造子
- `GenName` / `RecName` / `PendingName` — 同
- 是 doctrine 之 Chinese-character "registry"，不渲染为 English

### MonadRoot + Core consumers

[`Foundation/Core/MonadRoot.lean`](../../formal/SSBX/Foundation/Core/MonadRoot.lean),
[`AtomDerivation.lean`](../../formal/SSBX/Foundation/Core/AtomDerivation.lean),
[`Li.lean`](../../formal/SSBX/Foundation/Core/Li.lean),
[`HumanAlignment.lean`](../../formal/SSBX/Foundation/Core/HumanAlignment.lean),
[`MissingGlyphs.lean`](../../formal/SSBX/Foundation/Core/MissingGlyphs.lean):
- 消费 Roster.AtomName 之 CJK 构造子
- e.g., `«一元»` (root), `«生生不息»` (project name)
- 留 CJK 因为它们 mirror Roster

### Wenyan layer (文言 lambda calculus + meta-interpreter)

[`Foundation/Wen/WenyanText.lean`](../../formal/SSBX/Foundation/Wen/WenyanText.lean):
- `«不动»`, `«互»`, `«错»`, `«综»`, `«推»`, `«取»`, `«终»` — 文言 program keywords
- `«设时»`, `«翻爻»`, `«比爻»` — typed instructions
- 这些是 surface-syntax keywords，等价于 Wenyan-programming-language 之 `for/let/end`

[`Foundation/Wen/DaoSource.lean`](../../formal/SSBX/Foundation/Wen/DaoSource.lean):
- `«道源»`, `«道程»`, `«道源_解»` 等 — 「道」之自释 demo
- 保留 CJK 因为这是 Wenyan-language 之 source code 演示

[`Foundation/Wen/WenEval.lean`](../../formal/SSBX/Foundation/Wen/WenEval.lean):
- `«解执»`, `«道判源»`, `«端到端_乾»` etc.
- 同上

[`Foundation/Wen/MetaInterp/*.lean`](../../formal/SSBX/Foundation/Wen/MetaInterp/) (~20 files):
- 整个 meta-interpreter 是 Wenyan-language subsystem
- 留 CJK identifiers

## 6 · Renaming policy summary (Phase R)

| 类 | 操作 | 例 |
|---|---|---|
| Pinyin atoms (qian/kun/...) | → 描述性 English | qian → heaven |
| 「ASCII pinyin compound」 (jiFaint/etc.) | → 描述性 English | jiFaint → trace |
| CJK-quoted («仁»/«乾»/...) doctrinal | → 描述性 English | «仁» → benevolence |
| CJK-quoted architectural substrate (Roster/YiCore/Wenyan) | **保留 CJK** | `«加»`, `«一»` 不动 |
| Snake_case Chinese-prose theorem names | → 语义 English | shengsheng_buxi → unceasing_generation |
| 5 prefixed proper-noun theorems (zhuangzi_/sunzi_/chuci_/zhongyong_) | **preserve prefix** | zhuangzi_qi_state → zhuangzi_equal_state |
| Cardinality-based types (Cell128/Cell256) | → R-index (R7/R8) | Cell128 → R7 |

## 7 · 验证 (round-trip + spot-check)

[`Foundation/Lang/Lexicon.lean`](../../formal/SSBX/Foundation/Lang/Lexicon.lean):

```lean
theorem lexicon_summary :
    Lookup.englishOf "乾" = some "heaven" ∧
    Lookup.englishOf "仁" = some "benevolence" ∧
    Lookup.englishOf "既济" = some "complete" ∧
    Lookup.englishOf "印" = some "imprint" ∧
    Lookup.chineseOf "wisdom" = some "智" ∧
    hexagram.length = 64

theorem lexicon_round_trip_chinese :
    ∀ e ∈ Lookup.allEntries,
      ∃ en, Lookup.englishOf e.chinese = some en
        ∧ Lookup.chineseOf en ≠ none

theorem lexicon_round_trip_witnesses :
    Lookup.chineseOf "heaven" = some "乾" ∧
    Lookup.chineseOf "benevolence" = some "仁" ∧
    Lookup.chineseOf "complete" = some "既济" ∧
    Lookup.chineseOf "imprint" = some "印" ∧
    Lookup.chineseOf "wisdom" = some "智" ∧
    Lookup.chineseOf "greaterYang" = some "太阳" ∧
    Lookup.chineseOf "fatherSon" = some "父子" ∧
    Lookup.chineseOf "thing" = some "物"
```

## 8 · 完整 Lexicon 表统计

| Table | Entries | Layer |
|---|---:|---|
| yao | 2 | R₁ |
| sixiang | 4 | R₂ |
| trigram | 8 | R₃ |
| ben | 4 | R₄ (Ben axis) |
| zheng | 4 | R₄ (Zheng axis) |
| hexagram | 64 | R₆ |
| confucian | 38 | mixed R₁-R₇ + doctrine |
| operators | 27 | mixed |
| wuLun | 5 | R₅ |
| **Total** | **156** | |

(微小数差因 yao + sixiang + trigram + ben + zheng + hexagram + confucian + operators + wuLun = 162 in Lexicon definition, 但有 6 entries 是 `bits = ""` 之 predicate/proper-noun-only entries.)

## 9 · 三向对齐之 design 原则

1. **Wen** 是 historical / pinyin alias，保留以支持 旧 codebase reference + Wenyan layer 与 doctrine source 之 mapping
2. **English** 是 canonical Lean identifier, 项目 main programming layer 之 surface
3. **Chinese** 是 doctrine canonical form, docstring / Sexp / Wenyan surface 之 primary

每对 `(wen, english, chinese)` 应有：
- `chineseOf english = some chinese` (English → Chinese 反向查)
- `chineseOf wen = some chinese` (Wen alias 也支持反向查)
- `englishOf chinese = some english` (Chinese → English 正向查)

唯一例外：多义 (motion 既是 Ben atom 动 也是 Kernel primitive 動 — same English 对两个 Chinese)。Lexicon 之 polysemy 由 `aka` 列表 + 不同 entry 表达。

## 10 · 后续 maintenance

新增 entries 时：
1. 加 entry 到 [`Foundation/Lang/Lexicon.lean`](../../formal/SSBX/Foundation/Lang/Lexicon.lean) 之适当 table
2. 更新本文档之对应表
3. 跑 `lexicon_round_trip_chinese` 验证 round-trip
4. 跑 `lake build SSBX` 验证 build

新增 architectural CJK identifier 时：
- 文档说明 architectural-substrate 之原因
- 加 `aka` alias to Lexicon for round-trip lookup
- 不进入英语命名 layer

## 附录 A — Lexicon 之 9 Tables 完整内容

详见 [`Foundation/Lang/Lexicon.lean`](../../formal/SSBX/Foundation/Lang/Lexicon.lean) lines 64-298. 8 table:
- § 1: `yao` (2 entries)
- § 2: `sixiang` (4 entries)
- § 3: `trigram` (8 entries)
- § 4: `ben` + `zheng` (4 + 4 entries)
- § 5: `hexagram` (64 entries, with `hexagram_count` theorem)
- § 6: `confucian` (38 entries — 五常/四端/八目/三纲/三才/喜怒哀乐/元亨利贞/善恶/etc.)
- § 7: `operators` (27 entries — Cayley/atomic/predicates)
- § 8: `wuLun` (5 entries)

## 附录 B — Phase R 之 39 commits 之 rename summary

| Phase | commits | range | 内容 |
|---|---:|---|---|
| R.1a-h | 8 | f2bec91..094c149 | R-layer atom renames (Trigram/Hexagram/SiXiang/Ben/Zheng/Cayley ops/Wuchang CJK/Confucian CJK/Names) |
| R.2a-c | 3 | c9250ea..441816c | Kernel doctrinal-core pinyin (terminus/center/benevolence/etc.) |
| R.3a-e | 5 | 65dc580..0707f95 | Eight + Lang renames (SiDuan/ShuSuan/Yuan.yi/hua/bian/tou) |
| R.4a-s | 19 | ef0e2d9..8e0c816 | Cell yin→imprint, theorem names English, Eight/Bagua theorems |
| R.5 | 1 | a2b6cbb | L-tower (Foundation/Squaring) integration |
| R.6 | 1 | 56e2341 | Drop opacity + bridge axioms (kernel native to R₇) |
| R.7 | 1 | (commit) | Cell128/Cell256 → R7/R8 (drop Cell naming) |
| R.8 | 1 | 0195e49 | Squaring tower self-similarity isos |
| **Total** | **39** | | ~5000 line changes, 130+ files touched |

`lake build SSBX` clean throughout. 0 new sorries, 0 new axioms.
