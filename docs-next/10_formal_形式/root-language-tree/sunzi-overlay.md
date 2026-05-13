# 孙子兵法核心词 Overlay Mapping

> 状态：draft v0.1 (2026-05-13)
> 范围：把《孙子兵法》与兵家核心字/词映射到现有 `R0..R8` root language tree 条目，作为审名、教学和引用索引。
> 口径：本页不改 canonical root 名，不新增坐标，也不把兵法术语声称为形式系统 primitive。形式真值仍以 bitstring、cell / operator role 和 XOR mask 为准。

## 读法原则

1. `兵` 的首锚是 `师`，但孙子不是只讲战争动作；更大的结构是 `计 / 形 / 势 / 虚实 / 奇正 / 地 / 间`。
2. `道天地将法` 是孙子的 five factors，不是五个新 root：`道` 用全局 anchor，`天` 用乾与时，`地` 用坤与地形，`将` 用师/临/观，`法` 用节/纲/维。
3. `形 / 勢 / 虛實` 要分开：`形` 是可见态势，`勢` 是结构力与位势，`虛實` 是可攻可守的强弱分布。
4. `奇 / 正` 不是 moral right/wrong。`正` 是 regular disposition，`奇` 是 nonzero transform / surprise action；形式上更接近 operator overlay。
5. `用间` 优先落到 R4 `間` family、R7/R8 `印` 与 `無跡 / 有跡`，不要把间谍术语直接当成因位本体。

## 总表

| 兵家词 | 推荐锚点 | 辅助锚点 | 读法 | 状态 |
|---|---|---|---|---|
| 兵 | `R6-xoxxxx-cell` 师 | `R6-xxxxox-cell` 比、`R6-ooooxx-cell` 大壮、`R5-ooooo-cell` 力 | 军队、兵力、组织成军 | 已公开 |
| 战 | `R6-xoxxxx-cell` 师；`R6-xoxooo-cell` 讼 | `R6-oxxoxo-cell` 噬嗑、`R6-oxxoxx-cell` 震 | 交兵、冲突、强制裁断与震动 | 强 overlay |
| 计 | `R6-xxxxoo-cell` 观；`R5-xxooo-cell` 象；`R5-xxoox-cell` 占 | R4 `幾 / 機 / 兆` cells、`R5-xxxxo-cell` 記 | 观势、取象、测兆、庙算 | 强 overlay |
| 谋 | `R4-xxxx-cell` 事時；`R6-xxxxoo-cell` 观 | `R5-xxxxx-cell` 述、`易內` operators、R8 `未 / 已 / 今` Shi states | 未发之前的筹划、叙述与时态判断 | 强 overlay |
| 道 | `ROOT-undivided`；`OX["oooooooo"]` | R8 `道·*` family | 上下同欲、全局方向；借道 anchor 读，不改道家/儒家义理 | 已公开 |
| 天 | `R3-ooo-cell` 乾；R2 四时 cells | R4 `*時` family、R8 `未 / 已 / 今` states | 阴阳、寒暑、时制、先后 | 强 overlay |
| 地 | `R3-xxx-cell` 坤；R4 `間*` family | `R6-xoxxox-cell` 坎、`R6-xxoxxo-cell` 艮、`R6-xooxoo-cell` 巽 | 远近、险易、广狭、死生之地形 | 强 overlay |
| 将 | `R6-xoxxxx-cell` 师；`R6-ooxxxx-cell` 临；`R6-xxxxoo-cell` 观 | `R3-ooo-cell` 乾、`R6-ooxxoo-cell` 中孚 | 将帅统摄、临事、观势、可信 | 说明性 overlay |
| 法 | `R6-ooxxox-cell` 节；`R5-xoxxo-cell` 綱；`R5-xoxxx-cell` 維 | `R6-xoxxxx-cell` 师、`R5-xxxxx-cell` 述 | 曲制、官道、主用、军令与组织法度 | 强 overlay |
| 形 | `R5-ooxoo-cell` 質；`R5-xxooo-cell` 象 | `R6-oxooxo-cell` 离、R7 `有跡·*` cells | 可见形态、可观测部署、显迹 | 强 overlay |
| 無形 | R7 `無跡·*` cells | `R6-xxoooo-cell` 遁、`R6-xoxxox-cell` 坎 | 形兵之极，至于无形；不可直接等同 metaphysical 無 | 强 overlay |
| 勢 | R4 `物勢 / 動勢 / 間勢 / 事勢` family | `R6-ooooxx-cell` 大壮、`R6-ooxxxx-cell` 临、`R6-xoxxxx-cell` 师 | 结构势能、位势、可借之力 | 已有字面锚点 |
| 虛 | `R1-x-cell` 阴/虚 | `R6-xoxxox-cell` 坎、R7 `無跡` family | 虚处、空隙、隐伏、可诱之位 | 已有义理锚点 |
| 实 | `R1-o-cell` 阳/实；`R5-ooxoo-cell` 質 | `R6-ooxxoo-cell` 中孚、`R6-ooooxo-cell` 大有 | 实处、重兵、质实、可据之位 | 已有义理锚点 |
| 奇 | nonzero XOR operator family | `易 / 變 / 變化 / 改變 / 易外` operators、R7 `無跡` | 奇兵、非常道、出其不意 | 强 overlay |
| 正 | `R6-oooooo-operator` 恒；`R6-xoxxxx-cell` 师 | `R6-ooxxox-cell` 节、`R5-xoxxo-cell` 綱 | 正兵、常形、regular disposition | 强 overlay |
| 攻 | `R6-ooxxxx-cell` 临；`R6-oxxoxo-cell` 噬嗑 | `R6-oxxoxx-cell` 震、`R6-xoxxxx-cell` 师 | 临敌、攻取、突破、震动 | 强 overlay |
| 守 | `R6-xxoxxo-cell` 艮；`R6-oooxxo-cell` 大畜 | `R6-oooxox-cell` 需、`R6-xxxxxx-cell` 坤 | 守固、止、蓄、待 | 强 overlay |
| 胜 | `R6-oxoxox-cell` 既济；`R6-oooxxx-cell` 泰 | `R6-xxxxox-cell` 比、`R6-xoxoxx-cell` 解 | 成功闭合、通泰、聚合、解困 | 强 overlay |
| 败 | `R6-xxxooo-cell` 否；`R6-xoxoox-cell` 困 | `R6-xxoxox-cell` 蹇、`R6-xxxxxo-cell` 剥、`R6-xoxoxo-cell` 未济 | 阻塞、困顿、险阻、剥落、未成 | 说明性 overlay |
| 全 | `R6-oooxxx-cell` 泰；`R6-oxoxox-cell` 既济 | `R6-xxxxox-cell` 比、`R6-ooxxoo-cell` 中孚 | 全胜、全军、结构不破 | 强 overlay |
| 破 | `R6-xxxxxo-cell` 剥；`R6-oxxoxo-cell` 噬嗑 | `R6-ooxxxo-cell` 损 | 破军、剥夺、咬断、损减 | 强 overlay |
| 利 / 害 | `R6-oxxxoo-cell` 益；`R6-ooxxxo-cell` 损 | `R6-ooooxo-cell` 大有、`R6-xoxoox-cell` 困 | 利害相权、增益与损害 | 强 overlay |
| 间 | R4 `間幾 / 間勢 / 間機 / 間時` family | R7/R8 `印` operators、R7 `無跡 / 有跡` | 间隔、关系、情报通道、间者 | 强 overlay |

## 五事

| 五事 | 推荐锚点 | 说明 |
|---|---|---|
| 道 | `ROOT-undivided`；道 anchor | 上下同欲、全局方向。 |
| 天 | 乾；R2 四时；R4 `*時` | 阴阳、寒暑、时制、先后。 |
| 地 | 坤；R4 `間*`；坎/艮/巽 | 远近、险易、广狭、死生。 |
| 将 | 师、临、观、中孚 | 智、信、仁、勇、严的统摄位置。 |
| 法 | 节、綱、維、述 | 曲制、官道、主用、军令。 |

## 七计

| 七计 | 推荐锚点 | 说明 |
|---|---|---|
| 主孰有道 | 道 anchor、比 | 上下同欲与组织聚合。 |
| 将孰有能 | 师、临、观、力 | 将帅能力、临事与观势。 |
| 天地孰得 | 乾/坤、R2 四时、R4 `間 / 時` | 时地条件是否得宜。 |
| 法令孰行 | 节、綱、維、述 | 令能否贯彻成组织行为。 |
| 兵众孰强 | 师、比、大壮、力 | 兵众规模、凝聚与强度。 |
| 士卒孰练 | 小畜、大畜、履、渐 | 训练、蓄养、践履、渐进。 |
| 赏罚孰明 | 益、晋、噬嗑、剥、损、离/观 | 增益晋升与刑罚削夺，都必须可见可审。 |

## 形势虚实

| 词 | 推荐结构 | 说明 |
|---|---|---|
| 形 | `質 / 象 / 有跡` | 可见部署、可审态势。 |
| 势 | R4 `勢` family + `大壮 / 临 / 师` | 位势与结构力，不只是兵力多少。 |
| 虚 | `阴/虚 / 坎 / 無跡` | 空隙、隐伏、诱敌之处。 |
| 实 | `阳/实 / 質 / 大有 / 中孚` | 重实、可据、可信。 |
| 分合 | `涣 / 萃 / 比 / 解` | 分散、聚集、保持、解结。 |
| 疾徐 | `震 / 渐 / 需` | 疾如震，徐如渐，待如需。 |
| 迂直 | `徑 / 達 / 遁 / 临` | 直径、迂回、退避与临敌。 |
| 先后 | R8 `未 / 已 / 今` family；R4 `*時` | 先知、先胜后战、时态判断。 |

## 奇正与诡道

| 词 | 推荐锚点 | 说明 |
|---|---|---|
| 正 | `恒 / 师 / 节` | 常形、正兵、规则部署。 |
| 奇 | nonzero XOR operators | 变换、出奇、unexpected transform。 |
| 诡 | `奇 + 無跡 + 变` | 兵者诡道：遮蔽迹象并改变对手预期，不是新增伦理词。 |
| 示形 | `象 / 有跡 / 观` | 显示给敌方看的形。 |
| 隐形 | `無跡 / 坎 / 遁` | 藏形、伏势、退藏。 |
| 诱 | `虚 / 易外 / 观` | 外示可取之象，引敌入势。 |

## 谋攻层级

| 孙子层级 | 推荐锚点 | 说明 |
|---|---|---|
| 伐谋 | `观 / 幾 / 機 / 記` | 先破其计划与判断。 |
| 伐交 | `比 / 同人 / 合 / 契` | 破其联盟与关系。 |
| 伐兵 | `师 / 噬嗑 / 震` | 交兵、突破、震动。 |
| 攻城 | `困 / 坎 / 大畜 / 噬嗑` | 围困、险阻、蓄攻与强制突破；不宜作为首选。 |
| 不战而屈人之兵 | `全 / 比 / 解 / 临` | 以势和关系使对方解兵，保全结构。 |

## 九地与地形

| 兵法地名 | 推荐锚点 | 说明 |
|---|---|---|
| 散地 | `涣` | 易散之地。 |
| 轻地 | `旅` | 轻入、行旅、未深。 |
| 争地 | `讼 / 临` | 必争之位、临敌之位。 |
| 交地 | `通 / 比 / 同人` | 往来相交、关系通达。 |
| 衢地 | `通 / 井 / 比` | 多方通衢与公共节点。 |
| 重地 | `大畜 / 坤 / 师` | 深入、重载、兵势已重。 |
| 圮地 | `蹇 / 坎 / 困` | 难行、险阻、困陷。 |
| 围地 | `困 / 坎 / 艮` | 围困、险陷、止塞。 |
| 死地 | `剥 / 否 / 噬嗑`；反转读 `复` | 死地不是 root；可作剥尽后求复的战术语境。 |

## 火攻与用间

| 词 | 推荐锚点 | 说明 |
|---|---|---|
| 火攻 | `R3-oxo-cell` 离；`R6-oxooxo-cell` 离 | `噬嗑 / 震` 作强制与震动辅助。 |
| 水攻 / 水势 | `坎 / 井 / 涣 / 解` | 水险、供给、散结与解困。 |
| 用间 | R4 `間*` family；`印 / 观 / 記 / 述` | 间者、证迹、观察、记录与回报。 |
| 因间 | R7 因位、`印` | 借因位与既有 trace。 |
| 内间 | `易內` | 内部通道与 inward access。 |
| 反间 | `易 / 錯 / 改變` | 反用敌间，改变其归属与预期。 |
| 死间 | `無跡 / 剥` | 高风险、去迹、不可回收；只作战术语境。 |
| 生间 | `有跡 / 复 / 述` | 能返而述，留下可用 trace。 |

## 引用建议

- 正式 root table 仍引用 `layers/R*.md` 中的 `id`、`ox`、`role` 和 public candidate。
- 孙子术语出现在 prose 时，可引用本页表格作为 overlay index。
- `道天地将法 / 形势虚实 / 奇正 / 用间` 可以说有稳定 overlay anchors，但不要说它们已经是 primitive roots。
- 若将来要把兵家词升入 public naming，优先审 `师 / 势 / 观 / 间 / 印` 相关条目；不要只改本页。
