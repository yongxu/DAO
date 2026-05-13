# 法家核心词 Overlay Mapping

> 状态：draft v0.1 (2026-05-13)
> 范围：把法家核心字/词映射到现有 `R0..R8` root language tree 条目，作为审名、教学和引用索引。
> 口径：本页不改 canonical root 名，不新增坐标，也不把法家政治术语声称为形式系统 primitive。形式真值仍以 bitstring、cell / operator role 和 XOR mask 为准。

## 读法原则

1. `法 / 術 / 勢` 是法家三组功能，不是三个位。`勢` 已在 R4 有公开字面位置；`法` 与 `術` 则要分别映射到制度尺度和操作技术。
2. `法` 优先读作 public measure / institution：`节`、`綱 / 維`、`鼎 / 井`。不要把 `法` 只读成 punishment。
3. `術` 优先读作 hidden method / administrative technique：`易內`、`徑`、`觀`、`印`。不要把 `術` 直接公开成德目或道体。
4. `刑 / 赏 / 罚` 是执行机制 overlay：刑罚锚在 `噬嗑 / 剥 / 损`，赏赐锚在 `益 / 晋 / 升 / 大有`。
5. `名 / 实 / 参验 / 考课` 是可审计治理链条，优先落到 `記 / 述 / 質 / 印 / 觀 / 中孚`，而不是另造一套名实 primitive。

## 总表

| 法家词 | 推荐锚点 | 辅助锚点 | 读法 | 状态 |
|---|---|---|---|---|
| 法 | `R6-ooxxox-cell` 节；`R5-xoxxo-cell` 綱；`R5-xoxxx-cell` 維 | `R6-xoooxo-cell` 鼎、`R6-xooxox-cell` 井 | 公开尺度、制度纲维、可执行的公共规则 | 强 overlay |
| 術 | `R5-oooox-operator` 易內；`R5-oooxo-cell` 徑 | `R6-xxxxoo-cell` 观；R7/R8 `印` operators | 内藏的操作技术、行政方法、观察与验证 | 强 overlay |
| 勢 | R4 `物勢 / 動勢 / 間勢 / 事勢` family | `R5-ooooo-cell` 力、`R6-ooooxx-cell` 大壮、`R6-ooooxo-cell` 大有 | 位势、权势、可动员的力与位置 | 已有字面锚点 |
| 君 / 主 | `R3-ooo-cell` 乾；`R6-ooxxxx-cell` 临 | `R6-xoxxxx-cell` 师、`R6-ooooxo-cell` 大有 | 主位、临下、统摄与持有资源 | 说明性 overlay |
| 臣 / 吏 | `R5-xoxxo-cell` 綱；`R5-xoxxx-cell` 維 | `R6-xxxxoo-cell` 观、`R6-xoxxoo-cell` 涣 | 官僚网络、系属关系、可观察的职责分派 | 说明性 overlay |
| 名 | `R5-xxxxo-cell` 記；`R5-xxxxx-cell` 述 | `R5-xxooo-cell` 象、`R4-xxxx-cell` 事時 | 名号、职名、可记录的 claim | 强 overlay |
| 实 | `R5-ooxoo-cell` 質；`R6-ooxxoo-cell` 中孚 | R7/R8 `印` operators、`R6-oxxooo-cell` 无妄 | 实绩、质实、可验之内实 | 强 overlay |
| 刑名 | `記 / 述 + 質 / 印` | `R6-xoxooo-cell` 讼、`R6-oxxoxo-cell` 噬嗑 | 名称、职责、实绩与裁断之间的对应 | 强 overlay |
| 参验 | R7/R8 `印` operators | `R5-xxooo-cell` 象、`R5-xxoox-cell` 占、`R6-xxxxoo-cell` 观 | cross-check、witness、evidence、verification | 强 overlay |
| 考课 | `記 / 述 + 觀 + 印` | `R6-ooxxoo-cell` 中孚、`R6-oxxooo-cell` 无妄 | 记录、观察、核验、按实绩评定 | 强 overlay |
| 赏 | `R6-oxxxoo-cell` 益；`R6-xxxoxo-cell` 晋；`R6-xooxxx-cell` 升 | `R6-ooooxo-cell` 大有 | 增益、晋升、授予资源 | 强 overlay |
| 罚 | `R6-oxxoxo-cell` 噬嗑 | `R6-xxxxxo-cell` 剥、`R6-ooxxxo-cell` 损、`R6-xoxoox-cell` 困 | 咬断、削夺、损减、限制 | 强 overlay |
| 刑 | `R6-oxxoxo-cell` 噬嗑 | `R6-ooxxox-cell` 节、`R6-xxoxxo-cell` 艮 | 裁断、止禁、强制执行 | 强 overlay |
| 令 | `R6-ooxxxx-cell` 临；`R6-xoxxxx-cell` 师 | `R5-xxxxx-cell` 述、`R6-xxxxoo-cell` 观 | 命令下达、组织执行、公开可见 | 说明性 overlay |
| 禁 | `R6-ooxxox-cell` 节；`R6-xxoxxo-cell` 艮 | `R6-oxxoxo-cell` 噬嗑 | 限制、停止、禁令与执行 | 说明性 overlay |
| 权 / 柄 | `R5-ooooo-cell` 力；R4 `勢` family | `R6-ooooxx-cell` 大壮、`R6-ooooxo-cell` 大有 | 二柄、权力抓手、可动员的位置力 | 强 overlay |
| 公 | `R6-xoooxo-cell` 鼎；`R6-xooxox-cell` 井 | `R6-ooxxox-cell` 节、`R6-ooxxoo-cell` 中孚 | 公器、公度、公共供给与公共可验 | 说明性 overlay |
| 治 | `R6-xoooxo-cell` 鼎；`R6-xooxox-cell` 井；`R6-xxxxox-cell` 比 | `R6-oooxxx-cell` 泰、`R6-oxoxox-cell` 既济 | 制度成形、公共供给、聚合与秩序完成 | 强 overlay |
| 乱 | `R6-xxxooo-cell` 否；`R6-xooxxo-cell` 蛊；`R6-xoxoox-cell` 困 | `R6-xxoxox-cell` 蹇、`R6-xxxxxo-cell` 剥、`R6-xoxoxo-cell` 未济 | 阻塞、败坏、困蹇、剥落、未成 | 说明性 overlay |

## 法術勢细分

| 核心词 | 首选 | 次选 | 不建议 |
|---|---|---|---|
| 法 | 节、綱、維 | 鼎、井、观 | 不把 `法` 直接等同 `刑`；刑只是执行面 |
| 術 | 易內、徑 | 观、印、改+易內 | 不把 `術` 说成 public virtue；它是操作方法与控制技术 |
| 勢 | R4 勢 family、力 | 大壮、大有、临、师 | 不把 `勢` 只读成个人能力；重点是位势和结构力 |

## 名实链条

| 环节 | 推荐结构 | 说明 |
|---|---|---|
| 名 | `記 / 述 / 象` | 记录、陈述与可指称的表象。 |
| 实 | `質 / 中孚 / 无妄` | 质实、内实、无妄。 |
| 验 | `印 / 观` | 证迹与观察。 |
| 断 | `讼 / 噬嗑 / 节` | 争讼、裁断、以尺度执行。 |
| 课 | `記 + 觀 + 印` | 把职责、观测和证迹合为行政考课。 |

## 赏罚二柄

| 机制 | 推荐锚点 | 说明 |
|---|---|---|
| 赏 | `益 / 晋 / 升 / 大有` | 增益、晋升、授予与资源持有。 |
| 罚 | `噬嗑 / 剥 / 损 / 困` | 裁断、削夺、损减与限制。 |
| 二柄 | `力 + 勢`；`赏 / 罚` 两组 cell | 柄是可操作的权力抓手，不是单独 root。 |
| 信赏必罚 | `中孚 + 印 + 赏罚锚点` | 重点是可预期、可验、按名实执行。 |

## 国家术语

| 词 | 推荐锚点 | 说明 |
|---|---|---|
| 富国 | `大有 / 益 / 井` | 资源持有、增益与公共供给。 |
| 强兵 | `大壮 / 师 / 比` | 力势、军队组织与聚合。 |
| 耕战 | `颐 / 井 + 师` | 供养、公共生产与军事动员。 |
| 变法 | `革`；`改 / 變 / 變化` operators | 制度更张；cell 用 `革`，动作读为 operator 组合。 |
| 定分 | `节 / 綱 / 維 / 記` | 定尺度、定职分、定记录。 |
| 一法 | `节 / 鼎 / 井` | 统一公共尺度与制度器物；不应读成 single bit。 |

## 引用建议

- 正式 root table 仍引用 `layers/R*.md` 中的 `id`、`ox`、`role` 和 public candidate。
- 法家术语出现在 prose 时，可引用本页表格作为 overlay index。
- 对外文档中可说“`法 / 術 / 勢` have stable overlay anchors”，但不要说它们已经是 three primitive roots。
- `刑名 / 赏罚 / 考课` 这类组合词，优先引用组合锚点；不要为了它们新增 public root name。
