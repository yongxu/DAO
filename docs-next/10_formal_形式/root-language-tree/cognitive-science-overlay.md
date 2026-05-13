# 认知科学概念 Overlay Mapping

> 状态：draft v0.1 (2026-05-13)
> 范围：把认知科学常用概念映射到现有 `R0..R8` root language tree 条目，作为审名、教学和跨学科引用索引。
> 口径：本页不改 canonical root 名，不新增坐标，也不把当代认知科学概念声称为形式系统 primitive。形式真值仍以 bitstring、cell / operator role 和 XOR mask 为准。

## 判断

整体是对得上的，但对上的方式不是“一个现代术语 = 一个 root”。更准确的说法是：

- 感知、注意、行动、记忆、预测、证据、学习、社会认知这些功能链条，有稳定 overlay anchors。
- 表征、概念、语言、推理、决策这些中层概念，可以用 `象 / 記 / 述 / 綱 / 維 / 觀 / 臨` 组合读。
- 意识、qualia、自由意志、概率权重、神经实现，只能作说明性 overlay；当前 tree 没有直接给出神经基质或数值概率。
- 形式上最接近的桥是：`cell = state / representation`，`operator = action / transition`，`印 = evidence / trace`，`投 = projection / prediction`，`未 / 已 / 今 = prospective / retrospective / present state`。

## 读法原则

1. 认知科学术语优先按 functional role 映射，不按心理学流派强行命名。
2. `觀 / 象 / 占 / 幾 / 機 / 兆` 是 perception、inference、salience 的核心锚点。
3. `作 / 履 / 徑 / 力 / 改 / 化 / 變` 是 action、agency、motor control 的核心锚点。
4. `記 / 述 / 已 / 有跡 / 印` 是 memory、record、evidence 的核心锚点。
5. `未 / 投 / 幾 / 兆 / 占` 是 prediction、prospection、generative projection 的核心锚点。
6. `易內 / 易外` 分别给 inward / outward attention 与 self/world boundary 的读法，但不等于现代 self 模型的全部。

## 总表

| 认知科学概念 | 推荐锚点 | 辅助锚点 | 读法 | 状态 |
|---|---|---|---|---|
| sensation / 感觉 | R4 `物幾 / 物機`；`R5-xxooo-cell` 象 | `R3-oxo-cell` 离、`R3-xox-cell` 坎 | 从物之迹象与枢机进入感觉表象 | 强 overlay |
| perception / 知觉 | `R6-xxxxoo-cell` 观；`R5-xxooo-cell` 象；`R5-xxoox-cell` 占 | R8 `道/未/已/今·观` family | 观、取象、占验，形成可用 percept | 强 overlay |
| attention / 注意 | `R6-ooxxxx-cell` 临；`R6-xxxxoo-cell` 观 | `易內 / 易外` operators、`R6-ooxxox-cell` 节 | 临其对象、选择焦点、内外调度 | 强 overlay |
| salience / 显著性 | R4 `幾 / 兆` cells；`R6-oxxoxx-cell` 震 | `R5-xxooo-cell` 象、`R8-*-今` states | 有迹象、突显、惊动、进入当前场 | 强 overlay |
| representation / 表征 | `R5-xxooo-cell` 象；`R5-xxxxo-cell` 記；`R5-xxxxx-cell` 述 | `R5-ooxoo-cell` 質 | 表象、记录、陈述；质实作为 grounded content | 强 overlay |
| concept / 概念 | `R5-xoxxo-cell` 綱；`R5-xoxxx-cell` 維 | `R5-xxooo-cell` 象、`R5-xxxxx-cell` 述 | 分类纲维、概念结构、可述 schema | 强 overlay |
| category / 范畴 | `綱 / 維` | `比 / 同人 / 合` | 以纲维聚合相似项和关系项 | 强 overlay |
| working memory / 工作记忆 | R8 `今·*` family；`R5-xxxxo-cell` 記 | `易內` operators、`R6-xxxxoo-cell` 观 | 当前可访问、可维持、可操作的记录 | 强 overlay |
| episodic memory / 情景记忆 | R8 `已·*` family；R7 `有跡·*` cells；`印` operators | `R5-xxxxo-cell` 記 | past trace、事件记录、可回溯证迹 | 强 overlay |
| semantic memory / 语义记忆 | `R5-xxxxx-cell` 述；`R5-xoxxo-cell` 綱；`R5-xoxxx-cell` 維 | `R5-xxooo-cell` 象 | 可陈述知识、概念网络、稳定语义结构 | 强 overlay |
| procedural memory / 程序性记忆 | `R5-oooxx-cell` 履；`R5-oooxo-cell` 徑 | `R6-oooooo-operator` 恒、`R6-oxxxxx-cell` 复 | 路径、践履、习惯化程序 | 强 overlay |
| prediction / 预测 | R8 `未·*` family；R8 `投` operators | `R4-xxoo-cell` 事幾、`R5-xxoox-cell` 占、`R6-xxxxoo-cell` 观 | future projection、见兆、占测 | 强 overlay |
| prediction error / 预测误差 | `投 + 印`；`未 / 已 / 今` cross-check | `改 / 變化` operators | 投射与证迹不合后触发更新 | 说明性 overlay |
| inference / 推断 | `幾 / 機 / 兆 + 占 / 觀` | `記 / 述` | 从迹象、枢机和记录推出判断 | 强 overlay |
| learning / 学习 | `改 / 變化` operators；`印` operators；`記` | `复 / 恒 / 履` | evidence-driven update，记录后形成习惯或技能 | 强 overlay |
| reinforcement / 强化 | `R6-oxxxoo-cell` 益；`R6-ooxxxo-cell` 损 | `R6-xxxoxo-cell` 晋、`R6-xxxxxo-cell` 剥 | reward / punishment、增益/损减 | 强 overlay |
| action / 行动 | `R5-oooox-cell` 作；`R5-oooxx-cell` 履 | `改 / 化 / 變` operators、`R5-ooooo-cell` 力 | enactment、treading、state transition | 强 overlay |
| agency / 能动性 | `R5-ooooo-cell` 力；`R5-oooox-cell` 作 | `易內` operators、`R6-ooxxoo-cell` 中孚 | 内在力、发作、可归属的行动 | 强 overlay |
| affordance / 可供性 | `R5-oooxo-cell` 徑；R4 `物機 / 間機` | R4 `勢` family、`R5-oooxx-cell` 履 | 环境给出的可行路径与可行动枢机 | 强 overlay |
| sensorimotor loop / 感知行动回路 | `觀 + 履 + 易內/易外` | `象 / 印 / 改` | 观测、行动、内外调度、证迹反馈 | 强 overlay |
| embodiment / 具身 | `履 / 作 / 徑 / 力` | `R6-ooxooo-cell` 履 | 认知落在身体路径与行动能力上 | 强 overlay |
| interoception / 内感受 | `易內` operators；`R6-ooxxoo-cell` 中孚 | `R6-xoxxox-cell` 坎、`R6-oxxxxo-cell` 颐 | inward sensing、内实、身体内部状态 | 说明性 overlay |
| emotion / 情绪 | `R3-oox-cell` 兑、`R3-xox-cell` 坎、`R3-oxx-cell` 震、`R3-xxo-cell` 艮 | `益 / 损` | 悦、险、震、止，以及 valence shift | 说明性 overlay |
| affective valence / 情感效价 | `益 / 损` | `兑 / 坎` | 正负效价可借增益/损减与悦/险读 | 说明性 overlay |
| consciousness access / 意识访问 | R8 `今·*` family；`R6-xxxxoo-cell` 观 | `記 / 述 / 易內` | 当前可访问、可报告、可内观 | 说明性 overlay |
| global workspace / 全局工作空间 | `今 + 觀 + 述` | `比 / 會 / 綱 / 維` | 当前广播、可述、可整合；非严格神经模型 | 说明性 overlay |
| metacognition / 元认知 | `易內 + 觀` | `印 / 記 / 述` | 对自身认知状态的观察、记录和校验 | 强 overlay |
| self-model / 自我模型 | `易內 + 記 / 述 + 履` | `中孚 / 无妄` | 自身行动、记录、叙述与内在一致性 | 说明性 overlay |
| social cognition / 社会认知 | `R6-oxoooo-cell` 同人；`R6-oxoxoo-cell` 家人 | `契 / 合 / 維 / 易外` | 他者、关系、共同体和外向建模 | 强 overlay |
| theory of mind / 心智理论 | `易外 + 觀 + 述` | `同人 / 契 / 合` | 对他者状态的外向观察与叙述建模 | 说明性 overlay |
| language / 语言 | `記 / 述 / 象` | `契 / 合 / 綱 / 維` | 记录、陈述、符号表象与共享约定 | 强 overlay |
| decision-making / 决策 | `臨 / 節 / 改` | `占 / 觀 / 赴 / 向` | 临事、限选、改变状态、趋赴目标 | 强 overlay |
| planning / 计划 | R8 `未·*` family；R8 `投` operators | `向 / 赴 / 徑 / 記` | prospective projection、目标方向、路径安排 | 强 overlay |
| executive control / 执行控制 | `節 / 臨 / 改+易內` | `綱 / 維 / 恒` | 抑制、选择、内向控制与稳定策略 | 强 overlay |

## 功能链条

| 链条 | 推荐结构 | 说明 |
|---|---|---|
| perception loop | `物幾/物機 -> 象 -> 觀 -> 記` | 从物的迹象/枢机生成表象，经观察进入记录。 |
| prediction loop | `未 + 投 -> 今 + 觀 -> 已 + 印` | 投射未来，在当前观察，用已然证迹校验。 |
| learning loop | `投/印 mismatch -> 改/變化 -> 記/履` | 预测与证据不合后更新，并沉淀为记录或技能。 |
| action loop | `易內 -> 徑/履/作 -> 易外 -> 印` | 内部选择路径，行动外化，再留下证迹。 |
| social loop | `易外 -> 同人/家人 -> 契/合/維 -> 述` | 外向建模他者，形成关系与共享叙述。 |

## 现代模型 Crosswalk

| 现代概念 | Root-tree 对应 | 说明 |
|---|---|---|
| state | cell | 当前 carrier element 或某层 cell reading。 |
| action / transition | operator | `lambda s, mask xor s` 的 action reading。 |
| observation | `觀 / 象 / 印` | 观察、表象、证迹。 |
| latent state | `無跡` | 未显迹或无因位读法；不等于 metaphysical 無。 |
| evidence | `印 / 有跡 / 記` | trace、witness、record。 |
| projection | `投 / 未` | projection bit 与 prospective Shi state。 |
| update | `改 / 變化` | 状态转换、模型修正。 |
| policy | `徑 / 履 / 臨 / 節` | 路径、执行、临事选择、限制控制。 |
| model | `象 / 記 / 述 / 綱 / 維` | 表象、记录、可述结构、schema。 |
| reward / cost | `益 / 损` | 增益和损减；没有数值 reward scale。 |

## 对不上或只能弱对上的部分

| 概念 | 目前状态 | 建议说法 |
|---|---|---|
| probability / 概率权重 | 无直接 root | 可在 prose 中说 `占 / 投 / 印` 支持 probabilistic reading，但 root table 不编码数值概率。 |
| neural substrate / 神经基质 | 无直接 root | 当前 tree 是功能/形式层，不是神经解剖层。 |
| qualia / 感质 | 弱 overlay | 可借 `今 + 觀 + 易內` 读当前内观经验，但不要声称已形式化 qualia。 |
| free will / 自由意志 | 弱 overlay | 可借 `agency / 改 / 易內` 讨论能动性，不作 metaphysical commitment。 |
| consciousness hard problem | 不映射 | 可列为外部哲学问题，不纳入 root naming。 |
| statistical learning weights | 无直接 root | 可用 `印 -> 改 -> 恒/履` 描述学习过程，但不表示参数矩阵。 |

## 引用建议

- 正式 root table 仍引用 `layers/R*.md` 中的 `id`、`ox`、`role` 和 public candidate。
- 认知科学术语出现在 prose 时，可引用本页表格作为 overlay index。
- 对外文档中可说“perception/action/memory/prediction have stable functional overlay anchors”，但不要说它们已经是 primitive roots。
- 若将来要增强形式化，对认知科学最有价值的扩展不是改字，而是给 `投 / 印 / 未 / 已 / 今` 增加更明确的 prediction-evidence-update examples。
