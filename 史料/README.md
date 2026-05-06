# 史料

研究过程中之早期文档与已被取代之版本。本目录存档之前的研究路径——不在第一个完整版（三本文 / formal/SSBX 当前布局 / 真理 v12 模块化 / 四级生成 / 六表）的呈现范围内，但不舍弃，以为来路可追。

## 目录

| 文件 | 来源 | 性质 | 已被何处取代 |
|---|---|---|---|
| `daoli-v11.md` | 真理/ | 道理 v11 单体版 | `真理/daoli-v12-main.md` + 9 个 `daoli-v12-*.md`（v12 是 v11 严格扩展） |
| `daoli-v11.1.md` | 真理/ | v11.1 keystone refinement（53/54/55 法则 + 5 verifications + 2-category） | `真理/daoli-v12-frames.md` + `daoli-v12-fa-ze.md` + `daoli-v12-verifications.md` |
| `daoli-v12.md` | 真理/ | v12 单体合订 | 9 个 `daoli-v12-*.md` 模块化 |
| `生生不息.md` | docs/ | v9→v10 间「间开本/致知版」32 项改进总结 | `生生不息论_三本文完整版/03_补篇一_间开本_致知版/`（卷一–卷十）+ `01_正篇_v13.2/`（卷三–卷十五）|
| `间本体论_元三相与场修订稿.md` | docs/ | 間/Jian 五层架构早期修订稿 | `formal/SSBX/Foundation/Jian/Jian.lean` + `JianOntology.lean` + `四级生成/B_六征体系.md` + `六表_/表一_六征本表.md` |
| `atom-derivation-report.md` | docs/ | 单字整合实施报告（221→43 CoreAtom） | `formal/SSBX/Foundation/Core/AtomDerivation.lean` + `MonadRoot.lean` |
| `生生不息论_v14_形式证明骨架版.md` | 根 | v14 proof skeleton 草稿 | `生生不息论_三本文完整版/01_正篇_v13.2/`（卷〇/十三/十四/附录甲/附录乙）+ `formal/SSBX/Core.lean` + `formal/SSBX/Foundation/Core/MathAxiomMap.lean` |

## 仍保留主目录之早期/开放文档

不在本目录，但有相关性，记录于此：

- `真理/urbit-jian-isomorphism.md`：Urbit ↔ 间/生生不息同构分析；P1–P8 仍是开放工程清单（对应 `formal/SSBX/Foundation/{Jian,Yi,Bagua}/` 之未来 Lean 工作），故保留主目录。
- `formal/SSBX/notes/monad-root-plan.md`（原 `docs/monad-root-plan.md`）：活的 contributor 契约文档（ConceptDAG / ConstructionDAG / MonadDAG 三图分判 + 16 项核心证明清单 + 8 条验收标准），从 docs/ 迁入 formal/SSBX/notes/ 归位。

## 早期文档之遗漏点（记录，待后整合）

扫描时识别到这些只在早期文档存在、未被当前规范主文档覆盖的内容。整合工作未做；本节是 todo 清单。

### 来自 `daoli-v12.md`（单体）

- §21 「Implications」整章 21 条 framework 之 living significance（21.1–21.21）。模块化版本仅在 main 之 §3 三面 + §27 文言宣言点到，未保留 21 条逐项。
  - 建议归宿：`真理/daoli-v12-implications.md`（新模块）。
- §24 6 项 v12-specific test cases（三 names cross-applicability / 4 aspects empirical features 与 mutual perspectival / 文 = pattern AND culture / 8 frames cross-applicability / 矫正 mechanism / cross-cultural attestation strict）。
  - 建议归宿：扩 `真理/daoli-v12-verifications.md`（已有 5 verifications，加这 6 项 cases）。

### 来自 `生生不息.md`（v9→v10 总结）

- §30 「原词 / 问题词 → 改进后」完整对照表（约 20 项，field/focus/relation/state/... → 境/著/系/态/...）。
  - 建议归宿：`生生不息论_三本文完整版/00_编校说明/02_词汇迁移历史.md`。
- §31 「总体最终总式」压缩段（从「境生间」到「道为能续而不夺共续」）。
  - 建议归宿：`三本文完整版/00_编校说明/` 附录或合入 `01_正篇/19_卷十七_总链与全式.md`。
- §32 4 项 「下一步还可继续改的方向」（全文三相化恢复 / 单字元生成表 21 字 / 公理/定理/推论分层 / 8 域应用验例）。
  - 建议归宿：合并入开放课题清单（与 urbit P1–P8 同处）或 `三本文完整版/00_编校说明/`。

### 来自 `间本体论_元三相与场修订稿.md`

- §二、三 「位 = 物 ∩ 間，括除 動」等"括除/相交"语义的散文读法。Lean 有 `bracketedRoot` 字段但缺自然语言读法说明。
- §五 「合成不可逆」具体说明（位+際 不唯一确定一个網）。Lean 有 `network_composition_arrangement_not_unique` 定理但散文动机已压缩。
  - 建议归宿：补 `formal/SSBX/notes/JianOntology.md`（已有，可加节）。

### 来自 `atom-derivation-report.md`

- 「已经可以整合的字」按 9 类目（文法 / 物面 / 生面 / 审校 / 价值 / 模型 / 证明 / 心智 / 人行）的 ~150 个单字归并清单。Lean 中按字典序排列，未保留义类编组。
- 「仍需义项拆分」27 个字的具体义位 split 候选（生1/生2/生3、之1/之2/之3、天1/天2/天3、子1/子2 等）。Lean 仅有 `needsSenseSplitAtoms` 占位 list。
- 「暂不应整合」原始接口 9 项 + 派生接口记号 ~22 项的英文记号 → 单字 dispatch 映射表（`I_F := 域`、`oplus_F := 生`、`κ := 格权` 等）。
- 尾部两个「和谐映射」建议（`型 := 模形 / 格形`、`性 ≈ 心生`）。
  - 建议归宿：`formal/SSBX/notes/atom-naming.md`（新建，作为 `AtomDerivation.lean` 之人类可读伴随）。

### 来自 `生生不息论_v14_形式证明骨架版.md`

- §十二 完整 11 行**数学公设字元生成表**（数学域 × 现代公设/结构 × 字元生成/映射 × 为何需另加结构 × 形式位阶）。`MathAxiomMap.lean` 是 Lean 形式，缺这张人类可读对照大表。
- §十二 「完备数学的限定命题」论证（哥德尔不完备 vs 本论"完备"含义辨析的关键段落）。
- §十一 「定义、公理、接口假设分离」三类句子的明确分类原则。
- §十四 4 项 「下一步机器验证任务」（迁移元定理至 Lean / MathAxiomMap 注册表 / 接口假设替换为定义 / 推荐系统案例小模型）。
  - 建议归宿：
    - 数学公设大表 + 完备限定命题 → `生生不息论_三本文完整版/01_正篇_v13.2/23_附录丙_数学公设字元生成表.md`（新增附录）或 `formal/SSBX/notes/math-axiom-map.md`。
    - 三分原则 + roadmap → `formal/SSBX/notes/v14-roadmap.md`。

## 注意

本目录仅作历史保存。更新中现规范文档后，**不要回头修改本目录之文件**——它们是 frozen snapshot。新发现/再发现之内容应进现规范，史料之原貌保持。
