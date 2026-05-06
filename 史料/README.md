# 史料

研究过程中之早期文档与已被取代之版本。本目录存档之前的研究路径——不在第一个完整版（三本文 / formal/SSBX 当前布局 / 真理 v12 模块化 / 四级生成 / 六表）的呈现范围内，但不舍弃，以为来路可追。

## 目录

| 文件 | 来源 | 性质 | 已被何处取代 |
|---|---|---|---|
| `daoli-v11.md` | 真理/ | 道理 v11 单体版 | `真理/daoli-v12-main.md` + 9 个 `daoli-v12-*.md`（v12 是 v11 严格扩展） |
| `daoli-v11.1.md` | 真理/ | v11.1 keystone refinement（53/54/55 法则 + 5 verifications + 2-category） | `真理/daoli-v12-frames.md` + `daoli-v12-fa-ze.md` + `daoli-v12-verifications.md` |
| `daoli-v12.md` | 真理/ | v12 单体合订 | 9 个 `daoli-v12-*.md` 模块化 |
| `生生不息.md` | docs/ | v9→v10 间「间开本/致知版」32 项改进总结 | `生生不息论_三本文完整版/03_补篇一_间开本_致知版/`（卷一–卷十）+ `01_正篇_v13.2/`（卷三–卷十五）|
| `间本体论_元三相与场修订稿.md` | docs/ | 間/Jian 五层架构早期修订稿 | `formal/SSBX/Foundation/Jian/Jian.lean` + `JianOntology.lean` + `四级生成_太极两翼四象八卦/B_六征体系.md` + `六表_实虚史真/表一_六征本表.md` |
| `atom-derivation-report.md` | docs/ | 单字整合实施报告（221→43 CoreAtom） | `formal/SSBX/Foundation/Core/AtomDerivation.lean` + `MonadRoot.lean` |
| `生生不息论_v14_形式证明骨架版.md` | 根 | v14 proof skeleton 草稿 | `生生不息论_三本文完整版/01_正篇_v13.2/`（卷〇/十三/十四/附录甲/附录乙）+ `formal/SSBX/Core.lean` + `formal/SSBX/Foundation/Core/MathAxiomMap.lean` |

## 仍保留主目录之早期/开放文档

不在本目录，但有相关性，记录于此：

- `真理/urbit-jian-isomorphism.md`：Urbit ↔ 间/生生不息同构分析；P1–P8 仍是开放工程清单（对应 `formal/SSBX/Foundation/{Jian,Yi,Bagua}/` 之未来 Lean 工作），故保留主目录。
- `formal/SSBX/notes/monad-root-plan.md`（原 `docs/monad-root-plan.md`）：活的 contributor 契约文档（ConceptDAG / ConstructionDAG / MonadDAG 三图分判 + 16 项核心证明清单 + 8 条验收标准），从 docs/ 迁入 formal/SSBX/notes/ 归位。

## 早期文档之遗漏点（已整合，回填去向）

扫描时识别到这些只在早期文档存在、未被当前规范主文档覆盖的内容。整合已完成；下文每节末标 ✓ 与实际去向。

### 来自 `daoli-v12.md`（单体）

- §21 「Implications」整章 21 条 framework 之 living significance（21.1–21.21）。
  - ✓ 迁入 `真理/daoli-v12-implications.md`（新模块，21 条全保留）。
- §24 6 项 v12-specific test cases（三 names cross-applicability / 4 aspects empirical features 与 mutual perspectival / 文 = pattern AND culture / 8 frames cross-applicability / 矫正 mechanism / cross-cultural attestation strict）。
  - ✓ 迁入 `真理/daoli-v12-verifications.md` 末尾 §7。

### 来自 `生生不息.md`（v9→v10 总结）

- §30 「原词 / 问题词 → 改进后」完整对照表（约 20 项，field/focus/relation/state/... → 境/著/系/态/...）。
- §31 「总体最终总式」压缩段（从「境生间」到「道为能续而不夺共续」）。
- §32 4 项 「下一步还可继续改的方向」（全文三相化恢复 / 单字元生成表 21 字 / 公理/定理/推论分层 / 8 域应用验例）。
  - ✓ 三节合并迁入 `生生不息论_三本文完整版/00_编校说明/02_词汇迁移与早期方向.md`（新增编校附录），并对每项 v10 方向标注当前 v13.2 + 三本文阶段之落地状态。

### 来自 `间本体论_元三相与场修订稿.md`

- §二、三 「位 = 物 ∩ 間，括除 動」等"括除/相交"语义的散文读法。Lean 有 `bracketedRoot` 字段但缺自然语言读法说明。
- §三 0 维坍缩说明（「位的静面不是缺数据，而是结构声明」）。
- §五 「合成不可逆」具体说明（位+際 不唯一确定一个網）。
  - ✓ 三节迁入 `formal/SSBX/notes/JianOntology.md` 三个新增 subsection（散文读法 / 0 维坍缩说明 / 合成是涌现的）。

### 来自 `atom-derivation-report.md`

- 「已经可以整合的字」按 9 类目（文法 / 物面 / 生面 / 审校 / 价值 / 模型 / 证明 / 心智 / 人行）的 ~150 个单字归并清单。
- 「仍需义项拆分」27 个字的具体义位 split 候选。
- 「暂不应整合」原始接口 + 派生接口记号 → 单字 dispatch 映射表。
- 尾部两个「和谐映射」建议（`型 := 模形 / 格形`、`性 ≈ 心生`）。
  - ✓ 全部迁入 `formal/SSBX/notes/atom-naming.md`（新建，作为 `Foundation/Core/AtomDerivation.lean` 之人类可读伴随）。

### 来自 `生生不息论_v14_形式证明骨架版.md`

- §十二 完整 11 行**数学公设字元生成表** + 元定理六（数学接口有根）+ 「完备数学的限定命题」论证。
  - ✓ 迁入 `formal/SSBX/notes/math-axiom-map.md`（新建，伴随 `Foundation/Core/MathAxiomMap.lean`）。
- §十一 「定义、公理、接口假设分离」三分原则 + §十四 4 项机器验证 roadmap。
  - ✓ 迁入 `formal/SSBX/notes/v14-roadmap.md`（新建，含与现状对照表）。

## 注意

本目录仅作历史保存。更新中现规范文档后，**不要回头修改本目录之文件**——它们是 frozen snapshot。新发现/再发现之内容应进现规范，史料之原貌保持。
