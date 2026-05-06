# SSBX Lean Codebase

生生不息论之 Lean 4 形式化。

## 目录布局

```
formal/SSBX/
├── Core.lean、Roster.lean        # 项、注册表、三值、最小模型、续接接口
├── Text/                         # 字 / 算子目录
│   ├── Glyph.lean                # 字与编号义位注册表
│   ├── WenyanOperators.lean      # 文言算子总表（源：wenyan-operators.md）
│   ├── Completeness.lean         # 字与算子覆盖定理
│   └── SenseSyntax.lean
├── Truth/                        # 真 / 语义 / claim 账本
│   ├── Basic.lean、ClaimLedger.lean、Semantics.lean
│   ├── Adequacy.lean、Absolute.lean
├── Model/Adequacy.lean           # 充足模型原则
├── Foundation/                   # 主体形式化（按簇分目录）
│   ├── Core/                     # 字根 · 注义 · 单根证书
│   │   ├── Yuan.lean、Monism.lean、MonadRoot.lean
│   │   ├── AtomDerivation.lean、MissingGlyphs.lean、MathAxiomMap.lean
│   │   ├── ShengshengBuxi.lean、Li.lean
│   │   └── HumanAlignment.lean、Attention.lean
│   ├── Wen/                      # 古文虚字 · 核 · 自释
│   │   ├── Operators.lean、Kernel.lean
│   │   ├── WenyanText.lean、WenyanSelfInterp.lean
│   ├── Jian/                     # 间之核（14 字粒子核）
│   │   ├── JianOntology.lean、Jian.lean
│   │   ├── JianSTLC.lean、JianMinimality.lean、JianModeKernel.lean
│   │   └── JianYiBridge.lean
│   ├── Yi/                       # 易之代数
│   │   ├── Yi.lean、YiCore.lean
│   ├── Bagua/                    # 八卦 · 192 · Gödel/Rice
│   │   ├── BaguaAlgebra.lean、Cell192.lean、BaguaTuring.lean
│   │   ├── Newman.lean、KleeneInternal.lean、GodelLi.lean
│   └── Eight/                    # 八衍：数 / 推 / 测 / 形 / 类 / 动 / 识 / 象
│       ├── ShuSuan.lean、LuoJi.lean、TongJi.lean、XingWei.lean
│       └── LeiYing.lean、DongLi.lean、XinZhi.lean、WuXiang.lean
├── diagrams/                     # 概念 DAG（生成产物，可由 scripts/ 重建）
│   ├── ConceptDAG.{complete,core,full,layered}.{mmd,svg}
│   ├── MonadDAG.{mmd,svg}、ConstructionDAG.{mmd,svg}
│   ├── AttentionDAG.{mmd,svg}、HumanAlignmentDAG.{mmd,svg}
│   └── MonadTree.txt
└── notes/                        # 伴随说明（人类可读）
    ├── ConceptDAG.md、MonadDAG.md、ConstructionDAG.md
    ├── JianOntology.md、Attention.md、HumanAlignment.md
    └── MissingGlyphRootReport.md
```

## 主要模块要点

- `Core/MonadRoot.lean`：单根 DAG，所有形式符、构造阶段、claim 经一字回到一元。
- `Core/Monism.lean`：内容构造 DAG（Γ → 三本 → 三显 → 三征 → 開/閉 → 生生不息论）。
- `Jian/JianOntology.lean`：Tier-1 間/Jian 本体（三本／三显／三征／開閉／網體流／自指见证）。
- `Wen/Kernel.lean`：完备自指之核——一字 (動) + 古文算子 ⊢ 生生不息 ∧ 自指 ∧ 自洽。
- `Bagua/GodelLi.lean`：理之不完备 · 哥德尔在 192（49 定理 / 1 公理 / 0 sorry）。
- `Eight/`：八衍（八道之展开），269 公开声明 / 0 sorry。

## 构建

```bash
/Users/ren/.elan/bin/lake build
```

顶层 module：`SSBX.lean`（按簇分组导入）。

## 重新生成 DAG

```bash
# 概念 DAG（输入 Roster.lean，输出 diagrams/*.mmd + notes/ConceptDAG.md）
scripts/generate_concept_dag.py
scripts/render_concept_dag.sh

# 单根 Monad DAG
scripts/generate_monad_dag.py
scripts/render_monad_dag.sh

# 单根明文树
scripts/generate_monad_tree.py

# 注意力 / 人对齐 / 构造 DAG（已有 .mmd，重新渲染）
scripts/render_attention.sh
scripts/render_human_alignment.sh
scripts/render_construction_dag.sh
```
