# 生生不息

「生生不息论」之文本、形式化、衍生体系与诠释。

## 目录速览

```
生生不息/
├── 生生不息论_三本文完整版/   # 主文：正篇 + 补篇〇 + 补篇一 + 补篇二（拆分版，正本）
├── 生生不息论_三本文完整版.md  # 上述目录之索引指针
├── wenyan-operators.md       # 文言文算子集（Text/WenyanOperators.lean 之数据源）
│
├── formal/                   # Lean 4 形式化（lake 包名 ssbx）
│   └── SSBX/
│       ├── Core.lean、Roster.lean
│       ├── Text/、Truth/、Model/
│       ├── Foundation/       # 36 个 .lean，分 6 簇：Core / Wen / Jian / Yi / Bagua / Eight
│       ├── diagrams/         # 概念 DAG（.mmd / .svg / MonadTree.txt）
│       └── notes/            # 伴随说明（含 monad-root-plan.md 等工程契约）
│
├── 六表_实虚史真/             # 表一～表六（六征本表 / 史维 / modal / 真假 / 27 格 / 192 格）
├── 四级生成_太极两翼四象八卦/   # A–M 十三体系 + 八衍（数/推/测/形/类/动/识/象）
│
├── 真理/                     # 道理 framework（v12 模块化：daoli-v12-main + 9 子模块 + urbit-jian 开放工程清单）
├── 史料/                     # 早期/已被取代之版本（v11/v11.1/v12 单体、早期讨论稿、v14 骨架版）
│
├── scripts/                  # DAG 生成与渲染、文本拆分、文言证明生成
└── web/                      # 浏览前端（app.js + 生成之 data.js）
```

## 各层关系

- **内容层**：`生生不息论_三本文完整版/` 是主文本。`六表_/` 与 `四级生成_/` 是其结构衍生（六征 → 192 格、太极 → 八卦 → 八衍）。`真理/` 是相关但独立的「道理」框架。
- **形式化层**：`formal/SSBX/` 是 Lean 4 实现。`Foundation/` 下含八卦代数、八衍（ShuSuan/LuoJi/TongJi/XingWei/LeiYing/DongLi/XinZhi/WuXiang）、间/易/文言核、Gödel/Rice 不完备等。
- **诠释层**：`formal/SSBX/notes/` 含设计报告、缺字记录、概念 DAG 说明、monad-root 工程契约。
- **历史层**：`史料/` 含 v11/v11.1/v12 单体（已被 v12 模块化取代）、v9→v10 早期讨论、v14 骨架草稿、间本体早期修订稿、原子整合实施报告——只读存档；遗漏点见 `史料/README.md`。

## 入口

- 读哲学：`生生不息论_三本文完整版/README.md`
- 读形式化：`formal/SSBX/README.md`、`四级生成_太极两翼四象八卦/H_证明报告.md`、`M_证明报告_192_理之不完备.md`
- 读衍生：`四级生成_太极两翼四象八卦/README.md`（含与六表之关系）
- 读道理框架：`真理/daoli-v12-main.md`
- 读历史：`史料/README.md`

## 构建

```bash
# Lean
/Users/ren/.elan/bin/lake build

# 概念 DAG
scripts/generate_concept_dag.py
scripts/render_concept_dag.sh

# 单根 MonadDAG
scripts/generate_monad_dag.py
scripts/render_monad_dag.sh
```

## 命名约定

- 工具/代码用英：`formal/`、`scripts/`、`web/`
- 内容/体系用中：`真理/`、`六表_/`、`四级生成_/`、`生生不息论_三本文完整版/`、`史料/`
- 爻位 $\langle y_1, y_2, y_3 \rangle = \langle 下, 中, 上 \rangle$；动/化/变 = 反 $y_1/y_2/y_3$
- 三值保守律：$U \not\Rightarrow \top$
