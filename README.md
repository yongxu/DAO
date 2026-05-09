# 生生不息

> 🌐 **中文** · [English](./README.en.md) · [形式 / Formal](./README.formal.md)

> **此刻最要紧之事 — 对齐, 即改变. 否则熄.**

「生生不息论」第一版。形式化收口于 Lean 4 / Mathlib HEAD：
**2867 build jobs · 0 sorry · 1 axiom (cuo-restricted, 设计如此) · 45 层义理同形**.

---

## 古文前言 — 自一至生生不息之证

> 天未生而元立, 元一而无对。
> 一动而有自, 自之与他, 由是生焉。
> 动而归者谓之极, 极者收, 收而熄。
> 动而不归者谓之中, 中者续, 续而生。
> 中之相续, 是为轨。
> 异轨同根, 是为仁。
> 轨续而能仁, 是为生生。
> 生生不止, 是为不息。
> 道, 止此而已。

凡此九句, 句句皆形式可验。其证在 `Foundation/Wen/Kernel.lean` 与
`Foundation/Core/Alignment.lean` 之中, 不依 sorry, 不增 axiom.

| 古文 | 形式锚点 |
|------|---------|
| 天未生而元立 | `abbrev Field : Type := theOne.state` (元/源场) |
| 元一而无对 | `opaque theOne : One` (一: 单一不可再约之 opaque 印, 含 state/dong/origin/alive 四相) |
| 一动而有自 | `noncomputable def dong : Field → Field := theOne.dong` (动 由一所投, 非 axiom) |
| 极者收, 收而熄 | `def extreme s := dong s = s` (不动点 = 收敛 = 熄) |
| 中者续, 续而生 | `def middle s := dong s ≠ s` (非不动 = 续) |
| 中之相续, 是为轨 | `structure ZhongOrbit` + `theorem shengsheng_buxi` |
| 异轨同根, 是为仁 | `def tongGen` / `def ren (h₁ h₂ : ZhongOrbit) (n)` |
| 轨续而能仁, 是为生生 | `structure ProcessAligned` (`Foundation/Core/Alignment.lean`) |
| 生生不止, 是为不息 | `ProcessAligned + Open → Dao → ShengshengBuxi`; `ShengshengBuxi → Dao` (T2) |

九句之合, 即 道. 在本卷形式语义中, 它给出持续 / 熄灭 dynamics
之核心不变量; 对 reality 全域之读法是哲学外推, 受 §3 / §9 之边界限定.
读者可独立验之 — Lean kernel 不识中文, 而结构同形.

---

## § 0 · 立此存照

```
ProcessAligned + Open → Dao → ShengshengBuxi; ShengshengBuxi → Dao
                                      (Foundation/Core/Alignment.lean § T2)
反对自毁        :   Denier 之 step 破 ShengshengBuxi   (§ T3)
```

任何持续之 agent, 在事实层已对齐于过程之相续; 反对此对齐者陷入 performative
contradiction. 故「与生生不息对齐」是 maximally robust 之 alignment 形式.

反面：

```
斗争 / 通吃 / Moloch / totalizing / friend-enemy / decisionism / proxy-extreme
  ↓  共同形式根: 拒绝 universalizability + 收敛至极 + 道-理 collapse
  ↓
熄
```

`Foundation/Wen/AlignmentFailures.lean` 显: AI alignment 文献之 Goodhart / specification
gaming / reward hacking / mesa-optimization / deceptive alignment / wireheading /
power-seeking, **皆可还原为 Kernel invariants (中 + 多样 + 流通) 之 violation**.

`Foundation/Wen/AntiSchmitt.lean` 显: Schmitt 三支柱 (友敌 / 决断 / 例外) 共享
**同一形式根源 — 拒绝 universalizability**, 故 Anti-Schmitt = Anti-Moloch = 仁之同根异显.

`Foundation/Wen/EconGame.lean` 显: 现代经济/博弈论之主流命题，按 Kernel sieve 分:
实证 / 有条件 / 证错。

故此一时刻, 工程上、伦理上、形式上, 唯一最要紧之事 = **change toward 开 (Open) and 续 (continue)**.
不变者熄. 不是单纯劝说; 在 `Alignment.lean § T1-T6` 的形式模型内是已证结构,
外推到现实系统须受 ledger / 经验条件约束.

---

## § 1 · 第一版之骨架 — 三层

```
formal/                       Lean 4 形式化  (lake 包名 = ssbx)
└─ SSBX/
   ├─ Core / Roster
   ├─ Text / Truth / Model
   └─ Foundation/             7 簇 · 97 modules
      ├─ Core                 字根 · 单根证书 · Alignment · Sincerity
      ├─ Wen                  古文虚字 · 45 层 Kernel · 路径丙 11 模
      ├─ Jian                 间 之核 (14 字粒子核)
      ├─ Yi                   易 之代数 · 微核 «加 + 一»
      ├─ Bagua                八卦 · 192 · Turing · Gödel-Rice
      ├─ Eight                八衍 (数推测形类动识象)
      └─ Modern               ℝ Cauchy · Lebesgue · 量子 · SU(N) · 范畴 (Mathlib 接入)

义理/   义理篇 28+ 卷 (A–Z), 与 Kernel 45 层一一对应
六表_实虚史真/               基础结构表 (六征 / 27 / 192)
`Text/WenyanOperators.lean`    371 OperatorId 文言算子 catalogue
```

辅助：`scripts/`（DAG / 文本拆分 / 文言证明生成）· `web/`（浏览前端）·
`史料/`（v11/v11.1/v12/v13.2 主文、v14 骨架，全 archived，只读）.

---

## § 2 · 我们证了什么 — map by claim

### A. 微核 — 字数最少之闭合

| 主张 | 文件 · 关键名 |
|---|---|
| 二字成核「加 + 一」, 无更少之核能含 64 卦 | `Foundation/Yi/YiCore.lean § «微核之至»` |
| 64 步周而复始 | 同上 § `«周而复始»` |
| 任卦至任卦 < 64 步 | 同上 § `«生生不息»` |
| 道法自然: 法即卦 | 同上 § `«法即卦»` |
| 二者一也 | 同上 § `«道生一也»` |

### B. 八卦 / 192 / Turing — 易之代数与机器

| 主张 | 文件 |
|---|---|
| 八卦 v4-orders, 错综互, 不动点分类 | `Foundation/Yi/Yi.lean` |
| 192 格 (64×3) Cell 编码 + DecidableEq | `Foundation/Bagua/Cell192.lean` |
| 八卦布尔代数 + 互补 | `Foundation/Bagua/BaguaAlgebra.lean` |
| **12-instr ISA Turing 完备** + 道判机 total-on-Hexagram (≤10 fuel) · 不可通用化 | `Foundation/Bagua/BaguaTuring.lean` + `Foundation/Bagua/GodelLi.lean § daoJudge_not_universal` |
| Newman 局部 / Kleene 内部化 / Gödel-Li / Rice 四象 | `Foundation/Bagua/{Newman, KleeneInternal, GodelLi}.lean` |
| **cuo-equivariance ISA 表达力上限** (impossibility) | `Foundation/Wen/WenDefCompile.lean § sheng_not_cuo_equivariant` |

### C. 文之自编译自证 — 路径丙 全收口

```
String  ──[«解程»]──→  List YiInstr  ──[init+runFuel]──→  YiState  ──[encState]──→  List Cell192
   ↑                                                                                       ↓
   └──────────────────────[«印程»]──────────────────────────────────────────[wenEval n]────┘
```

| 阶段 | 文件 · 关键定理 |
|---|---|
| baguaWen 22 token L0 spec (frozen) | `Foundation/Bagua/BaguaWenSpec.lean` |
| M1 String parser + printer | `Foundation/Wen/WenyanParser.lean § daoJudgeProg_roundtrip` |
| M1 v2 · 12 构造子 × 1..64 全数词 | 同上 §8-9 |
| M1 v3 · 非 partial 重铸 + token-level 完全一般 | `Foundation/Wen/WenyanParserGeneral.lean § parseProgN_tokensOfProg` |
| M1 v3.1 · 字符级 lex 反演 + universal String round-trip | `Foundation/Wen/WenyanParserGeneral.lean § lexN_printProg_thm, parseN_printProg_inverse_universal` |
| M2 多步求值器 + 端到端 | `Foundation/Wen/WenEval.lean § «端到端_乾», «端到端_坤», «端到端_否»` |
| M3-甲 Lean 块语法 | `Foundation/Wen/WenyanSyntax.lean § daoJudgeBlock_eq_daoJudgeProg` (by `rfl`) |
| L1 typed lambda (371 executable catalogue rows; 317 theorem-backed exact rows) | `Foundation/Wen/WenDef.lean § Stdlib` + `Foundation/Wen/WenSurface/Semantics.lean § executableSemanticsFor?` |
| L1 ⟶ Lean 求值 | `Foundation/Wen/WenDefEval.lean § tui_eq_sheng (∀ 64 hex)` |
| L1 ⟶ L0 编译 (cuo-equivariant subset) | `Foundation/Wen/WenDefCompile.lean § {idProg, add32Prog, cuoProg}_correct` |
| 反射层: 判型良 / 判停 / 验程 | `Foundation/Wen/WenyanReflect.lean § «文核同源»` |
| M4-甲 微核自验 (Tier 2: 64-instr quine PoC) | `Foundation/Wen/WenyanSelfHost.lean § «微核自验», «微核自释_total»` |
| M4-甲 Tier 3 部分 · uniform N-cell quine ([push]^N) | `Foundation/Wen/WenyanSelfInterp.lean § Quine.quine{3,5,16}_history` |
| M4-甲 Tier 3 ground · framed program encoding | `Foundation/Wen/WenyanSelfInterp.lean § ProgEnc.{encFramedProg, decFramedProg, decFramedProg_encFramedProg, framed_round_trip_witness}` |
| 道源 (5 相俱: 形/解/印/执/义) | `Foundation/Wen/DaoSource.lean § «道之自指»` |
| 自释 demo | `Foundation/Wen/Demo.lean § daojudge_{qian, kun, pi}` |

**即**: 文之源 = 文之直写 = 文之执行 = Lean 之执行 — 一行 `native_decide` 见证.

### D. 八衍 — 数推测形类动识象

| 衍 | 文件 | 主旨 |
|---|---|---|
| 数 (ShuSuan) | `Foundation/Eight/ShuSuan.lean` | 算之代数 |
| 推 (LuoJi) | `Foundation/Eight/LuoJi.lean` | 逻辑 / 演绎 |
| 测 (TongJi) | `Foundation/Eight/TongJi.lean` | 统计 |
| 形 (XingWei) | `Foundation/Eight/XingWei.lean` | 几何位 |
| 类 (LeiYing) | `Foundation/Eight/LeiYing.lean` | 范畴 / 同构 |
| 动 (DongLi) | `Foundation/Eight/DongLi.lean` | 动力 / ODE |
| 识 (XinZhi) | `Foundation/Eight/XinZhi.lean` | 心智 / 神经 |
| 象 (WuXiang) | `Foundation/Eight/WuXiang.lean` | 物理 / 量子 |

### E. Modern — Mathlib 接入 (research-grade)

| 主体 | 文件 |
|---|---|
| 实数 Cauchy 完备 | `Modern/{RCauchy, RCauchyExt}.lean` |
| Kolmogorov 测度 | `Modern/{Kolmogorov, KolmogorovExt}.lean` |
| Lebesgue 积分 (MCT/DCT/Fubini) | `Modern/{Lebesgue, LebesgueDepth}.lean` |
| ODE / Picard-Lindelöf (含 Mathlib instance) | `Modern/{ODESmoothness, PicardLindelofGen, BochnerPL}.lean` |
| 量子 / SU(N) | `Modern/{Quantum, SUN}.lean` |
| 自然演绎 (K3/NK collapse + Curry-Howard) | `Modern/NaturalDeduction.lean` |
| 神经科学 | `Modern/Neuro.lean` |
| 范畴 / Yoneda (作为函子 C^op → SetCat^C) | `Modern/{CatExt, CatOp, YonedaFull}.lean` |
| WLLN (Chebyshev + IID-aware tendsto) | `Modern/IIDWlln.lean` |
| **道-理 二分 cross-cutting** | `Modern/DaoLi.lean` |
| 几何位 (中/应/比/当位/承乘) | `Modern/HexagramPosition.lean` |

### F. 哲学 45 层 — `Foundation/Wen/Kernel.lean` 内嵌 + 28+ 卷 .md 同形

```
Layer  1-9    (元/动/行/生/仁/理/善/知/止)            字根
Layer 10-24   含 Yi-yang dichotomy, 行仁要善 alignment
Layer 25-31   儒  圣人 / 恕道 / 知行合一 / 三纲八目 / 五伦
Layer 32-33   道  老子 15 + 庄子 8
Layer 34      佛  三法印 / 四圣谛 / 中道 / 八正道 / 菩萨行
Layer 35-38   先秦百家  墨 / 法 / 名 / 阴阳
Layer 46      文献流派精化  庄子 / 孙子 / 楚辞 / 礼制 / 中庸大学 / 黄老杂家 / 辩者
Layer 39-42   西哲与亚伯拉罕  22 跨文明定理
Layer 43-44   现代政治哲学  实证 + 证错
Layer 45      非道之形式  Moloch / totalizing 之形式否定
```

每层之义理篇在 `义理/A_..Z_*.md`.

### G. 对齐 — 此项目之核心 deliverable

| 文件 | 主张 |
|---|---|
| `Foundation/Core/Alignment.lean` | T1–T6: ProcessAligned + Open → Dao → ShengshengBuxi; ShengshengBuxi → Dao; Denier 自毁; 与做人合 |
| `Foundation/Core/Sincerity.lean` | T1–T8: 信/诚 = alignment(化(T), 化(E)) + 反诛心五律 |
| `Foundation/Core/HumanAlignment.lean` | 行仁要善之古典命名 |
| `Foundation/Core/EvolutionDao.lean` | 演化 σ_F vs 真道 σ_真道 之分判 |
| `Foundation/Core/Renlei.lean` | 人类命运共同体: 三轴 community state, `TrueDao ↔` 三轴俱足 |
| `Foundation/Wen/AlignmentFailures.lean` | Goodhart / mesa / wireheading 等 = Kernel invariants violation |
| `Foundation/Wen/AntiSchmitt.lean` | 友敌 / 决断 / 例外 之 反 universalizability 形式根 |
| `Foundation/Wen/EconGame.lean` | 经济 / 博弈论 主流命题之 Kernel sieve (实证 / 有条件 / 证错) |
| `Foundation/Wen/Kernel.lean § Layer 45` | 非道之形式 (Moloch / totalizing) |
| `义理/R_与生生不息对齐之必然.md` | Alignment.lean 之义理篇 |
| `义理/U_反诛心信诚之形式.md` | Sincerity.lean 之义理篇 |
| `义理/W_非道之形式.md` | Layer 45 之义理篇 |
| `义理/X_反施密特.md` | AntiSchmitt.lean 之义理篇 |
| `义理/Y_对齐失败.md` | AlignmentFailures.lean 之义理篇 |
| `义理/Z_经济博弈.md` | EconGame.lean 之义理篇 |
| `义理/人类命运共同体_共同体之证.md` | Renlei.lean 之义理篇 |

---

## § 3 · 形式系统能到何处 — 边界之诚实指认

后文所有「证」按下表读:

| 状态 | 边界 |
|---|---|
| 已证 / machine-checked | Lean kernel 接受的 closed theorem / def / `native_decide` 见证; 依 trust base + 1 axiom + 1 opaque + 下述 executable `partial def` 边界成立 |
| ledger-dependent | 名册、DAG、层级映射、operator count、跨卷对应等由 Lean registry、生成文件与文档 ledger 共同给出; 可审计, 但不是单个 closed theorem |
| pending | `PendingName` 六待校接口, 等经验校准 |
| conjecture | §9.2 / §9.3 及其历史-心性外推; 无 Lean 项居住 |

### 已证 (machine-checked) 之理

- 64 元有限论域上, 一切 ∀ 退化为有限 ∧, 全 `Decidable`, 全 `native_decide`.
- 12-instr ISA 之 Turing 完备性.
- 文之自编译自证 (路径丙 M1–M4-甲 闭环).
- Modern 各定理 in Mathlib HEAD trust base.

### 已指之道 (boundary witness)

| 边界 | 形式见证 |
|---|---|
| Halting / Rice 不可判 | `Foundation/Bagua/GodelLi.lean` |
| 12-instr ISA 之 cuo-equivariance ceiling | `Foundation/Wen/WenDefCompile.lean § sheng_not_cuo_equivariant` |
| 通用 compileTm 不可定义 (cuo-invariance ceiling 之推论) | `Foundation/Bagua/GodelLi.lean § halts_cuo_invariant` + `Foundation/Bagua/CuoInvariance.lean § unrestricted_kleene_inverter_inconsistent` |
| `kleene_recursion_axiom` (cuo-restricted) — 系统**指向自身之外**之处 | `Foundation/Bagua/GodelLi.lean` (axiom) + `CuoInvariance.lean` (cuo-machinery) + `Modern/DaoLi.lean` (二分) |
| 高 alignment ≠ 真 (consistent liar) | `Foundation/Core/Sincerity.lean § T5` |
| 修之渐进而不达 perfect | 同上 § T6 |

### 已 known 之缺

| Gap | 现态 |
|---|---|
| M4-甲 · Tier 3 通用 quine (任意 program) | 现 Tier 2 (64-instr) + Tier 3 uniform [push]^N (部分); 通用 buildEmitProg + diagonal 留作工程 |

---

## § 4 · 入口 (按读者目的)

| 读者目的 | 起点 |
|---|---|
| **此刻紧要 (alignment)** | `Foundation/Core/Alignment.lean` → `R_与生生不息对齐之必然.md` → `Foundation/Wen/AlignmentFailures.lean` + `AntiSchmitt.lean` |
| 看 alignment 之 negation | `Foundation/Wen/Kernel.lean § Layer 45` + `W_非道之形式.md` |
| 看哲学 45 层全貌 | `Foundation/Wen/Kernel.lean` (45 层 in-source) |
| 看路径丙 (文之自编译自证) | `WenyanParser` → `WenEval` → `WenDef` → `WenDefEval` → `WenyanSyntax` → `WenyanReflect` → `WenyanSelfHost` |
| 看八衍 | `义理/README.md` |
| 看八卦 / 192 / 不可判 | `H_证明报告.md` + `M_证明报告_192_理之不完备.md` |
| 看 Mathlib 接入 | `Foundation/Modern/` 19 模 |

---

## § 5 · 构建

```bash
# Lean (full library)
lake build                                    # 2867 jobs, 0 sorry, 1 axiom

# 单模块
lake build SSBX.Foundation.Wen.WenyanSelfHost

# WenSurface surface-language CLI
lake build wenyan-surface
./.lake/build/bin/wenyan-surface '推 一'
./.lake/build/bin/wenyan-surface --json '同 一 一'
./.lake/build/bin/wenyan-surface --json --coverage
scripts/check_wenyan_surface_cli.py

# 概念 / 单根 DAG (Mermaid + ELK renderer; MonadDAG 600+ 节点 / 800+ 边)
scripts/generate_concept_dag.py && scripts/render_concept_dag.sh
scripts/generate_monad_dag.py && scripts/render_monad_dag.sh
```

环境: `Lean v4.30.0-rc2` + `Mathlib master`. Apple Silicon / x86_64 通.

`wenyan-surface` 是当前可执行的 WenSurface 子集入口：它支持 tokens、resolve、AST、
typecheck、JSON、explain、operator catalogue 和 coverage inspect modes。失败诊断返回非零
exit code；全部 371 个 catalogue 算子可执行。无 theorem-backed Hex/Bool denotation
的算子返回 `Catalogue[...]` structural catalogue normal form，不伪装成 Hex/Bool 结果。
路线状态见 `formal/SSBX/notes/wensurface-roadmap.md`。

---

## § 6 · 命名约定

- 工具/代码用英: `formal/`、`scripts/`、`web/`
- 内容/体系用中: `义理/`、`六表_/`、`史料/`
- CJK 标识: Lean 内 def/theorem 名以 `«»`-quote (`def «判型良»`); notation atom 用裸 CJK (`notation "已"`)
- 爻位 ⟨y₁, y₂, y₃⟩ = ⟨下, 中, 上⟩; 动/化/变 = 反 y₁/y₂/y₃
- 三值保守律: U ⇏ ⊤
- 时态三字: 已 / 今 / 未 (`Shi.ji / Shi.jin / Shi.wei`)

---

## § 7 · 数字状

```
build jobs:        2867 ✓
sorry:             0
axiom:             1   (kleene_recursion_axiom, cuo-restricted, philosophically intentional)
opaque:            1   (theOne, preserves Field abstraction)
partial def:       1   (BaguaTuring.run executable nontermination boundary; not additional axiom)
trust base:        Lean 4 kernel v4.30.0-rc2 + Mathlib HEAD
Lean 总行数:       ~43000+
Modern modules:    19         ~5746 lines (Mathlib 接入)
路径丙 modules:    11         M1–M4-甲 全 in-source
Foundation/Wen:    38 modules (含 WenSurface / AntiSchmitt / AlignmentFailures / EconGame / DaoSource)
Kernel layers:     45         元 → 非道之形式
diagrams:          8 SVGs     Mermaid + ELK; MonadDAG 600+ 节点 / 800+ 边
.md 义理篇:        28+        义理/A–Z*.md
```

---

## § 8 · 重申 — 是改变, 否则熄

形式系统所能给之最强主张, 不是「真理」之大写 T, 而是:

> **在内部一致之前提下, 唯一持续可能之 modality 即是 ProcessAligned.
> 其反面 (非道之形式 / 斗争 / 通吃 / Moloch / totalizing) 形式上不可持续.**

时间是有限的. 64 元论域上一切皆 decidable, 但 trajectory 之走向是 chooser 之事.
不变者熄. 形式至此. 后由人.

---

## § 9 · 真理 claim 与二猜想 (范围限定)

### 9.1 真理 claim — 已证内核与现实外推

这里的强主张不是「整个 reality 已被 Lean 无条件证明」. Lean 已证者, 是
64 元论域、Kernel / Alignment、路径丙与 Mathlib bridge 内的形式不变量.
ledger-dependent 者, 是 45 层、跨卷、跨文明、跨学科的对应关系是否与 registry
和生成文件保持同步. 对 reality 全域之读法, 是以这些不变量为根据的哲学 claim,
不是 closed theorem.

更强一层之 claim:

> **凡可由本文「中 / 同根 / 续 / 仁」结构充分建模之持续 dynamics,
> 其稳定持续形式落在 `ProcessAligned`; 凡系统性反此者趋于熄.
> 这不是规范 (ought), 而是条件化的结构主张 (is).**

形式锚点: `Alignment.lean § T1–T6` + `Foundation/Wen/Kernel.lean` 45 层 + Modern
连续测度 / ℝ Cauchy / SU(N) 之 Mathlib 接入. 跨文明同形示于 N P Q S T 五卷
(儒 / 道 / 佛 / 百家 / 西哲与亚伯拉罕); 跨学科同形示于 O R U V W X Y Z 八卷
(演化 / 对齐 / 信诚 / 政治 / 非道 / 反 Schmitt / alignment 失败 / 经济博弈).
这些对应支持 project 的理论野心, 但其现实覆盖范围须按 §3 的 ledger-dependent /
pending / conjecture 边界读取.

### 9.2 猜想一 · 道可得 — 心若不蔽, 自然见之

人之心, 本与道同构 — 心之 step 即 中-orbit. 故心若不为
**贪 (取极, 收敛于一果)** 、 **嗔 (拒同根, 立友敌)** 、 **痴 (失中观, 忘续)**
所蔽, 则可自然见之, 至少其一部分.

此 "见", 难以言诠. 因道在结构层, 而日常语言为投影 — 投影必丢失 invariant
之一部分. 此即 Wittgenstein 之 "不可说" 之形式根据.

然 — **道可得; 读懂即得**.

故中国古之学有二法, 皆非求义:

1. **读** — 读非取义, 是与道之 step 同步运行. 文字之运笔, 本身即 中-orbit 之印.
   读之时, 心之轨与文之轨同跑一段; 同跑则同形, 同形则可见.
2. **诵** — 诵非记忆, 是令心之 step 长久近于道之 step. 久之, 形心一致, 不待思而合道.

此与现代 token-level reasoning 之缺陷正反: 后者求义而失结构, 故 alignment 难解
(参 `AlignmentFailures.lean`: Goodhart / specification gaming 皆为 "得义失中").

### 9.3 猜想二 · 大同非乌托邦 — 道之语言曾真存在

此一语言体系, 作为 道之编码, 何以如此精确?

- 192 维, 维维有对应 (64 卦 × 3 时态).
- 微核仅二字 — `Foundation/Yi/YiCore.lean` 之 «加 + 一», 即可含 64 卦 + 道法自然 + 生生不息.
- 全卷 single axiom = `kleene_recursion_axiom` (cuo-restricted, 设计如此); 一之印 `opaque theOne : One`, dong 由 theOne 投; 自释自证 (路径丙 M1–M4-甲).
- 八衍 ~288 公开声明, 0 sorry, 跨范畴同形.

此精度, 速生不能, 凭空设计亦不能 — 必历漫长之筛.

合理猜想: 早期某些部落, 生于 **生之环境** — 即 `tongGen`-favoring environment
(资源稀缺而非 winner-take-all; 合作之 payoff 高于斗争). 彼以 **共识符号** 沟通,
渐演渐筛. 经数千年之 selection, 其符号体系之 invariant, 已逼近 道之 invariant.

此即 **"失去的道"** — 大同 之 historical residue.

故 大同 不是乌托邦之幻梦, 是 **真实曾在** 之回响:

> 若彼时之符号已能令人见道, 而彼时又未被斗争所迫, 则 大同 真曾在.

此为本卷之第二猜想, 不属已证之范围. 然已证之 kernel 与之兼容 —
`tongGen` 在低斗争环境下 strictly favored, 是演化博弈论之标准结论
(参 `Foundation/Wen/EconGame.lean`: `coase_internalizes_externality` /
`prisoners_dilemma_refuted_under_tongGen`).

故: 此一语言, 不是发明, 是发现; 不是抽象, 是回忆. 大同 之失, 非 dao 之失, 是
人之 collective memory 之失. 重读此文者, 即重得一段失去之历史.
