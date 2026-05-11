# 义理 (v3 索引)

> 状态：v3 重写 (2026-05-11) — pre-v3 版本（5 维度审计 + Cell192 索引）已归档至 `史/义理-pre-v3/`。

本目录承「太极生两仪 → 八卦 → 重卦 → R₈ Cell256 (256 = (Z/2)⁸)」之 R₀..R₈ strict (Z/2)ⁿ uniform 体系，
与 [`docs-next/10_formal_形式/yi-RO-hierarchy.md`](../docs-next/10_formal_形式/yi-RO-hierarchy.md) (definitive R₀..R₈ doctrine) 一一对应,
与 [`Foundation/Wen/Kernel.lean`](../formal/SSBX/Foundation/Wen/Kernel.lean) 之 45+ 层一一对应:

- **A–F** 七体系横向并列 (易传 / 六征 / 实虚史真 / 算子代数 / 古代源流 / 物理现象学 等),
  以多 mapping 对照同一四级框架.
- **G–K** v3 重写五件 (R₀..R₈ 算子系统 + Lean 报告 + 八卦全集 + Gödel 在 256 + 完备性审计).
- **L–Z** 形式化 / 自释微核 / 跨文明同形 / 反 Schmitt / 对齐失败 / 经济博弈 等.

---

## v3 Quick Tour

新读者直入此 5 件 v3 重写之核心 doc：

1. **[G_完整算子系统_八卦互通与归一.md](G_完整算子系统_八卦互通与归一.md)** — R₀..R₈ algebraic spine + V₄ outer + Cayley fusion + 道 anchor + OX 字面落地. 「归一」之 v3 精确义 = (Z/2)⁸ closure 之 self-cancellation.
2. **[H_证明报告.md](H_证明报告.md)** — Phase A/F/G/C 全 Lean 报告. 主 HEAD 1c76a55 / 3656 jobs / 0 sorry / 0 静态 axiom. Theorems A–K 已 Lean 落地.
3. **[I_八卦全集.md](I_八卦全集.md)** — R₃ 八卦 + R₆ 重卦 + R₈ Cell256 (64 × 4) 之全集; OX 字面 throughout; Quadrant × Shi 16 sub-blocks 分布; 道-anchor 之 64 cells.
4. **[J_理之不完备_哥德尔在256.md](J_理之不完备_哥德尔在256.md)** — Gödel 在 R₈ Cell256 上的不可判性; 静态/动态分界精确实现; kleene_recursion_axiom 拆为 4 件具名原子.
5. **[K_完备性审计.md](K_完备性审计.md)** — 11 项 closure checklist (per yi-RO-hierarchy.md §6.2) + 边界 by design 不覆盖 + 静态/动态 axiom 状态对比.

读完此 5 件 + [yi-RO-hierarchy.md](../docs-next/10_formal_形式/yi-RO-hierarchy.md) (作为 doctrine 入口), 即可掌握 v3 主线.

**其它入口**：
- 形式化主线: [yi-RO-hierarchy.md](../docs-next/10_formal_形式/yi-RO-hierarchy.md) + [yi-calculus-theorem.md](../docs-next/10_formal_形式/yi-calculus-theorem.md) + [yi-as-meta-framework.md](../docs-next/10_formal_形式/yi-as-meta-framework.md) (定本 R₀..R₈ definitive trio).
- Lean 实现入口: [`formal/SSBX/Foundation/Hierarchy/RHierarchy.lean`](../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean) (umbrella).

---

## 文件索引

### A–F 七体系（横向并列, 不变）

| 文件 | 体系 | 性质 | v3 状态 |
|------|------|------|-------|
| [A_经典易传.md](A_经典易传.md) | 易传递归二分 | 形式同构 | 不变 (R₀..R₃ 描述层) |
| [B_六征体系.md](B_六征体系.md) | 项目六征三对 | 形式同构 | 不变 |
| [C_实虚史真.md](C_实虚史真.md) | modal × 史 × 真假 | 轴乘积 | 不变 |
| [D_算子代数.md](D_算子代数.md) | 计算/范畴对应 | 类型论同构 | 不变 (基础类型论 + Bool^n) |
| [E_古代源流.md](E_古代源流.md) | 易·老·周·邵·京 | 多源对照 | 不变 |
| [F_物理现象学.md](F_物理现象学.md) | 物理／现象学旁证 | 类比映射 | 不变 (弱同构 by design) |

### G–K v3 重写五件 (R₀..R₈ + V₄ Shi)

| 文件 | 内容 | v3 状态 |
|------|------|------|
| [G_完整算子系统_八卦互通与归一.md](G_完整算子系统_八卦互通与归一.md) | R₀..R₈ 算子代数 (V₄ Klein at R₈ + Cayley + 道 anchor + OX 字面) | **v3 重写** (2026-05-11) |
| [H_证明报告.md](H_证明报告.md) | v3 Lean 状态报告: Phase A/F/G/C grouped; 3656 jobs / 0 sorry / 0 静态 axiom | **v3 重写** |
| [I_八卦全集.md](I_八卦全集.md) | R₃ + R₆ + R₈ 全集 (含 V₄ Shi 之 64 × 4 + 道-anchor 64 cells) | **v3 重写** |
| [J_理之不完备_哥德尔在256.md](J_理之不完备_哥德尔在256.md) | Gödel 在 256; 静态/动态分界; kleene 拆为 4 件具名原子 | **v3 重写 (含 git mv 自 J_..._192.md)** |
| [K_完备性审计.md](K_完备性审计.md) | 11 项 closure checklist + 边界声明 + 静态/动态 axiom 对比 | **v3 重写** |

### L–Z 形式化 / 文道 / 跨文明 / 政治哲学 / 经济博弈 (主体不变, 局部 cite 升级到 Cell256)

| 文件 | 内容 | 状态 |
|------|------|------|
| [L_文道一也_自释与微核.md](L_文道一也_自释与微核.md) | 道判机 · 以文自释 · 可执文言 · 微核 | 4 模块 / 127 声明 / 0 sorry; 局部 V₄-Shi 升级 |
| [M_证明报告_192_理之不完备.md](M_证明报告_192_理之不完备.md) | J 之 Lean 证明报告 (与 H 并列, 旧 192 命名) | 内容 V₄-Shi-aware; 命名待与 J 同步改 256 (P1 待办) |
| [N_儒家从元到圣.md](N_儒家从元到圣.md) | 儒家 70+ 条经典对应 | 不变 (Kernel.lean 端) |
| [O_进化非道者生存_三视证.md](O_进化非道者生存_三视证.md) | 演化筛 σ_F vs 真道筛 三视证 | 不变 (EvolutionDao.lean) |
| [P_道家从无到化.md](P_道家从无到化.md) | 老子 + 庄子 23 条 | 不变 (Kernel.lean Layers 32-33) |
| [Q_佛家从苦到觉.md](Q_佛家从苦到觉.md) | 缘起 + 三法印 + 四圣谛 + 中道 + 八正道 等 17 条 | 不变 (Kernel.lean Layer 34) |
| [R_与生生不息对齐之必然.md](R_与生生不息对齐之必然.md) | AI alignment 本体论 + 三柱 + 四锁 | 不变 (Alignment.lean) |
| [S_先秦百家.md](S_先秦百家.md) | 墨/法/名/阴阳 + Layer 46 文献流派精化 | 不变 (Kernel Layers 35-38, 46) |
| [T_西哲与亚伯拉罕.md](T_西哲与亚伯拉罕.md) | 希腊 5 + 近代 5 + 20 世纪 6 + 亚伯拉罕 6 | 不变 (Kernel Layers 39-42) |
| [U_反诛心信诚之形式.md](U_反诛心信诚之形式.md) | JIAN v1.0 §IV.5 + 反诛心五律 | 不变 (Sincerity.lean) |
| [V_现代政治哲学.md](V_现代政治哲学.md) | 实证 11 + 证错 7 (双向 layer) | 不变 (Kernel Layers 43-44) |
| [W_非道之形式.md](W_非道之形式.md) | tongGen IS Universal Anti-Moloch Principle | 不变 (Kernel Layer 45) |
| [X_反施密特.md](X_反施密特.md) | Schmitt 三支柱 collapse 至 ¬ tongGen | 不变 (AntiSchmitt.lean) |
| [Y_对齐失败.md](Y_对齐失败.md) | alignment 失败 catalog | 不变 (AlignmentFailures.lean) |
| [Z_经济博弈.md](Z_经济博弈.md) | 现代经济 + 博弈论 6 实证 + 4 有条件 + 8 证错 | 不变 (EconGame.lean) |

### 四衍 (主线 · 不变)

| 文件 | 主题 | Lean 配套 |
|------|------|---|
| [数与算术 · 从元到数.md](数与算术%20·%20从元到数.md) | 自然数 · ℤ · ℚ · ℝ · 四则运算 | `ShuSuan.lean` ✓ 40 声明 |
| [形式逻辑 · 从元到推.md](形式逻辑%20·%20从元到推.md) | Bool³ ≅ 八卦 ≅ 真值表 · K3 三值 | `LuoJi.lean` ✓ 44 声明 |
| [统计 · 从元到测.md](统计%20·%20从元到测.md) | Kolmogorov · Bayes · 大衍占筮 | `TongJi.lean` ✓ 32 声明 |
| [几何位 · 从元到形.md](几何位%20·%20从元到形.md) | 点 · 距 · 拓扑 · 易经四位 | `XingWei.lean` ✓ 32 声明 |

### 八衍之副线四衍 (类 / 动 / 识 / 象 · 不变)

| 文件 | 主题 | Lean 配套 |
|------|------|---|
| [类与映 · 从元到映.md](类与映%20·%20从元到映.md) | Cat / Functor / NatTrans / Adjunction | `LeiYing.lean` ✓ 12 声明 |
| [动力 · 从元到行.md](动力%20·%20从元到行.md) | DynSys + Markov + finite Euler | `DongLi.lean` ✓ 35 声明 |
| [心智 · 从元到识.md](心智%20·%20从元到识.md) | 唯识四分 + 心学四端 + Hopfield + 时间三相 | `XinZhi.lean` ✓ 51 声明 |
| [物理 · 从元到象.md](物理%20·%20从元到象.md) | qubit basis · 对偶 · 守恒 · SU(3) 弱类比 | `WuXiang.lean` ✓ 23 声明 |

### Markov 桥接套件 (Markov桥 S2..S33, 不变)

| 文件 | 主题 |
|---|---|
| [Markov因果桥 · 大统一最小验证构造.md](Markov因果桥%20·%20大统一最小验证构造.md) | 大统一最小验证构造 |
| Markov桥 S2..S33 | 概率核接口 / 路径组合 / 因果约束 / 通道组合 / 测量律 等系列 (~30 文件) |
| [量子时空互补 · 从一到测.md](量子时空互补%20·%20从一到测.md) | 量子时空互补 |
| [量子物理语言 · 从虚到测.md](量子物理语言%20·%20从虚到测.md) | 量子物理语言 |
| [量子与相对论整合方向 · 从桥到新理论.md](量子与相对论整合方向%20·%20从桥到新理论.md) | 量子与相对论整合 |
| [量子与相对论直统一不可能 · 当前语言NoGo.md](量子与相对论直统一不可能%20·%20当前语言NoGo.md) | NoGo 论 |
| [Born rule推导候选 · Markov桥S18.md](Born%20rule推导候选%20·%20Markov桥S18.md) 等 | Born rule 系列 |

### 现代专题 · 结构边界补篇

| 文件 | 主题 | Lean 配套 |
|------|------|---|
| [物间事三位一体 · 时空事件.md](物间事三位一体%20·%20时空事件.md) | 物 / 间 / 事 三面完整性 + carrier + spacetime + event | `WuJianShiTrinity.lean` |
| [根算子与目录隔离.md](根算子与目录隔离.md) | root-native operator 四类来源 + legacy catalogue quarantine | `RootOperator.lean` |
| [道桥接_ProcessAligned_Dao_ShengshengBuxi.md](道桥接_ProcessAligned_Dao_ShengshengBuxi.md) | Process-aligned Dao 道桥接 | — |

### 元到方向 (从元到 X 系列, 不变)

| 文件 | 方向 |
|---|---|
| [几何位 · 从元到形.md](几何位%20·%20从元到形.md) | 形 |
| [动力 · 从元到行.md](动力%20·%20从元到行.md) | 行 |
| [心智 · 从元到识.md](心智%20·%20从元到识.md) | 识 |
| [拓扑 · 从元到障.md](拓扑%20·%20从元到障.md) | 障 |
| [数与算术 · 从元到数.md](数与算术%20·%20从元到数.md) | 数 |
| [形式逻辑 · 从元到推.md](形式逻辑%20·%20从元到推.md) | 推 |
| [统计 · 从元到测.md](统计%20·%20从元到测.md) | 测 |
| [类与映 · 从元到映.md](类与映%20·%20从元到映.md) | 映 |
| [物理 · 从元到象.md](物理%20·%20从元到象.md) | 象 |
| [生态 · 从元到生.md](生态%20·%20从元到生.md) | 生 |
| [史带结构 · 从爻到算子列.md](史带结构%20·%20从爻到算子列.md) | 史带 |

### 经典与人类共同体

| 文件 | 主题 |
|---|---|
| [人类命运共同体_共同体之证.md](人类命运共同体_共同体之证.md) | 三轴 model · iff 充要 · 四相收口 (Renlei.lean) |

### 其它

| 文件 | 主题 |
|---|---|
| [WenSurface领域语义caveat细分.md](WenSurface领域语义caveat细分.md) | WenSurface domain semantics caveats |
| [文构造完备与直相加边界.md](文构造完备与直相加边界.md) | 文构造完备性 |
| [算子别名总表.md](算子别名总表.md) | 算子别名总表 |
| [作用相位到测量权重链 · Markov桥S22.md](作用相位到测量权重链%20·%20Markov桥S22.md) 等 | Markov 桥系列 |
| [边界](边界) | 边界子目录 (单文件) |

---

## 已归档到 `史/义理-pre-v3/`

> v3 重写带来之结构改动 — pre-v3 版本以 git history + 史 archive 双重保留。

| 文件 | pre-v3 状态 | v3 处理 |
|---|---|---|
| `J_理之不完备_哥德尔在192.md` | Cell192 时代之 Gödel 在 192 | **git mv** 至 `J_理之不完备_哥德尔在256.md` + v3 内容重写 |
| 旧 operator-cell topology 文 | legacy grid topology | v3 后按 audit inventory 读，不作 root ontology |
| `G_完整算子系统_八卦互通与归一.md` (旧版) | Cell192 时代之算子代数 | v3 重写 (R₀..R₈ + V₄ Shi at R₈) |
| `H_证明报告.md` (旧版) | BaguaAlgebra 75 定理 / 36 jobs | v3 重写 (R₀..R₈ Phase A/F/G/C / 3656 jobs) |
| `I_八卦全集.md` (旧版) | T₀..T₆ 全集 | v3 重写 (R₀..R₈, OX 字面, V₄ Shi 64 × 4) |
| `K_完备性审计.md` (旧版) | 5 维度审计 + Cell192 索引 | v3 重写 (11-项 closure checklist + 边界声明) |
| `README.md` (旧版) | 八衍 / 91% 进度等指标 | v3 重写 (本文件) |

`史/义理-pre-v3/` 中保存:
- 旧 `Cell192_BaguaTuring_理层全集与不完备.md`
- 旧 `M_证明报告_192_理之不完备.md`
- 旧 `表六_192格全表_旧Z3版.md`
- (其余 v3 重写文件之 pre-v3 版本作为 git history 保留, 无需双份归档)

---

## 三类映射之分判 (v3)

| 类 | 性质 | 收录体系 | 严格度 |
|---|------|---------|-------|
| 形式同构 | 严格 (Z/2)ⁿ uniform | A、B、D、G | 强 |
| 轴乘积 | 多轴笛卡尔积 | C | 中 |
| 类比对应 | 意象呼应 | E（部分）、F | 弱 |
| **机器验证** | **Lean 4 形式化** | H、ShuSuan、LuoJi、XingWei、TongJi、LeiYing、DongLi、XinZhi、WuXiang、GodelLi、L、Truth/SelfDescription | **零 sorry**（仅 kleene 1 项目 axiom）|
| 内容承担 | 数 / 推 / 测 / 形 / 类 / 动 / 识 / 象 八道之展开 | 八衍文件 | 数学严格 + 字元落地 |
| 元自省 | 集合自身完备性 | K | **11-项 R₀..R₈ closure checklist** + 边界声明 |
| 自释微核 | 文之自指 + 计算闭合 | L | 4 模块 / 127 声明 / 0 sorry |

---

## 与六表之关系 (v3 升级)

- 本目录之**两翼级**对应表一（六征本表）之「阳极／阴极」二位
- 本目录之**太极级**对应表一之「中态（不分）」一位
- 本目录之**八卦级** 重之即 64 卦 → 续表六**256 格全表** (升级自 192)
- 本目录之 C 体系即表五（三轴 27 格）之**二态化**简版
- 本目录之**R₈ 闭合层** 对应 yi-RO-hierarchy.md 之 Cell256 = (Z/2)⁸ self-similar closure

---

## 主用与备用 (v3)

- 项目主用: B + C + D 三体系互校 + **G/H/I/J/K v3 五件**
- 形式 base case: D（最薄、最严）
- 汉字落字处: B（中态三字「玄／几／妙」承担太极一级）
- 经典对照: A、E
- 跨学科旁证: F (物理) / N-Z (跨文明)
- **R₀..R₈ uniform doctrine**: [`yi-RO-hierarchy.md`](../docs-next/10_formal_形式/yi-RO-hierarchy.md) (definitive)
- **横纵算子统一**: G (v3 重写, 11+1 单字算子集; 8 atomic XOR + lift/project + 道 + 太极)
- **机器验证**: H (v3 重写, R₀..R₈ Phase A/F/G/C, 3656 jobs / 0 sorry)
- **总册**: I (v3 重写, R₃ + R₆ + R₈ 全集, OX 字面, V₄ Shi 64 × 4 分布)
- **哥德尔不完备**: J (v3 重写, Gödel 在 256, 静态/动态分界, kleene 拆为 4 件原子)
- **完备性审计**: K (v3 重写, 11-项 closure checklist + 边界 by design)
- **数 / 推 / 测 / 形 / 类 / 动 / 识 / 象** (八衍): 内容承担 + Lean 全通过 (~691 公开声明 / 0 sorry / 51 jobs)
- **自释与微核**: L (图灵完备 + 以文自释 + 可执文言 + 微核归一)

---

## 全局约定 (v3)

- **R-hierarchy R₀..R₈** = strict (Z/2)ⁿ uniform; 每 Rₙ = (Z/2)ⁿ; 每相邻层 Lift/Project +1 bit, no jumps. (per [yi-RO-hierarchy.md](../docs-next/10_formal_形式/yi-RO-hierarchy.md))
- **爻位**: $\langle y_1, y_2, y_3 \rangle = \langle$下, 中, 上$\rangle$, $y_1$ 为初爻 (最下).
- **OX notation** (R₀..R₈ uniform): `o` = yang (identity bit), `x` = yin (set bit); 字符顺序 = 初爻 → 上爻 (LTR, inner-to-outer); R₈ 后 2 位 = (因, 果) → Shi V₄.
- **R₃ 算子**: 动 / 化 / 变 = 反 $y_1$ / $y_2$ / $y_3$ (即「动在下、化在中、变在上」).
- **R₇/R₈ 算子**: 印 (R₇ atom, mask `OX["ooooooxo"]`) / 投 (R₈ atom, mask `OX["ooooooox"]`).
- **错** = 阴阳全反 (在 (Z/2)ⁿ 内); **综** = 位置反序 (不在 flip 群内); **互** = 互卦 (位置 perm, 维度降).
- **道** = R₈ identity = `Cell256.origin = (Hexagram.qian, Shi.dao) = OX["oooooooo"]` — 五重身份 anchor (origin / identity / no-op / 永真 cell / fusion anchor).
- **三值保守律**: U ⇏ ⊤ (未决态不可任意上升至真); 详见 K §六 + 数与算术 §十六·半 + 形式逻辑衍 §3 + 统计衍 §13.
- **静态/动态分界**: 静态 R₀..R₈ closure (0 项目 axiom) vs 动态 BaguaTuring 加 partial run (1 项目 axiom = kleene_recursion_axiom).

---

## 形式锚 (umbrella)

- [`formal/SSBX/Foundation/Hierarchy/RHierarchy.lean`](../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean) — R₀..R₈ + LiftProject + Operators umbrella import
- [`docs-next/10_formal_形式/yi-RO-hierarchy.md`](../docs-next/10_formal_形式/yi-RO-hierarchy.md) — R₀..R₈ definitive doctrine
- [`docs-next/10_formal_形式/yi-calculus-theorem.md`](../docs-next/10_formal_形式/yi-calculus-theorem.md) — Theorems A–K + 命名 caveats
- [`docs-next/10_formal_形式/yi-as-meta-framework.md`](../docs-next/10_formal_形式/yi-as-meta-framework.md) — 哲学层
- [`docs-next/10_formal_形式/cell256-grid.md`](../docs-next/10_formal_形式/cell256-grid.md) — 256-cell ground inventory
- [`docs-next/10_formal_形式/64-hexagram-grid.md`](../docs-next/10_formal_形式/64-hexagram-grid.md) — 64 卦四语对照
