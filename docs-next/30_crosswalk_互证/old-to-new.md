# 旧文到新版

> 状态：v3 定本 (2026-05-11) — Cell256 / V₄ Klein Shi / 严格 uniform R₀..R₈ / Phase C `Shi := YinBit × GuoBit`

本页给旧 `义理/`、`史料/` 与新版 docs-next 的迁移读法。**两层并陈**：上半为术语层（旧形式概念 → v3 新结构），下半为入口层（旧文范围 → 新版入口与归档）。代码层之具体 diff 不在本页，见 sibling [`cell192-to-cell256-migration.md`](cell192-to-cell256-migration.md)。

## 总原则

- v3 之结构核心：**R₀..R₈ strict (Z/2)ⁿ uniform** + V₄ Klein Shi at R₈ + 印/投 atomic XOR-mask 算子 + 道作为 R₈ origin (= identity = no-op = 永真 cell) + 太极作为 R₀ absolute zero-anchor。
- 旧文（v2 期，主要为 Cell192 + Z/3 Shi）之大部分**结论**仍可援引，但**结构编码**多数已过期，迁移时必须对接 v3 之新型号。
- 旧文不在 docs-next 中重写成长篇合订；新版优先说明「去哪里读」「当前强度如何」「是否有 Lean 或生成索引支撑」。
- 已被 v3 严格取代、不宜再作为读者入口之文件归 `史/`；仍有研究价值之早期手稿（v9–v14、daoli-v11/v12 等）归 `史料/`。
- 旧文中之宏大论断进入新版时，必须降到可审计状态：theorem、claim、model、registry、pending 或 archive。
- 本表只迁移**形式与结构**口径；价值层、对齐层、伦理层之旧文表述（善/仁/义/邪/道德等）原则上仍读 `../20_theory_义理/`。

---

## Cell192 → Cell256 transition (2026-05-10/11)

这是 docs-next v3 与 v2 的核心 ontological 升级。**Cell192 / Z/3 cyclic Shi 已被完全删除**，取代为 Cell256 / V₄ Klein Shi。代码层迁移指引见 sibling [`cell192-to-cell256-migration.md`](cell192-to-cell256-migration.md)；本页只给术语 + 顶层结构对照。

### 顶层差异

| 维度 | 旧 (Cell192, v2 及更早) | 新 (Cell256, v3 / 2026-05-10/11 起) |
|---|---|---|
| Cell space 基数 | **192** = 64 hex × 3 Shi | **256** = 64 hex × 4 Shi = (Z/2)⁸ |
| Shi 群结构 | Z/3 cyclic {已, 今, 未} | **V₄ Klein {道, 已, 今, 未}** |
| Shi.dao | 缺失 (Z/3 没有 V₄ identity) | **first-class V₄ identity = origin = 永真** |
| Shi 编码 | inductive 3 ctors，cyclic +1 mod 3 | Phase C: **`abbrev Shi := YinBit × GuoBit`**（4 名字 = `@[match_pattern] def`） |
| `shiNext` | +1 mod 3 cycle | **`Shi.cuo` involution (V₄, period 2, self-inverse)** |
| R-hierarchy 编号 | R₁..R₆，含 R₃→R₄ 之 +3 bit chong jump | **严格 uniform R₀..R₈，每层 +1 bit, no jumps** |
| Cell-content 卡片基数 | 192 × 371 = 71232 | 256 × 371 = 94976 |
| 道之地位 | 哲学附加 anchor (不在 Shi 内) | V₄ identity = (因=0, 果=0)，algebraic 必然 |
| Self-description witness | `Cell192OperatorComplete` | **`Cell256OperatorComplete`** |
| R-closure bundle | 旧 `R7_complete` (256 单层视角，已废) / `R6_complete` (192 视角) | **`R8_complete`**, depends only on `propext + native_decide` |

### R-hierarchy 重号

| v2 编号 (旧) | v3 编号 (新) | size | 名 | 说明 |
|---|---|---|---|---|
| (隐含) | **R₀** | 1 | 太极 | 显式 Unit 入 |
| R₁ | R₁ | 2 | 爻 / 两仪 | 不变 |
| R₂ | R₂ | 4 | 四象 | 不变 |
| R₃ | R₃ | 8 | 八卦 | 不变 |
| (跳过) | **R₄** | 16 | 面 (Mian) = Ben × Zheng | 显式补 |
| (跳过) | **R₅** | 32 | 五爻 (provisional) | 显式补，无传统 anchor |
| R₄ | **R₆** | 64 | 重卦 (Hexagram) | 重号 |
| R₅ | **R₇** | 128 | 因卦 (Cell128) | 重号 |
| R₆ | **R₈** | 256 | 果卦 (Cell256) | 重号 |

旧 v1/v2 之「R₃ → R₄ chong jump」(直接 +3 bit 到 hexagram，跳过 (Z/2)⁴ = 16 与 (Z/2)⁵ = 32)，在 v3 中被显式拆为 R₃ → R₄ → R₅ → R₆ 三步 +1 bit lift composite。

### Shi V₄ 双射结构

```
v3: Shi ↔ (YinBit × GuoBit) ∈ Bool²    -- Phase C: abbrev (非 inductive)
  道 ↔ (false, false) = (因=0, 果=0) = V₄ identity = origin = no-op = 永真
  已 ↔ (true,  false) = (因=1, 果=0) = past closed
  未 ↔ (false, true ) = (因=0, 果=1) = future open
  今 ↔ (true,  true ) = (因=1, 果=1) = PT, present
```

道 = V₄ 单位元 = 跨时空 anchor — 把它从 Shi 删除（如 Cell192 的 Z/3 cyclic）即丧失「描述者本身之恒在 anchor」，破坏 R-hierarchy 之 (Z/2)ⁿ self-similarity。

---

## 主迁移表（术语层 + 结构层概念）

| # | 旧术语 / 旧概念 | v3 新术语 / 新结构 | v3 规范文档 | 史/ 归档（旧来源） |
|---|---|---|---|---|
|  1 | **Cell192** = 64 卦 × 3 史态 (Z/3 cyclic) | **Cell256** = 64 卦 × 4 时态 (V₄ Klein) = `Hexagram × Shi` | [`../10_formal_形式/cell256-grid.md`](../10_formal_形式/cell256-grid.md), [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) | [`史/docs-next-pre-v3/cell192-grid_Z3-Shi_旧版.md`](../../史/docs-next-pre-v3/cell192-grid_Z3-Shi_旧版.md) |
|  2 | **Shi : Z/3** cyclic（如 `dao→cur→fin→dao`） | **Shi : V₄ Klein** = `{道, 已, 今, 未}`，由 (因, 果) ∈ Bool² emerge；非 cyclic；Phase C 起 `abbrev Shi := YinBit × GuoBit` | [`../10_formal_形式/v4-shi.md`](../10_formal_形式/v4-shi.md), [`shi-v4.md`](../10_formal_形式/shi-v4.md), `Cell256.lean § 1` | 同上 |
|  3 | 旧 R-hierarchy 编号 **R₁..R₆**（含 R₃→R₄ 之 +3 bit chong jump，跳过 16 / 32） | **R₀..R₈ strict (Z/2)ⁿ uniform**，每加 1 bit 升 1 层，无跳跃；R₀ = 太极 = Unit；R₈ = Cell256 | [`../10_formal_形式/yi-RO-hierarchy.md`](../10_formal_形式/yi-RO-hierarchy.md) | [`史/docs-next-pre-v3/yi-RO-hierarchy_v1_旧R1-R6编号.md`](../../史/docs-next-pre-v3/yi-RO-hierarchy_v1_旧R1-R6编号.md) |
|  4 | 旧 R₄ = Hexagram (64) | 新 R₆ = Hexagram (重号 +2) | `yi-RO-hierarchy.md § 3.6` | 同 #3 |
|  5 | 旧 R₅ = Cell128 (128) | 新 R₇ = Cell128 = `Hexagram × YinBit` (重号 +2) | [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean), `RHierarchy.lean` R₇ | 同 #3 |
|  6 | 旧 R₆ = Cell192 (192) | 新 R₈ = Cell256 = `Hexagram × Shi` (重号 +2; 同时 192 → 256) | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) | 同 #1, #3 |
|  7 | **「Mian = Ben × Zheng = 16」是最大不可分单位**（旧 BenZheng 文档语境） | **Mian = R₄**（(Z/2)⁴）是 R-hierarchy 之**第 4 层**；之上还有 R₅..R₈，最大是 **R₈ = 256** | [`../10_formal_形式/yi-RO-hierarchy.md § 3.4`](../10_formal_形式/yi-RO-hierarchy.md), [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) | 旧 BenZheng 论稿（仍主要在 `义理/`） |
|  8 | **Face 12-枚举**（M-line 名册分类，旧顶层 ontology） | Face 现作 M-line atom 分类，**不再当 R-axis**；与 BenZheng 4×4 并存（P5b 试图删 Face，P6 部分回滚） | [`../00_start/phase-status.md`](../00_start/phase-status.md) | — |
|  9 | **3-元 surface (legacy JianOntology)** | **4本/4征 = R₃ Ben×Zheng = 16 Mian = R₄**；P6 起 BenZheng 主导，JianOntology 降级为 legacy 3-元 surface | [`../10_formal_形式/jian.md`](../10_formal_形式/jian.md), [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) | — |
| 10 | **「192 格全表」**（表六旧版） | **「256 格全表」**（表六新版，64 × 4 + 因/果 标注） | `六表_实虚史真/表六_256格全表.md`, `Cell256.lean` `xuGua256` | [`史/义理-pre-v3/表六_192格全表_旧Z3版.md`](../../史/义理-pre-v3/表六_192格全表_旧Z3版.md) |
| 11 | `Cell192.Shi` (Z/3 cyclic ctor `dao / cur / fin`) | `Cell256.Shi` (V₄ ctor `dao / ji / jin / wei`；Phase C 后为 `Bool × Bool` 之 `@[match_pattern] def`) | `Cell256.lean § 1`, [`v4-shi.md`](../10_formal_形式/v4-shi.md) | `史/docs-next-pre-v3/` |
| 12 | `cur` (中态, Z/3 中点) | `今` = `Shi.jin` = (因=1, 果=1) = V₄ 中心元 = PT | `Cell256.lean`, `v4-shi.md` | 同上 |
| 13 | `fin` (终态, Z/3 终点) | 拆为两支：`已` = `Shi.ji` = (1,0) (过去封闭) + `未` = `Shi.wei` = (0,1) (未来开放) | `Cell256.lean`, `v4-shi.md` | 同上 |
| 14 | `Cell192Stratify.lean` / `cell192_complete` | [`Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) / `R8_complete` bundle | `Cell256Stratify.lean § 7`, `R8_complete : ...` | 旧 `Cell192Stratify.lean`（已删） |
| 15 | `R6_complete` 收口定理 | `R8_complete` 收口定理（重号 +2；Cell256 基数 + R-hierarchy + P/T/Y closure + 群作用 simply-transitive + BenZheng 投影 + 位置-算子树 + xuGua256；依赖只 `propext + native_decide`） | `Cell256Stratify.lean` | 旧 `R6_complete`（已迁） |
| 16 | 旧 `chong : R₃ × R₃ → R₄`（"3-bit jump"，跳过 16/32） | `chong : R₃ × R₃ → R₆` 仍是 hexagram-合卦传统语义；**结构上**显式拆为 3 步 +1 bit lift `R₃ → R₄ → R₅ → R₆`（unfolded composite，无 jump） | `yi-RO-hierarchy.md § 3.9`, [`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) | 旧 yi-RO-hierarchy v1 |
| 17 | **印 / 投 仅作 Shi inductive 上的 V₄ 算子**（Cell192 期：印=cuo on Shi, 投=zong on Shi） | **印 / 投 first-class XOR-mask 算子 at Cell256**（R₇/R₈ atomic）：`yin = (· ⊕ yin_mask)`；`tou = (· ⊕ tou_mask)` | [`../10_formal_形式/yin-tou-operators.md`](../10_formal_形式/yin-tou-operators.md), [`Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) | 旧 Shi-only 印/投（旧 Cell192.lean） |
| 18 | 旧「Shi 的 Z/3 cyclic 是史维三态本体」 | Shi V₄ = (因, 果) Bool² emergence；**Z/3 cyclic 不是必要**，而是 v2 期之结构错误 | `Cell256.lean § 1` 注解；`yi-RO-hierarchy.md` 附录 A | `史/docs-next-pre-v3/` README 解释 |
| 19 | 旧「道」字仅作哲学 anchor，无形式地位 | 道 = `Shi.dao` = (因=0, 果=0) = V₄ identity = R₈ origin = identity = no-op = 永真 cell；**形式 first-class** | `Cell256.lean § 1`, [`OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) `OX["oooooooo"]` | — |
| 20 | 旧无 R₀ 显式（Unit 隐含） | **R₀ = 太极 = Unit** 显式纳入 R-hierarchy，作 absolute zero-anchor | `yi-RO-hierarchy.md § 3.0`, `RHierarchy.lean R₀_Taiji` | — |
| 21 | 旧无 R₅ (五爻) 层（被 chong jump 跳过） | **R₅ = 五爻 (provisional)** = `Mian × Bool` = 32；descriptive baseline，无传统 Yi anchor | [`../10_formal_形式/r5-wuyao-provisional.md`](../10_formal_形式/r5-wuyao-provisional.md), `R5_Wuyao.lean` | — |
| 22 | 旧 `WenyanSelfInterp.lean` 之 base-192 dispatch | base-256 dispatch；Phase F.1 已迁 atomic encoding 到 `Cell256.Shi`（cite commit `7de5064`） | `WenyanSelfInterp.lean` head comment | 旧 base-192 dispatch（已删） |

### 文件迁移（Lean）

| 旧路径 | 新路径 / 状态 |
|---|---|
| `Foundation/Bagua/Cell192.lean` | **DELETED** (commit `8e4406e`, Phase F.6) |
| `Foundation/Bagua/Cell192Stratify.lean` | **REPLACED** by `Cell256Stratify.lean` (R₀..R₈ + R8_complete) |
| (无) | `Foundation/Bagua/Cell256.lean` (R₈ carrier + Shi V₄ + Cayley / 投) |
| (无) | `Foundation/Bagua/Cell128.lean` (R₇ carrier + 因 / 印) |
| (无) | `Foundation/Hierarchy/R0_Taiji.lean` .. `R8_GuoHex.lean` (9 R-index alias 文件) |
| (无) | `Foundation/Hierarchy/RHierarchy.lean` (umbrella import) |
| (无) | `Foundation/Hierarchy/R5_Wuyao.lean` (R₅ provisional, Mian × Bool) |
| (无) | `Foundation/Hierarchy/LiftProject.lean` (8 R-layer pairs + retract 引理) |
| (无) | `Foundation/Hierarchy/Operators/Atomic.lean` (XOR-subgroup atomic) |
| (无) | `Foundation/Hierarchy/Operators/V4Outer.lean` (zong / hu / cuoZong) |
| (无) | `Foundation/Notation/OXNotation.lean` (`OX["xxxxxxxx"]` macro) |

### 文件迁移（docs-next）

| 旧路径 | 新路径 / 状态 |
|---|---|
| `docs-next/10_formal_形式/cell192-grid.md` | **moved** → [`史/docs-next-pre-v3/cell192-grid_Z3-Shi_旧版.md`](../../史/docs-next-pre-v3/cell192-grid_Z3-Shi_旧版.md)；新版 [`cell256-grid.md`](../10_formal_形式/cell256-grid.md) |
| `docs-next/10_formal_形式/yi-RO-hierarchy.md` (v1) | **moved** → [`史/docs-next-pre-v3/yi-RO-hierarchy_v1_旧R1-R6编号.md`](../../史/docs-next-pre-v3/yi-RO-hierarchy_v1_旧R1-R6编号.md)；新版同名 (v2.1 strict uniform 提为正本) |
| `表六_192格全表.md` | **renamed** → `表六_256格全表.md` (64 × 4 + 因/果 标注)；旧本归 [`史/义理-pre-v3/表六_192格全表_旧Z3版.md`](../../史/义理-pre-v3/表六_192格全表_旧Z3版.md) |
| 旧 191/192/3-Shi 论述零散段落 | **不迁移**；以 [`yi-RO-hierarchy.md`](../10_formal_形式/yi-RO-hierarchy.md) + [`yi-calculus-theorem.md`](../10_formal_形式/yi-calculus-theorem.md) 为定本 |

### 下游 (Modern/* 等) 级联

`finite_probability_bridge_summary` / `wen_constructive_coverage_192_371` 等数值定理保留旧引理名（避免重命名级联），但 cardinal 内容已升级到 256：

- `192 × 371 = 71232` → `256 × 371 = 94976`
- 下游 cascade 包括 StepwiseUnification, NormalizedMass, FiniteProbabilityNormalization (Phase F.x.5, commit `0003224`)

### MetaInterp / SubDispatch 重构

V₄ 之 4 ctor 替代 Z/3 之 3 ctor，导致 dispatch 树从 4 × 3 重排为 3 × 4：

- `Block_*.lean` (5 文件): Branches, HuCuoZong, Jump, PushPop, SetShi_FlipYao
- `SubDispatch_Shi.lean`: tree 3-way → 4-way
- `SubDispatch_YaoEq.lean`: 9 → 10 cases
- `Dispatch.lean`: top-level tree 4 × 3 → 3 × 4 (16 instr; 12 routing theorems 重做)
- `MetaInterp.lean` entry: `decCounter` / `decHaltedFlag` 增 dao 臂

详见 commit `7de5064` Phase F.3 (~13 文件), `8e4406e` Phase F.6 (Cell192.lean 删), `90c34f0` Phase C (`Shi := Bool × Bool` abbrev).

---

## 旧文（旧 docs + 旧 义理）→ v3 入口

| 旧文范围 | 新版入口 | 备注 |
|---|---|---|
| `义理/A`–`G` | `../20_theory_义理/core-framework.md` | 核心框架与算子骨架 — 已升级至 R₀..R₈ |
| `义理/H`–`M` | `../20_theory_义理/formal-and-proof.md` | 证明报告、Cell256 (替代 Cell192)、自释路线；旧「证明报告」请同时对接 #14, #15, #22 |
| `义理/N`、`P`、`Q`、`S`、`E` | `../20_theory_义理/traditions.md` | 传统映射，多数在 v3 下结构稳定，不改写为史学定论 |
| `义理/O`、`R`、`U`–`Z` | `../20_theory_义理/modern-and-alignment.md` | 对齐 / 政治 / 经济 / 失败模式；形式接口少，受 v3 影响有限 |
| 八衍专题文（数 / 推 / 测 / 形 / 类 / 动 / 识 / 象） | `../20_theory_义理/extensions.md` | 涉及形式骨架之处用本表 #1–#22 迁移 |
| `义理/算子别名总表.md` | `../40_reference_参考/operators.md` | 人工别名表须对照算子索引 |

## 旧史料入口

| 史料范围 | 新版入口 | 备注 |
|---|---|---|
| `史料/生生不息论_三本文完整版/` | `../40_reference_参考/historical-sources.md` | frozen snapshot，不重写 |
| `史料/真理/daoli-v12-*.md` | `../40_reference_参考/historical-sources.md` | 早期 truth framework |
| v11/v12 单体稿 | `../40_reference_参考/historical-sources.md` | 版本追踪 |
| `史料/v14_形式证明骨架版.md` | `../50_maintenance/archive-policy.md` | 归档与后续维护口径 |
| `史/docs-next-pre-v3/` | [`archive-pointers.md`](archive-pointers.md) (如存在) / `史/README.md` | v2 (Cell192 / 旧 R₁..R₆) frozen 副本 |

## 迁移时的降级规则（与 v3 之 claim 强度对接）

| 旧文表述 | v3 处理 |
|---|---|
| 「证明」/「已证」 | 查对应 Lean 模块（多数已 `Cell256` 化）；写「Lean 已检查」仅当 theorem 存在 |
| 「模型验证」 | 查是否 `modelComputed`；否则写「模型接口」 |
| 「完备」 | 区分 registry 完备、表完备、语义完备和哲学完备 |
| 「必然」 | 查是否 theorem；否则写「在该框架内主张」 |
| 「对应」 | 写清是文本映射、算子映射、claim 映射还是形式同构 |
| 「Cell192 / Z/3 Shi」 | 改写为 Cell256 / V₄ Shi；如指历史叙述则保留并加「v2 旧」记号 |
| 「Z/3 cyclic 是史维三态」 | 写「v2 期采用 Z/3，已被 v3 V₄ Klein 取代为结构层正确编码」 |
| 「192 格全表」 | 写「256 格全表（v3）」；旧 192 表归 `史/义理-pre-v3/` |
| 「Mian 是最大」 | 写「Mian = R₄ = (Z/2)⁴；R-hierarchy 之上仍有 R₅..R₈」 |
| 「印 / 投 是 Shi V₃ 内三相算子」 | 写「印 / 投 = Cell256 之 XOR-mask atomic 算子（mask 见 `Cell256.lean § 8`）」 |
| 「R₆ 是顶层」 | 写「R₈ = Cell256 是 (Z/2)ⁿ self-describing 之自然闭合（无第 9 个独立 binary axis）」 |

## 不迁移内容

- 旧文之修辞段落不搬入 v3。
- `史料/` 之合订稿不做现代化改写；只引用。
- 未落地的经验接口（pending interface）不写成 Lean 事实。
- 自动生成索引（`_generated/`）之内容不复制到人工页（如生成）。
- Cell192 / Z/3 Shi 主张不在 v3 文档中陈述，只在「历史回顾」(本页) 与 `史/docs-next-pre-v3/` frozen 副本里保留。
- 旧 Cell192 时期之**模型直觉**（如 64 卦 × 3 状态、史维三态等）允许在解释层引用，但形式层一律以 Cell256 + V₄ Shi 为准。

## 参见

- 完整概念辞典：[`../40_reference_参考/glossary.md`](../40_reference_参考/glossary.md)
- 详细迁移操作指引（含 Lean 代码 diff 样例）：[`cell192-to-cell256-migration.md`](cell192-to-cell256-migration.md)
- claim 状态读法：[`claim-status.md`](claim-status.md)
- v3 doctrine 主干：[`../10_formal_形式/yi-RO-hierarchy.md`](../10_formal_形式/yi-RO-hierarchy.md)
- Phase 状态（Face / BenZheng 当前并存口径）：[`../00_start/phase-status.md`](../00_start/phase-status.md)

## 形式锚

- [`formal/SSBX/Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) — Cell256 / Shi V₄ / 印 / 投 / Cayley
- [`formal/SSBX/Foundation/Bagua/Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) — R₇ Cell128 / YinBit
- [`formal/SSBX/Foundation/Bagua/Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) — `R8_complete` 收口
- [`formal/SSBX/Foundation/Hierarchy/RHierarchy.lean`](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean) — R₀..R₈ umbrella
- [`formal/SSBX/Foundation/Hierarchy/LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) — 8 对 lift/project + retract 引理
- [`formal/SSBX/Foundation/Notation/OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) — `OX["o/x×8"]` 字面量
- [`formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) — XOR-mask atomic 算子
- [`formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) — V₄ outer permutations
- 史/ 归档：[`史/README.md`](../../史/README.md)
