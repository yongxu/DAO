# 旧文到新版

> 状态：v3 定本 (2026-05-11) — Cell256 / V₄ Klein Shi / 严格 uniform R₀..R₈

本页给旧 `义理/`、`史料/` 与新版 docs-next 的迁移读法。旧文保留为来源和历史论证，新版负责入口、状态和互证。

## 总原则

- 旧文不在 docs-next 中重写成长篇合订。
- 新版优先说明「去哪里读」「当前强度如何」「是否有 Lean 或生成索引支撑」。
- 旧文中的宏大论断进入新版时，必须降到可审计状态：theorem、claim、model、registry、pending 或 archive。
- 路径存在性和统计以 `../_generated/markdown-index.md`、`../_generated/crossrefs.md` 为准。

---

## Cell192 → Cell256 transition (2026-05-10/11)

这是 docs-next v3 与 v2 的核心 ontological 升级。**Cell192 / Z/3 cyclic Shi 已被完全删除**，取代为 Cell256 / V₄ Klein Shi。

### 顶层差异

| 维度 | 旧 (Cell192, v2 及更早) | 新 (Cell256, v3 / 2026-05-10/11 起) |
|---|---|---|
| Cell space 基数 | **192** = 64 hex × 3 Shi | **256** = 64 hex × 4 Shi = (Z/2)⁸ |
| Shi 群结构 | Z/3 cyclic {已, 今, 未} | **V₄ Klein {道, 已, 今, 未}** |
| Shi.dao | 缺失 (Z/3 没有 V₄ identity) | **first-class V₄ identity = origin = 永真** |
| Shi 编码 | inductive 3 ctors，cyclic +1 mod 3 | inductive 4 ctors ↔ (YinBit × GuoBit) ∈ Bool² |
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
v3: Shi ↔ (YinBit × GuoBit) ∈ Bool²
  道 ↔ (false, false) = (因=0, 果=0) = V₄ identity = origin = no-op = 永真
  已 ↔ (true,  false) = (因=1, 果=0) = past closed
  未 ↔ (false, true ) = (因=0, 果=1) = future open
  今 ↔ (true,  true ) = (因=1, 果=1) = PT, present
```

道 = V₄ 单位元 = 跨时空 anchor — 把它从 Shi 删除（如 Cell192 的 Z/3 cyclic）即丧失「描述者本身之恒在 anchor」，破坏 R-hierarchy 之 (Z/2)ⁿ self-similarity。

### 文件迁移

#### Lean 文件（formal/SSBX/）

| 旧路径 | 新路径 / 状态 |
|---|---|
| `Foundation/Bagua/Cell192.lean` | **DELETED** (commit `8e4406e`, Phase F.6) |
| `Foundation/Bagua/Cell192Stratify.lean` | **REPLACED** by `Cell256Stratify.lean` (R₀..R₈ + R8_complete) |
| `Foundation/Bagua/Cell256.lean` | new (R₈ carrier + Shi V₄ + Cayley / 投) |
| `Foundation/Bagua/Cell128.lean` | new (R₇ carrier + 因 / 印) |
| (无) | `Foundation/Hierarchy/R0_Taiji.lean` .. `R8_GuoHex.lean` (9 R-index alias 文件) |
| (无) | `Foundation/Hierarchy/RHierarchy.lean` (umbrella import) |
| (无) | `Foundation/Hierarchy/R5_Wuyao.lean` (R₅ provisional, Mian × Bool) |
| (无) | `Foundation/Hierarchy/LiftProject.lean` (8 R-layer pairs) |
| (无) | `Foundation/Hierarchy/Operators/Atomic.lean` (XOR-subgroup re-export) |
| (无) | `Foundation/Hierarchy/Operators/V4Outer.lean` (zong / hu / cuoZong) |
| (无) | `Foundation/Notation/OXNotation.lean` (`OX["xxxxxxxx"]` macro) |

#### 文档文件（docs-next/）

| 旧路径 | 新路径 / 状态 |
|---|---|
| `docs-next/10_formal_形式/cell192-grid.md` | **moved** → [`史/docs-next-v2/cell192-grid_Z3-Shi_旧版.md`](../../史/docs-next-v2/cell192-grid_Z3-Shi_旧版.md)，新版 [`cell256-grid.md`](../10_formal_形式/cell256-grid.md) (创建中) |
| `docs-next/10_formal_形式/yi-RO-hierarchy.md` (v1) | **moved** → [`史/docs-next-v2/yi-RO-hierarchy_v1_旧R1-R6编号.md`](../../史/docs-next-v2/yi-RO-hierarchy_v1_旧R1-R6编号.md)，新版 [`yi-RO-hierarchy.md`](../10_formal_形式/yi-RO-hierarchy.md) (原 -v2 提为正本) |
| `表六_192格全表.md` | **renamed** → `表六_256格全表.md` (64 × 4 + 因/果 标注) |
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

详见 commit `7de5064` Phase F.3 (~13 文件), `8e4406e` Phase F.6 (Cell192.lean 删).

---

## 旧义理入口（v3 路由不变）

| 旧文范围 | 新版入口 | 备注 |
|---|---|---|
| `义理/A`–`G` | `../20_theory_义理/core-framework.md` | 核心框架与算子骨架 — 已升级至 R₀..R₈ |
| `义理/H`–`M` | `../20_theory_义理/formal-and-proof.md` | 证明报告、Cell256 (替代 Cell192)、自释路线 |
| `义理/N`、`P`、`Q`、`S`、`E` | `../20_theory_义理/traditions.md` | 传统映射，不改写为史学定论 |
| `义理/O`、`R`、`U`–`Z` | `../20_theory_义理/modern-and-alignment.md` | 对齐、政治、经济、失败模式 |
| 八衍专题文 | `../20_theory_义理/extensions.md` | 数、推、测、形、类、动、识、象等专题 |
| `义理/算子别名总表.md` | `../40_reference_参考/operators.md` | 人工别名表须对照生成算子索引 |

## 早期 Face → BenZheng 升级（保留）

P5/P6 阶段重构的旧 → 新映射（仍有效）：

| 旧概念 | 新概念 | 状态 |
|---|---|---|
| Face 12-枚举 (M-line 名册分类) | 与 BenZheng 4×4 **并存** (P5b 试图删 Face，P6 部分回滚) | 详 [`../00_start/phase-status.md`](../00_start/phase-status.md) |
| Face = 12 顶层分类 (顶层 ontology) | Face 现作 M-line atom 分类，不再当 R-axis | 仍存在 |
| 3-元 surface (legacy JianOntology) | **4本/4征 = R₃ Ben×Zheng = 16 Mian = R₄** | P6 起 BenZheng 主导 |

---

## 旧史料入口

| 史料范围 | 新版入口 | 备注 |
|---|---|---|
| `史料/生生不息论_三本文完整版/` | `../40_reference_参考/historical-sources.md` | frozen snapshot |
| `史料/真理/daoli-v12-*.md` | `../40_reference_参考/historical-sources.md` | 早期 truth framework |
| v11/v12 单体稿 | `../40_reference_参考/historical-sources.md` | 版本追踪 |
| v14 骨架稿 | `../50_maintenance/archive-policy.md` | 归档与后续维护口径 |
| `史/docs-next-v2/` | `archive-pointers.md` | v2 (Cell192/旧 R₁..R₆) frozen 副本 |

## 迁移时的降级规则

| 旧文表述 | 新版处理 |
|---|---|
| 「证明」 | 查 Lean；无 theorem 时写「论证」或「ledger 承接」 |
| 「模型验证」 | 查是否 modelComputed；否则写「模型接口」 |
| 「完备」 | 区分 registry 完备、表完备、语义完备和哲学完备 |
| 「必然」 | 查是否 theorem；否则写「在该框架内主张」 |
| 「对应」 | 写清是文本映射、算子映射、claim 映射还是形式同构 |
| 「Cell192 / Z/3 Shi」 | 改写为 Cell256 / V₄ Shi；如指历史叙述则保留并加「v2 旧」记号 |

## 不迁移内容

- 旧文的修辞段落不搬入新版。
- 史料目录不做现代化改写。
- 未落地的经验接口不写成 Lean 事实。
- 生成文件内容不复制到人工页；只引用 `../_generated/`。
- Cell192 / Z/3 Shi 主张不在 v3 文档中陈述，只在「历史回顾」(本页) 与 `史/docs-next-v2/` frozen 副本里保留。
