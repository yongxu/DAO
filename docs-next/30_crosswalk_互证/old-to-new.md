> 状态：v3 (2026-05-11) — 旧术语到新版（Cell256 / V₄ Klein Shi / R₀..R₈ strict-uniform）的迁移读法。每行给一个旧概念、它的新对应、新版规范文档与（如适用）`史/` 中之归档来源。

# 旧术语 → v3 新术语（迁移读法）

本页**不是**旧文与新版长篇互译，也不是旧 docs 与 docs-next 的篇目对照（那一份在 `../00_start/migration-from-legacy.md` 与 `../50_maintenance/archive-policy.md`）。本页是**术语层与结构层**的迁移图：v3 之前曾被项目正式使用、但已被 strict (Z/2)ⁿ uniform R₀..R₈ + V₄ Klein Shi 取代之**形式概念**，对每一个给出新版替代、规范定义所在与考古路径。

## 总原则

- v3 之结构核心：**R₀..R₈ strict (Z/2)ⁿ uniform** + V₄ Klein Shi at R₈ + 印/投 atomic XOR-mask 算子 + 道作为 R₈ origin (= identity = no-op = 永真 cell) + 太极作为 R₀ absolute zero-anchor。
- 旧版（v3 之前，主要为 Cell192 + Z/3 Shi 时期）之大部分**结论**仍可援引，但**结构编码**多数已过期，迁移时必须对接 v3 的新型号。
- 已被 v3 严格取代、不宜再作为读者入口之文件归 `史/`；仍有研究价值之早期手稿（v9–v14、daoli-v11/v12 等）归 `史料/`。
- 任何在文档中遇到的「Cell192」「Z/3」「R₁..R₆ 含 chong jump」「Mian = Ben×Zheng = 16 是最大」「192 格全表」之类表述都应以本页迁移到 v3 对应。
- 本表只迁移**形式与结构**口径；价值层、对齐层、伦理层之旧文表述（善/仁/义/邪/道德等）原则上仍读 `../20_theory_义理/`。

## 主迁移表（结构 + 形式概念）

| # | 旧术语 / 旧概念 | v3 新术语 / 新结构 | v3 规范文档 | 史/ 归档（旧来源） |
|---|---|---|---|---|
|  1 | **Cell192** = 64 卦 × 3 史态 (Z/3 cyclic) | **Cell256** = 64 卦 × 4 时态 (V₄ Klein) = `Hexagram × Shi` | [`../10_formal_形式/cell256-grid.md`](../10_formal_形式/cell256-grid.md), [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) | [`史/docs-next-pre-v3/cell192-grid_Z3-Shi_旧版.md`](../../史/docs-next-pre-v3/cell192-grid_Z3-Shi_旧版.md) |
|  2 | **Shi : Z/3** cyclic（如 `dao→cur→fin→dao`） | **Shi : V₄ Klein** = `{道, 已, 今, 未}`，由 (因, 果) ∈ Bool² emerge；非 cyclic | [`../10_formal_形式/v4-shi.md`](../10_formal_形式/v4-shi.md), `Cell256.lean § 1` | 同上 |
|  3 | 旧 R-hierarchy 编号 **R₁..R₆**（含 R₃→R₄ 之 +3 bit chong jump，跳过 16 / 32） | **R₀..R₈ strict (Z/2)ⁿ uniform**，每加 1 bit 升 1 层，无跳跃；R₀ = 太极 = Unit；R₈ = Cell256 | [`../10_formal_形式/yi-RO-hierarchy.md`](../10_formal_形式/yi-RO-hierarchy.md) | [`史/docs-next-pre-v3/yi-RO-hierarchy_v1_旧R1-R6编号.md`](../../史/docs-next-pre-v3/yi-RO-hierarchy_v1_旧R1-R6编号.md) |
|  4 | 旧 R₄ = Hexagram (64) | 新 R₆ = Hexagram (重号 +2) | `yi-RO-hierarchy.md § 3.6` | 同 #3 |
|  5 | 旧 R₅ = Cell128 (128) | 新 R₇ = Cell128 = `Hexagram × YinBit` (重号 +2) | [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean), `RHierarchy.lean` R₇ | 同 #3 |
|  6 | 旧 R₆ = Cell192 (192) | 新 R₈ = Cell256 = `Hexagram × Shi` (重号 +2; 同时 192 → 256) | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) | 同 #1, #3 |
|  7 | **「Mian = Ben × Zheng = 16」是最大不可分单位**（旧 BenZheng 文档语境） | **Mian = R₄**（Z/2)⁴）是 R-hierarchy 之**第 4 层**；之上还有 R₅..R₈，最大是 **R₈ = 256** | [`../10_formal_形式/yi-RO-hierarchy.md § 3.4`](../10_formal_形式/yi-RO-hierarchy.md), [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean), `RHierarchy.lean` R₄ | 旧 BenZheng 论稿（仍主要在 `义理/`） |
|  8 | **「192 格全表」**（表六旧版） | **「256 格全表」**（表六新版，由并行 agent 在 `六表_实虚史真/表六_256格全表.md` 产出） | `六表_实虚史真/表六_256格全表.md`（forthcoming）, `Cell256.lean` `xuGua256` | [`史/义理-pre-v3/表六_192格全表_旧Z3版.md`](../../史/义理-pre-v3/表六_192格全表_旧Z3版.md) |
|  9 | `Cell192.Shi` (Z/3 cyclic ctor `dao / cur / fin`) | `Cell256.Shi` (V₄ ctor `dao / ji / jin / wei`) | `Cell256.lean § 1`, [`v4-shi.md`](../10_formal_形式/v4-shi.md) | `史/docs-next-pre-v3/` |
| 10 | `cur` (中态, Z/3 中点) | `今` = `Shi.jin` = (因=1, 果=1) = V₄ 中心元 = PT | `Cell256.lean`, `v4-shi.md` | 同上 |
| 11 | `fin` (终态, Z/3 终点) | 拆为两支：`已` = `Shi.ji` = (1,0) (过去封闭) + `未` = `Shi.wei` = (0,1) (未来开放) | `Cell256.lean`, `v4-shi.md` | 同上 |
| 12 | `Cell192Stratify.lean` / `cell192_complete` | [`Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) / `R8_complete` bundle | `Cell256Stratify.lean § 7`, `R8_complete : ...` | 旧 `Cell192Stratify.lean`（已删） |
| 13 | `R6_complete` 收口定理 | `R8_complete` 收口定理（重号 +2；Cell256 基数 + R-hierarchy + P/T/Y closure + 群作用 simply-transitive + BenZheng 投影 + 位置-算子树 + xuGua256） | `Cell256Stratify.lean:498` | 旧 `R6_complete`（已迁） |
| 14 | 旧 `chong : R₃ × R₃ → R₄`（"3-bit jump"，跳过 16/32） | `chong : R₃ × R₃ → R₆` 仍是 hexagram-合卦传统语义；**结构上**显式拆为 3 步 +1 bit lift `R₃ → R₄ → R₅ → R₆`（unfolded composite，无 jump） | `yi-RO-hierarchy.md § 3.9`, [`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) | 旧 yi-RO-hierarchy v1 |
| 15 | **印 / 投 仅作 Shi inductive 上的 V₄ 算子**（Cell192 期：印=cuo on Shi, 投=zong on Shi） | **印 / 投 first-class XOR-mask 算子 at Cell256**（R₇/R₈ atomic）：`yin = (· ⊕ yin_mask)` with `yin_mask = (qian, ji)`；`tou = (· ⊕ tou_mask)` with `tou_mask = (qian, wei)` | [`../10_formal_形式/yin-tou-operators.md`](../10_formal_形式/yin-tou-operators.md), `Cell256.lean § 8`, [`Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) | 旧 Shi-only 印/投（旧 Cell192.lean） |
| 16 | 旧「Shi 的 Z/3 cyclic 是史维三态本体」 | Shi V₄ = (因, 果) Bool² emergence；**Z/3 cyclic 不是必要**，而是 v2 期之结构错误 | `Cell256.lean § 1` 注解；`yi-RO-hierarchy.md` 附录 A | `史/docs-next-pre-v3/` README 解释 |
| 17 | 旧「道」字仅作哲学 anchor，无形式地位 | 道 = `Shi.dao` = (因=0, 果=0) = V₄ identity = R₈ origin = identity = no-op = 永真 cell；**形式 first-class** | `Cell256.lean § 1`, [`OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) `OX["oooooooo"]` | — |
| 18 | 旧无 R₀ 显式（Unit 隐含） | **R₀ = 太极 = Unit** 显式纳入 R-hierarchy，作 absolute zero-anchor | `yi-RO-hierarchy.md § 3.0`, `RHierarchy.lean R₀_Taiji` | — |
| 19 | 旧无 R₅ (五爻) 层（被 chong jump 跳过） | **R₅ = 五爻 (provisional)** = `Mian × Bool` = 32；descriptive baseline，无传统 Yi anchor | `yi-RO-hierarchy.md § 3.5`, [`R5_Wuyao.lean`](../../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean) | — |
| 20 | 旧 `WenyanSelfInterp.lean` 之 base-192 dispatch | base-256 dispatch；Phase F.1 已迁 atomic encoding 到 `Cell256.Shi`；**dispatch program 之具体 12-tag re-derivation 仍 pending**（cite commit `7de5064`） | [`WenyanSelfInterp.lean`](../../formal/SSBX/Foundation/Wen/WenyanSelfInterp.lean) head comment | 旧 base-192 dispatch（已删）|
| 21 | 旧 `OperatorAnchors.lean` 用 Cell192 编码 | 已迁 Cell256；编码层不变，cell-anchor 重 map 到 256 网格（cite commits `7de5064`, `0003224`, `8e4406e`） | [`OperatorAnchors.lean`](../../formal/SSBX/Text/OperatorAnchors.lean), [`OperatorCellMap.lean`](../../formal/SSBX/Text/OperatorCellMap.lean) | — |
| 22 | 旧 `Cell192 → Cell192` 算子（`OperatorInstructionSemantics`） | `Cell256 → Cell256`；语义保持，载体 V₄-extended | `OperatorInstructionSemantics.lean`（已迁） | — |

## 旧文（旧 docs-next + 旧 义理）→ v3 入口

> 这是**整篇文件**层之指针（不是术语层），保留以利反向跳转。

| 旧文范围 | 新版入口 | 备注 |
|---|---|---|
| `义理/A`–`G`（核心框架） | `../20_theory_义理/core-framework.md` | 算子骨架与生成原则；术语层用本页 #1–#22 迁移 |
| `义理/H`–`M`（形式与证明） | `../20_theory_义理/formal-and-proof.md` | 旧「证明报告」请同时对接 #12, #13, #20 |
| `义理/N, P, Q, S, E`（传统映射） | `../20_theory_义理/traditions.md` | 多数传统映射在 v3 下结构稳定 |
| `义理/O, R, U–Z`（对齐 / 政治 / 经济） | `../20_theory_义理/modern-and-alignment.md` | 形式接口少，受 v3 影响有限 |
| 八衍专题文（数 / 推 / 测 / 形 / 类 / 动 / 识 / 象） | `../20_theory_义理/extensions.md` | 涉及形式骨架之处用本表迁移 |
| `义理/算子别名总表.md` | `../40_reference_参考/operators.md` | 与 `_generated/operator-index.md` 对照 |
| `史料/生生不息论_三本文完整版/` | `../40_reference_参考/historical-sources.md` | frozen snapshot，不重写 |
| `史料/真理/daoli-v12-*.md` | `../40_reference_参考/historical-sources.md` | 早期 truth framework |
| `史料/v14_形式证明骨架版.md` | `../50_maintenance/archive-policy.md` | 归档 |
| 旧 `docs-next/10_formal_形式/cell192-grid.md` | [`../10_formal_形式/cell256-grid.md`](../10_formal_形式/cell256-grid.md)（forthcoming sibling） | 整篇换新；归档于 `史/docs-next-pre-v3/cell192-grid_Z3-Shi_旧版.md` |
| 旧 `docs-next/10_formal_形式/yi-RO-hierarchy.md` v1 | 同名（v2.1 strict uniform，已替换） | 归档于 `史/docs-next-pre-v3/yi-RO-hierarchy_v1_旧R1-R6编号.md` |
| 旧 `docs-next/六表_实虚史真/表六_192格全表.md` | `六表_实虚史真/表六_256格全表.md`（forthcoming） | 归档于 `史/义理-pre-v3/表六_192格全表_旧Z3版.md` |

## 迁移时的降级规则（与 v3 之 claim 强度对接）

| 旧文表述 | v3 处理 |
|---|---|
| 「证明」/「已证」 | 查对应 Lean 模块（多数已 `Cell256` 化）；写「Lean 已检查」仅当 theorem 存在 |
| 「Z/3 cyclic 是史维三态」 | 写「v2 期采用 Z/3，已被 v3 V₄ Klein 取代为结构层正确编码」 |
| 「192 格全表」 | 写「256 格全表（v3）」；旧 192 表归 `史/义理-pre-v3/` |
| 「Mian 是最大」 | 写「Mian = R₄ = (Z/2)⁴；R-hierarchy 之上仍有 R₅..R₈」 |
| 「印 / 投 是 Shi V₃ 内三相算子」 | 写「印 / 投 = Cell256 之 XOR-mask atomic 算子（mask 见 `Cell256.lean § 8`）」 |
| 「R₆ 是顶层」 | 写「R₈ = Cell256 是 (Z/2)ⁿ self-describing 之自然闭合（无第 9 个独立 binary axis）」 |

## 不迁移内容

- 旧文之修辞段落不搬入 v3。
- `史料/` 之合订稿不做现代化改写；只引用。
- 未落地的经验接口（pending interface）不写成 Lean 事实。
- 自动生成索引（`_generated/`）之内容不复制到人工页。
- 旧 Cell192 时期之**模型直觉**（如 64 卦 × 3 状态、史维三态等）允许在解释层引用，但形式层一律以 Cell256 + V₄ Shi 为准。

## 参见

- 完整概念辞典：[`../40_reference_参考/glossary.md`](../40_reference_参考/glossary.md)
- 详细迁移操作指引（含代码 diff 样例）：[`cell192-to-cell256-migration.md`](cell192-to-cell256-migration.md)
- claim 状态读法：[`claim-status.md`](claim-status.md)
- v3 doctrine 主干：[`../10_formal_形式/yi-RO-hierarchy.md`](../10_formal_形式/yi-RO-hierarchy.md)

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
