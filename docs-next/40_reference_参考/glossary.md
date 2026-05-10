> 状态：v3 (2026-05-11) — 术语小表。已扩展 v3 术语：道、印、投、因、果、V₄ Klein、Cayley、印/投 mask、OXNotation、Cell128 / Cell256 / Cell256Stratify、R₀..R₈ 各层、Atomic / V4Outer 算子分类、`R8_complete` 等。

# 术语小表

本表给 docs-next 常用词的最低读法。它不是哲学定义全集；精确定义以 Lean、claim ledger、旧文来源和生成索引为准。每条短释 ≤ 3 句 + 一个 code/doc 锚。

## 项目总名 / 元术语

| 术语 | 读法 | 锚 |
|---|---|---|
| 生生不息 | 项目总名；在形式层需查具体 theorem 或 claim | 全 repo |
| 一 | 根源或单根口径；形式层涉及 `theOne` 时保留 opaque 边界 | `Foundation/Core/MonadRoot.lean` |
| 元 | 生成与基础结构的读法，依上下文区分；在 R-O 层级中 = state / cell（与算子相对） | [`yi-RO-hierarchy.md`](../10_formal_形式/yi-RO-hierarchy.md) |
| 开 | 开放、展开或价值方向；claim 状态需查 ledger | — |
| 闭 | 闭合、保护或限制；不可直接等同负面价值 | — |
| 正 | 在给定判准下的正向状态或行为 | — |
| 邪 | 在给定判准下的偏离或破坏状态 | — |
| 善、仁、义、道 | 价值词，多由定义或 ledger 承接；不要默认 machineChecked。**注**：此处「道」为价值层「道」；与下文形式层「道 = R₈ origin」字同义不同 | — |

## v3 形式核心 — 道、太极与 R₀..R₈

| 术语 | 读法 | 锚 |
|---|---|---|
| **道**（形式义） | R₈ origin = V₄ identity = no-op operator = 永真 cell；`Shi.dao = (因=0, 果=0)`，`OX["oooooooo"]` = `(qian, dao)` = `Cell256.origin`。一字承担 origin / identity / no-op / 永真 / fusion anchor 五重身份 | [`Cell256.lean § 1, § 7`](../../formal/SSBX/Foundation/Bagua/Cell256.lean), [`OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) |
| **太极** | R₀ = `Unit` = (Z/2)⁰ = 1；absolute zero-anchor，「无分」之 ground，所有 binary distinction 之前 | `Unit` (Lean stdlib), `R0_Taiji.lean` |
| **R₀** | 太极 = 1 元（Unit） | `Foundation/Hierarchy/R0_Taiji.lean` |
| **R₁** | 爻 / 两仪 = 2 元 = `Yao` | `Foundation/Yi/Yi.lean` |
| **R₂** | 四象 = 4 元 = `SiXiang` | `Foundation/Bagua/BaguaAlgebra.lean` |
| **R₃** | 八卦 = 8 元 = `Trigram` | `Foundation/Yi/Yi.lean` |
| **R₄ / Mian** | 命 / 面 = 16 元 = `Ben × Zheng` = (Z/2)⁴；4 本 × 4 征之矩阵 | `Foundation/Bagua/BenZheng.lean` |
| **R₅ / Wuyao** | 五爻 (provisional 命名，无传统 Yi anchor) = 32 元 = `Mian × Bool` = (Z/2)⁵；descriptive baseline | `Foundation/Hierarchy/R5_Wuyao.lean` |
| **R₆** | 六十四卦 (Hexagram) = 64 元 = (Z/2)⁶；含 BenZheng quadrant 划分（本本 / 本征 / 征本 / 征征） | `Foundation/Yi/Yi.lean` |
| **R₇ / 因卦** | Cell128 = `Hexagram × YinBit` = 128 元 = (Z/2)⁷；引入 R₇ atomic 算子 印 | `Foundation/Bagua/Cell128.lean` |
| **R₈ / 果卦** | Cell256 = `Hexagram × Shi` = 256 元 = (Z/2)⁸；引入 R₈ atomic 算子 投；R-hierarchy 自然闭合 | `Foundation/Bagua/Cell256.lean` |

## v3 形式核心 — Shi V₄ Klein 群

| 术语 | 读法 | 锚 |
|---|---|---|
| **V₄ Klein**（四元群） | 阶 4 abelian 群，每元 involution（`x² = id`），非循环（**不是 Z/4**）；`{e, a, b, ab}`；中心元 = ab | 数学常识；`Shi` 之即视化在 `Cell256.lean § 1` |
| **Shi**（v3 时态） | V₄ 四态 inductive `dao / ji / jin / wei`；`dao = V₄ identity`，`ji = (1,0)`（已），`wei = (0,1)`（未），`jin = (1,1)`（今 = PT 中心元） | `Cell256.lean § 1` |
| **道**（V₄ 元） | `Shi.dao` = `(因=0, 果=0)` = V₄ identity element；R₈ origin | 同上 |
| **已** | `Shi.ji` = `(因=1, 果=0)` = parity-like (P) — 过去封闭，无未来 | 同上 |
| **未** | `Shi.wei` = `(因=0, 果=1)` = time-reversal-like (T) — 未来开放，无过去 | 同上 |
| **今** | `Shi.jin` = `(因=1, 果=1)` = PT (V₄ central element) — 过去与未来交汇 = 现在 | 同上 |
| **因 / YinBit**（state attribute） | R₇ binary axis，past-trace bit；`YinBit : Bool`；false = 无因，true = 有因；现象学 ≈ Husserl retention 之 binary 标记 | `Cell128.lean § 1` |
| **果 / GuoBit**（state attribute） | R₈ binary axis，future-projection bit；`GuoBit : Bool`；false = 无果，true = 有果 | `Cell256.lean § 1` |

## v3 形式核心 — 算子（atomic vs V₄ outer）

| 术语 | 读法 | 锚 |
|---|---|---|
| **印 (yìn)**（v3 atomic 算子） | R₇/R₈ atomic XOR-mask 算子 = toggle YinBit (因 axis)；at Cell256：`yin c = c ⊕ yin_mask`，`yin_mask = (qian, ji) = OX["ooooooxo"]`；involution；与 `tou` 交换 | `Cell256.lean § 8`, `Cell128.lean § 7` |
| **投 (tóu)**（v3 atomic 算子） | R₈ atomic XOR-mask 算子 = toggle GuoBit (果 axis)；at Cell256：`tou c = c ⊕ tou_mask`，`tou_mask = (qian, wei) = OX["ooooooox"]`；involution；与 `yin` 交换；`yin ∘ tou = (· ⊕ (qian, jin))` = V₄ central element | `Cell256.lean § 8` |
| **印 / 投 mask** | 两 mask 之 XOR = `(qian, jin)` = V₄ 中心元；`yin_mask ⊕ tou_mask = (qian, jin)` | `Cell256.lean § 8.5` `yin_mask_xor_tou_mask` |
| **Atomic（算子分类）** | XOR-with-fixed-mask 之算子集合；abelian subgroup；each involution；XOR is commutative | [`Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) |
| **V4Outer（算子分类）** | non-XOR permutation 之算子集合；`{id, cuo, zong, cuoZong}` ≅ V₄ Klein；含 sibling `hu`（**非** V₄ 元，有 `{乾, 坤}` 不动点） | [`Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) |
| **cuo (错)** | XOR with all-yin mask；R₃ 上 = `(· ⊕ xxx)`，R₆ 上 = `(· ⊕ xxxxxx)`；物理 P (parity) | `BaguaAlgebra.lean`, `Operators/V4Outer.lean § 1` |
| **zong (综)** | yao 序反转 permutation；非 XOR；involution；物理 T (time-reversal) | `Yi.lean` `Hexagram.zong`, `Operators/V4Outer.lean § 1` |
| **cuoZong (错综)** | `cuo ∘ zong`；involution；物理 PT；V₄ 内之 PT 元 | `Operators/V4Outer.lean § 1` |
| **hu (互)** | 取中四爻 permutation；非 XOR；非 involution；fixed points = `{乾, 坤}`；2-cycle = `{既济, 未济}`；物理 Y / Y-combinator (self-reference) | `Yi.lean` `Hexagram.hu`, `Operators/V4Outer.lean § 6` |

## v3 形式核心 — Cayley fusion 与 Lift/Project

| 术语 | 读法 | 锚 |
|---|---|---|
| **Cayley regular representation** | 群在自身上的左作用 ι : G → Aut(G), c ↦ (· ⊕ c)；对 (Z/2)ⁿ abelian 群恰好与 XOR-with-mask subgroup 同构；R-O 二元之代数实现 | `Cell256.lean § 7.6` `cayley`, `cayley_inj`, `cayley_hom` |
| **ε（origin-evaluation）** | ε : (G → G) → G, f ↦ f(origin)；与 Cayley ι 互逆，retract `ε ∘ ι = id` | `Cell256.lean § 7.6` `epsAtOrigin`, `epsAtOrigin_cayley` |
| **fusion** | 元 ≅ 算子 之严格同构（在选定 origin 后）；abelian 群 + Cayley + origin 三者合 = self-description 之代数本质 | `yi-RO-hierarchy.md § 5` |
| **Lift_n** | R_n → Bool → R_{n+1}（n=0..7）；古文「分」 | `Foundation/Hierarchy/LiftProject.lean` |
| **Project_n** | R_{n+1} → R_n；古文「合」；为 Lift 之右逆 | 同上 |
| **proj_lift_id_R{n}**（n=0..7） | 8 件 retract 引理 `projR_{n+1}toR_n (liftR_ntoR_{n+1} r b) = r`；表 R_n ↪ R_{n+1} 是 faithful embedding | `LiftProject.lean § 9` `liftProject_summary` |

## v3 形式核心 — 编码与表示

| 术语 | 读法 | 锚 |
|---|---|---|
| **OXNotation** | term-level 字面量 macro `OX["o/x×8"]`；8-char `o`/`x` 字符串解码为 `Cell256 = Hexagram × Shi`；`o` = `Yao.yang` (identity bit)，`x` = `Yao.yin`；位 7 = YinBit，位 8 = GuoBit；parse-time 验证长度与字符集 | [`Foundation/Notation/OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) |
| **Cell128** | R₇ carrier = `Hexagram × YinBit`，128 元 = (Z/2)⁷；`AddCommGroup`-flavor instance 已绑（`+ / 0 / -`） | `Foundation/Bagua/Cell128.lean` |
| **Cell256** | R₈ carrier = `Hexagram × Shi`，256 元 = (Z/2)⁸；`AddCommGroup` + `SMul` self-action（Cayley）已绑 | `Foundation/Bagua/Cell256.lean` |
| **Cell256Stratify** | R7/R8 双层收口模块；含 R₀..R₈ 别名 + P/T/Y 算子 anchoring + 位置-算子树双射 + xuGua256 + `R8_complete` 收口定理 | `Foundation/Bagua/Cell256Stratify.lean` |
| **R8_complete bundle** | R₈ 收口主定理（基数 256 + R-hierarchy + P/T/Y closure + (Z/2)⁸ 群作用 simply-transitive + BenZheng 投影 + 位置-算子树双射 + xuGua256 length + Nodup）；axiom 依赖只 propext + native_decide | `Cell256Stratify.lean § 7` `R8_complete:498` |
| **xuGua256** | 序卦 256-cell 扩展（64 卦 × 4 时态）；`Shi` 顺序为 `dao→ji→jin→wei` 之 V₄ 序，`wei` 后跳到下卦 `dao` | `Cell256Stratify.lean § 6` |
| **xuGua** | 序卦传 64 卦序（King Wen order） | `Cell256.lean § 4` |

## 旧术语 / 已被取代

| 术语 | 读法 | 锚 |
|---|---|---|
| **Cell192** | v2 期 R₆ carrier (192 = 64 × 3 with Z/3 Shi)；**v3 已被 Cell256 取代**；旧 Lean 文件已删；旧文 `史/docs-next-pre-v3/`、`史/义理-pre-v3/` | [`old-to-new.md`](../30_crosswalk_互证/old-to-new.md), `史/README.md` |
| **Z/3 Shi**（旧） | v2 期 cyclic three-state 时态；**v3 已被 V₄ Klein 取代**；ctor 旧名 `dao / cur / fin` → 新 `dao / ji / jin / wei` | 同上 |
| **R₁..R₆**（旧编号） | v1 R-hierarchy 编号（含 R₃→R₄ chong jump）；**v3 已重号为 R₀..R₈ strict (Z/2)ⁿ uniform** | [`yi-RO-hierarchy.md`](../10_formal_形式/yi-RO-hierarchy.md) 附录 A |

## 项目骨架 / 名册

| 术语 | 读法 | 锚 |
|---|---|---|
| 六征 | 项目分类骨架；入口见 [`six-tables.md`](six-tables.md) | `六表_实虚史真/` |
| 实虚史真 | modal、历史维度与认识状态的三轴读法 | 表三 / 表四 / 表二 |
| 算子 | 受控文字或结构操作的登记项；入口见 [`operators.md`](operators.md) | `Foundation/Hierarchy/Operators/`, `Text/WenyanOperators.lean` |
| 字元 | glyph/atom/roster 相关登记项；入口见 [`glyphs-registry.md`](glyphs-registry.md) | `Roster.lean`, `Text/Glyph.lean` |
| 字文 | 受控文本到形式结构的桥；入口见 [`ziwen-language.md`](ziwen-language.md) | `Foundation/Wen/`, `ziwen-spec.md` |
| BenZheng | R₄ Mian 之具体落地：4 本（物 / 动 / 间 / 事）× 4 征（几 / 势 / 机 / 时）= 16 命 | `Foundation/Bagua/BenZheng.lean` |
| Quadrant | R₆ 之 BenZheng 划分：本本 / 本征 / 征本 / 征征 各 16 卦 | `BenZheng.lean`, `Cell256Stratify.lean § 3` |

## Claim / Ledger / 信任边界

| 术语 | 读法 | 锚 |
|---|---|---|
| claim | 可审计主张；状态见 [`claim-status.md`](../30_crosswalk_互证/claim-status.md) | `Truth/ClaimLedger.lean` |
| ledger | claim 与来源的账本，不等于 theorem | 同上 |
| theorem | Lean 已检查命题 | 全 repo |
| modelComputed | 模型或案例计算结果 | `_generated/claim-index.md` |
| pending interface | 待落地接口，不是已证明事实 | `_generated/registry-index.md` |
| trust boundary | 形式层必须明示的 axiom、opaque 或 partial 边界 | `_generated/trust-boundary.md` |
| DAG | 图式审计工具，不替代 theorem | `_generated/diagram-index.md` |
| frozen | 史料归档状态；不在新版中重写 | [`historical-sources.md`](historical-sources.md) |

## 使用规则

- 遇到术语歧义，先查 `../_generated/`。
- 涉及旧文来源，查 [`historical-sources.md`](historical-sources.md)。
- 涉及证明强度，查 [`../30_crosswalk_互证/claim-status.md`](../30_crosswalk_互证/claim-status.md)。
- 涉及 v2 → v3 之结构迁移，查 [`../30_crosswalk_互证/old-to-new.md`](../30_crosswalk_互证/old-to-new.md) 与 [`../30_crosswalk_互证/cell192-to-cell256-migration.md`](../30_crosswalk_互证/cell192-to-cell256-migration.md)。
- 本页只做短释，不扩写成论证。

## 形式锚

- [`formal/SSBX/Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean)
- [`formal/SSBX/Foundation/Bagua/Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean)
- [`formal/SSBX/Foundation/Bagua/Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean)
- [`formal/SSBX/Foundation/Hierarchy/RHierarchy.lean`](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean)
- [`formal/SSBX/Foundation/Hierarchy/LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean)
- [`formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean)
- [`formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean)
- [`formal/SSBX/Foundation/Notation/OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean)
- [`formal/SSBX/Foundation/Bagua/BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean)
- [`docs-next/10_formal_形式/yi-RO-hierarchy.md`](../10_formal_形式/yi-RO-hierarchy.md)
