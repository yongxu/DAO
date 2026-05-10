# 术语小表 · Glossary

> 状态：v3 定本 (2026-05-11)
> 父链：[`docs-next/40_reference_参考/`](./) · 上层导航见 [`docs-next/`](../)
> 配套：[`yi-RO-hierarchy.md`](../10_formal_形式/yi-RO-hierarchy.md) (R₀..R₈ definitive) · [`yi-calculus-theorem.md`](../10_formal_形式/yi-calculus-theorem.md) (Theorems A–K + §16 命名)

本表给 docs-next 常用词的最低读法 (minimal readings, bilingual where bilingual is project style). 它不是哲学定义全集；精确定义以 Lean、claim ledger、旧文来源和生成索引为准。R-hierarchy / Cell256 / V₄ Shi 项以 2026-05-11 定本为准 (Cell192 与 Z/3 Shi 已废，仅作历史更正出现)。

---

## A. R-hierarchy 与 cell carriers · R-layers and cell carriers

| 术语 | 读法 | Lean / canonical |
|---|---|---|
| **R₀ Taiji** | 太极 = `Unit` = trivial group `{*}` = 1 元 origin singleton; "无极而太极" 之 algebraic zero-anchor; 在所有 binary distinction 之前. | [`R0_Taiji.lean`](../../formal/SSBX/Foundation/Hierarchy/R0_Taiji.lean) · [yi-RO § 3.0](../10_formal_形式/yi-RO-hierarchy.md) |
| **R₁ Yao** | 爻 / 两仪 = `Bool` = ℤ/2; 阴阳二值 (`o` 阳 / `x` 阴); minimal binary atom. | [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) `Yao` · [`R1_Yao.lean`](../../formal/SSBX/Foundation/Hierarchy/R1_Yao.lean) |
| **R₂ SiXiang** | 四象 = Yao² = (ℤ/2)² ≅ V₄; 太阳/少阴/少阳/太阴. | [`BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) · [`R2_SiXiang.lean`](../../formal/SSBX/Foundation/Hierarchy/R2_SiXiang.lean) |
| **R₃ Trigram** | 八卦 = Yao³ = (ℤ/2)³ = 8 卦; zong 强制 4 本 + 4 征 partition. | [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) `Trigram` · [`R3_Trigram.lean`](../../formal/SSBX/Foundation/Hierarchy/R3_Trigram.lean) |
| **R₄ Mian (面)** | 面 = Ben × Zheng = (ℤ/2)² × (ℤ/2)² = (ℤ/2)⁴ = 16 命; first-class layer (was hidden in v1's R₃→R₆ chong jump). | [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) `Mian` · [`R4_Mian.lean`](../../formal/SSBX/Foundation/Hierarchy/R4_Mian.lean) |
| **R₅ Wuyao (五爻)** *(provisional, §16)* | 五爻 = Mian × Bool = (ℤ/2)⁵ = 32; the unique R-layer with no traditional Yi anchor — "(ℤ/2)ⁿ 机械补全" 之产物. Naming candidates: 五爻 / 接 / 临 / 渐 / 进. | [`R5_Wuyao.lean`](../../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean) |
| **R₆ Hexagram** | 六十四卦 = 重卦 = Yao⁶ = (ℤ/2)⁶ = 64; quadrant 本本/本征/征本/征征 各 16 (Theorem F). | [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) `Hexagram` · [`R6_Hexagram.lean`](../../formal/SSBX/Foundation/Hierarchy/R6_Hexagram.lean) |
| **R₇ Cell128 / YinHex** | 因卦 = Hexagram × YinBit = (ℤ/2)⁷ = 128 cells; introduces 因 (yīn, past-trace bit) as 7th binary axis. | [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) · [`R7_YinHex.lean`](../../formal/SSBX/Foundation/Hierarchy/R7_YinHex.lean) |
| **R₈ Cell256 / GuoHex** | 果卦 = Hexagram × Shi = Cell128 × GuoBit = (ℤ/2)⁸ = 256 cells; introduces 果 (guǒ, future-projection bit) as 8th binary axis; closure layer (no R₉ in self-describing kernel). | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) · [`R8_GuoHex.lean`](../../formal/SSBX/Foundation/Hierarchy/R8_GuoHex.lean) |
| **(ℤ/2)ⁿ strict uniform** | Each Rₙ = (ℤ/2)ⁿ exactly; every layer adds **exactly 1** binary bit (no jumps, no gaps). 与 v1 之 "R₃→R₄ 3-bit chong jump" 对照. | [yi-RO § 公理 2](../10_formal_形式/yi-RO-hierarchy.md) |

---

## B. Shi V₄ — Klein four-group · 时态 V₄

| 术语 | 读法 | Lean / canonical |
|---|---|---|
| **Shi V₄** | 时态 = Klein four-group V₄ = (ℤ/2)² = {道, 已, 今, 未}; **NOT** Z/3 cyclic. (因, 果) ∈ Bool² 双射. Emerges at R₈ as a tensor of R₇ 因 axis + R₈ 果 axis (per Theorem J). | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) `Shi` · [yi-calculus § 12 Theorem J](../10_formal_形式/yi-calculus-theorem.md) |
| **道 (dào)** | V₄ identity = (因=0, 果=0) = origin = no-op = (qian, dao) cell = "永真" anchor; **一字承担五重身份** (origin + identity + no-op + 永真 + V₄ unit). | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) `Shi.dao` / `Cell256.origin` |
| **已 (jǐ)** | V₄ element σ_P = (因=1, 果=0); "有因无果" — 过去封闭, parity-like. | `Shi.ji` |
| **未 (wèi)** | V₄ element σ_T = (因=0, 果=1); "无因有果" — 未来开放, time-reversal-like. | `Shi.wei` |
| **今 (jīn)** | V₄ central element σ_PT = (因=1, 果=1); "因果俱在" — present, PT 复合点. | `Shi.jin` |
| **因 (yīn)** *(provisional, §16)* | R₇ state-bit = YinBit = past-trace bit; 0 = 无因, 1 = 有因. Naming candidates: 因/印/始/持 (per yi-calculus §16). | [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) `YinBit` |
| **果 (guǒ)** *(provisional, §16)* | R₈ state-bit = GuoBit = future-projection bit; 0 = 无果, 1 = 有果. Naming candidates: 果/投/终/期. | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) `GuoBit` |

---

## C. Atomic operators · 原子算子

| 术语 | 读法 | XOR mask / type | Lean |
|---|---|---|---|
| **印 (yìn)** | R₇ atomic operator = toggle 因 bit = XOR with `(qian, ji)` mask. Involution. *(provisional, §16)* | `Cell256 → Cell256`; mask `OX["oooooooi"]` | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) `Cell256.yin` · [`Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) `cell256_yin` |
| **投 (tóu)** | R₈ atomic operator = toggle 果 bit = XOR with `(qian, wei)` mask. Involution; commutes with 印. *(provisional, §16)* | `Cell256 → Cell256`; mask `OX["ooooooon"]` | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) `Cell256.tou` · [`Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) `cell256_tou` |
| **flip1..flip6** | Six atomic single-yao XOR toggles (yao 1..6); generators of Hexagram (ℤ/2)⁶ XOR subgroup. | `Cell256 → Cell256` | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) `flip1`..`flip6` |
| **反 (fǎn) / neg** | R₁ atomic operator = negate Yao (`o` ↔ `x`). | `Yao → Yao` | [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) `Yao.neg` |

For full operator inventory see [`operators.md`](operators.md).

---

## D. V₄-outer operators · V₄ 外算子 (cuo / zong / hu)

| 术语 | 读法 | Type / impl | Lean |
|---|---|---|---|
| **cuo (错)** | XOR with all-yin mask (yao-wise negation); physics P (parity); V₄ generator. | XOR, Hexagram → Hexagram | [`V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) `hex_cuo` · `Hexagram.cuo` |
| **zong (综)** | Yao-order reversal `(y₁..y₆) ↦ (y₆..y₁)`; **non-XOR permutation**; physics T (time-reversal); V₄ generator. | perm, Hexagram → Hexagram | [`V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) `hex_zong` · `Hexagram.zong` |
| **错综 (cuoZong)** | cuo ∘ zong = PT; V₄ central element. | composite | `hex_cuoZong` |
| **hu (互)** | Inner-trigram extraction `(y₁..y₆) ↦ (y₂, y₃, y₄, y₃, y₄, y₅)`; **non-XOR**; **NOT** a V₄ member (has 乾/坤 fixed points, not invertible); Y-combinator-like sibling. | perm, non-invertible | `hex_hu` · `Hexagram.hu` |
| **shiCuo / shiZong / shiCuoZong** | Shi-side V₄ (acts on the (因,果) block, fixes Hexagram). | Cell256 → Cell256 | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) |
| **hexCuo / hexZong / hexHu** | Hex-side V₄ + hu sibling (acts on Hexagram, fixes Shi). | Cell256 → Cell256 | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) |
| **V₄ Klein four-group** | {id, cuo, zong, cuoZong} on Hexagram; physics {1, P, T, PT}. R₈ has **double V₄** (hex V₄ × Shi V₄). | (ℤ/2)² | [yi-RO § 4.2](../10_formal_形式/yi-RO-hierarchy.md) |

---

## E. Cayley action · Cayley 自作用

| 术语 | 读法 | Lean |
|---|---|---|
| **Cayley action** | Regular representation of (ℤ/2)⁸: `c • s = c ⊕ s`. Bridges 元 ↔ 算子 (any cell doubles as the operator that XORs with itself); same 8-bit object, two usages. | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) `Cell256.cayley`, `SMul Cell256 Cell256` |
| **ι (iota)** | `ι : R₈ → Aut(R₈)`, `ι(c) = (· ⊕ c)`; group homomorphism + injection. | `Cell256.cayley_inj`, `Cell256.cayley_hom` |
| **ε (epsilon)** | `ε : (R₈ → R₈) → R₈`, `ε(f) = f(origin)`; right inverse of ι. | `Cell256.epsAtOrigin`, `Cell256.epsAtOrigin_cayley` |
| **xor / + / SMul** | Cell256 carries Add / Zero / Neg / Sub + SMul instances; `+` = XOR, `0` = 道 = origin, `-c = c` (involution). | `Cell256.xor`, `add_def`, `zero_def`, `neg_def`, `smul_def` |
| **R-O fusion** | "Element ≅ operator" on each Rₙ via Cayley. The minimal algebraic content of "self-description". | [yi-RO § 5](../10_formal_形式/yi-RO-hierarchy.md) |

---

## F. Lift / Project · 升降函子

| 术语 | 读法 | Lean |
|---|---|---|
| **Lift_n** | Uniform R_n → R_{n+1} pair: attach 1 binary bit. 8 pairs total (R₀↔R₁ ... R₇↔R₈). | [`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) `liftRntoRn+1` |
| **Project_n** | Uniform R_{n+1} → R_n pair: drop 1 binary bit (right inverse of Lift). | [`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) `projRn+1toRn` |
| **proj_lift_id** | Retract lemma: `proj ∘ lift = id` for every (Rₙ, R_{n+1}) pair (faithful Rₙ ↪ R_{n+1}). | `proj_lift_id_R0`..`proj_lift_id_R7` · `liftProject_summary` |
| **chong (重)** | 3-step composite R₃ → R₄ → R₅ → R₆ (was treated as a "+3 bit jump" in v1; now an explicit chain of three Lift steps). | [yi-RO § 3.9 + § 4.4 模式 C](../10_formal_形式/yi-RO-hierarchy.md) |

---

## G. OX 字面量 · OX literal notation

| 术语 | 读法 | Lean |
|---|---|---|
| **OX[...] notation** | 8-char string macro `OX["xxxxxxxx"]` → Cell256 literal. `o` = yang/false, `x` = yin/true; positions 1..6 = hexagram yaos (LTR, 初爻 在左), positions 7/8 encode YinBit/GuoBit → Shi. | [`OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) |
| **道 cell** | `OX["oooooooo"]` = (qian, dao) = origin = identity = no-op = 永真 anchor. | `Cell256.origin` |
| **印 mask / 投 mask** | `OX["oooooooi"]` (印, only YinBit) / `OX["ooooooon"]` (投, only GuoBit). XOR them ⇒ V₄ central element `(qian, jin)`. | `Cell256.yin_mask` / `Cell256.tou_mask` |

(Reading: `i` and `n` here are the doc-style positional bit names for the YinBit/GuoBit columns; the macro accepts standard `o` / `x` characters — see `OXNotation.lean` for the canonical alphabet.)

---

## H. Project lexicon · 项目内常用术语

| 术语 | 读法 |
|---|---|
| 生生不息 | 项目总名；在形式层需查具体 theorem 或 claim |
| 一 | 根源或单根口径；形式层涉及 `theOne` 时保留 opaque 边界 |
| 元 | 生成与基础结构的读法，依上下文区分；R-O fusion 视角下 元 ≅ 算子 |
| 算子 | 受控文字或结构操作的登记项；入口见 [`operators.md`](operators.md) |
| 字元 | glyph/atom/roster 相关登记项；入口见 `glyphs-registry.md` |
| 字文 | 受控文本到形式结构的桥；入口见 `ziwen-language.md` |
| 六征 | 项目分类骨架；入口见 [`six-tables.md`](six-tables.md) |
| 实虚史真 | modal、历史、真假认识三轴的读法；六表之轴 |
| 开 / 闭 | 开放/闭合；价值方向；claim 状态需查 ledger |
| 正 / 邪 | 在给定判准下的正向/偏离状态 |
| 善、仁、义、道 | 价值词，当前多由定义或 ledger 承接；不要默认 machineChecked。注意 "道" 在 R₈ 中已是 V₄ identity (本表 §B). |
| claim | 可审计主张；状态见 `claim-status.md` |
| ledger | claim 与来源的账本，不等于 theorem |
| theorem | Lean 已检查命题 |
| modelComputed | 模型或案例计算结果 |
| pending interface | 待落地接口，不是已证明事实 |
| trust boundary | 形式层必须明示的 axiom、opaque 或 partial 边界 |
| DAG | 图式审计工具，不替代 theorem |
| frozen | 史料归档状态；不在新版中重写 |

---

## I. 历史更正 · Historical corrections (deprecated terms)

These terms appear in older docs; current canonical doctrine has superseded them.

| 旧术语 (deprecated) | 现读法 |
|---|---|
| **Cell192** | **DEPRECATED.** 旧 R-hierarchy 把 Shi 编为 Z/3 cyclic {已, 今, 未} (192 = 64 × 3), 丧失 V₄ 单位元 + 道 anchor; 是 R₈ 的 partial image (去掉 (因,果)=(0,0) 之 64 道-cells). 取而代之: **Cell256 = 64 × 4 V₄ Klein** (本表 §A/§B). 出现 Cell192 处仅作历史更正使用. |
| **Z/3 Shi (cyclic)** | **DEPRECATED.** Shi 不是 Z/3 cyclic; 正确是 V₄ Klein four-group. 详 [yi-calculus § 11 Theorem I.3 + § 12 Theorem J](../10_formal_形式/yi-calculus-theorem.md). |
| **R₁..R₆ as top** (旧 R-编号) | **DEPRECATED.** v1 之 R₁..R₆ 编号含 R₃→R₄ 3-bit chong jump, 跳过 (ℤ/2)⁴ 与 (ℤ/2)⁵; v3 strict-uniform 把 v1 之 R₄/R₅/R₆ 重号为 R₆/R₇/R₈, 并显式补 R₀ (Unit) + R₄ (Mian) + R₅ (Wuyao). 详 [yi-RO § v1→v2.1 mapping](../10_formal_形式/yi-RO-hierarchy.md). |
| **256-Cell as R₇** (旧编号) | 旧文偶把 Cell256 称为 R₇ (因 / Shi 整体当作 R₇ 单层 atom). v3 拆为 R₇ (因) + R₈ (果) 双层 (Theorem J)，Shi V₄ 是 R₇⊗R₈ emergence 不是 R₇ 单层 atom. |

---

## 使用规则

- 遇到术语歧义，先查 `../_generated/`。
- 涉及旧文来源，查 `historical-sources.md`。
- 涉及证明强度，查 `../30_crosswalk_互证/claim-status.md`。
- 本页只做短释，不扩写成论证。
- 涉及 R-hierarchy / Cell256 / Shi V₄ 必先看 [yi-RO-hierarchy.md](../10_formal_形式/yi-RO-hierarchy.md) + [yi-calculus-theorem.md](../10_formal_形式/yi-calculus-theorem.md), 二者为定本.
- 标 *(provisional, §16)* 的命名暂行, 详见 [yi-calculus-theorem.md §16](../10_formal_形式/yi-calculus-theorem.md) 命名附录.
