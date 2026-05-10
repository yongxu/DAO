> 状态：v3 (2026-05-11) — 算子参考。已加入 v3 first-class 算子 印 / 投，V₄ Shi 之 cuo / zong / cuoZong，Cell128 / Cell256 lifted hexZong / hexHu，并明确 Atomic（XOR 子群）vs V4Outer（Klein-four permutation 群）二分。

# 算子参考

本页是 **R-hierarchy R₀..R₈ 上 Lean-grounded 算子 + 文字层 catalogue 的人读入口**。机器事实以 `../_generated/operator-index.md` 和 Lean 源为准；本页不维护总数、分组数量或完整 catalogue 表格，但完整覆盖 R-hierarchy 上每层之原子 / V₄-外 / Cayley / 复合算子。

配套：[`yi-RO-hierarchy.md`](../10_formal_形式/yi-RO-hierarchy.md) (R₀..R₈ definitive) · [`yi-calculus-theorem.md`](../10_formal_形式/yi-calculus-theorem.md) (Theorems A–K + §16 命名附录) · [`glossary.md`](glossary.md)

## 主要来源

| 来源 | 用途 |
|---|---|
| `../_generated/operator-index.md` | 当前算子索引、分组和 code/id |
| `wenyan-operators.md` | 人工长表与文字说明 |
| [`formal/SSBX/Text/WenyanOperators.lean`](../../formal/SSBX/Text/WenyanOperators.lean) | 算子数据源 |
| [`formal/SSBX/Text/OperatorReadings.lean`](../../formal/SSBX/Text/OperatorReadings.lean) | 读法登记 |
| [`formal/SSBX/Text/OperatorSignatures.lean`](../../formal/SSBX/Text/OperatorSignatures.lean) | 签名和形态 |
| [`formal/SSBX/Text/OperatorCellMap.lean`](../../formal/SSBX/Text/OperatorCellMap.lean) | 单元映射（已迁 Cell256 anchor） |
| [`formal/SSBX/Text/OperatorAnchors.lean`](../../formal/SSBX/Text/OperatorAnchors.lean) | 文言算子到八卦系统的锚点（已迁 Cell256） |
| [`formal/SSBX/Foundation/Wen/Operators.lean`](../../formal/SSBX/Foundation/Wen/Operators.lean) | Wen 层算子接口 |
| [`formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) | XOR-mask atomic 算子（v3 入口） |
| [`formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) | V₄ Klein outer permutation 算子（v3 入口） |

## v3 算子分类（核心二分：Atomic vs V4Outer）

v3 把基础算子（在 Cell128 / Cell256 / Hexagram 上的）严格分为两组，按代数性质区分：

| 类别 | 代数性质 | 群结构 | 典型算子 | Lean 文件 |
|---|---|---|---|---|
| **Atomic** | XOR with fixed mask | (Z/2)ⁿ abelian subgroup；each involution；all pairs commute | 印 / 投（at Cell256），flip1..flip6 / 印 / hexCuo（at Cell128） | [`Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) |
| **V4Outer** | non-XOR permutation | `{id, cuo, zong, cuoZong}` ≅ V₄ Klein-four；含 sibling `hu`（**不在** V₄，有 `{乾, 坤}` 不动点） | hex_zong / hex_cuoZong / hex_hu / cell128_zong / hu / cell256_zong / hu | [`Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) |

> 注：`cuo` 本身是 XOR-mask（with all-yin / kun mask），代数上是 atomic；但其 V₄ **结构**作用与 `zong` / `cuoZong` 不可分割，故在 V4Outer.lean 中亦作 V₄ 生成元出现。

按代数性质分四类（贯通本页 §2–§5）：

- **A. XOR atoms by layer (atomic XOR-mask group)** — abelian (ℤ/2)ⁿ subgroup；每元 involutive；任两个 commute. 见 §2.
- **B. V₄-outer (cuo / zong / hu)** — Klein four-group {id, cuo, zong, cuoZong} + sibling hu（非 V₄ 但 outer non-XOR）. 见 §3.
- **C. Cayley action** — `c • s = c ⊕ s` 把每个 cell 当作算子 (regular representation). 见 §4.
- **D. Composition patterns** — within-layer 自映 / cross-layer Lift+Project / multi-step composite (chong). 见 §5.

> Provisional names — 印/投 / 因/果 / 五爻 等暂用，备选见 [yi-calculus-theorem.md §16](../10_formal_形式/yi-calculus-theorem.md). 标 *(prov)* 即 provisional. 详见本页 §7.

## 读表方法

每个 R-hierarchy 算子至少有四个层面：

| 层面 | 问题 | 审计入口 |
|---|---|---|
| **形态 (shape)** | 它在 OX 8-bit string 上长成什么样 (mask / permutation)? | OX 列，见 §2/§3 |
| **R-layer** | 它在哪个 R_n 出生 (atomic axis 在哪一层)? | R-layer 列 |
| **Type signature** | 它是 `Cell256 → Cell256`? `Hexagram → Hexagram`? `Cell128 → Cell128`? | Sig 列 |
| **Lean anchor** | 它在哪个 Lean 文件 + def 名? | Lean 列 |
| **群结构（v3 新加）** | 它属于 Atomic 还是 V4Outer；involution / non-involution | `Operators/Atomic.lean` / `Operators/V4Outer.lean` |

每个 catalogue（文字层）算子至少有四个层面（与上述正交，见 §6）：

| 层面 | 问题 | 审计入口 |
|---|---|---|
| 文字 | 这个字或短语如何写 | `wenyan-operators.md` |
| code/id | 它在表中如何定位 | `../_generated/operator-index.md` |
| 签名 | 它怎样接收和产生结构（catalogue 形态分类，与 §1 R-hierarchy type sig 不同） | `OperatorSignatures.lean` |
| 语义 | 它在候选 cell 或 family 中怎样解释 | `Operator*Semantics.lean` |

## § 2 Atomic XOR operators · 原子 XOR 算子

每个原子算子 = XOR with a fixed mask. 全体在 (ℤ/2)ⁿ 上构成 abelian subgroup；每元自逆 (involution)；任两个 commute. 共 8 个 atomic generators on R₈.

### 2.1 By R-layer · 按层

| Name | EN | 拼音 | R-layer | Sig | Mask (8-bit OX) | 翻位 | Lean anchor |
|---|---|---|---|---|---|---|---|
| **反 (neg)** | negate yao | fǎn | R₁ | `Yao → Yao` | (1-bit) `x` | y₀ | [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) `Yao.neg` |
| **dongInner / flip1** | flip y₁ | dòng | R₃→R₆ | `Hexagram → Hexagram` | `xooooooo` | y₁ (初爻) | [`BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) `dongInner`; [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) `flip1` |
| **huaInner / flip2** | flip y₂ | huà | R₃→R₆ | `Hexagram → Hexagram` | `oxoooooo` | y₂ | `huaInner`; `flip2` |
| **bianInner / flip3** | flip y₃ | biàn | R₃→R₆ | `Hexagram → Hexagram` | `ooxooooo` | y₃ | `bianInner`; `flip3` |
| **dongOuter / flip4** | flip y₄ | dòng | R₆ | `Hexagram → Hexagram` | `oooxoooo` | y₄ | `dongOuter`; `flip4` |
| **huaOuter / flip5** | flip y₅ | huà | R₆ | `Hexagram → Hexagram` | `ooooxooo` | y₅ | `huaOuter`; `flip5` |
| **bianOuter / flip6** | flip y₆ | biàn | R₆ | `Hexagram → Hexagram` | `oooooxoo` | y₆ (上爻) | `bianOuter`; `flip6` |
| **印 (yìn)** *(prov, §7)* | toggle YinBit (因 axis) | yìn | **R₇** | `Cell256 → Cell256` | `OX["oooooooi"]` (= `(qian, ji)`) | y₇ (因) | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) `Cell256.yin` · [`Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) `cell256_yin` |
| **投 (tóu)** *(prov, §7)* | toggle GuoBit (果 axis) | tóu | **R₈** | `Cell256 → Cell256` | `OX["ooooooon"]` (= `(qian, wei)`) | y₈ (果) | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) `Cell256.tou` · [`Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) `cell256_tou` |

### 2.2 Cell256 / Cell128 lifted variants · 提升版

flip1..flip6 都有一个 `Cell256 → Cell256` 提升（保 Shi 不动）；同样 R₇ 因/印 在 R₈ 上 Cell256-lifted, R₈ 果/投 是 native R₈.

| Name | Sig | 行为 | Lean |
|---|---|---|---|
| `Cell256.flip1..flip6` | `Cell256 → Cell256` | 翻 hexagram 第 i 爻，保 Shi（V₄ component） | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) `flip1`..`flip6` |
| `Cell128.flip1..flip6` | `Cell128 → Cell128` | 翻 hexagram 第 i 爻，保 YinBit | [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) `flip1`..`flip6` |
| `Cell128.yin` | `Cell128 → Cell128` | toggle YinBit；mask 形与直接形等价（`yinM_eq_yin`） | [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) `yin` (= mask form `yinM`) |
| `Cell128.hexCuo` | `Cell128 → Cell128` | yao-wise negation (XOR with kun mask)；保 YinBit | [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) `hexCuo` |

### 2.3 Atomic group property — involutive + abelian

对每个 atomic op `f`：`f (f c) = c`；任两个 atomic ops commute (XOR 是 abelian). 见 `Atomic.atomic_all_involutive` bundle in [`Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean).

## § 3 V₄-outer operators · V₄ 外算子 (cuo / zong / hu / cuoZong)

V₄ Klein four-group lives on Hexagram (R₆) and lifts to R₇/R₈. `hu` is sibling outer (non-V₄, has fixed points；included for the canonical "outer" family).

### 3.1 V₄ Klein four-group on Hexagram (R₆)

| Name | EN | 物理 | Type | Mask / perm | Lean |
|---|---|---|---|---|---|
| **id** | identity | 1 (identity) | `Hexagram → Hexagram` | mask `OX["oooooo"]` | implicit |
| **cuo (错)** | yao-wise negation | **P** (parity) | `Hexagram → Hexagram` | XOR with `kun` (all-yin) mask `xxxxxx` | [`V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) `hex_cuo`; `Hexagram.cuo` |
| **zong (综)** | reverse yao order | **T** (time-reversal) | `Hexagram → Hexagram` | perm: `(y₁..y₆) ↦ (y₆..y₁)`; **non-XOR**；involution | `hex_zong`; `Hexagram.zong` |
| **cuoZong (错综)** | cuo ∘ zong | **PT** | `Hexagram → Hexagram` | composite；involution | `hex_cuoZong`; `Hexagram.cuoZong` |

V₄ relations (Lean-checked, see [`V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) `v4_outer_summary`):

- `cuo² = zong² = cuoZong² = id` (involutivity)
- `cuo ∘ zong = zong ∘ cuo` (abelian)
- `cuoZong = cuo ∘ zong` (defining composite)

### 3.2 Sibling outer · hu (互, Y-combinator-like)

| Name | EN | Type | Behavior | Lean |
|---|---|---|---|---|
| **hu (互)** | inner-trigram extraction | `Hexagram → Hexagram` | perm: `(y₁..y₆) ↦ (y₂, y₃, y₄, y₃, y₄, y₅)`; **non-XOR**, **non-invertible**；fixed points {乾, 坤}, 2-cycle {既济 ↔ 未济} | [`V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) `hex_hu`; `Hexagram.hu` |

`hu` is **NOT** a V₄ member — it has fixed points and is not invertible. Acts as Y-combinator-like fixed-point witness for self-reference (yi-RO § 7.2).

### 3.3 Cell128 / Cell256 V₄-outer lifts · 提升到 R₇/R₈

| Name | Sig | Behavior | Lean |
|---|---|---|---|
| `Cell128.hexCuo / hexZong / hexHu` | `Cell128 → Cell128` | hex-side V₄ (preserves YinBit / 因) | [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) |
| `Cell256.hexCuo / hexZong / hexHu` | `Cell256 → Cell256` | hex-side V₄ (preserves Shi V₄ component) | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) |
| `Cell256.shiCuo / shiZong / shiCuoZong` | `Cell256 → Cell256` | **Shi-side V₄** (preserves Hexagram, acts on `(因, 果) ∈ Bool²` block) | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) |

> Phase C (2026-05-11) note: `Shi : Type := YinBit × GuoBit` is now an `abbrev` over `Bool × Bool`, not an inductive. 印 / 投 / V₄ outer 之 Shi-side ops 都通过 (因, 果) bit pair 直接定义，与 mask form 等价。

Shi V₄ on the (因, 果) ∈ Bool² block:

- `shiCuo` (P-like): toggle 因 axis — 道↔已, 未↔今 (≡ 印 acting on Shi)；与 Cell256 atomic `cell256_yin` 等价（XOR-mask 形）.
- `shiZong` (T-like): toggle 果 axis — 道↔未, 已↔今 (≡ 投 acting on Shi)；与 `cell256_tou` 等价.
- `shiCuoZong` (PT): toggle both — 道↔今, 已↔未；V₄ central element 之 toggle；= `(· ⊕ (qian, jin))`.

R₈ has **double V₄** structure: `hex V₄ × Shi V₄` ≅ V₄ × V₄ ≅ (ℤ/2)⁴, giving 16 outer-symmetry transforms (yi-RO § 4.6 / yi-calculus Cor J.2).

## § 4 Cayley action · Cayley 自作用 (regular representation)

Each Cell256 cell `c` doubles as the operator `(· ⊕ c)`. 元 ≅ 算子 通过 Cayley regular representation 严格同构 (yi-RO § 5.1).

| Name | EN | Type | Lean |
|---|---|---|---|
| **xor** | (ℤ/2)⁸ XOR | `Cell256 → Cell256 → Cell256` | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) `Cell256.xor` |
| **+ / 0 / - / -** | Add / Zero / Neg / Sub via XOR | (instances) | `add_def`, `zero_def`, `neg_def`, `sub_def` |
| **• (smul)** | self-action: `c • s = c ⊕ s` | `Cell256 → Cell256 → Cell256` | `smul_def` |
| **cayley (ι)** | left translation `cayley c s = xor c s` | `Cell256 → (Cell256 → Cell256)` | `Cell256.cayley` |
| **epsAtOrigin (ε)** | evaluate at origin: `f ↦ f(origin)` | `(Cell256 → Cell256) → Cell256` | `Cell256.epsAtOrigin` |
| **origin** | (Z/2)⁸ identity = (qian, dao) = 道 cell | `Cell256` | `Cell256.origin` |

Key facts (Lean-checked, [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) `cell256_phaseA_summary`):

- `origin_xor` / `xor_origin`: identity laws.
- `xor_self`: `c ⊕ c = origin` (every element is self-inverse).
- `xor_comm`, `xor_assoc`: abelian + associative.
- `cayley_inj`: ι is injective ⇒ R₈ ↪ Aut(R₈).
- `cayley_hom`: ι is a group homomorphism.
- `epsAtOrigin_cayley`: ε ∘ ι = id.

Cell128 carries the analogous (ℤ/2)⁷ structure；见 [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) `cell128_phaseA_summary`.

## § 5 Composition patterns · 复合模式

### 5.1 Within-layer (mode A) · 同层复合

XOR 子群内 mask 复合 = XOR 复合: `(· ⊕ m₁) ∘ (· ⊕ m₂) = (· ⊕ (m₁ ⊕ m₂))`.

Examples:

- `flip1 ∘ flip2 ∘ flip3 = (· ⊕ xxxooooo)` = inner-trigram cuo.
- `dongInner ⊕ huaInner ⊕ bianInner = cuo` on Trigram (yi-calculus § 4.5 et al.).
- `印 ⊕ 投 = (· ⊕ OX["ooooooin"])` = `(qian, jin)` = Shi V₄ central element. (`Cell256.yin_tou_eq_central`.)

### 5.2 Cross-layer (mode B) · 跨层升降

Uniform Lift / Project pair `R_n ↔ R_{n+1}` (8 pairs total, see [`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean)):

- `liftRntoRn+1 : R_n → bit → R_{n+1}` (attach 1 bit).
- `projRn+1toRn : R_{n+1} → R_n` (drop 1 bit).
- Retract: `proj ∘ lift = id` (`liftProject_summary`).

### 5.3 Multi-step composite (mode C) · 重 (chong)

`chong` = R₃ → R₄ → R₅ → R₆: a 3-step composite of consecutive Lifts (was treated as a 3-bit jump in v1；v3 makes it explicit). 具体: 8 trigrams × 2 trigram = 64 hexagrams via `liftR3toR4 ∘ liftR4toR5 ∘ liftR5toR6` (each step adds 1 yao). Alternative: existing `BaguaAlgebra.chong : Trigram → Trigram → Hexagram` (R₃ × R₃ → R₆) is the 1-shot variant for legacy trigram-pair callers.

| Form | Sig | Source |
|---|---|---|
| `chong` (legacy 1-shot) | `Trigram → Trigram → Hexagram` | [`BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) |
| Lift composite (uniform) | `Trigram → Yao → Bool → Yao → Hexagram` | [`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) |

Both produce hexagrams；the uniform composite is preferred for layer-by-layer audits.

## 印 / 投 / Shi V₄ 之关系（v3 总图）

```
Cell256 = Hexagram × Shi,   Shi = V₄ Klein = {道, 已, 今, 未}
Shi ≅ (因, 果) ∈ Bool²:       道=(0,0)  已=(1,0)  未=(0,1)  今=(1,1)

印 (Atomic)   = XOR with (qian, 已) = toggle 因   ↔ Shi.cuo (V₄ generator 1)
投 (Atomic)   = XOR with (qian, 未) = toggle 果   ↔ Shi.zong (V₄ generator 2)
印 ⊘ 投       = XOR with (qian, 今) = V₄ central  ↔ Shi.cuoZong (V₄ central element)
道            = Shi.dao = V₄ identity = R₈ origin = no-op operator = 永真 cell
```

`cuo` / `zong` 在 R₃/R₆ Hexagram 上是 V₄ outer permutation；在 Shi V₄ 上 `Shi.cuo` / `Shi.zong` 是 V₄ generator；二者**不要混淆**：同名不同 layer，统一在 V₄ 之代数 family 中。

## 群关系（已 machineChecked）

| 关系 | 形式 | 锚 |
|---|---|---|
| Atomic 算子皆 involution（10 件） | `op (op c) = c` | `Operators/Atomic.lean § 5` `atomic_all_involutive` |
| 印 / 投 commute | `yin (tou c) = tou (yin c)` | `Cell256.lean § 8` `yin_tou_comm`, `Operators/Atomic.lean § 4` |
| 印 ∘ 投 = `(· ⊕ (qian, jin))` | `yin (tou c) = c ⊕ (qian, jin)` | `Cell256.lean § 8` `yin_tou_eq_central` |
| `{id, cuo, zong, cuoZong}` Hexagram 上 = V₄ Klein | involutivity + commute + composite | `Operators/V4Outer.lean § 7` `v4_outer_summary` |
| `hu` 不动点 = `{乾, 坤}` | `hu h = h ↔ h = qian ∨ h = kun` | `Operators/V4Outer.lean § 6` `hu_fixed_iff` |
| Cell128 / Cell256 zong involution | lift to product carrier 保持 involution | `Operators/V4Outer.lean § 5` |

## § 6 Text-layer operators · 文字层算子 (orthogonal catalogue)

R-hierarchy operators (§2–§5) are **algebraic** (Cell256 / Hexagram / Yao / Bool transforms). The wenyan **catalogue** (separate inventory of natural-language operators e.g. 关于、若、依、致 …) is **text-layer** and orthogonal. Bridges below.

### 6.1 Catalogue sources

见本页顶 "主要来源". 核心入口: [`OperatorAnchors.lean`](../../formal/SSBX/Text/OperatorAnchors.lean) bridges 文言 token ↔ Bagua/Yi 锚；[`OperatorCellMap.lean`](../../formal/SSBX/Text/OperatorCellMap.lean) maps 文字算子 → Cell256 候选 (R₈ 已对齐)；[`OperatorCellSemantics.lean`](../../formal/SSBX/Text/OperatorCellSemantics.lean) 给候选 cell 的保守语义.

### 6.2 Catalogue locator fields

生成索引同时给出三种定位字段：

| 字段 | 用途 |
|---|---|
| `Group` | 稳定机器分组，例如 `R`、`T`、`LIJ` |
| `Key` | 人读助记码，例如 `REL`、`TRN`、`RIT` |
| `Action Position` | 中文作用位，例如「结构关系位」「状态变换位」「礼制角色位」 |
| `Signature` / `Sig Key` / `Arity` | 形态层编码 (text-layer)；说明它是一元映射、二元关系、抽取、构造、量化等. 与 §1 的 Type signature 不同——前者是 catalogue 形态分类，后者是 Lean 上 R-hierarchy 实际 type. |
| `Action Bit` | 效果位，说明这个形态落到哪类操作位置，例如关联位、变换位、抽取位 |
| `Operator Mode` | 该效果位允许的 operator 模式，例如 `relate`、`transform`、`extract` |
| `Effect` | 该模式的保守效果说明；这是账本语义，不等于完整可执行解释 |
| `Full Code` | 全路径码：`GroupKey.SignatureKeyArity.ActionKey.Code`，例如 `REL.REL2.LINK.R-1` |

引用定理或代码时仍用 `Code`/`Id`；面向阅读、讨论和图示时可显示 `Full Code`，它把分组、形态、效果位、原始编号合成一个可读定位。

`Action Bit` 是比 `Signature` 再低一层的索引：`Signature` 回答「它长成什么形」，`Action Bit` 回答「它能当什么 operator 用、作用后产生什么类型的效果」。能执行到 **`Cell256 → Cell256`** 的效果以 [`OperatorInstructionSemantics.lean`](../../formal/SSBX/Text/OperatorInstructionSemantics.lean) 里的证明为准（v3 已迁；旧 `Cell192 → Cell192` 表述见 [`../30_crosswalk_互证/old-to-new.md`](../30_crosswalk_互证/old-to-new.md) #22）。

### 6.3 Grouping conventions

算子分组是阅读与审计工具，不是宣称传统文献天然如此分类。常见组别包括关系、容纳、转化、流动、起止、量词、因果、模态、否定、同异、句法、核心义理、墨经、名家、时间副词等。完整 group 列表以生成索引为准。

## § 7 Provisional naming caveats · 命名暂行说明

R₇ atom (因/印) 与 R₈ atom (果/投) 命名暂用 因/果 (state) + 印/投 (action). 备选 (per [yi-calculus-theorem.md §16](../10_formal_形式/yi-calculus-theorem.md)):

| 候选 | 哲学 | 形式科学 | Yi-native | 项目耦合 |
|---|---|---|---|---|
| 因 / 果 (current) | 佛 hetu-phala + Pearl 因果 | causal DAG / lightcones | 《说文》古义 | "因"/"已" 听觉撞 |
| 印 / 投 | Husserl retention/protention | predictive filter | 《说文》"印, 执政所持信"/"投, 擿也" | 与 XinZhi.lean 三相直对接 |
| 始 / 终 | Aristotle arche/telos | initial/terminal | **《系辞下》"原始要终"** (Yi-native!) | — |
| 持 / 期 | retention/protention 标准汉译 | E[X] expected value | 《诗经》/《左传》 | 概率/统计 anchor |

R₅ name (Wuyao 五爻) is also provisional — has no traditional Yi anchor (the only R-layer with that property). Candidates: 五爻 (descriptive) / 接 / 临 / 渐 / 进 (per yi-RO § 3.5).

回看时机: Cell128 / Cell256 落码 + Theorems H–K 形式化稳定后. (As of 2026-05-11, both done — but final naming choice deferred to allow ecosystem use.)

## 与义理的关系

- `义理/D_算子代数.md` 和 `义理/G_完整算子系统_八卦互通与归一.md` 是旧解释入口。
- 新版义理只摘要结构，不复制长表。
- 若旧别名表与生成索引冲突，先信任生成索引，再回到 Lean 源确认。
- 算子出现于图或 claim 时，仍需查对应 theorem 或 registry 状态。
- v2 期之「印 / 投 仅作 Shi 三态 (Z/3) 算子」已被 v3 的 first-class XOR-mask 算子取代；旧叙述见 [`../30_crosswalk_互证/old-to-new.md`](../30_crosswalk_互证/old-to-new.md) #15。

## § 8 维护规则

- 不在本页手写完整算子清单 (catalogue 入口在 §6.1)。
- 不把同字复用自动解释为同一语义；复用要看 id、group 和 reading。
- 不把 operator table complete 误读成所有自然语言句子可解析。
- 新增 R-hierarchy 算子: 同时更新本页 §2/§3 + 对应 Lean 文件 (Atomic.lean / V4Outer.lean) + summary bundle.
- 新增 catalogue 算子后应重新生成 `../_generated/operator-index.md`，再检查本页 §6 是否需要补充入口。
- v3 之 Atomic / V4Outer 分类是结构性约束；新增算子若属此二分应在相应 Lean 文件中归类。
- R-hierarchy 算子之 ground truth 是 [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) + [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) + [`V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) + [`Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean)；文字算子 ground truth 是 `WenyanOperators.lean` + 索引.

## 形式锚

- [`formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) — XOR-mask atomic 算子
- [`formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) — V₄ Klein outer permutation 算子
- [`formal/SSBX/Foundation/Hierarchy/LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) — Lift / Project 跨层
- [`formal/SSBX/Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) — Cell256 / Shi V₄ / 印 / 投 mask / Cayley
- [`formal/SSBX/Foundation/Bagua/Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) — Cell128 / 印 / flip1..flip6
- [`formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) — `dong/hua/bian`, `FlipCombo`, `chong` (legacy)
- [`formal/SSBX/Foundation/Yi/Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) — `Yao.neg`, `Hexagram.cuo / zong / hu`
- [`formal/SSBX/Text/OperatorAnchors.lean`](../../formal/SSBX/Text/OperatorAnchors.lean) — 文言算子到八卦系统的锚点
- [`formal/SSBX/Text/OperatorCellMap.lean`](../../formal/SSBX/Text/OperatorCellMap.lean) — 单元映射
- [`formal/SSBX/Text/WenyanOperators.lean`](../../formal/SSBX/Text/WenyanOperators.lean) — 算子数据源
