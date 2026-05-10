# 算子参考 · Operator Reference

> 状态：v3 定本 (2026-05-11)
> 父链：[`docs-next/40_reference_参考/`](./) · 上层导航见 [`docs-next/`](../)
> 配套：[`yi-RO-hierarchy.md`](../10_formal_形式/yi-RO-hierarchy.md) (R₀..R₈ definitive) · [`yi-calculus-theorem.md`](../10_formal_形式/yi-calculus-theorem.md) (Theorems A–K + §16 命名附录) · [`glossary.md`](glossary.md)

本页是 **R-hierarchy R₀..R₈ 上 Lean-grounded 算子的人读参考**. 文字层算子 (catalogue 入口、reading registry 等) 与本页正交; 见本页末 §6.

机器事实以 Lean 源 + `../_generated/operator-index.md` 为准. 本页不维护 catalogue 总数，但完整覆盖 R-hierarchy 上每层之原子 / V₄-外 / Cayley / 复合算子.

---

## § 1 Reading the operator tables · 读表方法

每个 R-hierarchy 算子至少有四个层面:

| 层面 | 问题 | 审计入口 |
|---|---|---|
| **形态 (shape)** | 它在 OX 8-bit string 上长成什么样 (mask / permutation)? | OX 列, 见 §2/§3 |
| **R-layer** | 它在哪个 R_n 出生 (atomic axis 在哪一层)? | R-layer 列 |
| **Type signature** | 它是 `Cell256 → Cell256`? `Hexagram → Hexagram`? `Cell128 → Cell128`? | Sig 列 |
| **Lean anchor** | 它在哪个 Lean 文件 + def 名? | Lean 列 |

按代数性质分四类:
- **A. XOR atoms by layer (atomic XOR-mask group)** — abelian (ℤ/2)ⁿ subgroup; 每元 involutive; 任两个 commute.
- **B. V₄-outer (cuo / zong / hu)** — Klein four-group {id, cuo, zong, cuoZong} + sibling hu (非 V₄ 但 outer non-XOR).
- **C. Cayley action** — `c • s = c ⊕ s` 把每个 cell 当作算子 (regular representation).
- **D. Composition patterns** — within-layer 自映 / cross-layer Lift+Project / multi-step composite (chong).

Provisional names — 印/投 / 因/果 / 五爻 等暂用, 备选 见 [yi-calculus-theorem.md §16](../10_formal_形式/yi-calculus-theorem.md). 标 *(prov)* 即 provisional.

---

## § 2 Atomic XOR operators · 原子 XOR 算子

每个原子算子 = XOR with a fixed mask. 全体在 (ℤ/2)ⁿ 上构成 abelian subgroup; 每元自逆 (involution); 任两个 commute. 共 8 个 atomic generators on R₈.

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
| **印 (yìn)** *(prov, §16)* | toggle YinBit (因 axis) | yìn | **R₇** | `Cell256 → Cell256` | `OX["oooooooi"]` (= `(qian, ji)`) | y₇ (因) | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) `Cell256.yin` · [`Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) `cell256_yin` |
| **投 (tóu)** *(prov, §16)* | toggle GuoBit (果 axis) | tóu | **R₈** | `Cell256 → Cell256` | `OX["ooooooon"]` (= `(qian, wei)`) | y₈ (果) | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) `Cell256.tou` · [`Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) `cell256_tou` |

### 2.2 Cell256-lifted variants · Cell256 提升版

flip1..flip6 都有一个 `Cell256 → Cell256` 提升 (保 Shi 不动)；同样 R₇ 因/印 在 R₈ 上 Cell256-lifted, R₈ 果/投 是 native R₈.

| Name | Cell256 sig | 行为 | Lean |
|---|---|---|---|
| `Cell256.flip1..flip6` | `Cell256 → Cell256` | 翻 hexagram 第 i 爻, 保 Shi | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) `flip1`..`flip6` |
| `Cell128.flip1..flip6` | `Cell128 → Cell128` | 翻 hexagram 第 i 爻, 保 YinBit | [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) `flip1`..`flip6` |
| `Cell128.yin` | `Cell128 → Cell128` | toggle YinBit (legacy direct form `(h, !b)`) | [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) `yin` (= mask form `yinM`) |

### 2.3 Atomic group property — involutive + abelian

对每个 atomic op `f`: `f (f c) = c`; 任两个 atomic ops commute (XOR 是 abelian). 见 `Atomic.atomic_all_involutive` bundle in [`Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean).

---

## § 3 V₄-outer operators · V₄ 外算子 (cuo / zong / hu / cuoZong)

V₄ Klein four-group lives on Hexagram (R₆) and lifts to R₇/R₈. `hu` is sibling outer (non-V₄, has fixed points; included for the canonical "outer" family).

### 3.1 V₄ Klein four-group on Hexagram (R₆)

| Name | EN | 物理 | Type | Mask / perm | Lean |
|---|---|---|---|---|---|
| **id** | identity | 1 (identity) | `Hexagram → Hexagram` | mask `OX["oooooo"]` | implicit |
| **cuo (错)** | yao-wise negation | **P** (parity) | `Hexagram → Hexagram` | XOR with `kun` (all-yin) mask `xxxxxx` | [`V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) `hex_cuo`; `Hexagram.cuo` |
| **zong (综)** | reverse yao order | **T** (time-reversal) | `Hexagram → Hexagram` | perm: `(y₁..y₆) ↦ (y₆..y₁)`; **non-XOR** | `hex_zong`; `Hexagram.zong` |
| **cuoZong (错综)** | cuo ∘ zong | **PT** | `Hexagram → Hexagram` | composite | `hex_cuoZong`; `Hexagram.cuoZong` |

V₄ relations (Lean-checked, see [`V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) `v4_outer_summary`):
- `cuo² = zong² = cuoZong² = id` (involutivity)
- `cuo ∘ zong = zong ∘ cuo` (abelian)
- `cuoZong = cuo ∘ zong` (defining composite)

### 3.2 Sibling outer · hu (互, Y-combinator-like)

| Name | EN | Type | Behavior | Lean |
|---|---|---|---|---|
| **hu (互)** | inner-trigram extraction | `Hexagram → Hexagram` | perm: `(y₁..y₆) ↦ (y₂, y₃, y₄, y₃, y₄, y₅)`; **non-XOR**, **non-invertible**; fixed points {乾, 坤}; 2-cycle {既济 ↔ 未济} | [`V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) `hex_hu`; `Hexagram.hu` |

`hu` is **NOT** a V₄ member — it has fixed points and is not invertible. Acts as Y-combinator-like fixed-point witness for self-reference (yi-RO § 7.2).

### 3.3 Cell128 / Cell256 V₄-outer lifts · 提升到 R₇/R₈

| Name | Sig | Behavior | Lean |
|---|---|---|---|
| `Cell128.hexCuo / hexZong / hexHu` | `Cell128 → Cell128` | hex-side V₄ (preserves YinBit / 因) | [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) |
| `Cell256.hexCuo / hexZong / hexHu` | `Cell256 → Cell256` | hex-side V₄ (preserves Shi V₄) | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) |
| `Cell256.shiCuo / shiZong / shiCuoZong` | `Cell256 → Cell256` | **Shi-side V₄** (preserves Hexagram, acts on (因,果) block) | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) |

Shi V₄ on the (因, 果) ∈ Bool² block:
- `shiCuo` (P-like): toggle 因 axis — 道↔已, 未↔今 (≡ 印 acting on Shi).
- `shiZong` (T-like): toggle 果 axis — 道↔未, 已↔今 (≡ 投 acting on Shi).
- `shiCuoZong` (PT): toggle both — 道↔今, 已↔未.

R₈ has **double V₄** structure: `hex V₄ × Shi V₄` ≅ V₄ × V₄ ≅ (ℤ/2)⁴, giving 16 outer-symmetry transforms (yi-RO § 4.6 / yi-calculus Cor J.2).

---

## § 4 Cayley action · Cayley 自作用 (regular representation)

Each Cell256 cell `c` doubles as the operator `(· ⊕ c)`. 元 ≅ 算子 通过 Cayley regular representation 严格同构 (yi-RO § 5.1).

| Name | EN | Type | Lean |
|---|---|---|---|
| **xor** | (ℤ/2)⁸ XOR | `Cell256 → Cell256 → Cell256` | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) `Cell256.xor` |
| **+ / 0 / - / -** | Add / Zero / Neg / Sub via XOR | (instances) | `add_def`, `zero_def`, `neg_def`, `sub_def` |
| **• (smul)** | self-action: `c • s = c ⊕ s` | `Cell256 → Cell256 → Cell256` | `smul_def` |
| **cayley** | left translation `cayley c s = xor c s` | `Cell256 → (Cell256 → Cell256)` | `Cell256.cayley` |
| **epsAtOrigin** | evaluate at origin: `f ↦ f(origin)` | `(Cell256 → Cell256) → Cell256` | `Cell256.epsAtOrigin` |
| **origin** | (Z/2)⁸ identity = (qian, dao) = 道 cell | `Cell256` | `Cell256.origin` |

Key facts (Lean-checked, [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) `cell256_phaseA_summary`):
- `origin_xor` / `xor_origin`: identity laws.
- `xor_self`: `c ⊕ c = origin` (every element is self-inverse).
- `xor_comm`, `xor_assoc`: abelian + associative.
- `cayley_inj`: ι is injective ⇒ R₈ ↪ Aut(R₈).
- `cayley_hom`: ι is a group homomorphism.
- `epsAtOrigin_cayley`: ε ∘ ι = id.

Cell128 carries the analogous (ℤ/2)⁷ structure; see [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) `cell128_phaseA_summary`.

---

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

`chong` = R₃ → R₄ → R₅ → R₆: a 3-step composite of consecutive Lifts (was treated as a 3-bit jump in v1; v3 makes it explicit). Concretely 8 trigrams × 2 trigram = 64 hexagrams via `liftR3toR4 ∘ liftR4toR5 ∘ liftR5toR6` (each step adds 1 yao). Alternative: existing `BaguaAlgebra.chong : Trigram → Trigram → Hexagram` (R₃ × R₃ → R₆) is the 1-shot variant for legacy trigram-pair callers.

| Form | Sig | Source |
|---|---|---|
| `chong` (legacy 1-shot) | `Trigram → Trigram → Hexagram` | [`BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) |
| Lift composite (uniform) | `Trigram → Yao → Bool → Yao → Hexagram` | [`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) |

Both produce hexagrams; the uniform composite is preferred for layer-by-layer audits.

---

## § 6 Text-layer operators · 文字层算子 (orthogonal catalogue)

R-hierarchy operators (this page) are **algebraic** (Cell256 / Hexagram / Yao / Bool transforms). The wenyan **catalogue** (separate inventory of natural-language operators e.g. 关于、若、依、致 …) is **text-layer** and orthogonal. Bridges below.

### 6.1 Catalogue sources

| 来源 | 用途 |
|---|---|
| `../_generated/operator-index.md` | 当前算子索引、分组 (Group/Key/Action) 和 code/id |
| `wenyan-operators.md` | 人工长表与文字说明 |
| [`WenyanOperators.lean`](../../formal/SSBX/Text/WenyanOperators.lean) | 算子数据源 |
| [`OperatorReadings.lean`](../../formal/SSBX/Text/OperatorReadings.lean) | 读法登记 |
| [`OperatorSignatures.lean`](../../formal/SSBX/Text/OperatorSignatures.lean) | 签名和形态 (text-layer) |
| [`OperatorCellMap.lean`](../../formal/SSBX/Text/OperatorCellMap.lean) | 文字算子 → Cell256 候选 (R₈ 已对齐) |
| [`OperatorCellSemantics.lean`](../../formal/SSBX/Text/OperatorCellSemantics.lean) | 候选 cell 的保守语义 |
| [`OperatorAnchors.lean`](../../formal/SSBX/Text/OperatorAnchors.lean) | 文言 token ↔ Bagua/Yi 锚 |
| [`Foundation/Wen/Operators.lean`](../../formal/SSBX/Foundation/Wen/Operators.lean) | Wen 层算子接口 |

### 6.2 Catalogue locator fields

生成索引同时给出三种定位字段:

| 字段 | 用途 |
|---|---|
| `Group` | 稳定机器分组，例如 `R`、`T`、`LIJ` |
| `Key` | 人读助记码，例如 `REL`、`TRN`、`RIT` |
| `Action Position` | 中文作用位，例如 "结构关系位"、"状态变换位"、"礼制角色位" |
| `Signature` / `Sig Key` / `Arity` | 形态层编码 (text-layer); 与 §1 的 Type signature 不同——前者是 catalogue 形态分类，后者是 Lean 上 R-hierarchy 实际 type. |
| `Action Bit` | 效果位; 关联位 / 变换位 / 抽取位 |
| `Operator Mode` | 该效果位允许的模式 (`relate` / `transform` / `extract`) |
| `Effect` | 该模式的保守效果说明 (账本语义, 不等于完整可执行解释) |
| `Full Code` | 全路径码 `GroupKey.SignatureKeyArity.ActionKey.Code`，例如 `REL.REL2.LINK.R-1` |

`Action Bit` 是比 `Signature` 再低一层的索引: `Signature` 回答 "它长成什么形", `Action Bit` 回答 "它能当什么 operator 用、作用后产生什么类型的效果". 能执行到 `Cell256 → Cell256` 的效果以 [`OperatorInstructionSemantics.lean`](../../formal/SSBX/Text/OperatorInstructionSemantics.lean) 里的证明为准.

### 6.3 Grouping conventions

算子分组是阅读与审计工具，不是宣称传统文献天然如此分类。常见组别包括关系、容纳、转化、流动、起止、量词、因果、模态、否定、同异、句法、核心义理、墨经、名家、时间副词等。完整 group 列表以生成索引为准。

---

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

---

## § 8 Maintenance · 维护规则

- 不在本页手写完整文字算子清单 (catalogue 入口在 §6.1).
- 不把同字复用自动解释为同一语义；复用要看 id、group 和 reading.
- 不把 R-hierarchy operator inventory 误读成 "所有自然语言句子可解析".
- 新增 R-hierarchy 算子: 同时更新本页 §2/§3 + 对应 Lean 文件 (Atomic.lean / V4Outer.lean) + summary bundle.
- 新增 catalogue 算子: 重新生成 `../_generated/operator-index.md`, 检查本页 §6 是否需要补充入口.
- R-hierarchy 算子之 ground truth 是 [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) + [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) + [`V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) + [`Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean); 文字算子 ground truth 是 `WenyanOperators.lean` + 索引.
- 与义理: `义理/D_算子代数.md` 与 `义理/G_完整算子系统_八卦互通与归一.md` 是旧解释入口. 新版义理只摘要结构, 不复制长表. 若旧别名表与生成索引冲突, 先信任生成索引, 再回到 Lean 源确认.
