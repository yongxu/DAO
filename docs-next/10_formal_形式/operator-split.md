# Atomic vs V4Outer — 算子族之 XOR-内 / 非-XOR 分裂

> 状态：v3 canonical (2026-05-11) — R₈ 上的算子总族明确分裂为两类：**Atomic** = XOR-with-fixed-mask (abelian, 所有元素 involutive, 落在 (Z/2)⁸ subgroup)，与 **V4Outer** = 非-XOR permutations (含 zong / hu / cuoZong)。R-O 256-256 self-duality 严格只在 XOR closure 内成立；V4Outer 是其上之 enrichment。
> 角色：本文是「算子分类」之专文。Atomic 集 + 个 op 之解释见 [`yin-tou-operators.md`](yin-tou-operators.md) (印/投) + [`cell256-grid.md`](cell256-grid.md) (单爻翻 / hex cuo)；Shi V₄ 之 4 元结构见 [`v4-shi.md`](v4-shi.md)；R-O 自对偶之 algebraic spine 见 [`cell256-algebra.md`](cell256-algebra.md)。
> 形式锚：[`Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) + [`V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean)。

---

## 0. 一句话总纲

> **Atomic** = (Z/2)⁸ XOR subgroup 之 generators + 由 mask 表达的 ops（含 印 / 投 / 6 单爻翻 / hex cuo）；**V4Outer** = 真 permutations (zong, hu, cuoZong)，**不**是 XOR；它们独立形成 V₄ Klein 关系，而 hu 是 sibling outer op (有 fixed points {乾, 坤})。

---

## 1. 总览

```
R₈ = (Z/2)⁸ Cell256 之算子族
│
├── Atomic.lean (XOR subgroup, abelian, all involutive)
│   ├── R₈ Cell256 level
│   │   ├── cell256_yin = XOR with OX["ooooooxo"]   -- 印 (yin)
│   │   └── cell256_tou = XOR with OX["ooooooox"]   -- 投 (tou)
│   └── R₇ Cell128 level
│       ├── cell128_flip1..flip6   -- 单爻翻 (XOR with single-bit hex masks)
│       ├── cell128_yin            -- toggle YinBit (R₇ atom)
│       └── cell128_hexCuo         -- XOR with kun mask, preserves YinBit
│
└── V4Outer.lean (non-XOR permutations)
    ├── Hexagram level
    │   ├── hex_zong (综)            -- 反 yao 序 (perm)
    │   ├── hex_cuo (错)             -- (XOR mask 实现，但作为 V₄ generator 列于此)
    │   ├── hex_cuoZong (错综 = cuo ∘ zong)   -- composite
    │   └── hex_hu (互)              -- inner-trigram extraction; sibling, NOT V₄ member
    ├── Cell128 lifts
    │   ├── cell128_zong  -- preserves YinBit
    │   └── cell128_hu
    └── Cell256 lifts
        ├── cell256_zong  -- preserves Shi V₄
        └── cell256_hu
```

| 维度 | Atomic | V4Outer |
|---|---|---|
| 表达 | XOR with mask | true permutation |
| 群结构 | (Z/2)⁸ XOR abelian subgroup | V₄ Klein on {id, cuo, zong, cuoZong}（含 cuo 但 cuo 自身可表为 mask） |
| 元素阶 | 全 ≤ 2 (involution) | cuo / zong / cuoZong 全 ≤ 2; hu 不是 involution |
| commute | 全 pairwise commute | V₄ 内 commute；hu 与 V₄ 之 commute 不全成立 |
| R-O fusion | 严格 — \|Cell256\| = \|XOR(Cell256)\| = 256 | 是 enrichment — 把 Aut(Cell256) 扩到更大的群 |

---

## 2. Atomic — XOR subgroup

[`Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) 之 docstring：

> This file groups all "atomic" SSBX operators — those that act as XOR with a fixed mask on the underlying (Z/2)ⁿ carrier. Algebraically they form an **abelian subgroup** (every element of order ≤ 2, all pairs commute).

### 2.1 Cell256 level (R₈)

```lean
def cell256_yin (c : Cell256) : Cell256 := Cell256.yin c   -- XOR with (qian, ji)  = OX["ooooooxo"]
def cell256_tou (c : Cell256) : Cell256 := Cell256.tou c   -- XOR with (qian, wei) = OX["ooooooox"]
```

详 [`yin-tou-operators.md`](yin-tou-operators.md)。

### 2.2 Cell128 level (R₇)

6 个单爻 toggles + 印 + hexCuo：

```lean
def cell128_flip1..flip6 (c : Cell128) : Cell128 := flip{n} c
def cell128_yin (c : Cell128) : Cell128 := SSBX.Foundation.Bagua.Cell128.yin c
def cell128_hexCuo (c : Cell128) : Cell128 := SSBX.Foundation.Bagua.Cell128.hexCuo c
```

每个 `flip{n}` 是 XOR with single-bit mask（即翻第 n 个 yao），是 (Z/2)⁶ 之 `n`-th basis vector。`cell128_hexCuo` = XOR with kun-mask = `OX["xxxxxx_o"]`（preserves YinBit at position 6）。

### 2.3 Group property — every atomic op is involutive

```lean
theorem cell256_yin_involutive  : ∀ c, cell256_yin (cell256_yin c) = c
theorem cell256_tou_involutive  : ∀ c, cell256_tou (cell256_tou c) = c
theorem cell128_flip1_involutive : ∀ c, cell128_flip1 (cell128_flip1 c) = c
... (flip2..flip6 同)
theorem cell128_yin_involutive   : ∀ c, cell128_yin (cell128_yin c) = c
theorem cell128_hexCuo_involutive: ∀ c, cell128_hexCuo (cell128_hexCuo c) = c
```

每个证明都是 forward 到 source-file lemma（即 `Cell128.lean` / `Cell256.lean` 已建之 `*_yin_yin / flip{n}_flip{n} / hexCuo_hexCuo`）。

### 2.4 abelian — XOR commutes pairwise

代表：

```lean
theorem cell256_yin_tou_comm (c : Cell256) :
    cell256_yin (cell256_tou c) = cell256_tou (cell256_yin c)
```

更广 — XOR with any two fixed masks commute（`(c ⊕ m₁) ⊕ m₂ = (c ⊕ m₂) ⊕ m₁`）。所以 Atomic.lean 之全 9 个 ops + Cell256 之 印/投 全 11 ops（即 Cell128 之 8 + Cell256 之 2 + cell128_yin 与 cell128_hexCuo 互锁）pairwise commute — 它们形成一个**abelian subgroup of Aut(Cell256) of size ≤ 2⁸**。

### 2.5 Atomic 摘要定理

```lean
theorem atomic_all_involutive :
    -- Cell256 layer
    (∀ c : Cell256, cell256_yin (cell256_yin c) = c)
    ∧ (∀ c : Cell256, cell256_tou (cell256_tou c) = c)
    -- Cell128 single-yao toggles
    ∧ (∀ c : Cell128, cell128_flip1 (cell128_flip1 c) = c)
    ∧ (∀ c : Cell128, cell128_flip2 (cell128_flip2 c) = c)
    ∧ (∀ c : Cell128, cell128_flip3 (cell128_flip3 c) = c)
    ∧ (∀ c : Cell128, cell128_flip4 (cell128_flip4 c) = c)
    ∧ (∀ c : Cell128, cell128_flip5 (cell128_flip5 c) = c)
    ∧ (∀ c : Cell128, cell128_flip6 (cell128_flip6 c) = c)
    -- Cell128 印 + hexCuo
    ∧ (∀ c : Cell128, cell128_yin (cell128_yin c) = c)
    ∧ (∀ c : Cell128, cell128_hexCuo (cell128_hexCuo c) = c)
```

10 项 — atomic XOR subgroup property 在两层 (R₇ + R₈) 之全收口。

---

## 3. V4Outer — 非-XOR permutations

[`V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) 之 docstring：

> This file groups SSBX operators that are **not** XOR-with-fixed-mask. They involve genuine permutations of the underlying carrier ...

### 3.1 Hexagram level (R₆)

```lean
def hex_zong (h : Hexagram) : Hexagram := Hexagram.zong h
def hex_cuoZong (h : Hexagram) : Hexagram := Hexagram.cuoZong h
def hex_hu (h : Hexagram) : Hexagram := Hexagram.hu h
def hex_cuo (h : Hexagram) : Hexagram := Hexagram.cuo h  -- (XOR mask, but listed here as V₄ generator)
```

注释（[`V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) § 1）：

> Although `cuo` itself is XOR (atomic), the V₄ *structure* lives here because its non-trivial part (`zong`, `cuoZong`) requires the permutation. `hu` is included as a sibling non-XOR operator (it is NOT in the V₄ — it has fixed points 乾/坤 and is not invertible — but it is the canonical other "outer" op in the operator family).

### 3.2 Cell128 / Cell256 lifts

```lean
-- Cell128 (preserves YinBit)
def cell128_zong (c : Cell128) : Cell128 := hexZong c
def cell128_hu (c : Cell128) : Cell128 := hexHu c

-- Cell256 (preserves Shi V₄)
def cell256_zong (c : Cell256) : Cell256 := Cell256.hexZong c
def cell256_hu (c : Cell256) : Cell256 := Cell256.hexHu c
```

### 3.3 V₄ Klein 关系

```lean
theorem zong_involutive (h : Hexagram) : hex_zong (hex_zong h) = h
theorem cuo_involutive (h : Hexagram) : hex_cuo (hex_cuo h) = h
theorem cuoZong_involutive (h : Hexagram) : hex_cuoZong (hex_cuoZong h) = h
theorem cuo_zong_commute (h : Hexagram) :
    hex_cuo (hex_zong h) = hex_zong (hex_cuo h)
theorem cuoZong_eq_cuo_zong (h : Hexagram) :
    hex_cuoZong h = hex_cuo (hex_zong h) := rfl
```

V₄ 5 关系全证。注意 `cuo_zong_commute` 之非平凡：`hex_cuo` 是 XOR mask，`hex_zong` 是 perm；二者 **commute 是 BaguaAlgebra.lean 之 `Hexagram.cuo_zong_comm` 之结果**，不是 trivial 的群论 fact。

### 3.4 hu 之 fixed-point characterisation

hu 不是 V₄ member，因为它**有不动点** {乾, 坤}（hu 之逆映射不存在 — hu 把所有 hex 都映到只能由 4 个 yao 决定的 16 元 image，不是 bijection）：

```lean
theorem hu_fixed_iff (h : Hexagram) :
    hex_hu h = h ↔ h = Hexagram.qian ∨ h = Hexagram.kun
```

详 [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) `Hexagram.hu_fixed_point`。`hu` 是 sibling outer op — 它代表 Y-combinator / fixed-point operator anchor，详 [`yi-RO-hierarchy.md`](yi-RO-hierarchy.md) § 7.2。

### 3.5 V4Outer 摘要定理

```lean
theorem v4_outer_summary :
    -- Identity-element fact
    (∀ h : Hexagram, h = h)
    -- Three non-trivial involutions
    ∧ (∀ h : Hexagram, hex_cuo (hex_cuo h) = h)
    ∧ (∀ h : Hexagram, hex_zong (hex_zong h) = h)
    ∧ (∀ h : Hexagram, hex_cuoZong (hex_cuoZong h) = h)
    -- Abelian
    ∧ (∀ h : Hexagram, hex_cuo (hex_zong h) = hex_zong (hex_cuo h))
    -- Composite definition
    ∧ (∀ h : Hexagram, hex_cuoZong h = hex_cuo (hex_zong h))
    -- Cell128 / Cell256 lift involutivity
    ∧ (∀ c : Cell128, cell128_zong (cell128_zong c) = c)
    ∧ (∀ c : Cell256, cell256_zong (cell256_zong c) = c)
    -- Sibling outer hu fixed-point characterisation
    ∧ (∀ h : Hexagram, hex_hu h = h ↔ h = Hexagram.qian ∨ h = Hexagram.kun)
```

V₄ Klein 结构 + lifts + hu fixed-points 一齐。

---

## 4. 为什么要 split

R-O 256-256 self-duality（详 [`yi-RO-hierarchy.md`](yi-RO-hierarchy.md) § 5）严格只在 **XOR closure** 内成立 — Cayley `ι : Cell256 → Aut(Cell256)` 之像就是 XOR(Cell256) ⊆ Aut(Cell256)，且 ε ∘ ι = id。这给出：

$$|R_8| = |\text{XOR}(R_8)| = 256$$

把 zong / hu / cuoZong 加进来不会破坏 self-duality —— 它们只是把 Aut(Cell256) 之研究范围**扩到**更大的（非 abelian）群 V₄Outer ⋊ XOR。这意味着：

| 范围 | 群结构 | self-duality |
|---|---|---|
| Atomic 集合 only | (Z/2)⁸ abelian | strict R-O fusion |
| Atomic ⋊ V₄Outer | non-abelian (involve perms) | enrichment, no R-O fusion at this larger level |

**doctrine 之 split** 因此把：
- **fusion-relevant** ops 归 [`Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean)（这些是 self-duality 的 generators）
- **enrichment-only** ops 归 [`V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean)（这些不在 XOR subgroup，但承载 V₄ 物理 P/T/PT 结构 + Y-combinator）

---

## 5. 群结构对比

### 5.1 Atomic = (Z/2)⁸ abelian

8 atomic generators (6 单爻 + 印 + 投) 构成 (Z/2)⁸ basis — 它们 commute / square to identity / 任意 XOR 组合可达 256 个不同 mask（全 256 cells 之 XOR 子群即 Aut(Cell256) 中之 left-translation 子群，由 Cayley `ι` 就是其 isomorphism — 详 [`cell256-algebra.md`](cell256-algebra.md) § 6）。

### 5.2 V4Outer = V₄ + sibling hu

- V₄ Klein on `{id, cuo, zong, cuoZong}` — 4 元 abelian, 全 involution。
- sibling `hu` — 非 invertible, 有 fixed points {乾, 坤} (R₆), 在 R₈ 上 lift 到 16 个 attractor cells (4 hex × 4 Shi)。

V₄ + hu 之合集**不是群**（hu 不是 involution，与 V₄ 关系复杂）。但 V₄ alone 是 4 元 abelian 群；与 Atomic XOR subgroup 联合后形成 wreath-style 结构 V₄Outer ⋊ XOR(R₈)。

### 5.3 hu 之 fixed points / 2-cycles

```
hu(乾) = 乾    -- fixed
hu(坤) = 坤    -- fixed
hu(既济) = 未济, hu(未济) = 既济   -- 2-cycle
其余 60 hex   -- hu 把它们映到 8 hex 中之 4 nuclear hexagram
```

注意：`hu(既济) = 未济` 与 `hu(未济) = 既济` 形成一 2-cycle — 这是 algebraic self-reference 之 "Y-combinator 之 closing iteration" 的离散见证（[`yi-RO-hierarchy.md`](yi-RO-hierarchy.md) § 7.2）。

---

## 6. 跨层 lift 之保 invariant

V4Outer ops lifted to Cell128 / Cell256 时**保**额外 bit：

| op | Cell128 (R₇) lift | 保 | Cell256 (R₈) lift | 保 |
|---|---|---|---|---|
| zong | `cell128_zong` | YinBit 不动 | `cell256_zong` | Shi V₄ 不动 |
| hu | `cell128_hu` | YinBit 不动 | `cell256_hu` | Shi V₄ 不动 |
| cuo | `cell128_hexCuo` (Atomic!) | YinBit 不动 | `Cell256.hexCuo` (Atomic!) | Shi V₄ 不动 |

Atomic 与 V4Outer ops 都 preserves "新 axis" — 即只 act on Hexagram 部分，不动 (因, 果)。这是 R-hierarchy 之 strict (Z/2)ⁿ 自相似设计要求：每加 1 bit 之 atomic op 与 lift 之 outer op **正交**（commute）。

[`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 3 之相容定理：

```lean
theorem hexCuo_shiCuo_comm (c : Cell256) :
    hexCuo (shiCuo c) = shiCuo (hexCuo c)

theorem hexZong_shiZong_comm (c : Cell256) :
    hexZong (shiZong c) = shiZong (hexZong c)
```

---

## 7. parity / timeReversal / yComb 之关系

[`Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) § 2 把 V4Outer 之 hex 层 ops lift 到 R₈，加上 Shi 之 V₄ 双层得到 P/T/PT 之 anchor：

```lean
def parity (c : R8) : R8 := (Hexagram.cuo c.1, c.2)              -- hex side P, 保 Shi
def timeReversal (c : R8) : R8 := (Hexagram.zong c.1, c.2.zong)  -- hex zong + Shi.zong
def PT (c : R8) : R8 := timeReversal (parity c)
def yComb (c : R8) : R8 := (Hexagram.hu c.1, c.2)                 -- hu lift
```

所以 R₈ 上之物理 `parity` 是 hex `cuo` (XOR mask, atomic) lift；`timeReversal` 是 hex `zong` (V4Outer perm) + Shi `zong`（atomic on Shi side）双层 — 它**含 V4Outer 成分**故整体不是 XOR mask；`yComb` = hu lift, sibling outer.

---

## 8. Lean import 顺序

[`Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) 与 [`V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) 都 import `Cell256.lean / Cell128.lean`，不互相 depend；都被 [`RHierarchy.lean`](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean) umbrella import。

```lean
-- RHierarchy.lean
import SSBX.Foundation.Hierarchy.Operators.Atomic
import SSBX.Foundation.Hierarchy.Operators.V4Outer
```

下游模块如 [`SelfDescription.lean`](../../formal/SSBX/Truth/SelfDescription.lean) 使用 `Cell256OperatorComplete` 时同时引入两类 ops 之全集。

---

## 9. 与其他文档之关系

| 文档 | 关系 |
|---|---|
| [`yi-RO-hierarchy.md`](yi-RO-hierarchy.md) § 4.1 / 4.2 | XOR subgroup vs V₄ outer 之 doctrine 总论 |
| [`cell256-algebra.md`](cell256-algebra.md) | Atomic ops 之 Cayley fusion / self-duality |
| [`v4-shi.md`](v4-shi.md) | Shi V₄ 之 cuo / zong / cuoZong（皆 XOR on Shi side） |
| [`yin-tou-operators.md`](yin-tou-operators.md) | Atomic 中之 印 / 投 详解 |
| [`64-hexagram-grid.md`](64-hexagram-grid.md) | hex 之 错 / 综 / 互 algorithmic 表示 |
| [`yi-calculus-theorem.md`](yi-calculus-theorem.md) Theorem D | cuo–zong V₄ 代数 |

---

## 形式锚 (Lean modules)

- [`formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) — `cell256_yin / tou`, `cell128_flip1..6 / yin / hexCuo`，全 involutive，`atomic_all_involutive` bundle
- [`formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) — `hex_zong / hex_cuo / hex_cuoZong / hex_hu` + Cell128/Cell256 lifts + V₄ relations + hu fixed-point characterisation, `v4_outer_summary` bundle
- [`formal/SSBX/Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) — 源 Cell256 ops (`flip1..6`, `hexCuo / hexZong / hexHu`, `shiCuo / shiZong / shiCuoZong`)
- [`formal/SSBX/Foundation/Bagua/Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) — 源 Cell128 ops (`flip1..6`, `yin`, `hexCuo / hexZong / hexHu`)
- [`formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) — Trigram-level `dong / hua / bian` (R₃ atoms)
- [`formal/SSBX/Foundation/Yi/Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) — `Hexagram.cuo / zong / cuoZong / hu` + `hu_fixed_point`
- [`formal/SSBX/Foundation/Bagua/Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) — `parity / timeReversal / PT / yComb` (R₈-level P/T/PT/Y anchors)
