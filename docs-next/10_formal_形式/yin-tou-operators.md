# 印 (yin) / 投 (tou) — R₇ 与 R₈ 的 atomic XOR-mask 算子

> 状态：v3 canonical (2026-05-11) — 印 / 投 是 R₇ / R₈ 新引入的两个 binary axes 之 atomic toggle 算子；在 Cell256 (Phase A) 上重写为 XOR-with-fixed-mask form。
> 角色：本文是 R-hierarchy 中 R₇ (R₆ → 加 因 bit) 与 R₈ (R₇ → 加 果 bit) 之 atomic 算子 spec。Shi V₄ 整体（cuo / zong / cuoZong）见 [`v4-shi.md`](v4-shi.md)；其它 atomic 与 V4Outer 算子之总览见 [`operator-split.md`](operator-split.md)；OX["..."] mask 字面量见 [`ox-notation.md`](ox-notation.md)。
> 命名约定：因 / 果 是 state attributes；印 / 投 是相应 toggle 算子（此命名 **provisional**，详见 § 7）。

---

## 0. 一句话总纲

> **印 (yin) = XOR with `yin_mask = OX["ooooooxo"]`** — toggle 因 / YinBit (位置 6, R₇ atom)；
> **投 (tou) = XOR with `tou_mask = OX["ooooooox"]`** — toggle 果 / GuoBit (位置 7, R₈ atom)；
> 两者皆 (Z/2) involutions，相互 commute，复合 `印 ∘ 投 = XOR with OX["ooooooxx"] = Shi.cuoZong` 即 V₄ 中央元 PT。

---

## 1. R₇ atom = 因 (YinBit) — 引入位置 6

[`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) § 1：

```lean
abbrev YinBit : Type := Bool
abbrev Cell128 : Type := Hexagram × YinBit
```

R₇ 比 R₆ Hexagram 多 1 bit，成为 `Cell128 = Hexagram × YinBit`。这第 7 位 binary axis 是「过去印记 / past trace」的 atomic 标记：

- `false` (= `o` in OX) — 无因 (no past trace, "unmoored")
- `true` (= `x` in OX) — 有因 (with past trace, "conditioned")

### 1.1 印 (yin) — direct form

[`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) § 3：

```lean
def yin (c : Cell128) : Cell128 := (c.1, !c.2)

theorem yin_yin (c : Cell128) : yin (yin c) = c
theorem yin_preserves_hex (c : Cell128) : (yin c).1 = c.1
```

直接 toggle YinBit；保 hexagram 部分。

### 1.2 印 — XOR mask form (Phase A)

[`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) § 7 把 印 重写为 XOR-with-mask 形式：

```lean
/-- 印 mask at R₇: only the YinBit (bit 7) is set. -/
def Cell128.yin_mask : Cell128 := (Hexagram.qian, true)

/-- 印 (mask form): XOR with the YinBit-only mask. -/
def Cell128.yinM (c : Cell128) : Cell128 := xor c yin_mask

/-- mask form coincides with the legacy direct toggle. -/
theorem Cell128.yinM_eq_yin (c : Cell128) : yinM c = yin c

theorem Cell128.yinM_yinM (c : Cell128) : yinM (yinM c) = c
```

`yin_mask = (qian, true)` 在 OX 表示下是字面量 `"ooooooo" + "x" → "oooooox"` (注：Cell128 是 7-bit 长度；类似的 8-bit Cell256 mask 见下)。

---

## 2. R₈ atom = 果 (GuoBit) — 引入位置 7

[`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 1：

```lean
abbrev GuoBit : Type := Bool
abbrev Cell256 : Type := Hexagram × Shi
```

R₈ 比 R₇ 再多 1 bit (GuoBit)，封装为 Shi V₄。Shi 之 (因, 果) ∈ Bool² 双射详见 [`v4-shi.md`](v4-shi.md) § 3。

GuoBit 是「未来投影 / future projection」的 atomic 标记：

- `false` (= `o` in OX, 位置 7) — 无果 (no future projection)
- `true` (= `x` in OX, 位置 7) — 有果 (with future projection)

---

## 3. Cell256 上 印 / 投 — XOR mask form (Phase A)

[`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 8 把 R₇/R₈ 两个 atom 都重写为 Cell256-level XOR with fixed masks：

```lean
/-- 印 mask: only the YinBit (因 axis, R₇ atom) is set.
    `(qian, ji) = (qian, (1, 0)) = "ooooooxo"`. -/
def Cell256.yin_mask : Cell256 := (Hexagram.qian, Shi.ji)

/-- 投 mask: only the GuoBit (果 axis, R₈ atom) is set.
    `(qian, wei) = (qian, (0, 1)) = "ooooooox"`. -/
def Cell256.tou_mask : Cell256 := (Hexagram.qian, Shi.wei)

/-- 印 (yìn) at Cell256: XOR with the YinBit-only mask. -/
def Cell256.yin (c : Cell256) : Cell256 := xor c yin_mask

/-- 投 (tóu) at Cell256: XOR with the GuoBit-only mask. -/
def Cell256.tou (c : Cell256) : Cell256 := xor c tou_mask
```

### 3.1 OX 字面对应

| 算子 | mask | OX 字面 | 翻位 |
|---|---|---|---|
| 印 (yin) | `(qian, Shi.ji)` | `OX["ooooooxo"]` | YinBit / 因 axis (位置 6) |
| 投 (tou) | `(qian, Shi.wei)` | `OX["ooooooox"]` | GuoBit / 果 axis (位置 7) |
| 印 ∘ 投 | `(qian, Shi.jin)` | `OX["ooooooxx"]` | (因 + 果) 双轴 = V₄ central element / cuoZong |

### 3.2 Lean 形式锚 — involutions + commute + composite

[`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 8：

```lean
/-- 印 is involutive (mask is self-inverse). -/
theorem Cell256.yin_yin (c : Cell256) : yin (yin c) = c

/-- 投 is involutive. -/
theorem Cell256.tou_tou (c : Cell256) : tou (tou c) = c

/-- 印 and 投 commute (both are XOR-with-fixed-mask). -/
theorem Cell256.yin_tou_comm (c : Cell256) : yin (tou c) = tou (yin c)

/-- 印 ∘ 投 = XOR with `(qian, jin)` = the V₄ central mask. -/
theorem Cell256.yin_tou_eq_central (c : Cell256) :
    yin (tou c) = xor c (Hexagram.qian, Shi.jin)

/-- The two masks together generate the V₄ central element. -/
theorem Cell256.yin_mask_xor_tou_mask :
    xor yin_mask tou_mask = (Hexagram.qian, Shi.jin)
```

证明只用 `xor_assoc` + `xor_self` + `xor_origin` + `xor_comm` 几个 (Z/2)⁸ 群律 lemmas（详 [`cell256-algebra.md`](cell256-algebra.md) § 4–6）。

---

## 4. 与其他 atomic ops 的 commute

XOR-with-fixed-mask 之 abelian 群性质保证：印 / 投 与所有其他 atomic XOR ops（[`Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean)）pairwise commute。

`Cell256.yin_tou_comm` 是其中一个公开 sample；同样的 commute pattern 对 `flip1..flip6` (单爻翻) + `hexCuo` (整 hex 翻 = XOR with kun mask) 也都成立 — 见 [`Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) § 4 注释，及 [`operator-split.md`](operator-split.md) 之 atomic 列表。

---

## 5. 为何 印 / 投 是 R₇ / R₈ atoms

R-hierarchy 之 strict-uniform 设计要求**每加 1 bit = 1 个 atomic XOR generator**。R₆ Hexagram 已有 6 atomic 单爻 flips (`dongInner / huaInner / bianInner / dongOuter / huaOuter / bianOuter` from [`BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean)，lifted to Cell128/Cell256 as `flip1..flip6`)。

| R-layer | size | 新 binary axis | 新 atomic XOR mask |
|---|---|---|---|
| R₀ | 1 | (none) | (none) |
| R₁ | 2 | y₁ | `neg` (`x`) |
| R₂ | 4 | y₂ | (lift) |
| R₃ | 8 | y₃ | `dong / hua / bian` |
| R₄ | 16 | y₄ | (lift to Mian-axis) |
| R₅ | 32 | y₅ | (lift to 5-yao) |
| R₆ | 64 | y₆ | + outer 3 flips |
| **R₇** | **128** | **因 (YinBit)** | **印 (yin) = `OX["ooooooxo"]`** |
| **R₈** | **256** | **果 (GuoBit)** | **投 (tou) = `OX["ooooooox"]`** |

R₇ 与 R₈ 之 atomic generator 必须各对应新引入的 binary axis；`yin / tou` 即此精确意义下的 R₇/R₈ atoms — 没有它们，Cell256 上的 (Z/2)⁸ XOR generator 集就不完整。

详 [`yi-RO-hierarchy.md`](yi-RO-hierarchy.md) § 4.1：

> R₈ 之 8 atomic generators：dongInner / huaInner / bianInner / dongOuter / huaOuter / bianOuter / **印 (yìn)** / **投 (tóu)**

---

## 6. 现象学映射 — Husserl retention / protention

`yi-calculus-theorem.md` §16 的命名附录中讨论了几对替代命名：

| 候选 | 哲学 anchor | 形式 anchor |
|---|---|---|
| 因 / 果 (current) | 佛教 hetu-phala + Pearl 因果 + Aristotle 4 因 | causal DAG / lightcones |
| **印 / 投** | Husserl retention/protention; Heidegger Geworfenheit/Entwurf | signal frame buffer / predictive filter |
| 始 / 终 | Aristotle arche/telos; 系辞「原始要终」 | graph source/sink; coalgebra initial/terminal |
| 持 / 期 | 现象学 retention/protention 标准汉译 | E[X] expected value |

当前 doctrine 之 split：

- **state attributes**: 因 / 果 (作为 binary axis 之名)
- **action 算子**: 印 / 投 (toggle 那个 axis 之名)

这与 Husserl 现象学三相 retention / primalImpression / protention 之直对接 (`XinZhi.lean`) 在记号 level 已对齐：
- 印 (yin) ↔ retention（保留过去之印记 / past-trace stamp）
- 投 (tou) ↔ protention（投射未来之意向 / future-cone projection）

---

## 7. 命名 caveat (provisional)

[`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) 顶部 docstring：

> **命名 caveat (provisional)**: 因 = state attribute, 印 = action.
> 备选 (per yi-calculus-theorem.md §16): 印/投, 始/终, 持/期。
> 等 R5/R6 实战使用后回看是否改换。

[`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 1：

> **命名 caveats (provisional)**: 因/果 / 印/投 暂用，备选 印/投 (Husserl) / 始/终 (Yi-native) / 持/期 (现象学) — 详 yi-calculus-theorem.md §16.

回看时机：Cell128 / Cell256 落码 + Theorems H–K 形式化稳定后 — 当前 (2026-05-11) 形式化已稳定 (`R8_complete` 0 axiom)，可重审。

---

## 8. R₇ vs R₈ 之 印 — 名字相同，作用域不同

注意 namespace 区分：

| Lean 名 | namespace | 作用域 | 形式 |
|---|---|---|---|
| `yin` | `SSBX.Foundation.Bagua.Cell128` | Cell128 (R₇) | direct toggle `(c.1, !c.2)` |
| `Cell128.yinM` | `SSBX.Foundation.Bagua.Cell128.Cell128` | Cell128 (R₇) | XOR mask form, ≡ `yin` |
| `Cell256.yin` | `SSBX.Foundation.Bagua.Cell256.Cell256` | Cell256 (R₈) | XOR mask form on R₈ |
| `Shi.yin` | `SSBX.Foundation.Bagua.Cell256.Shi` | Shi (V₄ block 内部) | = `Shi.cuo` (legacy V₄ wrap) |

3 个 print mention "yin" 但 work on different types。Cell128 是 R₇ 上的 direct + Phase A mask form；Cell256 是 R₈ 上的 mask form (推荐版本)；Shi.yin 是 V₄ 内部 wrap (= `Shi.cuo`)。下游模块倾向用 Cell256 之 mask form，因为它直接给 (Z/2)⁸ Abelian 群 spine 上的明确 generator。

---

## 9. R₇/R₈ R-index 别名 re-export

[`R7_YinHex.lean`](../../formal/SSBX/Foundation/Hierarchy/R7_YinHex.lean) 与 [`R8_GuoHex.lean`](../../formal/SSBX/Foundation/Hierarchy/R8_GuoHex.lean) 给出 R-index navigability 的 re-export shim：

```lean
-- R7_YinHex.lean
namespace SSBX.Foundation.Hierarchy.R7
def yin (c : Cell128) : Cell128 := SSBX.Foundation.Bagua.Cell128.yin c
end

-- R8_GuoHex.lean
namespace SSBX.Foundation.Hierarchy.R8
def yin (c : Cell256) : Cell256 := Cell256.yin c  -- mask form
def tou (c : Cell256) : Cell256 := Cell256.tou c
end
```

R-index aliasing 让 `R7.yin / R8.yin / R8.tou` 直接可用，**无需 Mathlib，无新逻辑**。

---

## 10. 与其他文档之关系

| 文档 | 关系 |
|---|---|
| [`yi-RO-hierarchy.md`](yi-RO-hierarchy.md) § 3.7–3.8 | R₇ 之 印 + R₈ 之 投 之 layer-内 角色 |
| [`v4-shi.md`](v4-shi.md) | Shi V₄ 总论；印 / 投 ≡ Shi.cuo / Shi.zong (legacy) |
| [`cell256-algebra.md`](cell256-algebra.md) | (Z/2)⁸ 群律 + Phase A spine（印/投 是 generators） |
| [`ox-notation.md`](ox-notation.md) | OX[" "] mask 字面量与位 6/7 = (因, 果) 之约定 |
| [`operator-split.md`](operator-split.md) | Atomic XOR ops 总览（印/投 在 atomic 一侧） |
| [`yi-calculus-theorem.md`](yi-calculus-theorem.md) §16 | 命名 caveats 之四候选评分 |

---

## 形式锚 (Lean modules)

- [`formal/SSBX/Foundation/Bagua/Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) — `YinBit`, `yin` (direct), `Cell128.yin_mask`, `Cell128.yinM` (mask form), `yinM_eq_yin`, `cell128_phaseA_summary`
- [`formal/SSBX/Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) — `GuoBit`, `Cell256.yin_mask` / `tou_mask`, `Cell256.yin / tou` (mask form), `yin_yin / tou_tou / yin_tou_comm / yin_tou_eq_central / yin_mask_xor_tou_mask`
- [`formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) — `cell256_yin / cell256_tou`, `cell128_yin`, `atomic_all_involutive` bundle
- [`formal/SSBX/Foundation/Hierarchy/R7_YinHex.lean`](../../formal/SSBX/Foundation/Hierarchy/R7_YinHex.lean) — R₇ R-index alias (`R7.yin`)
- [`formal/SSBX/Foundation/Hierarchy/R8_GuoHex.lean`](../../formal/SSBX/Foundation/Hierarchy/R8_GuoHex.lean) — R₈ R-index alias (`R8.yin / R8.tou`)
- [`formal/SSBX/Foundation/Notation/OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) — `OX["ooooooxo"]` / `OX["ooooooox"]` / `OX["ooooooxx"]` 字面量
