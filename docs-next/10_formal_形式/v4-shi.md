# V₄ Shi — 时态作为 Klein 四群 {道, 已, 今, 未}

> 状态：v3 canonical (2026-05-11) — Shi (时态) 之 definitive 群论刻画。Shi = V₄ Klein four-group，V₄ identity = 道 = (Z/2)⁸ origin；通过 (因, 果) ∈ Bool² emerge 自 R₇ ⊗ R₈ 双轴 tensor。
> 角色：本文是「Shi 是什么群」之专文。256 元清单与 quadrant 分布见 [`cell256-grid.md`](cell256-grid.md)；R₇/R₈ atomic 算子 印/投 见 [`yin-tou-operators.md`](yin-tou-operators.md)；(Z/2)⁸ AddCommGroup spine 见 [`cell256-algebra.md`](cell256-algebra.md)。
> 关系：替代 v1 时之 Z/3 cyclic Shi {已, 今, 未}（旧文档保留于 [`史/docs-next-pre-v3/cell192-grid_Z3-Shi_旧版.md`](../../史/docs-next-pre-v3/cell192-grid_Z3-Shi_旧版.md)）。

---

## 0. 一句话总纲

> **Shi = V₄ Klein four-group = {道, 已, 今, 未}**；V₄ identity = 道 = (因=0, 果=0)；3 个非平凡 involutions {cuo, zong, cuoZong} ↔ 物理 {P, T, PT}；与 R₆ Hexagram 张积成 R₈ Cell256 之 (Z/2)⁸ 闭合层。

---

## 1. 为什么 Z/3 是错的

v1（"Cell192 时代"）把时态编为 Z/3 cyclic 三态 {已, 今, 未}：

```
已 → 今 → 未 → 已 → ...
```

这破坏了整个 R-hierarchy 的 **(Z/2)ⁿ strict-uniform self-similarity**：

| 问题 | 后果 |
|---|---|
| Z/3 cyclic 不是 (Z/2)ⁿ | R-hierarchy 无法纯 binary 闭合；某层 size 不再 = 2ⁿ |
| 3 != 2ᵏ for any k | 无 mask-XOR 表达；算子-与-元 fusion 失效 |
| 缺 V₄ identity | 没有「永真 anchor」；fusion 之 origin 选不了 |
| 192 = 2⁶ × 3 | factorization 含非二维素因子；Pontryagin 自对偶坏 |

**v3 修正**：升 1 bit，Shi 由 {已, 今, 未} 升为 {道, 已, 今, 未}，**4 = 2² = (Z/2)²**。新元 **道** 是 V₄ Klein 四群的 identity，承担「跨时空永真 anchor」之多重身份。整个 Cell256 = (Z/2)⁸ = 256，R-hierarchy 再次纯 (Z/2)ⁿ 闭合。

详见 [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) 顶部 docstring：

> 之前版本 (Cell192.lean) 把 Shi 编为 Z/3 cyclic 是结构错误，破坏了 R-hierarchy 的 (Z/2)ⁿ 自相似闭合。本文件是 R5 真闭合版。

---

## 2. V₄ Klein 四群 — 形式定义

### 2.1 类型与构造

[`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 1：

```lean
inductive Shi : Type
  | dao   -- 道 (eternal / V₄ identity)
  | ji    -- 已 (past)
  | jin   -- 今 (present, PT)
  | wei   -- 未 (future)
  deriving Repr, DecidableEq, BEq

namespace Shi

def all : List Shi := [dao, ji, jin, wei]
theorem all_length : all.length = 4 := rfl
```

### 2.2 V₄ 群 abstract

V₄ = Z/2 × Z/2 = {e, a, b, ab}，每元素阶 ≤ 2，群表对称。Shi 之 V₄ 同构定为 (因, 果) ∈ Bool² ≅ Z/2 × Z/2：

| Shi | (因, 果) | V₄ 元 | 阶 |
|---|---|---|---|
| 道 | (0, 0) | $e$ identity | 1 |
| 已 | (1, 0) | $a = \sigma_P$ | 2 |
| 未 | (0, 1) | $b = \sigma_T$ | 2 |
| 今 | (1, 1) | $ab = \sigma_{PT}$ | 2 |

群表（V₄ 满足 $x^2 = e$ 和交换律）：

| ⊕ | 道 | 已 | 未 | 今 |
|---|---|---|---|---|
| **道** | 道 | 已 | 未 | 今 |
| **已** | 已 | 道 | 今 | 未 |
| **未** | 未 | 今 | 道 | 已 |
| **今** | 今 | 未 | 已 | 道 |

---

## 3. (因, 果) ∈ Bool² 双射 — Shi.toYinGuo / Shi.ofYinGuo

V₄ 结构通过 (因, 果) 双 bit 显式暴露。这是 **R₇ (因) + R₈ (果) 双层 emergent**——并非 R₇ 单层 atom（关键修正！）：

```lean
def toYinGuo : Shi → YinBit × GuoBit
  | .dao => (false, false)  -- 道 = V₄ identity
  | .ji  => (true,  false)  -- 已 = (有因, 无果)
  | .wei => (false, true)   -- 未 = (无因, 有果)
  | .jin => (true,  true)   -- 今 = PT 交汇 (因果俱在)

def ofYinGuo : YinBit × GuoBit → Shi
  | (false, false) => .dao
  | (true,  false) => .ji
  | (false, true)  => .wei
  | (true,  true)  => .jin
```

双向双射两个方向都被证：

```lean
theorem ofYinGuo_toYinGuo (s : Shi) : ofYinGuo (toYinGuo s) = s := by cases s <;> rfl
theorem toYinGuo_ofYinGuo (yg : YinBit × GuoBit) :
    toYinGuo (ofYinGuo yg) = yg := by rcases yg with ⟨y, g⟩; cases y <;> cases g <;> rfl
```

其中：

- `YinBit` (位 7) — 在 [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) 引入，是 R₇ 之 atom；含义 = 「过去印记」(past trace)。
- `GuoBit` (位 8) — 在 [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) 引入，是 R₈ 之 atom；含义 = 「未来投影」(future projection)。
- Shi V₄ = YinBit × GuoBit，即 **R₇ 与 R₈ 之 tensor product** emerge。

---

## 4. 三个 V₄ involutions — cuo / zong / cuoZong

### 4.1 Shi.cuo (P-like, 翻 因 轴)

```lean
def cuo : Shi → Shi
  | .dao => .ji
  | .ji  => .dao
  | .jin => .wei
  | .wei => .jin
```

字符表：

| s     | cuo s |
|-------|-------|
| 道    | 已    |
| 已    | 道    |
| 今    | 未    |
| 未    | 今    |

`cuo` 是 P (parity) 之 anchor：道 ↔ 已 (toggle 因)；今 ↔ 未 (同时 toggle 因)。在 (因, 果) coord 下相当于 $(\text{因}, \text{果}) \mapsto (\neg\text{因}, \text{果})$。

### 4.2 Shi.zong (T-like, 翻 果 轴)

```lean
def zong : Shi → Shi
  | .dao => .wei
  | .ji  => .jin
  | .jin => .ji
  | .wei => .dao
```

字符表：

| s     | zong s |
|-------|--------|
| 道    | 未     |
| 已    | 今     |
| 今    | 已     |
| 未    | 道     |

`zong` 是 T (time-reversal)：道 ↔ 未 (toggle 果)；已 ↔ 今 (同时 toggle 果)。在 (因, 果) coord 下相当于 $(\text{因}, \text{果}) \mapsto (\text{因}, \neg\text{果})$。

### 4.3 Shi.cuoZong (PT, 双轴翻)

```lean
def cuoZong : Shi → Shi
  | .dao => .jin
  | .ji  => .wei
  | .jin => .dao
  | .wei => .ji
```

字符表：

| s     | cuoZong s |
|-------|-----------|
| 道    | 今        |
| 已    | 未        |
| 今    | 道        |
| 未    | 已        |

`cuoZong` 是 PT 复合：道 ↔ 今, 已 ↔ 未。在 (因, 果) coord 下相当于 $(\text{因}, \text{果}) \mapsto (\neg\text{因}, \neg\text{果})$。

---

## 5. V₄ 关系 — Lean 形式化清单

[`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 1 给出全部 5 项 V₄ axioms 之严格证明：

| 关系 | Lean 名 | 证明 |
|---|---|---|
| `cuo² = id` | `Shi.cuo_cuo` | `by cases s <;> rfl` |
| `zong² = id` | `Shi.zong_zong` | `by cases s <;> rfl` |
| `cuoZong² = id` | `Shi.cuoZong_cuoZong` | `by cases s <;> rfl` |
| `cuo ∘ zong = zong ∘ cuo` (abelian) | `Shi.cuo_zong_comm` | `by cases s <;> rfl` |
| `cuoZong = cuo ∘ zong` (composite identity) | `Shi.cuoZong_eq_compose` | `by cases s <;> rfl` |

5 项一起就是 V₄ Klein 四群之**完整 axiomatic 描述**：3 involutions + abelian + composite。Lean 4 的 `by cases s <;> rfl` 把 4 行 enum case 折成一行 — 这是 V₄ 在 finite type 上之 "definition by exhaustion" 之 minimal certificate。

---

## 6. Hexagram 层 V₄ 与 Shi 层 V₄ — 双层 V₄

V₄ 在 R₈ 上**两次出现**：

| 层 | 元 | 结构 | 物理 anchor |
|---|---|---|---|
| **R₆ Hexagram side** | `{id, Hexagram.cuo, Hexagram.zong, Hexagram.cuoZong}` | XOR mask 与 perm 混合 | hex P/T/PT |
| **R₈ Shi side** | `{id, Shi.cuo, Shi.zong, Shi.cuoZong}` | (Z/2)² XOR (因, 果) | Shi P/T/PT |

R₈ 整体的算子族 = **V₄ × V₄** (hex + Shi)，独立张积。详 [`Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) § 2 之 `parity / timeReversal / PT / yComb`：

```lean
def parity (c : R8) : R8 := (Hexagram.cuo c.1, c.2)             -- hex side P, 保 Shi
def timeReversal (c : R8) : R8 := (Hexagram.zong c.1, c.2.zong) -- 双层 T (hex + Shi)
def PT (c : R8) : R8 := timeReversal (parity c)
def yComb (c : R8) : R8 := (Hexagram.hu c.1, c.2)               -- Y-combinator on hex; 保 Shi

theorem parity_parity (c : R8) : parity (parity c) = c
theorem timeReversal_timeReversal (c : R8) : timeReversal (timeReversal c) = c
theorem PT_PT (c : R8) : PT (PT c) = c
theorem parity_timeReversal_comm (c : R8) : parity (timeReversal c) = timeReversal (parity c)
```

注意：**Hexagram-side `cuo` 是 XOR mask (`xxxxxx`)**（atomic，详 [`operator-split.md`](operator-split.md)），但 **Hexagram-side `zong` 不是 XOR**（permutation, V₄ outer）；**Shi-side cuo / zong 都是 XOR mask**（在 (因, 果) coord 下 toggle 一轴）。这非对称性来自 hex 之 6-yao 顺序 vs Shi 之 2-bit 平铺。

---

## 7. 印 / 投 ≡ Shi.cuo / Shi.zong (legacy 等价)

[`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 1 末尾：

```lean
def yin (s : Shi) : Shi := s.cuo  -- 印 = toggle YinBit (因 axis) = Shi.cuo
def tou (s : Shi) : Shi := s.zong -- 投 = toggle GuoBit (果 axis) = Shi.zong

theorem yin_yin (s : Shi) : yin (yin s) = s := cuo_cuo s
theorem tou_tou (s : Shi) : tou (tou s) = s := zong_zong s
theorem yin_tou_comm (s : Shi) : yin (tou s) = tou (yin s) := cuo_zong_comm s
theorem yin_tou_eq_cuoZong (s : Shi) : yin (tou s) = cuoZong s
```

这是 Shi-only 之 legacy form。Phase A 之后 [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 8 把 印/投 重写为 Cell256-level XOR mask 算子（详 [`yin-tou-operators.md`](yin-tou-operators.md)）。

---

## 8. 物理 P / T / PT 对应

V₄ Klein 四群 = $\mathbb{Z}_2 \times \mathbb{Z}_2$ 是 **离散对称群中最简单的非平凡 abelian 群**；它在物理上对应：

| V₄ 元 | 物理 | Shi 之解读 |
|---|---|---|
| $e$ identity | trivial 变换 | **道** — 跨时空 anchor; 既无过去 cause 也无 future projection |
| $\sigma_P$ parity | 空间反演 | **已** — 过去封闭 (因 set) 但未来未开 (果 unset) |
| $\sigma_T$ time-reversal | 时间反演 | **未** — 未来开放 (果 set) 但无过去印记 (因 unset) |
| $\sigma_{PT}$ PT | CPT 之类比 | **今** — 因果俱在 = 现在 = 流变交汇 |

这映射在 [`yi-calculus-theorem.md`](yi-calculus-theorem.md) §12 严格化为 Theorem J（Shi V₄ emerges at R8）。

---

## 9. 道作为 V₄ identity 之 5 重身份

道 = V₄ identity 不仅是 Shi-内之单位元，更是整个 Cell256 之 **(Z/2)⁸ origin**。

[`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 7：

```lean
def origin : Cell256 := (Hexagram.qian, Shi.dao)

theorem origin_xor (c : Cell256) : xor origin c = c    -- (Z/2)⁸ identity
theorem epsAtOrigin_cayley (c : Cell256) : epsAtOrigin (cayley c) = c  -- Cayley anchor
```

5 重身份（per [`yi-RO-hierarchy.md`](yi-RO-hierarchy.md) § 5.6）：

1. **V₄ identity** — Shi 之 4 元中之 e
2. **(Z/2)⁸ origin** — Cell256 之 zero / additive identity
3. **Cayley fusion anchor** — `ε(f) = f origin` 把任何 Cell256 endo 变回 cell
4. **no-op operator** — 自身作 XOR mask 是 identity 算子
5. **永真 cell** — 跨时空 anchor，OX 字面 `oooooooo`

---

## 10. 与其他文档之关系

| 文档 | 关系 |
|---|---|
| [`yi-RO-hierarchy.md`](yi-RO-hierarchy.md) § 3.8 | R₈ 闭合层之 Shi V₄ 总论 |
| [`yi-calculus-theorem.md`](yi-calculus-theorem.md) Theorem J + §12 | Shi V₄ emerges at R8 之严格证明 |
| [`cell256-grid.md`](cell256-grid.md) | Cell256 = Hexagram × Shi 256 元清单 |
| [`yin-tou-operators.md`](yin-tou-operators.md) | 印 / 投 atomic 形式 (R₇/R₈ 各一) |
| [`cell256-algebra.md`](cell256-algebra.md) | (Z/2)⁸ AddCommGroup + Cayley 自对偶 |
| [`operator-split.md`](operator-split.md) | Atomic vs V₄Outer 之区分（Shi 全部 V₄ 都在 atomic 一侧；Hexagram 之 zong/hu 在 V4Outer） |

---

## 形式锚 (Lean modules)

- [`formal/SSBX/Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) — `Shi` inductive, V₄ ops, `toYinGuo` / `ofYinGuo`, `cuo_cuo` / `zong_zong` / `cuoZong_cuoZong` / `cuo_zong_comm` / `cuoZong_eq_compose`
- [`formal/SSBX/Foundation/Bagua/Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) — `YinBit` (R₇ 因 atom)
- [`formal/SSBX/Foundation/Bagua/Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) — `parity / timeReversal / PT / yComb`，R₈ 上 V₄ 之 P/T/PT 物理 anchor
- [`formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) — Hexagram 层 V₄ outer perms (zong / hu / cuoZong)
- [`formal/SSBX/Foundation/Hierarchy/R8_GuoHex.lean`](../../formal/SSBX/Foundation/Hierarchy/R8_GuoHex.lean) — R₈ R-index 别名 + Shi/GuoBit re-export
