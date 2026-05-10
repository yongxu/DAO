# Cell256 256-格全表 — R₈ = Hexagram × Shi 闭合层

> 状态：v3 定本 (2026-05-11)
> 父文档：[yi-RO-hierarchy.md](yi-RO-hierarchy.md) (R₀..R₈ strict-uniform 定义) · [yi-calculus-theorem.md](yi-calculus-theorem.md) Theorems H–K (R₇/R₈ 拆层 + (Z/2)⁸ closure)
>
> 作用：把 R₈ = Cell256 = Hexagram × Shi (V₄) = (Z/2)⁸ = 256 一格不漏地展开。本文是 R-hierarchy 闭合层的**几何 / 枚举 / 代数**全表，三种视角并存：
>   1. **几何**：4 BenZheng 象限 × 4 V₄ Shi = 16 super-cells × 16 cells = 256
>   2. **枚举**：256 格按 (hex, shi) 二维定位
>   3. **代数**：Cell256 = (Z/2)⁸ Abelian 群 + Cayley 自作用 + 道 origin
>
> 配套 v3 兄弟文档：[ox-notation.md](ox-notation.md) · [shi-v4.md](shi-v4.md) · [r5-wuyao-provisional.md](r5-wuyao-provisional.md) · [r7-yin-r8-guo.md](r7-yin-r8-guo.md) · [lift-project.md](lift-project.md) · [yi-bagua.md](yi-bagua.md) · [64-hexagram-grid.md](64-hexagram-grid.md) · [sanben-sijieduan-grid.md](sanben-sijieduan-grid.md)
> 形式锚：[`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) · [`Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) · [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) · [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean)
> 表格全表：[`表六_256格全表.md`](表六_256格全表.md)（per-cell 标注 — 由 `表六_192格全表.md` 升级而来）

---

## 0. 命题摘要 (TL;DR)

```
R₈ = Cell256 = Hexagram × Shi
            = (Z/2)⁶  ×  V₄
            = 64       ×  4
            = 256     格
            = (Z/2)⁸ Abelian 群 (componentwise XOR)
            = Cayley 自作用 + 道 (qian, dao) origin
```

256 格 = 64 BenZheng-quadrant × Shi V₄ 之 tensor 全枚举。

| 维度 | 来源 | 群 | 元数 |
|---|---|---|---|
| Hex side | R₆ Hexagram = 6-yao | (Z/2)⁶ | 64 |
| Shi side | R₇ 因 ⊗ R₈ 果 emerge | V₄ = (Z/2)² | 4 |
| Cell256 | tensor product | (Z/2)⁸ | **256** |

**16 super-cells** = 4 BenZheng quadrants × 4 V₄ Shi = 4 × 4。每 super-cell 16 元 = 16 hex/quadrant × 1 Shi 状态。

```
256 = 16 super-cells × 16 cells = (4 quadrant × 4 Shi) × 16
    = 4 quadrant × 64 Shi-trajectories
    = 64 hex × 4 Shi-states
```

---

## 1. 三层结构

### 1.1 第一层：64 卦 × 4 时态 (cardinality view)

每个 hex `h ∈ Hexagram` 配 4 个 Shi state, 共 64 × 4 = 256.

```
(乾, 道) (乾, 已) (乾, 今) (乾, 未)         -- "永真乾" + 3 时态化乾
(坤, 道) (坤, 已) (坤, 今) (坤, 未)
(屯, 道) (屯, 已) (屯, 今) (屯, 未)
...
(未济, 道) (未济, 已) (未济, 今) (未济, 未)
```

64 hex × 4 Shi = 256 cells. 每行展开:
- **(h, 道)** = 永真 anchor of h — V₄ 单位元 / "atemporal" position
- **(h, 已)** = h 之 past-closed slice (P, parity-like)
- **(h, 未)** = h 之 future-open slice (T, time-reversal-like)
- **(h, 今)** = h 之 PT 交汇 = "present"

### 1.2 第二层：4 BenZheng quadrants × 4 V₄ Shi = 16 super-cells

每 super-cell = 4 BenZheng quadrant × 1 V₄ Shi 元，含 16 cells。

```
(本本, 道) (本本, 已) (本本, 今) (本本, 未)        16 ↑↑↑↑
(本征, 道) (本征, 已) (本征, 今) (本征, 未)        4 super-cells × 4 Shi
(征本, 道) (征本, 已) (征本, 今) (征本, 未)        各 16 cells
(征征, 道) (征征, 已) (征征, 今) (征征, 未)
```

每行 4 个 super-cell（Shi 不同），每列 4 个 super-cell（quadrant 不同）。**16 super-cells × 16 cells/super-cell = 256**.

### 1.3 第三层：Mian × Shi (内存视角)

R₄ Mian = Ben × Zheng = 16 (BenZheng.lean)。一个 hex 在 4 quadrant 内之具体定位 = (innerType, outerType) ∈ Ben × Zheng × Ben × Zheng （4 selections, 16 each）；折回到 R₆ 即 16 hex / quadrant.

Cell256 view: **R₆ × R₂(Shi)** = 64 × 4 = 256 = R₈.

但若按 Mian × Mian × Shi：16 × 16 × 4 = 1024 不对 — 因为 hex 不是 Mian × Mian 的 4-tuple，而是 (inner_trigram, outer_trigram) ∈ Trigram × Trigram = 8 × 8 = 64. 而 inner_trigram ∈ {本} ⊔ {征} (4+4 = 8)，outer 同；4 quadrant × 4 inner-本征 × 4 outer-本征 / quadrant 之具体细分对应 16 hex / quadrant。

---

## 2. Lean 形式签名

### 2.1 Cell256 类型

```lean
-- formal/SSBX/Foundation/Bagua/Cell256.lean
abbrev Cell256 : Type := Hexagram × Shi

inductive Shi : Type
  | dao   -- 道 (V₄ identity, 永真)
  | ji    -- 已 (past, P)
  | jin   -- 今 (present, PT)
  | wei   -- 未 (future, T)
  deriving Repr, DecidableEq, BEq

-- |Cell256| = 256
theorem Cell256.all_length : Cell256.all.length = 256 := by native_decide
theorem Cell256.all_nodup   : Cell256.all.Nodup       := by native_decide
theorem Cell256.mem_all     : ∀ c : Cell256, c ∈ Cell256.all
```

### 2.2 V₄ Klein on Shi

```lean
def Shi.cuo : Shi → Shi      -- P (因-axis flip): 道↔已, 未↔今
def Shi.zong : Shi → Shi     -- T (果-axis flip): 道↔未, 已↔今
def Shi.cuoZong : Shi → Shi  -- PT (双轴翻):       道↔今, 已↔未

theorem Shi.cuo_cuo     (s : Shi) : cuo (cuo s) = s
theorem Shi.zong_zong   (s : Shi) : zong (zong s) = s
theorem Shi.cuoZong_cuoZong (s : Shi) : cuoZong (cuoZong s) = s
theorem Shi.cuo_zong_comm (s : Shi) : cuo (zong s) = zong (cuo s)
theorem Shi.cuoZong_eq_compose (s : Shi) : cuoZong s = cuo (zong s)
```

### 2.3 (因, 果) bijection

```lean
def Shi.toYinGuo  : Shi → YinBit × GuoBit
  | .dao => (false, false)  -- (无因, 无果) = V₄ identity
  | .ji  => (true,  false)  -- (有因, 无果) = past-closed (P)
  | .wei => (false, true)   -- (无因, 有果) = future-open (T)
  | .jin => (true,  true)   -- (有因, 有果) = PT 交汇

def Shi.ofYinGuo : YinBit × GuoBit → Shi
theorem Shi.ofYinGuo_toYinGuo (s : Shi)             : ofYinGuo (toYinGuo s) = s
theorem Shi.toYinGuo_ofYinGuo (yg : YinBit × GuoBit) : toYinGuo (ofYinGuo yg) = yg
```

### 2.4 (Z/2)⁸ Abelian 群 + Cayley 自作用 (Phase A spine)

```lean
-- componentwise XOR on Cell256 = Hexagram × Shi
def Cell256.xor (c1 c2 : Cell256) : Cell256

-- 道 cell at R₈ = (qian, dao) = (Z/2)⁸ identity
def Cell256.origin : Cell256 := (Hexagram.qian, Shi.dao)

instance : Add  Cell256 := ⟨Cell256.xor⟩
instance : Zero Cell256 := ⟨Cell256.origin⟩
instance : Neg  Cell256 := ⟨id⟩          -- (Z/2)ⁿ self-inverse
instance : Sub  Cell256 := ⟨Cell256.xor⟩
instance : SMul Cell256 Cell256 := ⟨Cell256.xor⟩  -- Cayley 自作用

theorem Cell256.origin_xor (c : Cell256) : xor origin c = c
theorem Cell256.xor_self   (c : Cell256) : xor c c = origin
theorem Cell256.xor_comm   (c1 c2 : Cell256) : xor c1 c2 = xor c2 c1
theorem Cell256.xor_assoc  (c1 c2 c3 : Cell256) : xor (xor c1 c2) c3 = xor c1 (xor c2 c3)

-- Cayley regular representation
def Cell256.cayley (c : Cell256) : Cell256 → Cell256 := fun s => xor c s
def Cell256.epsAtOrigin (f : Cell256 → Cell256) : Cell256 := f origin

theorem Cell256.epsAtOrigin_cayley (c : Cell256) : epsAtOrigin (cayley c) = c
theorem Cell256.cayley_inj : Function.Injective Cell256.cayley
theorem Cell256.cayley_hom (c1 c2 : Cell256) :
    cayley (xor c1 c2) = cayley c1 ∘ cayley c2
```

### 2.5 印 / 投 atomic operators (XOR mask form)

```lean
def Cell256.yin_mask : Cell256 := (Hexagram.qian, Shi.ji)   -- 因-轴 only
def Cell256.tou_mask : Cell256 := (Hexagram.qian, Shi.wei)  -- 果-轴 only

def Cell256.yin (c : Cell256) : Cell256 := xor c yin_mask  -- 印 = toggle 因
def Cell256.tou (c : Cell256) : Cell256 := xor c tou_mask  -- 投 = toggle 果

theorem Cell256.yin_yin (c : Cell256) : yin (yin c) = c
theorem Cell256.tou_tou (c : Cell256) : tou (tou c) = c
theorem Cell256.yin_tou_comm (c : Cell256) : yin (tou c) = tou (yin c)

-- 印 ∘ 投 = XOR with V₄ central element (qian, jin) = `oooooooxx` 
theorem Cell256.yin_tou_eq_central (c : Cell256) :
    yin (tou c) = xor c (Hexagram.qian, Shi.jin)
```

---

## 3. Shi V₄ 之 (因, 果) emergence — 一图全清

```
        Shi V₄ = R₇.因 ⊗ R₈.果 emergence (R₇/R₈ 双 axis)

        果\因   |   0 (无因)    |   1 (有因)
        ────────┼──────────────┼──────────────
        0 (无果)|   道 (V₄ id) │   已 (P)
        1 (有果)|   未 (T)     │   今 (PT)
```

| Shi | (因, 果) | V₄ 元 | 物理 anchoring | OX 后 2 位 mask |
|---|---|---|---|---|
| **道** | (0, 0) | $e$ (identity) | 无因无果 — 跨时空永真 / V₄ 单位元 | `oo` |
| **已** | (1, 0) | $\sigma_P$ | 有因无果 — 过去封闭 (parity-like) | `xo` |
| **未** | (0, 1) | $\sigma_T$ | 无因有果 — 未来开放 (time-reversal-like) | `ox` |
| **今** | (1, 1) | $\sigma_{PT}$ | 因果俱在 — "现在"即 PT 交汇 | `xx` |

V₄ Klein 群表 ($\sigma_P^2 = \sigma_T^2 = \sigma_{PT}^2 = e$, $\sigma_P \sigma_T = \sigma_{PT}$):

| ∘ | 道 | 已 | 未 | 今 |
|---|---|---|---|---|
| **道** | 道 | 已 | 未 | 今 |
| **已** | 已 | 道 | 今 | 未 |
| **未** | 未 | 今 | 道 | 已 |
| **今** | 今 | 未 | 已 | 道 |

详见 [shi-v4.md](shi-v4.md) (V₄ Klein structure 专文) + [r7-yin-r8-guo.md](r7-yin-r8-guo.md) (R₇/R₈ atomic axes 因/果 详尽剖析)。

---

## 4. 道-row：64 个永真 anchor

**道-row** = (h, 道) for all h ∈ Hexagram —— 64 cells, V₄ 单位元 row。

意义：每 hex h 都有自己的「永真版本」 (h, 道) — 它是 h 之 R₈-cell **不受 causation flow 约束**之状态。

| # | 卦 | (h, 道) cell | 解读 |
|---|---|---|---|
| 1 | 乾 | (乾, 道) | 「实在」之永真 atomic state |
| 2 | 坤 | (坤, 道) | 「受成」之永真 atomic state |
| 11 | 泰 | (泰, 道) | 「通畅」之永真 atomic state — 通本身是恒态 |
| 12 | 否 | (否, 道) | 「否塞」之永真 atomic state |
| 29 | 坎 | (坎, 道) | 「重险」之永真 atomic state |
| 30 | 离 | (离, 道) | 「重明」之永真 atomic state |
| 63 | 既济 | (既济, 道) | 「已决」之永真 atomic state — 完成之"模板" |
| 64 | 未济 | (未济, 道) | 「未决」之永真 atomic state — 未完成之"原型" |

道-row 之 64 cells 是 R₈ 之**「描述者本身永在 anchor」**集合 — Cell192 时代不可表达 (Cell192 只有 {已, 今, 未} 之 Z/3 cyclic, 无 V₄ 单位元), Cell256 让其 first-class 入本体。

完整 64 个 (h, 道) cell 列表见 [`表六_256格全表.md`](表六_256格全表.md) 第 1 节。

---

## 5. 已 / 未 / 今 三 row：P / T / PT slices

### 5.1 已-row (P slice)

(h, 已) for all h ∈ Hexagram = 64 cells — past-closed slice.

| # | 卦 | (h, 已) cell | (因, 果) | 解读 |
|---|---|---|---|---|
| 1 | 乾 | (乾, 已) | (1, 0) | 「实在」之已成态 |
| 2 | 坤 | (坤, 已) | (1, 0) | 「受成」之已成态 |
| 11 | 泰 | (泰, 已) | (1, 0) | 「通畅」过去封闭 — 已通而不再延展 |
| 63 | 既济 | (既济, 已) | (1, 0) | 「已决」+ past closed = 完全确定 |

### 5.2 未-row (T slice)

(h, 未) for all h ∈ Hexagram = 64 cells — future-open slice.

| # | 卦 | (h, 未) cell | (因, 果) | 解读 |
|---|---|---|---|---|
| 1 | 乾 | (乾, 未) | (0, 1) | 「实在」之未来投射 — 无过去印记 |
| 64 | 未济 | (未济, 未) | (0, 1) | 「未决」+ future open = 双重未定 |

### 5.3 今-row (PT slice)

(h, 今) for all h ∈ Hexagram = 64 cells — PT 交汇 = "present"。

| # | 卦 | (h, 今) cell | (因, 果) | 解读 |
|---|---|---|---|---|
| 1 | 乾 | (乾, 今) | (1, 1) | 「实在」之 PT 交汇 — 因果俱在 |
| 11 | 泰 | (泰, 今) | (1, 1) | 「通畅」之 present moment |
| 63 | 既济 | (既济, 今) | (1, 1) | 「已决」之"刚刚成"的瞬间 |
| 64 | 未济 | (未济, 今) | (1, 1) | 「未决」之"正在"的瞬间 |

**4 个 row 严格不交且全枚举**：
$$\bigsqcup_{s \in \mathcal{S}} \{(h, s) : h \in \mathcal{H}\} = \mathcal{R}_8, \quad |row| = 64, \text{ # rows} = 4$$

---

## 6. 16-grid view: BenZheng quadrant × Shi V₄

把 64 hex 按 BenZheng quadrant 分为 4 × 16, 把 4 Shi 沿正交轴排, 得 4×4 = **16 super-cells**, 每 super-cell 含 **16 cells**。

```
                    Shi axis (V₄)
                    道       已       今       未
                  ┌────────┬────────┬────────┬────────┐
       本本(16)  │  16    │  16    │  16    │  16    │  ← 64-row
                  ├────────┼────────┼────────┼────────┤
       本征(16)  │  16    │  16    │  16    │  16    │  ← 64-row
                  ├────────┼────────┼────────┼────────┤
       征本(16)  │  16    │  16    │  16    │  16    │  ← 64-row
                  ├────────┼────────┼────────┼────────┤
       征征(16)  │  16    │  16    │  16    │  16    │  ← 64-row
                  └────────┴────────┴────────┴────────┘
                    64       64       64       64       (Shi-column counts)
                  total: 4 × 4 × 16 = 256
```

每 super-cell label: `(quadrant, shi)`，16 cells per super-cell。

### 6.1 16 super-cells 全枚举

| super-cell | quadrant | shi | hex 数 | label |
|---|---|---|---|---|
| 1 | 本本 | 道 | 16 | "实在道" |
| 2 | 本本 | 已 | 16 | "实在已" |
| 3 | 本本 | 今 | 16 | "实在今" |
| 4 | 本本 | 未 | 16 | "实在未" |
| 5 | 本征 | 道 | 16 | "改之道" |
| 6 | 本征 | 已 | 16 | "改之已" |
| 7 | 本征 | 今 | 16 | "改之今" |
| 8 | 本征 | 未 | 16 | "改之未" |
| 9 | 征本 | 道 | 16 | "造之道" |
| 10 | 征本 | 已 | 16 | "造之已" |
| 11 | 征本 | 今 | 16 | "造之今" |
| 12 | 征本 | 未 | 16 | "造之未" |
| 13 | 征征 | 道 | 16 | "动之道" |
| 14 | 征征 | 已 | 16 | "动之已" |
| 15 | 征征 | 今 | 16 | "动之今" |
| 16 | 征征 | 未 | 16 | "动之未" |

合计 16 × 16 = 256.

### 6.2 一个 super-cell 之 16 cells 完全展开 (本本, 道)

本本 quadrant 内 16 hex（按 King Wen 序）见 [64-hexagram-grid.md §1](64-hexagram-grid.md)：

```
1乾   2坤   5需   6讼   7师   8比   11泰  12否
13同人 14大有 29坎  30离  35晋  36明夷 63既济 64未济
```

配 Shi=道，得 (本本, 道) super-cell 的 16 cells:

| # | 卦 | Shi | Cell256 元 | 形式 |
|---|---|---|---|---|
| 1 | 乾 | 道 | (乾, 道) | ⊤ / unit · 永真 |
| 2 | 坤 | 道 | (坤, 道) | ⊥ / void · 永真 |
| 5 | 需 | 道 | (需, 道) | Future T · 永真 |
| 6 | 讼 | 道 | (讼, 道) | type mismatch · 永真 |
| 7 | 师 | 道 | (师, 道) | quotient · 永真 |
| 8 | 比 | 道 | (比, 道) | binary relation · 永真 |
| 11 | 泰 | 道 | (泰, 道) | g∘f succeeds · 永真 |
| 12 | 否 | 道 | (否, 道) | composition blocked · 永真 |
| 13 | 同人 | 道 | (同人, 道) | Equiv · 永真 |
| 14 | 大有 | 道 | (大有, 道) | Sigma · 永真 |
| 29 | 坎 | 道 | (坎, 道) | List/Stream nesting · 永真 |
| 30 | 离 | 道 | (离, 道) | Kleene star · 永真 |
| 35 | 晋 | 道 | (晋, 道) | Functor.map · 永真 |
| 36 | 明夷 | 道 | (明夷, 道) | private · 永真 |
| 63 | 既济 | 道 | (既济, 道) | ⊨ · 永真 |
| 64 | 未济 | 道 | (未济, 道) | ⊭ · 永真 |

读法：「这 16 cells 是 value-semantic kernel 在 V₄ identity 下的"永真版本"——formal logic 之 16 个 atomic 真值类型自身。」

### 6.3 全部 16 super-cells 之 hex 内容

256 cells = 4 quadrants × 16 hex × 4 Shi。每 quadrant 之 16 hex 列表见 [64-hexagram-grid.md](64-hexagram-grid.md) §1–§4。本节只列每 super-cell 之 cardinality + cuo/zong invariant。

| quadrant | hex 列表（按 King Wen 序）| 16-cell # |
|---|---|---|
| **本本** | 1乾 2坤 5需 6讼 7师 8比 11泰 12否 13同人 14大有 29坎 30离 35晋 36明夷 63既济 64未济 | 16 |
| **本征** | 4蒙 9小畜 16豫 20观 22贲 23剥 26大畜 34大壮 37家人 40解 43夬 45萃 47困 49革 55丰 59涣 | 16 |
| **征本** | 3屯 10履 15谦 19临 21噬嗑 24复 25无妄 33遁 38睽 39蹇 44姤 46升 48井 50鼎 56旅 60节 | 16 |
| **征征** | 17随 18蛊 27颐 28大过 31咸 32恒 41损 42益 51震 52艮 53渐 54归妹 57巽 58兑 61中孚 62小过 | 16 |

每 quadrant 16 hex × 4 Shi = 64 cells per quadrant × 4 quadrants = 256.

详见 [`表六_256格全表.md`](表六_256格全表.md) — per-cell 表，含 (hex, shi) ⊕ 形式 type ⊕ (因, 果) ⊕ V₄ orbit 等多列。

---

## 7. 算子代数 (R₈ level)

### 7.1 三大算子家族

**A. Within-layer XOR subgroup of Cell256** (8 atomic generators, (Z/2)⁸ Abelian)：

| Generator | OX mask | 翻位 | 作用 |
|---|---|---|---|
| dongInner | `xooooooo` | y₁ (初爻) | 翻初爻 |
| huaInner | `oxoooooo` | y₂ (二爻) | 翻二爻 (中爻 inner) |
| bianInner | `ooxooooo` | y₃ (三爻) | 翻三爻 |
| dongOuter | `oooxoooo` | y₄ (四爻) | 翻四爻 |
| huaOuter | `ooooxooo` | y₅ (五爻) | 翻五爻 (中爻 outer) |
| bianOuter | `oooooxoo` | y₆ (上爻) | 翻上爻 |
| 印 (yìn) | `ooooooxo` | y₇ (因) | 翻 YinBit (R₇ atom) |
| 投 (tóu) | `ooooooox` | y₈ (果) | 翻 GuoBit (R₈ atom) |

8 generators 完全生成 (Z/2)⁸ XOR subgroup。

**B. V₄ outer 在 Hex side**：

| 算子 | 类型 | 物理 | 作用 |
|---|---|---|---|
| Hexagram.cuo | XOR mask `xxxxxxoo` | P | 6-yao 全反, 保 quadrant |
| Hexagram.zong | non-XOR perm | T | y_i → y_{7-i}, 跨换本征/征本 |
| Hexagram.cuoZong | composite | PT | cuo ∘ zong |
| Hexagram.hu | non-XOR perm | Y (Y-comb) | (y₂,y₃,y₄,y₃,y₄,y₅), {乾,坤} fixed; {既济, 未济} 2-cycle |

**C. V₄ Klein 在 Shi side** (cuo/zong/cuoZong on V₄)：

| 算子 | (因, 果) action | 物理 |
|---|---|---|
| Shi.cuo | toggle 因 | P (= 印) |
| Shi.zong | toggle 果 | T (= 投) |
| Shi.cuoZong | toggle 因 ⊕ 果 | PT (= 印∘投) |

### 7.2 Hex × Shi tensor 之 V₄ × V₄ 双层结构

Cell256 上同时存在两种 V₄ — 它们正交：

```
hex-V₄  on Hexagram side:    {id, cuo₆, zong₆, cuoZong₆}  ← acts on (h, _)
shi-V₄  on Shi side:         {id, cuo_S, zong_S, cuoZong_S}  ← acts on (_, s)

⇒ V₄ × V₄ ≅ (Z/2)⁴ acts on Cell256 = 16 outer symmetries
```

```lean
-- Cell256 lateral operators (combined)
def Cell256.shiCuo     (c : Cell256) : Cell256 := (c.1,           c.2.cuo)
def Cell256.shiZong    (c : Cell256) : Cell256 := (c.1,           c.2.zong)
def Cell256.hexCuo     (c : Cell256) : Cell256 := (Hexagram.cuo c.1, c.2)
def Cell256.hexZong    (c : Cell256) : Cell256 := (Hexagram.zong c.1, c.2)
def Cell256.hexHu      (c : Cell256) : Cell256 := (Hexagram.hu c.1,   c.2)
def Cell256.flip1..6   (c : Cell256) : Cell256 := (single-yao flip on c.1, c.2)
```

**核心交换性** (tensor structure):

```lean
theorem Cell256.hexCuo_shiCuo_comm (c : Cell256) :
    hexCuo (shiCuo c) = shiCuo (hexCuo c)
theorem Cell256.hexZong_shiZong_comm (c : Cell256) :
    hexZong (shiZong c) = shiZong (hexZong c)
```

⇒ Hex 与 Shi 之 V₄ 完全独立, 总 V₄ × V₄ = (Z/2)⁴ Abelian。

### 7.3 Cayley 自对偶 — R₈ 闭合

```
ι : Cell256 → Aut(Cell256), c ↦ (· ⊕ c)
ε : Aut(Cell256) → Cell256, f ↦ f(origin)

ε ∘ ι = id (retraction, proved as Cell256.epsAtOrigin_cayley)
ι 单射 (Cell256.cayley_inj)
ι 同态 (Cell256.cayley_hom)
```

**结论**：Cell256 ≅ XOR(Cell256) 严格同构。元 ≅ 算子，fusion 闭合 — R₈ 之 (Z/2)⁸ self-action 完整。

---

## 8. (因, 果) 投影 — 256 → 4 之总析

把 Cell256 投影到 Shi 维度，得 4-block 划分:

| 投影 | block 大小 | 性质 |
|---|---|---|
| π_道(Cell256) = (h, 道) for h ∈ Hex | 64 | 永真 anchor row, V₄ 单位元 row |
| π_已(Cell256) = (h, 已) for h ∈ Hex | 64 | P-row, past-closed |
| π_未(Cell256) = (h, 未) for h ∈ Hex | 64 | T-row, future-open |
| π_今(Cell256) = (h, 今) for h ∈ Hex | 64 | PT-row, present |

256 = 64 + 64 + 64 + 64. 4 row 严格不交。

类似把 Cell256 投影到 BenZheng quadrant 维:

| 投影 | block 大小 | hex 集 |
|---|---|---|
| π_本本 | 64 = 16 hex × 4 Shi | 本本 16 hex |
| π_本征 | 64 = 16 hex × 4 Shi | 本征 16 hex |
| π_征本 | 64 = 16 hex × 4 Shi | 征本 16 hex |
| π_征征 | 64 = 16 hex × 4 Shi | 征征 16 hex |

---

## 9. 算子在 16-grid 上的 invariant

### 9.1 Hex-side 算子 在 quadrant × shi 上

| 算子 | quadrant | shi | 作用 |
|---|---|---|---|
| Hexagram.cuo | **保** | 不动 | Theorem F (BenZheng): cuo_preserves_quadrant |
| Hexagram.zong | 本本/征征自闭, 本征↔征本 | 不动 | Theorem F: zong_swap_benZheng_to_zhengBen |
| Hexagram.hu | hu attractors {乾, 坤, 既济, 未济} ⊂ 本本 | 不动 | hu_attractors_in_benBen |
| huaInner / huaOuter (中爻 flip) | **保** quadrant | 不动 | huaInner_preserves_quadrant |
| dongInner / bianInner / dongOuter / bianOuter | 跨 quadrant | 不动 | dong_flips_isZongFixed |

### 9.2 Shi-side 算子 在 quadrant × shi 上

| 算子 | quadrant | shi | 作用 |
|---|---|---|---|
| Shi.cuo (= 印) | 不动 | 道↔已, 未↔今 | toggle 因 |
| Shi.zong (= 投) | 不动 | 道↔未, 已↔今 | toggle 果 |
| Shi.cuoZong | 不动 | 道↔今, 已↔未 | toggle 因 ⊕ 果 |

### 9.3 hu attractor row in (本本, 道) super-cell

hu 之 4 attractors {1乾, 2坤, 63既济, 64未济} 全在本本 quadrant; 配 Shi=道 给一组**道-row hu fixed-point** sub-set:

```
{(乾, 道), (坤, 道), (既济, 道), (未济, 道)} ⊂ (本本, 道) super-cell
```

这 4 cells 是 R₈ 之**绝对 anchor 子集** — hu-fixed + V₄-identity (Shi=道) 双重稳定。

形式上：
```lean
-- hu fixed:
theorem qian_quadrant : Hexagram.qian.quadrant = .benBen  -- by native_decide
theorem kun_quadrant  : Hexagram.kun.quadrant  = .benBen
theorem jiji_quadrant : Hexagram.jiji.quadrant = .benBen
theorem weiji_quadrant: Hexagram.weiji.quadrant = .benBen
theorem hu_attractors_in_benBen : ...  -- 4 conjuncts
theorem jiji_hu_eq_weiji : Hexagram.jiji.hu = Hexagram.weiji  -- by rfl
theorem weiji_hu_eq_jiji : Hexagram.weiji.hu = Hexagram.jiji  -- by rfl
```

所以 Cell256 之**「最稳 anchor」** = (乾, 道), (坤, 道), (既济, 道), (未济, 道) 4 cells — Cayley center + hu center 之交集。

---

## 10. R₇ vs R₈：因 / 果 之 cumulative emergence

R₇ Cell128 = Hexagram × YinBit = 128, 引入第 7 个 binary axis "因".

R₈ Cell256 = Cell128 × GuoBit = 256, 引入第 8 个 binary axis "果".

**Cell256 是 Cell128 之 lift**:

```lean
abbrev Cell128 : Type := Hexagram × YinBit
abbrev Cell256 : Type := Hexagram × Shi
-- Bijection: Cell256 ≅ Cell128 × GuoBit
-- via Shi ≅ YinBit × GuoBit (Shi.toYinGuo / ofYinGuo)
```

视图对照：

| 层 | 类型 | 群 | 形式 carrier | 主 atom |
|---|---|---|---|---|
| R₆ | Hexagram | (Z/2)⁶ | 64 | y₁..y₆ |
| **R₇** | Cell128 | (Z/2)⁷ | 128 | + 因 (yīn) |
| **R₈** | Cell256 | (Z/2)⁸ | 256 | + 果 (guǒ) |

R₈ 闭合 = (Z/2)⁸ self-action 之自然 8-bit 终点 = ASCII 字符空间之 cardinality。详见 [r7-yin-r8-guo.md](r7-yin-r8-guo.md)。

---

## 11. 256-tree (root-to-256 prefix tree)

Cell256 之 8-bit binary tree decomposition:

```
                              root (1)
                             /        \
                          o (yang)   x (yin)        ← y₁ (R₁ → 2)
                        /  \         /   \
                       ...                    ← y₂..y₆ levels
                                               ← R₆ = 64
                       /  \  ...
                       因=0  因=1               ← y₇ (R₇ = 128)
                       /  \                     ← y₈ (R₈ = 256)
                       果=0 果=1
```

```lean
-- Cell256.lean
def Cell256.rootTo256TreeLevelCounts : List Nat :=
  [1, 2, 4, 8, 16, 32, 64, 128, 256]
theorem Cell256.rootTo256TreeLevelCounts_sum :
    rootTo256TreeLevelCounts.sum = 511 := by native_decide
theorem Cell256.rootTo256TreeEdgeCount :
    2 + 4 + 8 + 16 + 32 + 64 + 128 + 256 = 510 := by native_decide
```

9 levels (root + 8 binary axes), 256 leaves at depth 8。Pure (Z/2)⁸ binary tree — 没有 Z/3 异类层。

---

## 12. 与 Cell192 之关系 (历史 superseded)

旧 Cell192 = Hexagram × Shi_old, 其中 Shi_old = Z/3 cyclic {已, 今, 未} (无 道)。

修正：**Cell192 已废弃** (2026-05-10/11)，`Cell192.lean` 已删除。

```
Cell192 (旧, 192 cells, Z/3 Shi {已,今,未})  →  Cell256 (新, 256 cells, V₄ Shi {道,已,今,未})
```

迁移要点：

| 旧 (Cell192) | 新 (Cell256) | 改变 |
|---|---|---|
| Hexagram × Shi_Z3 | Hexagram × Shi_V₄ | 时态空间从 3 升到 4 |
| `Shi.next` (Z/3 cyclic) | `Shi.cuo / zong / cuoZong` (V₄ Klein) | 没有 canonical cyclic order, 改用 involution |
| 192 cells | 256 cells | (Z/2)⁶ × Z/3 (192) → (Z/2)⁸ (256) |
| 无 道 | **道 = (因=0, 果=0) = V₄ identity, first-class** | 「永真」入本体 |
| (Z/2)ⁿ self-similar broken | (Z/2)ⁿ closure restored at R₈ | 严格 binary self-similarity |
| `表六_192格全表.md` | [`表六_256格全表.md`](表六_256格全表.md) | per-cell 表升级 |
| Cell192Stratify.lean | Cell256Stratify.lean | bundle theorem 重写 |

详见 [yi-calculus-theorem.md §11 Theorem I + Corollary I.3](yi-calculus-theorem.md) (旧 Cell192 是 R₈ 之 partial image, 丧失 V₄ 单位元 anchor)。

---

## 13. 完整性 (Completeness) 在 R₈ 之验证

`R8_complete` bundle (Cell256Stratify.lean) 仅依赖 `propext` + `native_decide` 公理 (无项目自定义 axiom):

| 项 | ✓ |
|---|---|
| 元 256 cells 全枚举 | ✓ (`Cell256.all_length = 256`) |
| 元的群结构 (Z/2)⁸ | ✓ (Add/Zero/Neg/Sub/SMul instances) |
| Cayley 自作用 ι/ε | ✓ (`cayley_inj`, `epsAtOrigin_cayley`, `cayley_hom`) |
| Reachability (simply transitive) | ✓ |
| Decidability of finite props | ✓ (native_decide) |
| V₄ × V₄ outer symmetries | ✓ (hex side + shi side) |
| hu fixed points {乾, 坤, 既济, 未济} | ✓ (in 本本 quadrant) |
| 道 之 origin 五重身份 | ✓ (origin = identity = no-op = 永真 + V₄ id) |
| Pontryagin self-duality | ✓ ((Z/2)⁸ self-dual) |
| R-O frame duality | ✓ (Schrödinger ↔ Heisenberg) |
| Strict uniform R₀..R₈ | ✓ (no jumps) |

**完整性陈述 (Theorem K, R₈ closure)**:

> 五件 things — Cell256 (R₈), XOR subgroup, V₄ × V₄ outer, Lift/Project, 道 anchor — 加上 R₀..R₇ buildup, 构成 self-describing system 之**完整 algebraic closure**。

---

## 14. Lean 文件 → 表格 cross-reference

| 概念 | Lean 锚 | 行/表 |
|---|---|---|
| Cell256 type | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean):165 | §2.1 |
| Shi V₄ inductive | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean):62-67 | §2.1, §3 |
| Shi.cuo / zong / cuoZong | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean):77-95 | §7 |
| Shi.toYinGuo / ofYinGuo | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean):115-135 | §3 |
| Cell256.xor / origin | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean):481-487 | §2.4, §7.3 |
| Cell256.cayley / epsAtOrigin | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean):540-565 | §7.3 |
| 印 / 投 (XOR mask form) | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean):582-624 | §7.1 |
| 256-tree level counts | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean):189-198 | §11 |
| BenZheng 4 quadrants | [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean):263-279 | §6 |
| quadrant_partition_complete | [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean):325 | §6 |
| hu_attractors_in_benBen | [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean):444-449 | §9.3 |
| R8_complete bundle | [`Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) | §13 |
| Cell128 (R₇) | [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) | §10 |
| OX 8-char macro | [`OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) | §3 mask 列 |

完整 per-cell 表 (256 行, 含 OX literal / hex / shi / quadrant / (因,果) / 形式 type / V₄ orbit / cuo-pair / zong-pair) 见 [`表六_256格全表.md`](表六_256格全表.md).

---

## 15. 应用方向

### 15.1 BaguaTuring 文程序在 Cell256 上

`BaguaTuring.lean` 之 YiInstr ISA 现操作 Cell256:
- `YiInstr.setShi` 接受 4-state Shi (含 `.dao`)
- `YiInstr.branchShiEq` 4 分支
- `shiNext` 旧 Z/3 cyclic 替换为 `Shi.cuo` (involution, 因-axis)
- 道判机 verdict semantics 不变 (天道 ↦ Shi.ji, 心道 ↦ Shi.wei)

### 15.2 GodelLi / Rice / Kleene 在 Cell256 上

`GodelLi.lean` (理之不完备) 之 Halts / Diagonal / Rice 都基于 Cell256-state YiState。`KleeneInternal.lean` 之 universal interpreter + s-m-n 在 Cell256 操作。

### 15.3 道-anchored programs

(h, 道) cells 是「不与 causation flow 交互」之状态 — useful for 表达「永真断言」/ atomic 真值 / type-level invariant。在 Lean 中可直接 pattern match `(_, .dao)` 取出。

---

## 16. 三句话总论

1. **代数**: Cell256 = (Z/2)⁸ Abelian closure，Hexagram × Shi 之 tensor product，道 = (qian, dao) 是 V₄ × V₄ 双 origin 之统一 origin。

2. **几何**: 16 super-cells (4 BenZheng × 4 V₄) × 16 cells = 256；hu attractors {乾,坤,既济,未济} × Shi=道 4 cells 是绝对最稳定 sub-set。

3. **本体**: 道-row (64 cells) 是「描述者本身永在」之代数表达；已/未/今 三 row 是 P/T/PT 三 slice；V₄ 单位元 first-class 入本体让易系统真正自描述闭合 — 这是 Cell192 → Cell256 升级的本质意义。

---

## 附：与 v3 兄弟文档关系

| 文档 | 主题 | 与本文关系 |
|---|---|---|
| [yi-RO-hierarchy.md](yi-RO-hierarchy.md) | R₀..R₈ definitive | §3.8 R₈ 是本文之 parent layer 定义 |
| [yi-calculus-theorem.md](yi-calculus-theorem.md) | Theorems A–K | §10–§13 Theorems H/I/J/K 是本文之严格证据 |
| [shi-v4.md](shi-v4.md) | V₄ Klein on Shi 专文 | §3 (因,果)+V₄ table |
| [r7-yin-r8-guo.md](r7-yin-r8-guo.md) | R₇/R₈ atomic axes | §10 cumulative emergence |
| [r5-wuyao-provisional.md](r5-wuyao-provisional.md) | R₅ 五爻 provisional | sibling, R-hierarchy 中 R₅ 层 |
| [ox-notation.md](ox-notation.md) | OX["xxxxxxxx"] macro | §3 mask 列, 8-char OX literal |
| [lift-project.md](lift-project.md) | uniform Lift/Project | §10 R₆ → R₇ → R₈ 之具体 lift |
| [yi-bagua.md](yi-bagua.md) | Yi/Bagua + R-hier overview | parent navigation |
| [64-hexagram-grid.md](64-hexagram-grid.md) | 64 卦 4 quadrant 表 | §6 hex side 之上层 |
| [sanben-sijieduan-grid.md](sanben-sijieduan-grid.md) | Mian = Ben × Zheng (R₄) | §6 quadrant 之下层 R₄ |
| [`表六_256格全表.md`](表六_256格全表.md) | per-cell 表 | per-cell column 全展开 |
