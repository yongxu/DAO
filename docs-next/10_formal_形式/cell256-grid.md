# Cell256 网格 — 256-cell 全枚举与 Hexagram × Shi 分布

> 状态：v3 canonical (2026-05-11) — Cell256 = Hexagram × Shi 之 256 元 ground inventory；R₀..R₈ strict uniform 体系下 R₈ 闭合层之元清单。
> 角色：本文是 256 格的"内容/坐标/分布"之主文。algebraic spine 的 (Z/2)⁸ 群论结构见 [`cell256-algebra.md`](cell256-algebra.md)；V₄ Shi 的群结构与四态读法见 [`v4-shi.md`](v4-shi.md)；OX["..."] 字符串字面量见 [`ox-notation.md`](ox-notation.md)。
> 取代：v3 之前的 `cell192-grid.md`（Shi = Z/3 cyclic, |·| = 192）已归档至 [`史/docs-next-pre-v3/cell192-grid_Z3-Shi_旧版.md`](../../史/docs-next-pre-v3/cell192-grid_Z3-Shi_旧版.md)。结构错误与 v3 修正详情见 [`v4-shi.md`](v4-shi.md)。

---

## 0. 速览

```
Cell256 = Hexagram × Shi
        = 64        × 4
        = 256       = (Z/2)⁸
```

- **Hexagram (R₆)**: 64 重卦, 按 BenZheng 分 4 象限 (本本 / 本征 / 征本 / 征征) 各 16。
- **Shi (R₈ V₄ block)**: 4 时态 = V₄ Klein 四群 = {道 (dao), 已 (ji), 今 (jin), 未 (wei)}；通过 (因, 果) ∈ Bool² 双轴 emerge。
- **总分布**: 4 quadrant × 16 hex × 4 Shi = **256 cells**；Lean 中即 `Cell256.all`，长度 `256` 由 `native_decide` 验证（[`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) `Cell256.all_length`）。
- **道-anchor**: `(Hexagram.qian, Shi.dao)` = `OX["oooooooo"]` = `Cell256.origin` = (Z/2)⁸ identity。

---

## 1. Cell256 形式定义 (Lean 形式锚)

来自 [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 2：

```lean
abbrev Cell256 : Type := Hexagram × Shi

def Cell256.all : List Cell256 :=
  Hexagram.allHex.flatMap fun h => Shi.all.map fun s => (h, s)

theorem Cell256.all_length : all.length = 256 := by native_decide
theorem Cell256.all_nodup  : all.Nodup        := by native_decide
theorem Cell256.mem_all    : ∀ c, c ∈ all
```

Cell256 是 Lean 之 `Hexagram × Shi`，其 256 元枚举在 `Cell256.all`，全覆盖 (`mem_all`) 与无重 (`all_nodup`) 两性都被 `native_decide` 一证。

R-hierarchy 编号见 [`Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) § 1：

```lean
abbrev R6 := Hexagram         -- (Z/2)⁶ = 64
abbrev R7 := Cell128          -- (Z/2)⁷ = 128
abbrev R8 := Cell256          -- (Z/2)⁸ = 256

theorem R8_card_eq_256 : (Cell256.all : List R8).length = 256 := Cell256.all_length
```

### 1.1 Phase C Shi := YinBit × GuoBit (2026-05-11)

Phase C (commit 90c34f0) 起 `Shi` 不再是 inductive 4-字面量，而是 `abbrev Shi := YinBit × GuoBit` — V₄ 群结构由 (因, 果) ∈ Bool² 之 componentwise XOR 直接给出，4 个具名 `Shi.dao / Shi.ji / Shi.jin / Shi.wei` 是 abbrev 常量：

```lean
-- formal/SSBX/Foundation/Bagua/Cell256.lean § 1
abbrev Shi : Type := YinBit × GuoBit

@[reducible] def Shi.dao : Shi := (false, false)  -- (无因, 无果) = V₄ identity
@[reducible] def Shi.ji  : Shi := (true,  false)  -- (有因, 无果) = past-closed (P)
@[reducible] def Shi.wei : Shi := (false, true)   -- (无因, 有果) = future-open (T)
@[reducible] def Shi.jin : Shi := (true,  true)   -- (有因, 有果) = PT 交汇

def Shi.all : List Shi := [Shi.dao, Shi.ji, Shi.jin, Shi.wei]
```

历史 inductive Shi 已归档；下文所有 "Shi V₄" 引用均按 abbrev 形式。

### 1.2 V₄ Klein on Shi (cuo / zong / cuoZong involutions)

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

### 1.3 (因, 果) bijection (V₄ as YinBit × GuoBit)

在 Phase C 之 abbrev 形式下，`Shi.toYinGuo` / `Shi.ofYinGuo` 退化为 `id` / `id` (因为 `Shi := YinBit × GuoBit`)，但 API 仍保留以对接旧文：

```lean
def Shi.toYinGuo  : Shi → YinBit × GuoBit := id
  -- .dao ↦ (false, false) = (无因, 无果) = V₄ identity
  -- .ji  ↦ (true,  false) = (有因, 无果) = past-closed (P)
  -- .wei ↦ (false, true)  = (无因, 有果) = future-open (T)
  -- .jin ↦ (true,  true)  = (有因, 有果) = PT 交汇

def Shi.ofYinGuo : YinBit × GuoBit → Shi := id
theorem Shi.ofYinGuo_toYinGuo (s : Shi)             : ofYinGuo (toYinGuo s) = s
theorem Shi.toYinGuo_ofYinGuo (yg : YinBit × GuoBit) : toYinGuo (ofYinGuo yg) = yg
```

### 1.4 (Z/2)⁸ Abelian 群 + Cayley 自作用 (Phase A spine)

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

### 1.5 印 / 投 atomic operators (XOR mask form)

```lean
def Cell256.yin_mask : Cell256 := (Hexagram.qian, Shi.ji)   -- 因-轴 only
def Cell256.tou_mask : Cell256 := (Hexagram.qian, Shi.wei)  -- 果-轴 only

def Cell256.yin (c : Cell256) : Cell256 := xor c yin_mask  -- 印 = toggle 因
def Cell256.tou (c : Cell256) : Cell256 := xor c tou_mask  -- 投 = toggle 果

theorem Cell256.yin_yin (c : Cell256) : yin (yin c) = c
theorem Cell256.tou_tou (c : Cell256) : tou (tou c) = c
theorem Cell256.yin_tou_comm (c : Cell256) : yin (tou c) = tou (yin c)

-- 印 ∘ 投 = XOR with V₄ central element (qian, jin)
theorem Cell256.yin_tou_eq_central (c : Cell256) :
    yin (tou c) = xor c (Hexagram.qian, Shi.jin)
```

---

## 2. 8-bit layout

Cell256 cell 之 8 位编码（OX 字符串约定，详 [`ox-notation.md`](ox-notation.md)）：

```
位置:  0   1   2   3   4   5   6   7
意义:  y₁  y₂  y₃  y₄  y₅  y₆  因   果
       └──── 6 yao (inner-to-outer) ────┘ └ Shi V₄ ┘
       初爻..上爻                       (因, 果) ∈ Bool²
```

- `o` = yang (Yao.yang) / false (因/果 bit)
- `x` = yin (Yao.yin) / true (因/果 bit)
- 字符 6,7 经 `Shi.ofYinGuo` 重构 Shi V₄ 元

例：

| OX 字面 | Hex 部分 | (因, 果) | Shi | 解读 |
|---|---|---|---|---|
| `OX["oooooooo"]` | qian (乾) | (false, false) | 道 | (Z/2)⁸ identity (Cell256.origin) |
| `OX["ooooooxo"]` | qian | (true, false) | 已 | 乾·已 |
| `OX["ooooooox"]` | qian | (false, true) | 未 | 乾·未 |
| `OX["ooooooxx"]` | qian | (true, true) | 今 | 乾·今 |
| `OX["xxxxxxoo"]` | kun (坤) | (false, false) | 道 | 坤·道 |
| `OX["xxxxxxxx"]` | kun | (true, true) | 今 | 坤·今 |

---

## 3. Shi V₄ 四态分解

Shi 是 Klein 四群（**绝非 Z/3 cyclic**）；4 态由 (因, 果) ∈ Bool² 同构（双向双射 `Shi.toYinGuo` / `Shi.ofYinGuo` 见 [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 1）：

| Shi | (因, 果) | V₄ 元 | 解读 | 物理 anchor |
|---|---|---|---|---|
| **道** (dao) | (0, 0) | $e$ identity | 永真，跨时空 anchor | reference vacuum |
| **已** (ji) | (1, 0) | $\sigma_P$ | 过去封闭, 无未来 | parity (P) |
| **未** (wei) | (0, 1) | $\sigma_T$ | 未来开放, 无过去 | time-reversal (T) |
| **今** (jin) | (1, 1) | $\sigma_{PT}$ | 因果俱在 = 现在 | PT |

V₄ 群结构与 cuo / zong / cuoZong involutions 之完整代数见 [`v4-shi.md`](v4-shi.md)。

### 3.1 Shi V₄ 之 (因, 果) emergence — 一图全清

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

详见 [`v4-shi.md`](v4-shi.md) (V₄ Klein structure 专文) + [`r7-yin-r8-guo.md`](r7-yin-r8-guo.md) (R₇/R₈ atomic axes 因/果 详尽剖析)。

---

## 4. Quadrant × Shi = 4 × 4 总分布

Hexagram 按 BenZheng quadrant 分类（详 [`64-hexagram-grid.md`](64-hexagram-grid.md) 与 [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) § 6）；每个 quadrant 各 16 hexagram，配 4 Shi 得 64 cells；4 quadrant × 4 Shi = 16 sub-blocks，每 sub-block 16 cells；总 256：

```
                 Shi:   道       已       今       未       (× 16)
Quadrant ↓
本本   (16 hex):       16       16       16       16   = 64
本征   (16 hex):       16       16       16       16   = 64
征本   (16 hex):       16       16       16       16   = 64
征征   (16 hex):       16       16       16       16   = 64
                                                          ─────
                                                          256
```

Lean 形式锚（[`Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) § 3）：

```lean
def R8.quadrant (c : R8) : Quadrant := c.1.quadrant
def R8.quadrantList (q : Quadrant) : List R8 :=
  Cell256.all.filter (fun c => decide (c.1.quadrant = q))

theorem R8.benBen_count     : (R8.quadrantList .benBen).length     = 64 := by native_decide
theorem R8.benZheng_count   : (R8.quadrantList .benZheng).length   = 64 := by native_decide
theorem R8.zhengBen_count   : (R8.quadrantList .zhengBen).length   = 64 := by native_decide
theorem R8.zhengZheng_count : (R8.quadrantList .zhengZheng).length = 64 := by native_decide

theorem R8_quadrant_partition_complete :
    (R8.quadrantList .benBen).length + (R8.quadrantList .benZheng).length
    + (R8.quadrantList .zhengBen).length + (R8.quadrantList .zhengZheng).length
    = 256
```

---

## 5. 各 quadrant 之首尾样例

下面给每个 quadrant 抽 6 cells（quadrant-内首 hex × Shi 4 + quadrant-内末 hex × {道, 今} = 6），便于核验 OX 字面量与位置语义。Hexagram 的 King Wen 序号取自 [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 4 `xuGua`。

### 5.1 本本 (benBen) sub-grid

| KW # | Hex | 内·外 | OX 字面 (×4 Shi) |
|---|---|---|---|
| 1 | 乾 qian | 物·物 | `oooooooo` 道 / `ooooooxo` 已 / `ooooooxx` 今 / `ooooooox` 未 |
| 2 | 坤 kun | 事·事 | `xxxxxxoo` 道 / `xxxxxxxo` 已 / `xxxxxxxx` 今 / `xxxxxxox` 未 |
| 11 | 泰 tai | 物·事 | `oooxxxoo` 道 / `oooxxxxo` 已 / `oooxxxxx` 今 / `oooxxxox` 未 |
| 64 | 未济 weiji | 間·動 | `xoxoxooo` 道 / `xoxoxoxo` 已 / `xoxoxoxx` 今 / `xoxoxoox` 未 |

### 5.2 本征 (benZheng) sub-grid

| KW # | Hex | 内·外 | OX 字面（道 / 今） |
|---|---|---|---|
| 4 | 蒙 meng | 間·時 | `xoxxxooo` 道 / `xoxxxoxx` 今 |
| 9 | 小畜 xiaoxu | 物·幾 | `oxxoxoo` (Hex 6 字符) — 完整 OX：`oxxoxooo` 道 / `oxxoxoxx` 今 |
| 16 | 豫 yu | 事·勢 | `xxxxoxoo` 道 / `xxxxoxxx` 今 |
| 17 | 随 sui | 動·時 | `xooxxooo` 道 / `xooxxoxx` 今 |

### 5.3 征本 (zhengBen) sub-grid

| KW # | Hex | 内·外 | OX 字面（道 / 今） |
|---|---|---|---|
| 3 | 屯 zhun | 勢·間 | `xooxxooo` (示意) — 实际取自 [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) `xuGua` 第 3 项；OX 道：`xooxxooo` |
| 6 | 讼 song | 間·物 | `xooxoooo` 道 / `xooxooxx` 今 |
| 7 | 师 shi | 間·事 | `xooxxxoo` 道 / `xooxxxxx` 今 |
| 8 | 比 bi | 事·間 | `xxxxoxoo` 道 |

### 5.4 征征 (zhengZheng) sub-grid

| KW # | Hex | 内·外 | OX 字面（道 / 今） |
|---|---|---|---|
| 18 | 蛊 gu | 幾·時 | `oxxxooxoo` (示意, 6 字符 hex 部分) |
| 28 | 大过 daguo | 幾·勢 | `oxxxxooo` 道 / `oxxxxoxx` 今 |
| 32 | 恒 heng | 勢·勢 | `oxxxooxoo` (示意) |
| 53 | 渐 jian | 時·幾 | `xxoxooxoo` (示意) |

> 备注：上表用于直观感受；精确 6-yao 编码见 [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 4 `xuGua` 之 64 行。完整对照详 [`64-hexagram-grid.md`](64-hexagram-grid.md)。

---

## 6. 道-row：64 个永真 anchor

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

## 7. 已 / 未 / 今 三 row：P / T / PT slices

### 7.1 已-row (P slice)

(h, 已) for all h ∈ Hexagram = 64 cells — past-closed slice.

| # | 卦 | (h, 已) cell | (因, 果) | 解读 |
|---|---|---|---|---|
| 1 | 乾 | (乾, 已) | (1, 0) | 「实在」之已成态 |
| 2 | 坤 | (坤, 已) | (1, 0) | 「受成」之已成态 |
| 11 | 泰 | (泰, 已) | (1, 0) | 「通畅」过去封闭 — 已通而不再延展 |
| 63 | 既济 | (既济, 已) | (1, 0) | 「已决」+ past closed = 完全确定 |

### 7.2 未-row (T slice)

(h, 未) for all h ∈ Hexagram = 64 cells — future-open slice.

| # | 卦 | (h, 未) cell | (因, 果) | 解读 |
|---|---|---|---|---|
| 1 | 乾 | (乾, 未) | (0, 1) | 「实在」之未来投射 — 无过去印记 |
| 64 | 未济 | (未济, 未) | (0, 1) | 「未决」+ future open = 双重未定 |

### 7.3 今-row (PT slice)

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

## 8. 16-grid view: BenZheng quadrant × Shi V₄

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

### 8.1 16 super-cells 全枚举

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

### 8.2 一个 super-cell 之 16 cells 完全展开 (本本, 道)

本本 quadrant 内 16 hex（按 King Wen 序）见 [`64-hexagram-grid.md`](64-hexagram-grid.md) §1：

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

### 8.3 全部 16 super-cells 之 hex 内容

256 cells = 4 quadrants × 16 hex × 4 Shi。每 quadrant 之 16 hex 列表见 [`64-hexagram-grid.md`](64-hexagram-grid.md) §1–§4。本节只列每 super-cell 之 cardinality + cuo/zong invariant。

| quadrant | hex 列表（按 King Wen 序）| 16-cell # |
|---|---|---|
| **本本** | 1乾 2坤 5需 6讼 7师 8比 11泰 12否 13同人 14大有 29坎 30离 35晋 36明夷 63既济 64未济 | 16 |
| **本征** | 4蒙 9小畜 16豫 20观 22贲 23剥 26大畜 34大壮 37家人 40解 43夬 45萃 47困 49革 55丰 59涣 | 16 |
| **征本** | 3屯 10履 15谦 19临 21噬嗑 24复 25无妄 33遁 38睽 39蹇 44姤 46升 48井 50鼎 56旅 60节 | 16 |
| **征征** | 17随 18蛊 27颐 28大过 31咸 32恒 41损 42益 51震 52艮 53渐 54归妹 57巽 58兑 61中孚 62小过 | 16 |

每 quadrant 16 hex × 4 Shi = 64 cells per quadrant × 4 quadrants = 256.

详见 [`表六_256格全表.md`](表六_256格全表.md) — per-cell 表，含 (hex, shi) ⊕ 形式 type ⊕ (因, 果) ⊕ V₄ orbit 等多列。

---

## 9. 256 树视图

Cell256 还可视为深度 9 的二叉前缀树（[`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) § 2）：

```
level: 0  1  2  3  4  5  6   7   8
count: 1  2  4  8  16 32 64 128 256
```

```lean
def Cell256.rootTo256TreeLevelCounts : List Nat :=
  [1, 2, 4, 8, 16, 32, 64, 128, 256]

theorem rootTo256TreeLevelCounts_sum : rootTo256TreeLevelCounts.sum = 511 := by native_decide
```

每层 +1 bit 直接对应 R-hierarchy R₀..R₈ 之 strict uniform progression（详 [`yi-RO-hierarchy.md`](yi-RO-hierarchy.md) § 3.0–3.8）。

---

## 10. 序卦扩展到 256：xuGua256

[`Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) § 6 把 King Wen 64 卦序扩展为 Hex-major × Shi-minor 之 256 元有序列：

```lean
def xuGua256 : List R8 :=
  Cell256.xuGua.flatMap fun h =>
    [(h, Shi.dao), (h, Shi.ji), (h, Shi.jin), (h, Shi.wei)]

theorem xuGua256_length : xuGua256.length = 256 := by native_decide
theorem xuGua256_nodup  : xuGua256.Nodup        := by native_decide

theorem xuGua256_head : xuGua256.head?    = some (Hexagram.qian, Shi.dao)            := rfl
theorem xuGua256_last : xuGua256.getLast? = some (Hexagram.weiji, Shi.wei)
```

- **首** = (乾, 道) = `OX["oooooooo"]` = origin。
- **末** = (未济, 未) = `OX["xoxoxoox"]`（hex 部分 `xoxoxo` 即 64.未济，Shi 部分 `ox` = 未）。

---

## 11. 与旧 Cell192 / Z/3 Shi 之对比

| 维度 | 旧 Cell192 (Z/3 Shi) | v3 Cell256 (V₄ Shi) |
|---|---|---|
| Shi 群 | Z/3 cyclic {已, 今, 未} | V₄ Klein {道, 已, 今, 未} |
| 元数 | 64 × 3 = 192 | 64 × 4 = 256 |
| (Z/2)ⁿ 自相似 | 破坏（混入 Z/3） | 严格 (Z/2)⁸ |
| 道作为 V₄ identity | 缺 | first-class anchor |
| 旧表 | `表六_192格全表.md` | `六表_实虚史真/表六_256格全表.md` |
| 旧 doc | [`史/docs-next-pre-v3/cell192-grid_Z3-Shi_旧版.md`](../../史/docs-next-pre-v3/cell192-grid_Z3-Shi_旧版.md) | 本文 |

详细 V₄ 取代 Z/3 之必要性论证见 [`v4-shi.md`](v4-shi.md) § "为何 Z/3 是错的"。

---

## 12. 与其他文档之关系

| 文档 | 关系 |
|---|---|
| [`yi-RO-hierarchy.md`](yi-RO-hierarchy.md) § 3.8 | R₈ 在 R-hierarchy 中之地位（闭合层） |
| [`v4-shi.md`](v4-shi.md) | Shi V₄ 群结构、cuo/zong/cuoZong involutions、(因,果) emergence |
| [`cell256-algebra.md`](cell256-algebra.md) | (Z/2)⁸ AddCommGroup + Cayley 自对偶 |
| [`yin-tou-operators.md`](yin-tou-operators.md) | 印 / 投 = R₇/R₈ 新 atomic |
| [`ox-notation.md`](ox-notation.md) | `OX["xxxxxxxx"]` 字面量参考 |
| [`64-hexagram-grid.md`](64-hexagram-grid.md) | 64 卦四语对照与 4 象限基础 |
| [`sanben-sijieduan-grid.md`](sanben-sijieduan-grid.md) | 4 substrate 在内容线之展开 |
| [`yi-calculus-theorem.md`](yi-calculus-theorem.md) Theorem I/J | R₈ + Shi V₄ emergence 之严格证明 |

---

## 形式锚 (Lean modules)

- [`formal/SSBX/Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) — `Cell256`, `Shi`, `Cell256.all`, `xuGua`, Phase A 群结构
- [`formal/SSBX/Foundation/Bagua/Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) — R₀..R₈ abbrev, `R8.quadrant*`, `xuGua256`, `R8_complete` bundle
- [`formal/SSBX/Foundation/Bagua/Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) — `Cell128 = Hexagram × YinBit` (R₇)
- [`formal/SSBX/Foundation/Bagua/BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) — `Mian`, `Quadrant`, `Ben/Zheng` 4-fold partition
- [`formal/SSBX/Foundation/Yi/Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) — `Yao`, `Trigram`, `Hexagram`, `Hexagram.qian/kun`
- [`formal/SSBX/Foundation/Hierarchy/RHierarchy.lean`](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean) — 一站式 import
- [`formal/SSBX/Foundation/Notation/OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) — `OX["..."]` 字面宏
</content>
</invoke>