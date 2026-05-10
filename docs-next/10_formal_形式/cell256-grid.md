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

## 6. 256 树视图

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

## 7. 序卦扩展到 256：xuGua256

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

## 8. 与旧 Cell192 / Z/3 Shi 之对比

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

## 9. 与其他文档之关系

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
