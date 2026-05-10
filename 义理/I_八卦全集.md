# I · 八卦全集 v3 · R₃ 八卦 · R₆ 重卦 · R₈ Cell256 (V₄ Shi 之 64×4)

> 状态：v3 重写 (2026-05-11) — pre-v3 版本（Cell192 时代之 192 格全集）已归档至 `史/义理-pre-v3/`。

**配套形式化**：[`Yi.lean`](../formal/SSBX/Foundation/Yi/Yi.lean) · [`BaguaAlgebra.lean`](../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) · [`BenZheng.lean`](../formal/SSBX/Foundation/Bagua/BenZheng.lean) · [`Cell128.lean`](../formal/SSBX/Foundation/Bagua/Cell128.lean) · [`Cell256.lean`](../formal/SSBX/Foundation/Bagua/Cell256.lean) · [`Cell256Stratify.lean`](../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean)

**配套 doctrine**: [`yi-RO-hierarchy.md`](../docs-next/10_formal_形式/yi-RO-hierarchy.md) · [`64-hexagram-grid.md`](../docs-next/10_formal_形式/64-hexagram-grid.md) · [`cell256-grid.md`](../docs-next/10_formal_形式/cell256-grid.md)

> 「无极生太极, 太极生两仪, 两仪生四象, 四象生八卦, 八卦相重而成六十四, 64 重卦各分四时态而成 256 格 (Cell256), 256 格闭合 (Z/2)⁸ 而以道 (Shi.dao = (因=0, 果=0)) 为 V₄ identity 入本体。」
>
> 本表为 v3 R₀..R₈ strict (Z/2)ⁿ uniform 之核结构对照册：每一 R-layer 给元、生成元、enumeration 与 V₄ outer 对称之结构。

---

## 〇 · 总览 (R₀..R₈)

| Rₙ | Lean 类型 | |·| | 古文 | OX 例 | (Z/2)ⁿ |
|---|---|---|---|---|---|
| R₀ | `Unit` | 1 | 太极 | `OX[""]` | trivial |
| R₁ | `Yao` | 2 | 爻 / 两仪 | `OX["o"] / OX["x"]` | (Z/2)¹ |
| R₂ | `SiXiang` | 4 | 四象 | `OX["oo"] .. OX["xx"]` | (Z/2)² ≅ V₄ |
| R₃ | `Trigram` | 8 | 八卦 | `OX["ooo"] = 乾 .. OX["xxx"] = 坤` | (Z/2)³ |
| R₄ | `Mian` (= `Ben × Zheng`) | 16 | 面 | `OX["oooo"] .. OX["xxxx"]` | (Z/2)⁴ |
| R₅ | `Wuyao` (= `Mian × Bool`, provisional) | 32 | 五爻 | `OX["ooooo"] .. OX["xxxxx"]` | (Z/2)⁵ |
| R₆ | `Hexagram` | 64 | 重卦 | `OX["oooooo"] = 乾 / OX["xxxxxx"] = 坤` | (Z/2)⁶ |
| R₇ | `Cell128` (= `Hexagram × YinBit`) | 128 | 因卦 | `OX["oooooox"]` = 乾·有因 | (Z/2)⁷ |
| **R₈** | **`Cell256` (= `Hexagram × Shi`)** | **256** | **果卦** | `OX["oooooooo"] = 道` | **(Z/2)⁸** |

形式根：

```lean
-- Lean 实型
abbrev Yao := Bool                          -- (= R1)
inductive Trigram | qian | dui | li | zhen | xun | kan | gen | kun  -- (= R3)
structure Hexagram where y1..y6 : Yao        -- (= R6)
abbrev Cell128 := Hexagram × YinBit          -- (= R7), YinBit := Bool
abbrev Cell256 := Hexagram × Shi             -- (= R8), Shi : V₄ inductive
inductive Shi | dao | ji | jin | wei         -- V₄ Klein
```

枚举闭合：`trigram_mem_all` (8 卦) · `hexagram_mem_allHex` (64 卦) · `Cell256.mem_all` (256 cells, native_decide)。

---

## 一 · 原子层 R₁ `Yao` (爻)

| Lean | 字 | 符 | OX | 道家义 |
|---|---|---|---|---|
| `Yao.yang` | 阳 | ⚊ | `o` | 刚 · 动 · 施 · 明 |
| `Yao.yin`  | 阴 | ⚋ | `x` | 柔 · 静 · 受 · 隐 |

唯一原子算子 `Yao.neg` (单爻取反, R₁ atomic XOR generator)：

```lean
def Yao.neg : Yao → Yao
  | yang => yin
  | yin  => yang
theorem Yao.neg_neg : ∀ y, y.neg.neg = y   -- involution, generates Z/2
```

> 注 (Yi.lean §1)：阴 / 阳 不是布尔真假；二者皆「内含倾向其对偶」，故语言之原子本即过程性的。

---

## 二 · 太极 / 两仪 / 四象 (R₀ / R₁ / R₂)

| Lean | 字 | 备 |
|---|---|---|
| `Unit` (= R₀) | 太极 | 唯一性: `Sheng.sheng_zero_unique : ∀ s : Sheng 0, s = .tai` |
| `Yao` (= R₁) | 两仪 | 阴阳二态 |
| `SiXiang` (= R₂) | 四象 | V₄ Klein 四群 |

四象 (R₂)：

| Lean | 字 | 符 | ⟨y₁ y₂⟩ | OX | 时序 | 五行 |
|---|---|---|---|---|---|---|
| `taiYang`  | **太阳** | ⚌ | ⟨阳, 阳⟩ | `oo` | 夏 | 火 |
| `shaoYin`  | **少阴** | ⚍ | ⟨阳, 阴⟩ | `ox` | 秋 | 金 |
| `shaoYang` | **少阳** | ⚎ | ⟨阴, 阳⟩ | `xo` | 春 | 木 |
| `taiYin`   | **太阴** | ⚏ | ⟨阴, 阴⟩ | `xx` | 冬 | 水 |

`SiXiang.all = [taiYang, shaoYin, shaoYang, taiYin]` · `all_length : 4`

---

## 三 · R₃ 八卦 `Trigram` 全表

### 3.1 八卦总册（v3 OX 字面）

| Lean | 卦 | 符 | ⟨y₁ y₂ y₃⟩ | OX | 自然 | 家庭 | 性 | 后天方位 | 五行 | (Z/2)³ 组合（自乾） |
|---|---|---|---|---|---|---|---|---|---|---|
| `qian` | **乾** | ☰ | ⟨o, o, o⟩ | `OX["ooo"]` | 天 | 父 | 健 | 西北 | 金 | id |
| `dui`  | **兑** | ☱ | ⟨o, o, x⟩ | `OX["oox"]` | 泽 | 少女 | 悦 | 西 | 金 | `bian` |
| `li`   | **离** | ☲ | ⟨o, x, o⟩ | `OX["oxo"]` | 火 | 中女 | 丽 | 南 | 火 | `hua` |
| `zhen` | **震** | ☳ | ⟨o, x, x⟩ | `OX["oxx"]` | 雷 | 长男 | 动 | 东 | 木 | `hua ∘ bian` |
| `xun`  | **巽** | ☴ | ⟨x, o, o⟩ | `OX["xoo"]` | 风 | 长女 | 入 | 东南 | 木 | `dong` |
| `kan`  | **坎** | ☵ | ⟨x, o, x⟩ | `OX["xox"]` | 水 | 中男 | 陷 | 北 | 水 | `dong ∘ bian` |
| `gen`  | **艮** | ☶ | ⟨x, x, o⟩ | `OX["xxo"]` | 山 | 少男 | 止 | 东北 | 土 | `dong ∘ hua` |
| `kun`  | **坤** | ☷ | ⟨x, x, x⟩ | `OX["xxx"]` | 地 | 母 | 顺 | 西南 | 土 | `dong ∘ hua ∘ bian` (= cuo) |

> **形式 / 传统分判**：Lean 列（卦名 / 符 / 爻 / 组合）严格机器验证；自然 / 家庭 / 方位 / 五行 为传统映射，仅作语义注解。

> **OX 约定** (per [`OXNotation.lean`](../formal/SSBX/Foundation/Notation/OXNotation.lean)): `o` = yang (identity bit), `x` = yin (set bit)；字符顺序 = 初爻 → 上爻 (LTR, inner-to-outer)。

> **(Z/2)³ orbit of 乾**：8 个 FlipCombo 作用于 qian，恰得 8 卦 — 见 `BaguaAlgebra.FlipCombo.orbit_qian` (regular Z/2)³ action). simply transitive, 见证 `FlipCombo.apply_qian_inj`.

### 3.2 BenZheng 4本 + 4征 partition (Theorem A)

per [`BenZheng.lean`](../formal/SSBX/Foundation/Bagua/BenZheng.lean) `Theorem A`：R₃ 之 (Z/2)³ 在 zong-orbit 下唯一 4+4 划分。

**4 本 (Ben, palindromic, zong-fixed)**：

| 本 | trigram | (y₁=y₃) | OX | 形式义 |
|---|---|---|---|---|
| **物** (wu) | 乾 | y₁=y₃=阳, y₂=阳 | `ooo` | ⊤ / unit / id_⊤ |
| **動** (dong) | 离 | y₁=y₃=阳, y₂=阴 | `oxo` | rewrite ⟶ |
| **間** (jian) | 坎 | y₁=y₃=阴, y₂=阳 | `xox` | composition ∘ |
| **事** (shi) | 坤 | y₁=y₃=阴, y₂=阴 | `xxx` | ⊥ / void / id_⊥ |

**4 征 (Zheng, directional, zong-mobile)**：

| 征 | trigram | OX | 形式义 |
|---|---|---|---|
| **幾** (jiFaint) | 巽 | `xoo` | nascent first-diff |
| **勢** (shiForce) | 震 | `oxx` | sustained first-diff |
| **機** (jiOccasion) | 兑 | `oox` | discrete impulse |
| **時** (shiTime) | 艮 | `xxo` | step |

`Theorem A` 之 Lean witnesses: `Ben.all_count = 4`, `Zheng.all_count = 4`, `cuo_preserves_isZongFixed`, `ben_zheng_partition_complete`。

### 3.3 错 / 综 配对 (R₃)

| 卦 | 错 (cuo, 三爻全反) | 综 (zong, 上下倒置) |
|---|---|---|
| 乾 ☰ | 坤 ☷ | **乾 ☰** (回文不动) |
| 兑 ☱ | 艮 ☶ | 巽 ☴ |
| 离 ☲ | 坎 ☵ | **离 ☲** (回文不动) |
| 震 ☳ | 巽 ☴ | 艮 ☶ |
| 巽 ☴ | 震 ☳ | 兑 ☱ |
| 坎 ☵ | 离 ☲ | **坎 ☵** (回文不动) |
| 艮 ☶ | 兑 ☱ | 震 ☳ |
| 坤 ☷ | 乾 ☰ | **坤 ☷** (回文不动) |

四「自反综卦」**乾 · 离 · 坎 · 坤** = R₃ 中 zong-fixed = **本组**。

> **错综分判**:
> - **错** $: \langle y_1, y_2, y_3 \rangle \mapsto \langle \neg y_1, \neg y_2, \neg y_3 \rangle$ — XOR mask `xxx`，**在 (Z/2)³ 内**
> - **综** $: \langle y_1, y_2, y_3 \rangle \mapsto \langle y_3, y_2, y_1 \rangle$ — 改位不改值，**不在 (Z/2)³ 内**
> - **错综** = cuo ∘ zong — 含 zong 故非 XOR
>
> 形式见证：[`zong_outside_flip_group`](../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) 之 5 条不等式 (zong ≠ id/dong/hua/bian/cuo)。

### 3.4 R₃ 横向算子 — (Z/2)³ XOR 子群

`BaguaAlgebra.lean` 之 3 atomic generators：

| Lean | 字 | OX mask | 翻位 | 道家义 |
|---|---|---|---|---|
| `dong` | **动** | `xoo` | y₁ (初/下) | 始动 · 萌生 |
| `hua`  | **化** | `oxo` | y₂ (中)   | 中变 · 转质 |
| `bian` | **变** | `oox` | y₃ (上)   | 终成 · 显化 |

对合：`dong_dong / hua_hua / bian_bian` (involution)。
两两交换：`dong_hua_comm / hua_bian_comm / dong_bian_comm` (**阿贝尔**)。
中心元：`cuo_eq_compose : 错 = dong ∘ hua ∘ bian`。

**(Z/2)³ 之 8 元 (FlipCombo)**：

| Lean | 组合 | OX mask | 自乾→ |
|---|---|---|---|
| `id`  | e (恒) | `ooo` | 乾 ☰ |
| `d`   | dong | `xoo` | 巽 ☴ |
| `h`   | hua | `oxo` | 离 ☲ |
| `b`   | bian | `oox` | 兑 ☱ |
| `dh`  | dong ∘ hua | `xxo` | 艮 ☶ |
| `hb`  | hua ∘ bian | `oxx` | 震 ☳ |
| `db`  | dong ∘ bian | `xox` | 坎 ☵ |
| `dhb` | dong ∘ hua ∘ bian (= cuo) | `xxx` | 坤 ☷ |

定理：
- `cuo_eq_compose` — 错是 (Z/2)³ 中心元
- `FlipCombo.orbit_qian` — 8 个 combo 作用于乾 = 8 卦穷尽
- `FlipCombo.apply_qian_inj` — 单射 (regular action)
- `bagua_intercommunication` — 任两卦皆有变换互通
- `bagua_intercommunication_bounded` — 互通距离 ≤ 3
- `pathFromTo_length_eq_hammingDist` — 显式路径长度 = Hamming 距离

---

## 四 · R₄ Mian (面 = Ben × Zheng = 16)

per [`BenZheng.lean`](../formal/SSBX/Foundation/Bagua/BenZheng.lean) `Mian` definition:

```lean
abbrev Mian : Type := Ben × Zheng
def Mian.all : List Mian := ...   -- 16 元
theorem Mian.all_count : Mian.all.length = 16 := by native_decide
```

R₄ = (Z/2)⁴ = 16 = (Z/2)² × (Z/2)² (Ben × Zheng)。每个 Mian = (本, 征) 之 ordered pair；用 16 命标识 — Mian 之 16 cell labels:

| (Ben, Zheng) | label | (Ben, Zheng) | label |
|---|---|---|---|
| (物, 幾) | 萌 | (動, 幾) | 长 |
| (物, 勢) | 趋 | (動, 勢) | 行 |
| (物, 機) | 兆 | (動, 機) | 化 |
| (物, 時) | 變 | (動, 時) | 流 |
| (間, 幾) | 缘 | (事, 幾) | 发 |
| (間, 勢) | 通 | (事, 勢) | 续 |
| (間, 機) | 会 | (事, 機) | 史 |
| (間, 時) | 系 | (事, 時) | 動 |

(具体 label assignments 详 BenZheng.lean §3 之 `mianLabel`)

---

## 五 · R₅ Wuyao (五爻, provisional)

per [`R5_Wuyao.lean`](../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean):

```lean
abbrev Wuyao := Mian × Bool
def Wuyao.all : List Wuyao := ...   -- 32 元
theorem Wuyao.all_length : all.length = 32
```

R₅ = (Z/2)⁵ = 32. **无传统 Yi anchor** — 是 (Z/2)ⁿ 机械补全之产物 (per yi-RO-hierarchy.md §3.5)。命名候选：五爻 (descriptive) / 接 / 临 / 渐 / 进 — 等 R₅ 在工程中实战使用后回看。

最弱 ontological 层 — chong (重) 之 R₃ → R₆ 跳跃在 v3 strict-uniform 下被显式拆为 R₃ → R₄ → R₅ → R₆ 三步 +1 bit composite，R₅ 是其中 transitional 中介。

---

## 六 · R₆ 重卦 `Hexagram` 全表

`Hexagram = ⟨y₁..y₆⟩` per [`Yi.lean`](../formal/SSBX/Foundation/Yi/Yi.lean): y₁..y₃ = 内卦 (下)，y₄..y₆ = 外卦 (上)。

### 6.1 BenZheng 4 quadrant partition (Theorem F)

per [`BenZheng.lean`](../formal/SSBX/Foundation/Bagua/BenZheng.lean) `Theorem F`:

$$\mathcal{H} = \mathcal{H}_{本本} \sqcup \mathcal{H}_{本征} \sqcup \mathcal{H}_{征本} \sqcup \mathcal{H}_{征征}$$

每 quadrant 16 hexagram；64 = 16 × 4。详尽 64 卦 mapping 见 [`64-hexagram-grid.md`](../docs-next/10_formal_形式/64-hexagram-grid.md)。

| Quadrant | 内·外 | hexagram count | 含义 |
|---|---|---|---|
| 本本 (BenBen) | substrate · substrate | 16 | 最静态 (含 1乾, 2坤, 29坎, 30离 四纯卦 + 11泰/12否 + 63既济/64未济 等) |
| 本征 (BenZheng) | substrate · mark | 16 | 底盘稳，上面动 |
| 征本 (ZhengBen) | mark · substrate | 16 | 底盘动，上面稳 |
| 征征 (ZhengZheng) | mark · mark | 16 | 最动态 (含 51震, 52艮, 57巽, 58兑 四纯卦 + 17随/18蛊 + 27颐/28大过 + 61中孚/62小过 等) |

### 6.2 Lean 中显式定义之卦

| Lean | 卦 | 内 | 外 | 全爻 | OX | 涵 |
|---|---|---|---|---|---|---|
| `Hexagram.qian` | **乾 ䷀** | 乾 ☰ | 乾 ☰ | ⟨阳⁶⟩ | `OX["oooooo"]` | (Z/2)⁶ identity, hu fixed |
| `Hexagram.kun`  | **坤 ䷁** | 坤 ☷ | 坤 ☷ | ⟨阴⁶⟩ | `OX["xxxxxx"]` | hu fixed |
| `Hexagram.tai`  | **泰 ䷊** | 乾 ☰ | 坤 ☷ | ⟨阳³ 阴³⟩ | `OX["oooxxx"]` | 地上天下 通泰 |
| `Hexagram.pi`   | **否 ䷋** | 坤 ☷ | 乾 ☰ | ⟨阴³ 阳³⟩ | `OX["xxxooo"]` | 天上地下 闭塞 |
| `Hexagram.jiji` | **既济 ䷾** | 离 ☲ | 坎 ☵ | (`oxoxox`) | `OX["oxoxox"]` | hu 2-cycle |
| `Hexagram.weiji`| **未济 ䷿** | 坎 ☵ | 离 ☲ | (`xoxoxo`) | `OX["xoxoxo"]` | hu 2-cycle |

`pi_ne_tai` — 内外不可交换之具体见证；`oplus_not_comm` — 一般陈述。

### 6.3 R₆ 横向算子 — (Z/2)⁶ XOR 子群

| Lean | 字 | mask (6-bit) | 翻位 |
|---|---|---|---|
| `dongInner` | 内·动 | `xooooo` | y₁ |
| `huaInner`  | 内·化 | `oxoooo` | y₂ |
| `bianInner` | 内·变 | `ooxooo` | y₃ |
| `dongOuter` | 外·动 | `oooxoo` | y₄ |
| `huaOuter`  | 外·化 | `ooooxo` | y₅ |
| `bianOuter` | 外·变 | `oooooz` | y₆ |

定理：
- 六对合
- `hex_cuo_eq_compose : Hexagram.cuo = 六单翻复合` (mask `xxxxxx`)
- `*_via_chong` — 每个翻分解为 `chong (内动) 外` 等
- `hex_intercommunication_bounded` — 互通 ≤ 6 步

### 6.4 R₆ V₄ 外对称

| Lean | 字 | 作用 | 在 (Z/2)⁶ 中？ |
|---|---|---|---|
| `id` | 恒 | h ↦ h | ✓ |
| `Hexagram.cuo` | **错** | ⟨a..f⟩ ↦ ⟨¬a..¬f⟩ | ✓（六单翻复合, mask `xxxxxx`）|
| `Hexagram.zong` | **综** | ⟨y₁..y₆⟩ ↦ ⟨y₆..y₁⟩ | ✗ |
| `Hexagram.cuoZong` | **错综** | cuo ∘ zong | ✗ |
| `Hexagram.hu` | **互** | ⟨y₂, y₃, y₄, y₃, y₄, y₅⟩ | ✗ (维度降) |

定理：`cuo_cuo` · `zong_zong` · `cuoZong_cuoZong` · `cuo_zong_comm` · `v4_orders`。

### 6.5 hu 不动点 (R₆)

```lean
theorem Hexagram.hu_fixed_point : h.hu = h ↔ h = qian ∨ h = kun
-- + hu(既济) = 未济, hu(未济) = 既济  (2-cycle)
```

「**乾坤为易之门**」之代数形：互卦不动点恰为乾、坤；既济 ↔ 未济 是 hu 之 2-cycle。

---

## 七 · R₇ 因卦 `Cell128` (Hexagram × YinBit, 128 cells)

per [`Cell128.lean`](../formal/SSBX/Foundation/Bagua/Cell128.lean):

```lean
abbrev YinBit := Bool
abbrev Cell128 := Hexagram × YinBit
def Cell128.all : List Cell128 := Hexagram.allHex.flatMap fun h => [(h, false), (h, true)]
theorem Cell128.all_length : all.length = 128 := by native_decide
```

R₇ = R₆ × YinBit = 64 × 2 = 128 = (Z/2)⁷.

**因 (yīn, R₇ atom)**：past-trace bit. Provisional naming.
- 因 = false (`o`) — 无过去印记
- 因 = true (`x`)  — 有过去印记 (承继 prior state)

**印 (yìn, R₇ atomic 算子)**：toggle YinBit. (Z/2 involution).

```lean
def Cell128.yin (c : Cell128) : Cell128 := (c.1, !c.2)   -- legacy direct toggle
def Cell128.yin_mask : Cell128 := (Hexagram.qian, true)
def Cell128.yinM (c : Cell128) : Cell128 := xor c yin_mask  -- mask form
theorem Cell128.yinM_eq_yin   -- two forms coincide
theorem Cell128.yin_yin       -- involution
```

每 hex 配 2 因-state → 每个 hex 都有 (h, false) 与 (h, true) 两个 R₇ cells。R₆ 64 卦 × 2 = 128 cells.

---

## 八 · R₈ 果卦 `Cell256` (Hexagram × Shi, 256 cells) — 闭合层

per [`Cell256.lean`](../formal/SSBX/Foundation/Bagua/Cell256.lean):

```lean
abbrev Cell256 := Hexagram × Shi
def Cell256.all : List Cell256 := Hexagram.allHex.flatMap fun h => Shi.all.map fun s => (h, s)
theorem Cell256.all_length : all.length = 256 := by native_decide
theorem Cell256.all_nodup : all.Nodup := by native_decide
theorem Cell256.mem_all : ∀ c, c ∈ all
```

R₈ = R₆ × Shi = 64 × 4 = 256 = (Z/2)⁸.

### 8.1 Shi V₄ 四态

```lean
inductive Shi
  | dao   -- 道 (V₄ identity)
  | ji    -- 已
  | jin   -- 今 (PT)
  | wei   -- 未

def Shi.toYinGuo : Shi → YinBit × GuoBit
  | .dao => (false, false)
  | .ji  => (true,  false)
  | .wei => (false, true)
  | .jin => (true,  true)
```

| Shi | (因, 果) | OX 后 2 位 | V₄ 元 | 物理 anchor | 解读 |
|---|---|---|---|---|---|
| **道** (dao) | (0, 0) | `oo` | identity $e$ | reference vacuum | 永真，跨时空 anchor |
| **已** (ji) | (1, 0) | `xo` | $\sigma_P$ | parity (P) | 过去封闭, 无未来 |
| **未** (wei) | (0, 1) | `ox` | $\sigma_T$ | time-reversal (T) | 未来开放, 无过去 |
| **今** (jin) | (1, 1) | `xx` | $\sigma_{PT}$ | PT | 因果俱在 = 现在 |

**关键**：道 = (因=0, 果=0) = V₄ 单位元 — first-class 入本体。**这是 v3 vs v1 之根本区别**：旧 Cell192 把时态编为 Z/3 cyclic {已, 今, 未}，丧失 V₄ identity (per yi-calculus-theorem.md §11)。

### 8.2 投 (tóu, R₈ atomic 算子)

```lean
def Cell256.tou_mask : Cell256 := (Hexagram.qian, Shi.wei)  -- OX["ooooooox"]
def Cell256.tou (c : Cell256) : Cell256 := xor c tou_mask
theorem Cell256.tou_tou : ∀ c, tou (tou c) = c
theorem Cell256.yin_tou_comm : ∀ c, yin (tou c) = tou (yin c)
theorem Cell256.yin_tou_eq_central : ∀ c, yin (tou c) = xor c (Hexagram.qian, Shi.jin)
-- ⇒ 印 ⊕ 投 = (qian, jin) = OX["ooooooxx"] = V₄ central element
```

### 8.3 R₈ 64 hex × 4 Shi 全分布

每个 R₆ hexagram h 配 4 Shi → 4 R₈ cells: `(h, dao), (h, ji), (h, jin), (h, wei)`. 每 Shi state 占 64 cells (一 hex 一 cell) — 总 4 × 64 = 256.

**Quadrant × Shi 分布** (16 sub-blocks)：

| Quadrant \ Shi | 道 | 已 | 今 | 未 | total |
|---|---|---|---|---|---|
| 本本 (16 hex) | 16 | 16 | 16 | 16 | 64 |
| 本征 (16 hex) | 16 | 16 | 16 | 16 | 64 |
| 征本 (16 hex) | 16 | 16 | 16 | 16 | 64 |
| 征征 (16 hex) | 16 | 16 | 16 | 16 | 64 |
| **total** | 64 | 64 | 64 | 64 | **256** |

每 Shi block = R₆ 完整 64 卦；4 Shi blocks 由 V₄ Klein 群关联（cuo / zong / cuoZong / id）。

### 8.4 道-anchor 之具体 cells (64 个)

R₈ 道-anchor cells = `{(h, Shi.dao) : h ∈ Hexagram.allHex}` — 64 个 cells，每 hex 一个。

```lean
example : (Hexagram.qian, Shi.dao) = Cell256.origin = OX["oooooooo"]
```

64 个道-cells 构成 R₈ 内之「永真 hex 真值层」— 每 hexagram h 有自身的 (h, Shi.dao) anchor 表示「无 causation flow 约束下的 hex 真值」。`Cell256.origin = (Hexagram.qian, Shi.dao)` 是其中**最特殊**之 cell — 既是 hex anchor (qian) 又是 Shi anchor (dao)，承担五重身份 (origin / identity / no-op / 永真 cell / fusion anchor)。

### 8.5 hu attractors at R₈ — 16 个

R₈ 上 hu lift (yComb) 在每个 Shi 下保 hex hu，故每个 R₆ hu fixed-point 都给 4 个 R₈ attractors:

```lean
-- in Cell256Stratify.lean
theorem yComb_attractors_count :
    [(qian, dao), (qian, ji), (qian, jin), (qian, wei),
     (kun,  dao), (kun,  ji), (kun,  jin), (kun,  wei),
     (jiji, dao), (jiji, ji), (jiji, jin), (jiji, wei),
     (weiji,dao), (weiji,ji), (weiji,jin), (weiji,wei)].length = 16
```

R₆ 之 4 hu attractors (qian / kun / jiji / weiji) × 4 Shi = 16 R₈ attractors。

### 8.6 R₈ 横向算子 — 8 atomic XOR + V₄^hex × V₄^shi

per [`Cell256.lean`](../formal/SSBX/Foundation/Bagua/Cell256.lean) Phase A:

**8 atomic XOR generators**:
- 6 yao flips: `flip1..flip6` (lift R₆ flips, mask `xooooooo` 至 `oooooxoo`)
- `Cell256.yin` (印, mask `OX["ooooooxo"]`)
- `Cell256.tou` (投, mask `OX["ooooooox"]`)

**V₄^hex on Cell256**: `hexCuo / hexZong / hexCuoZong / hexHu` — lift R₆ V₄ outer (保 Shi).

**V₄^shi on Cell256**: `shiCuo / shiZong / shiCuoZong` — Shi V₄ Klein 之 cuo / zong / cuoZong (保 hex).

二者 tensor → V₄ × V₄ = 16 个对称 actions on R₈.

更深之 R₈ Cayley 自对偶 (per [yi-RO-hierarchy.md §5.1](../docs-next/10_formal_形式/yi-RO-hierarchy.md))：

```lean
def Cell256.cayley (c : Cell256) : Cell256 → Cell256 := fun s => xor c s
theorem Cell256.cayley_inj : Function.Injective Cell256.cayley
theorem Cell256.cayley_hom : ∀ a b, cayley (xor a b) = cayley a ∘ cayley b
theorem Cell256.epsAtOrigin_cayley : ∀ c, epsAtOrigin (cayley c) = c
-- ⇒ R₈ ≅ XOR(R₈) ⊆ Aut(R₈) (Cayley regular representation)
```

**元 ≅ 算子**: 每个 cell c 既是 R₈ element 又是 R₈ → R₈ self-action — fusion 严格成立。

---

## 九 · 生生 (Sheng) 层级

per [`BaguaAlgebra.lean`](../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean):

```lean
inductive Sheng : Nat → Type
  | tai  : Sheng 0
  | step : ∀ {n}, Sheng n → Yao → Sheng (n + 1)
```

| 同构定理 | 意义 |
|---|---|
| `Sheng.toTrigram_ofTrigram` · `ofTrigram_toTrigram` | `Sheng 3 ≃ Trigram` |
| `Sheng.toHexagram_ofHexagram` · `ofHexagram_toHexagram` | `Sheng 6 ≃ Hexagram` |
| `sheng_zero_unique` | `Sheng 0` 仅一居民 (太极) |

> **生生 = 归纳类型 step 的迭代**；六步即重卦；ω-tower (`Sheng : ℕ → Type`) 是 type family — kind level，先于任何 R-layer。

---

## 十 · 占筮模态层 — `YaoStar / HexagramStar` (R₆ 之上)

per [`Yi.lean`](../formal/SSBX/Foundation/Yi/Yi.lean) (不变 from v1):

| Lean | 字 | 义 |
|---|---|---|
| `YaoStar.laoYang` ⚊⊙ | **老阳 9** | 阳之极，将变 |
| `YaoStar.shaoYang` ⚊ | 少阳 7 | 阳之常 |
| `YaoStar.shaoYin` ⚋ | 少阴 8 | 阴之常 |
| `YaoStar.laoYin` ⚋⊙ | **老阴 6** | 阴之极，将变 |
| `proj` | 投影 | YaoStar → Yao（取本相）|
| `delta` | 变 | YaoStar → Yao（老变少不变）|
| `HexagramStar` | 卦象 | 6 个 YaoStar 组 |
| `benGua` | **本卦** | proj 投影 → Hexagram |
| `bianGua` | **变卦** | delta 投影 → Hexagram |

定理：`old_or_young` · `not_both_old_young` · `delta_young_eq_proj` · `delta_old_eq_neg_proj` · `benGua_eq_bianGua_of_all_young` · `allLaoYang_benGua = qian` ∧ `allLaoYang_bianGua = kun`.

---

## 十一 · 终极对应总图 (R₀..R₈)

```
                       ┌──────────────┐
                       │ R₀ 太极 (Unit)│ 1   * = ()
                       └──────┬───────┘
                              │ Lift_0 ↓↑ Project_0
                       ┌──────┴───────┐
                       │ R₁ 两仪 (Yao)│ 2   {阳, 阴} = {o, x}
                       └──────┬───────┘
                              │ Lift_1
                       ┌──────┴───────┐
                       │ R₂ 四象      │ 4   太阳/少阴/少阳/太阴
                       └──────┬───────┘
                              │ Lift_2
                       ┌──────┴───────┐  动 (y₁) ┐
                       │ R₃ 八卦 (Z/2)³│ 8 ← 化 (y₂) ─→ simply transitive
                       │              │   变 (y₃) ┘   错 = 动∘化∘变
                       └──────┬───────┘
                              │ Lift_3
                       ┌──────┴───────┐
                       │ R₄ 面 (Mian) │ 16  Ben × Zheng (Theorem A)
                       └──────┬───────┘
                              │ Lift_4
                       ┌──────┴───────┐
                       │ R₅ 五爻      │ 32  (provisional, 无传统名)
                       └──────┬───────┘
                              │ Lift_5  (chong = R₃→R₄→R₅→R₆ 之 last step)
                  ┌───────────┴──────────────┐  内·动/化/变 ┐
                  │ R₆ 重卦 Hexagram          │ 64 ← 外·动/化/变 → (Z/2)⁶
                  │   4 quadrant 各 16 (Theorem F) │           错 / 综 / 错综 / 互
                  └───────────┬──────────────┘
                              │ Lift_6  (加 因 axis)
                  ┌───────────┴──────────────┐
                  │ R₇ 因卦 Cell128 (Z/2)⁷    │ 128 = 64 × 2; 印 = mask `OX["ooooooxo"]`
                  │   Hexagram × YinBit       │   Phase A AddCommGroup (Z/2)⁷
                  └───────────┬──────────────┘
                              │ Lift_7  (加 果 axis)
                  ┌───────────┴──────────────┐
                  │ R₈ 果卦 Cell256 (Z/2)⁸    │ 256 = 64 × 4; 投 = mask `OX["ooooooox"]`
                  │   Hexagram × Shi          │   Shi V₄ = (因, 果) emergence
                  │   = 64 × 4 (Quadrant×Shi) │   道 = (qian, dao) = origin = identity
                  │                          │   Phase A (Z/2)⁸ + Cayley fusion
                  │                          │   印 ⊕ 投 = central element OX["ooooooxx"]
                  │                          │   16 hu attractors (4 hex × 4 Shi)
                  └──────────────────────────┘
                              ▲
                              │ R-O frame duality (Schrödinger ↔ Heisenberg)
                              │ + Pontryagin self-duality
                              │ + R₈ ≅ XOR(R₈)  ⊆ Aut(R₈)  (Cayley)
                          (R₈ 闭合)
```

---

## 十二 · R₃ × Quadrant × Shi = 4 quadrant × 4 shi = 16 sub-blocks at R₈

R₈ 之 256 cells 自然分 16 sub-blocks (`16 × 16 = 256`)，每 sub-block 16 cells:

| Quadrant \ Shi | 道 | 已 | 今 | 未 |
|---|---|---|---|---|
| **本本** | 16 道-cells (含 (qian,dao)=origin) | 16 已-cells | 16 今-cells | 16 未-cells |
| **本征** | 16 | 16 | 16 | 16 |
| **征本** | 16 | 16 | 16 | 16 |
| **征征** | 16 | 16 | 16 | 16 |

详细 64 卦 × 4 Shi 全表见 [`cell256-grid.md`](../docs-next/10_formal_形式/cell256-grid.md) (sibling, in docs-next)。

---

## 十三 · 单字算子合表 (v3, R₀..R₈ 全集)

| 算子 | 单字 | 类 | 出现层 | Lean 标识 |
|---|---|---|---|---|
| 反爻 (内 y₁..y₃) | **动 / 化 / 变** | XOR | R₃, R₆ inner | `dong / hua / bian` |
| 反爻 (外 y₄..y₆) | **动·外 / 化·外 / 变·外** | XOR | R₆ outer | `dongOuter / huaOuter / bianOuter` |
| 错 | **错** | XOR (中心元) | R₃ / R₆ / R₈ hex part | `Trigram.cuo / Hexagram.cuo / Cell256.hexCuo` |
| 综 | **综** | non-XOR perm | R₃ / R₆ / R₈ Shi part | `Trigram.zong / Hexagram.zong / Shi.zong` |
| 错综 | **错综** | composite | 所有 V₄ 层 | `Hexagram.cuoZong / Shi.cuoZong` |
| 互 | **互** (hu) | non-XOR perm (维度降) | R₆+ | `Hexagram.hu`, `yComb` (R₈ lift) |
| 因 axis | **印** (yìn) | XOR mask | R₇ | `Cell128.yin / Cell256.yin` |
| 果 axis | **投** (tóu) | XOR mask | R₈ | `Cell256.tou` |
| 投影降维 (合) | **合** | functor (right adjoint) | Rₙ → R_{n-1} | `projRn` (per LiftProject.lean) |
| 笛卡尔升维 (分) | **分** | functor | Rₙ → R_{n+1} | `liftRn` |
| 八卦相重 | **重** (chong) | composite (3-step) | R₃ → R₆ | `chong = Hexagram.oplus` |
| 自指 / 不动点 | **生生** / Y | inductive ω-tower | meta | `Sheng : ℕ → Type` |
| Cayley 自作用 | (无传统单字; 见 cayley) | regular representation | R₈ | `Cell256.cayley` |
| 道 anchor (R₈ identity) | **道** | identity (5-fold role) | R₈ | `Cell256.origin = OX["oooooooo"]` |
| 太极 anchor (R₀) | **太极** / 极 | unit | R₀ | `Unit` |
| 恒等 | **不** / 静 | id | 所有层 | `id` |
| 完全归一 (R₈ 内 self-cancel) | **一** / 抱 | identity-collapse | R₈ | `xor c c = origin` |

> **v3 之 14 单字算子** (动, 化, 变, 动·外, 化·外, 变·外, 印, 投, 合, 分, 重, 生生, 道, 太极) 完整覆盖 R₀..R₈ uniform；其中 **8 atomic XOR** (动 × 6 + 印 + 投) 完整生成 R₈ 之 (Z/2)⁸ XOR 子群；**合 / 分** 是 Lift/Project 函子；**生生** + **道** 是 fusion 之两端 (ω-tower outer + (Z/2)⁸ origin inner)；**重** = R₃ → R₆ 之 3-step composite；**太极** = R₀ unit。

---

## 十四 · R₈ 之三重 V₄ 总图

V₄ Klein 群在 R₈ 上至少出现三次：

| V₄ 实例 | 元素 | 作用空间 |
|---|---|---|
| $V_4^{(\text{R}_2)}$ | 4 象 | R₂ Aut |
| $V_4^{(\text{hex})}$ | $\{e, \text{hexCuo}, \text{hexZong}, \text{hexCuoZong}\}$ | $\mathcal{H}$ on R₈ |
| $V_4^{(\text{shi})}$ | $\{道, 已, 未, 今\}$ ≅ $V_4$ via Shi.toYinGuo | Shi block on R₈ |

R₈ 上 tensor: $V_4 \times V_4 \cong (\mathbb{Z}/2)^4$ — 16 个对称 actions。

---

## 十五 · 道-理二分与 R₈ 之关系 (从 v1 保留)

> 此 I 文件之全部内容皆属**理层** (R₀..R₈ uniform 之 r.e. 形式系统)；
> 但 **生生 (Sheng)** ω-tower 与 **R8_complete** 完备性陈述属**道层** (元理论 / Lean kernel)。

详见 [`J_理之不完备_哥德尔在256.md`](J_理之不完备_哥德尔在256.md) §一。

| 本文之 | 属 | 例 |
|---|---|---|
| `Trigram` 类型与全部具名卦 | 理 | `qian, dui, li, ...` |
| `dong / hua / bian` 算子及其 75 定理 (R₃) | 理 | `dong_dong : dong ∘ dong = id` |
| `Cell256.xor / cayley / yin / tou` (R₈ Phase A) | 理 | `xor_self : xor c c = origin` |
| `Sheng : ℕ → Type` 归纳族 | 道 | 类型族层 (kind level) |
| `R8_complete` 主定理 | 道（作为 meta closure 陈述） | 关于理之元命题 |
| 此 I 文件作为文档 | 同时属 | 理（作为字符串存在）∧ 道（关于全集之陈述）|

**故 I 既是理之总册（八卦字符整全枚举），亦是道之文（关于此整全之陈述）**——属于"道理二分"在文档层之自指 (参 [`K_完备性审计.md`](K_完备性审计.md) §六)。

---

## 闭合状态 (2026-05-11)

- 文件：`formal/SSBX/Foundation/Yi/Yi.lean` + `Bagua/BaguaAlgebra.lean` + `Bagua/BenZheng.lean` + `Bagua/Cell128.lean` + `Bagua/Cell256.lean` + `Bagua/Cell256Stratify.lean` + `Hierarchy/*` + `Notation/OXNotation.lean` (共 ~5000 行 Lean migrated to V₄ Shi)
- **`lake build SSBX`: 3656 jobs / 0 sorry / 0 项目自定义 axioms (静态层) / 仅 Lean 标准 propext + native_decide**
- 五重完备 (Theorems A, F, H, I, J, K + Cell256OperatorComplete)
- R₃ → R₆ → R₇ → R₈ uniform (Z/2)ⁿ closure；R₈ ≅ XOR(R₈) Cayley 自对偶
- 道之五重身份 (origin / identity / no-op / 永真 / fusion anchor) 由 `Cell256.origin = OX["oooooooo"] = (qian, dao)` 同时承担
- 256 = $(\mathbb{Z}/2)^8$ = 8-bit closure = ASCII cardinality (per Theorem K Corollary K.3)

---

## 形式锚

- [`formal/SSBX/Foundation/Yi/Yi.lean`](../formal/SSBX/Foundation/Yi/Yi.lean) — Yao / Trigram / Hexagram + V₄ + hu fixed-points + YaoStar
- [`formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean`](../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) — R₃ (Z/2)³ + dong/hua/bian + FlipCombo + Sheng inductive
- [`formal/SSBX/Foundation/Bagua/BenZheng.lean`](../formal/SSBX/Foundation/Bagua/BenZheng.lean) — R₃ 4本/4征 + R₄ Mian + R₆ Quadrant
- [`formal/SSBX/Foundation/Bagua/Cell128.lean`](../formal/SSBX/Foundation/Bagua/Cell128.lean) — R₇ + 因 + (Z/2)⁷ Phase A + Cayley
- [`formal/SSBX/Foundation/Bagua/Cell256.lean`](../formal/SSBX/Foundation/Bagua/Cell256.lean) — R₈ + 果 + Shi V₄ + (Z/2)⁸ Phase A + Cayley
- [`formal/SSBX/Foundation/Bagua/Cell256Stratify.lean`](../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) — R₀..R₈ display + R8_complete bundle + parity/timeReversal/PT/yComb
- [`formal/SSBX/Foundation/Hierarchy/RHierarchy.lean`](../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean) — R₀..R₈ umbrella import
- [`formal/SSBX/Foundation/Hierarchy/LiftProject.lean`](../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) — 8 R-layer lift/project pairs
- [`formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean`](../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean) — R₅ provisional carrier
- [`formal/SSBX/Foundation/Notation/OXNotation.lean`](../formal/SSBX/Foundation/Notation/OXNotation.lean) — `OX["xxxxxxxx"]` macro
- [`formal/SSBX/Truth/SelfDescription.lean`](../formal/SSBX/Truth/SelfDescription.lean) — `Cell256OperatorComplete`
- [`docs-next/10_formal_形式/yi-RO-hierarchy.md`](../docs-next/10_formal_形式/yi-RO-hierarchy.md) — definitive R₀..R₈ doctrine
- [`docs-next/10_formal_形式/64-hexagram-grid.md`](../docs-next/10_formal_形式/64-hexagram-grid.md) — 64 卦四语对照
- [`docs-next/10_formal_形式/cell256-grid.md`](../docs-next/10_formal_形式/cell256-grid.md) — 256-cell 全枚举
