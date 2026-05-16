# 位的算子树：所有命名位置的 op(...(op(爻)))

> 状态：v3 (2026-05-11) — 与 main @ 1c76a55 对齐。R₀..R₈ strict (Z/2)ⁿ uniform spine（旧 R₁..R₅ 编号已升 R₁..R₈）；Cell192 已删，R₈ Cell256 = Hexagram × Shi V₄ 是闭合层；新增 R₄ Mian / R₅ Wuyao / R₇ Cell128 三层。
> 作用：把整个系统所有命名位置（R₁ 到 R₈ + ontological grids + naming registry）**全部表达为 算子作用于爻 的算子树**。
> 起点假设：爻 = 唯一原子。所有位置都是有限算子组合作用于爻得到的导出位置。
> 配套：[yi-RO-hierarchy.md](yi-RO-hierarchy.md) (v2.1 doctrine) · [64-hexagram-grid.md](64-hexagram-grid.md) · [cell256-grid.md](cell256-grid.md) · [layer-axis-graph.md](layer-axis-graph.md) · [operator-split.md](operator-split.md) (sibling, v3 inner/outer 拆) · [lift-project.md](lift-project.md) (sibling, v3 R₀..R₈ pairs)。
>
> **命名注**：本文中之 "V₄" / "V₄ outer" / "V₄ × V₄" / "V₄ Klein" 指 R₂ 之 Klein-four-group 结构 —— R₂ 之两个可交换 involution 与其复合。"V₄" 是 legacy marquee 命名，因表中 row terseness、Lean 模块名 (`V4Outer.lean`、`ShiV4` 等) 与 v2 历史连续性而保留；algebraic content（R₂ 上之 Klein 4-group 作用）原样保留为 load-bearing claim。

---

## 0. 起点 + 算子全集

### 0.1 唯一原子

```
爻 (yao) ∈ {阳 (= o = false), 阴 (= x = true)}
```

爻 是 1 bit 的差异 —— yang 或 yin。**所有其它位置都从爻通过算子构造**。

### 0.2 算子分类（5 类，共 ~32 个原子算子）

| 类 | 算子 | 元数 | 作用 | Lean 锚 |
|---|---|---|---|---|
| **(A) 爻内** | 易 (yi) | 1→1 | 阳 ↔ 阴 | `Yao.neg` |
| **(B) 纵向加爻** | 分 (fen) / Lift | n→n+1 | 加一爻 | `liftR{n}toR{n+1}` (n=0..7) |
| **(B) 纵向减爻** | 合 (he) / Project | n→n-1 | 减一爻 | `projR{n+1}toR{n}` (n=0..7) |
| **(C) R₃ 爻位 flip (inner)** | 改 / 化 / 变 (= dong/hua/bian) | n→n | flip y_i (i=1,2,3) | `Yi.dong / hua / bian` |
| **(C) R₆ 外卦 flip (outer)** | 临 / 主 / 极 | n→n | flip y_i (i=4,5,6) | `flip4..6` (LayerCharacterMap 字根 + Hierarchy/Operators/Atomic) |
| **(C) R₃/R₆ 整卦 V₄ 外** | 错 (cuo) / 综 (zong) / 互 (hu) / 错综 | n→n | full transform | `cuo / zong / hu / cuoZong` |
| **(C) R₇ 因 atom** | 印 (yìn) | 7→7 | toggle bit 7 (因) | `Cell128.yin` (XOR mask `(qian, ji)`) |
| **(C) R₈ 果 atom** | 投 (tóu) | 8→8 | toggle bit 8 (果) | `Cell256.tou` (XOR mask `(qian, wei)`) |
| **(C) V₄ Shi cuo / 印投** | Shi.cuo (= 印 ⊕ 投 on Shi side) | 8→8 | V₄ Shi 跨格 cuoZong (PT) | `Cell256` Shi.cuo / Shi.toYinGuo 双射 |
| **(D) 维度提升** | 乘 (chong) | n×n→2n | 内外卦合并 (R₃ × R₃ → R₆) | `chong` |
| **(D) 维度时态化** | 置 (zhi) on R₈ | R₆ → R₆ × Shi V₄ | 加 Shi 坐标 | `setShi` (在 Cell256 上) |
| **(E) 本/征 投射** | 物 動 間 事 / 幾 勢 機 時 | yao → grid 4-cell | ontological projection | (logical, 详 §6) |
| **(E) 阶段升级** | 差/识/间/事 (4 stage) | layer → layer | 本体读法升级 | (待形式化) |

### 0.3 元位置：太极 = R₀

```
太极 = 一元 = 元 = ε  (空算子链 / Unit / 0-ary)
```

太极是"未应用任何算子时的零位置" —— 所有位置链的根。可读为 `Unit` 或空 list `[]`。

R₀ 在 v2.1 中已显式纳入：[`R0_Taiji.lean`](../../formal/SSBX/Foundation/Hierarchy/R0_Taiji.lean)。

---

## 1. R₁：爻 / 两仪 = 2 位

```
阳 = 爻               或者写成: 𝟙 ∘ 爻
阴 = 易(阳) = 易(爻)   即: 易 ∘ 爻
```

- 阳 = "默认爻态" = 一次 yao 应用
- 阴 = 易 ∘ 阳 = 一次 易 算子作用

### R₁ 算子等价：

```
易² = id           (易∘易 = identity；involution)
∴ 阴 = 易(阳), 阳 = 易(阴)
```

R₁ 共 **2 个位置**。

---

## 2. R₂：四象 = 4 位

每位 = 两个爻的有序对 = 分²(爻, 爻)。

```
太阳 (夏) = 分(阳, 阳)   = 分(爻, 爻)
少阴 (秋) = 分(阳, 阴)   = 分(爻, 易(爻))
少阳 (春) = 分(阴, 阳)   = 分(易(爻), 爻)
太阴 (冬) = 分(阴, 阴)   = 分(易(爻), 易(爻))
```

### 缩写：用 ⟨..⟩ 记 yao 序

```
太阳 = ⟨阳, 阳⟩
少阴 = ⟨阳, 阴⟩
少阳 = ⟨阴, 阳⟩
太阴 = ⟨阴, 阴⟩
```

### 单字读法

```
夏 = ⟨阳, 阳⟩
秋 = ⟨阳, 阴⟩
春 = ⟨阴, 阳⟩
冬 = ⟨阴, 阴⟩
```

R₂ 共 **4 个位置**（= 2² = `Yao²`）。

---

## 3. R₃：八卦 = 8 位（4 substrate + 4 mark）

每位 = 三个爻的有序三元组 = 分³(爻, 爻, 爻)。

### 3.1 4 substrate (本组, palindromic / zong-fixed)

```
乾 (物 / 健) = ⟨阳, 阳, 阳⟩
坤 (事 / 顺) = ⟨阴, 阴, 阴⟩
离 (動 / 显) = ⟨阳, 阴, 阳⟩    ← y2 是中爻 (palindromic)
坎 (間 / 险) = ⟨阴, 阳, 阴⟩    ← y2 是中爻
```

### 3.2 4 mark (征组, directional / zong-mobile)

```
震 (勢 / 起) = ⟨阳, 阴, 阴⟩    ← 一阳在底, 突起
艮 (時 / 止) = ⟨阴, 阴, 阳⟩    ← 一阳在顶, 收止
巽 (幾 / 入) = ⟨阴, 阳, 阳⟩    ← 一阴在底, 微入
兑 (機 / 悦) = ⟨阳, 阳, 阴⟩    ← 一阴在顶, 释机
```

### 3.3 R₃ 等价表

| 卦象 | trigram | 本/征 名 | 单字 | 形式 |
|---|---|---|---|---|
| ⟨阳,阳,阳⟩ | 乾 | 物 | 健 | ⊤ / 𝟙 |
| ⟨阴,阴,阴⟩ | 坤 | 事 | 顺 | ⊥ / 𝟘 |
| ⟨阳,阴,阳⟩ | 离 | 動 | 显 | rewrite ⟶ |
| ⟨阴,阳,阴⟩ | 坎 | 間 | 险 | composition ∘ |
| ⟨阳,阴,阴⟩ | 震 | 勢 | 起 | momentum / arousal |
| ⟨阴,阴,阳⟩ | 艮 | 時 | 止 | halt / fixpoint |
| ⟨阴,阳,阳⟩ | 巽 | 幾 | 入 | limit / penetration |
| ⟨阳,阳,阴⟩ | 兑 | 機 | 悦 | event / occasion |

R₃ 共 **8 个位置**（= 2³ = `Yao³`），分 4 substrate (palindromic) + 4 mark (directional)。

### 3.4 R₃ 同层算子（爻位 flip + V₄ 外）

```
R₃ atomic XOR (3 generators):
  改: ⟨a, b, c⟩ → ⟨易(a), b, c⟩       (flip y1 inner / dong)
  化: ⟨a, b, c⟩ → ⟨a, 易(b), c⟩       (flip y2 inner / hua)
  变: ⟨a, b, c⟩ → ⟨a, b, 易(c)⟩       (flip y3 inner / bian)
  cuo = 改 ⊕ 化 ⊕ 变: ⟨a, b, c⟩ → ⟨易(a), 易(b), 易(c)⟩

R₃ V₄ 外 (非 XOR):
  zong: ⟨a, b, c⟩ → ⟨c, b, a⟩  (反序; 物理 T)
  错综 = cuo ∘ zong              (物理 PT)
  hu (Y combinator)              (R₃ 上 trivial / lift 来源 R₆+)
```

详细 inner / outer 拆分见 [operator-split.md](operator-split.md) (sibling, v3)。

---

## 4. R₄：面 (Mian) = 16 位 ⭐ v2.1 显式纳入

**新 algebraic spine**：R₄ = (Z/2)⁴ = 16 = Ben × Zheng（zong-orbit 4+4 拆分之 product）。

```
R₄ = Mian = Ben × Zheng  (Lean: BenZheng.lean)
   - Ben (4 substrate) = (Z/2)² = {物, 動, 間, 事}
   - Zheng (4 mark) = (Z/2)² = {幾, 勢, 機, 時}
```

每位 = 四个爻的有序四元组 = 分⁴(爻, 爻, 爻, 爻)，or 等价地 = (Ben, Zheng) pair。

```
R₄ 例:
   (物, 幾)  (物, 勢)  (物, 機)  (物, 時)
   (動, 幾)  (動, 勢)  (動, 機)  (動, 時)
   (間, 幾)  (間, 勢)  (間, 機)  (間, 時)
   (事, 幾)  (事, 勢)  (事, 機)  (事, 時)
```

R₄ 共 **16 个位置**（= 2⁴）。详见 [yi-RO-hierarchy.md §3.4](yi-RO-hierarchy.md#34-r₄--面-mian-)。

---

## 5. R₅：五爻 (Wuyao) = 32 位 ⭐ v2.1 显式纳入 (provisional)

**新 algebraic spine**：R₅ = (Z/2)⁵ = 32 = Mian × Bool（Mian 加一个独立 bit）。

```
R₅ = Wuyao  (Lean: Hierarchy/R5_Wuyao.lean)
   = Mian × Bool
```

R₅ 是 R-hierarchy 中**唯一无传统 Yi anchor** 之层 —— 它 mathematically 存在但 philosophically 未独立刻画；是「(Z/2)ⁿ 机械补全」之产物（详 [yi-RO-hierarchy.md §3.5](yi-RO-hierarchy.md#35-r₅--五爻-5-yao--新显式纳入-provisional)）。

R₅ 共 **32 个位置**（= 2⁵）。

---

## 6. R₆：六十四卦 = 64 位

每位 = 乘(inner_trigram, outer_trigram) = 一对 trigram 合成的 hexagram = 6-yao 序列。

### 6.1 公式

```
六十四卦[i, j] = 乘(分³_i, 分³_j)
              = ⟨a, b, c, d, e, f⟩  其中 ⟨a,b,c⟩=inner, ⟨d,e,f⟩=outer
```

### 6.2 4 象限 (按 (inner本/征, outer本/征))

```
本本卦 (16): inner ∈ {乾,坤,离,坎}, outer ∈ {乾,坤,离,坎}
本征卦 (16): inner ∈ {乾,坤,离,坎}, outer ∈ {震,艮,巽,兑}
征本卦 (16): inner ∈ {震,艮,巽,兑}, outer ∈ {乾,坤,离,坎}
征征卦 (16): inner ∈ {震,艮,巽,兑}, outer ∈ {震,艮,巽,兑}
```

完整 64 卦详 [`64-hexagram-grid.md`](64-hexagram-grid.md)。每卦的 operator tree：

```
1乾   = 乘(乾, 乾)        = 乘(⟨阳,阳,阳⟩, ⟨阳,阳,阳⟩)        = ⟨阳⁶⟩
2坤   = 乘(坤, 坤)        = ⟨阴⁶⟩
11泰  = 乘(乾, 坤)        = ⟨阳,阳,阳, 阴,阴,阴⟩
12否  = 乘(坤, 乾)        = ⟨阴,阴,阴, 阳,阳,阳⟩
63既济 = 乘(离, 坎)        = ⟨阳,阴,阳, 阴,阳,阴⟩
64未济 = 乘(坎, 离)        = ⟨阴,阳,阴, 阳,阴,阳⟩
51震  = 乘(震, 震)        = ⟨阳,阴,阴, 阳,阴,阴⟩
52艮  = 乘(艮, 艮)        = ⟨阴,阴,阳, 阴,阴,阳⟩
57巽  = 乘(巽, 巽)        = ⟨阴,阳,阳, 阴,阳,阳⟩
58兑  = 乘(兑, 兑)        = ⟨阳,阳,阴, 阳,阳,阴⟩
... (60 more)
```

### 6.3 R₆ 同层算子 (6 爻 flip + 整卦)

```
R₆ atomic XOR (6 generators):
  改 = flip y1 (inner): ⟨a₁,a₂,a₃,a₄,a₅,a₆⟩ → ⟨易(a₁),...⟩
  化 = flip y2 (inner): → ⟨a₁,易(a₂),a₃,...⟩
  变 = flip y3 (inner): → ⟨...,易(a₃),...⟩
  临 = flip y4 (outer): → ⟨...,易(a₄),...⟩
  主 = flip y5 (outer): → ⟨...,易(a₅),...⟩
  极 = flip y6 (outer): → ⟨...,易(a₆)⟩

R₆ V₄ 外 (非 XOR):
  错 = 全反 = 改⊕化⊕变⊕临⊕主⊕极  (= XOR with `xxxxxx`)
  综 = 反序: ⟨a₆,a₅,a₄,a₃,a₂,a₁⟩
  互 (hu) = 取 y2-y5 重组
  错综 = 错 ∘ 综
```

inner (改/化/变) vs outer (临/主/极) 之拆分，详见 [operator-split.md](operator-split.md) (sibling, v3)。

R₆ 共 **64 个位置**（= 2⁶）。

---

## 7. R₇：因卦 (Cell128) = 128 位

每位 = (Hex, YinBit) = (Hex, 是否有因)。

```
R₇ = Cell128 = Hexagram × YinBit  (Lean: Cell128.lean)
```

YinBit ∈ {false, true} 是第 7 个 bit（"因" 是否标记）。

### 7.1 R₇ 新 atom

```
印 (yìn) = XOR with mask (qian, ji)
       = OX["ooooooxo"]
       = toggle 因 bit (位置 7)
```

物理上：印 是 past-cone marker 的 toggle —— "无因 ↔ 有因" 之翻转。

R₇ 共 **128 个位置**（= 2⁷ = 64 × 2）。

---

## 8. R₈：果卦 (Cell256) = 256 位 — 闭合层

每位 = (Hex, Shi) = (R₆ × V₄ Shi)。

```
R₈ = Cell256 = Hexagram × Shi V₄  (Lean: Cell256.lean)
   - Shi V₄ = {道, 已, 今, 未} = Klein 4-group
   - Shi.toYinGuo 双射: Shi ↔ YinBit × GuoBit
```

### 8.1 V₄ Shi 之 4 元

| Shi | (因, 果) | mask 后 2 位 | V₄ 元 | 与乾合 R₈ cell |
|---|---|---|---|---|
| 道 | (0, 0) | `oo` | identity | `OX["oooooooo"]` (= origin) |
| 已 | (1, 0) | `xo` | σ_P | `OX["ooooooxo"]` |
| 未 | (0, 1) | `ox` | σ_T | `OX["ooooooox"]` |
| 今 | (1, 1) | `xx` | σ_PT | `OX["ooooooxx"]` |

### 8.2 R₈ 新 atom

```
投 (tóu) = XOR with mask (qian, wei)
       = OX["ooooooox"]
       = toggle 果 bit (位置 8)

V₄ Shi 之 cuo (= Shi.cuo) = 印 ⊕ 投
       = OX["ooooooxx"]
       = (V₄ 内 PT-element σ_PT)
       = 道↔今, 已↔未 之 swap
```

物理上：投 是 future-cone marker 的 toggle；印 ⊕ 投 是 V₄ 内之 cuo involution（period 2，self-inverse）。

### 8.3 R₈ 同层算子（XOR + V₄ 外）

R₈ atomic XOR generators (8 个)：

```
内 3 (R₃ inner level):  改 (y₁)  化 (y₂)  变 (y₃)
外 3 (R₆ outer level):  临 (y₄)  主 (y₅)  极 (y₆)
Shi 2 (R₈ Shi level):    印 (y₇ = 因)  投 (y₈ = 果)
```

8 个 XOR generators 完全生成 (Z/2)⁸ = 256 个 XOR 算子。

R₈ V₄ 外（非 XOR）：

```
R₆-cuo (= XOR with `xxxxxxoo`)        - hex 全反, Shi 不动
R₆-zong (= 反序 of inner+outer 6 yao) - hex 反序, Shi 不动
R₆-hu (Y combinator)                   - hex 互, Shi 不动
Shi.cuo (= 印 ⊕ 投)                    - hex 不动, Shi V₄ cuo
```

V₄ × V₄ 双 V₄ 在 R₈ 上同时活动：(R₆ side V₄) × (Shi side V₄)。

### 8.4 R₈ 是 (Z/2)ⁿ 闭合（无 R₉）

R-hierarchy 在 R₈ 闭合。无 R₉ —— 无第 9 个独立 binary axis。

R₈ 共 **256 个位置**（= 2⁸ = 64 hex × 4 Shi V₄）。详细 256 cell 全表见 [cell256-grid.md](cell256-grid.md) (sibling, v3 并行写入)。

---

## 9. ontological grid：本/征 算子作为位置生成器

这是用户洞察的核心层次 —— 把 物動間事 / 幾勢機時 视为算子，而非位置。

### 9.1 基础定义

把 4 substrate 算子读作"投影/累积"算子：
- **物 (entity)** = 累积成实在 (∫-like)
- **動 (process)** = 累积成过程
- **間 (relation)** = 累积成关系
- **事 (event)** = 累积成事件

把 4 mark 算子读作"微分/突现"算子：
- **幾 (subtle)** = 微分成端倪 (d-like)
- **勢 (momentum)** = 微分成趋势
- **機 (occasion)** = 微分成时机
- **時 (time)** = 微分成历时

注意：在 v2.1 R-spine 上，4 substrate × 4 mark = 16 = R₄ Mian = (Z/2)⁴ —— 是 algebraic next-up 之 first-class 层 ([yi-RO-hierarchy.md §3.4](yi-RO-hierarchy.md#34-r₄--面-mian-))。本 §9 之 4×4 ontological grid 与 R₄ Mian 是**同一 16 元 algebraic 对象的两套 reading**。

### 9.2 用户洞察的精确化

用户的观察："物(爻) = 幾, 物²(爻) = 实在, 爻可以分成 4 个"

精确意义：

```
物¹(爻) = 幾(物)        ← 一次累积爻 = 物的微面 = 实质萌
物²(爻) = 实在 = 物本身  ← 二次累积 = 完整实在
物²(分(爻)) = (動, 行, 化, 流) ← 累积 4 sub-yao = 4 substantial modes
```

也即：

```
分: 爻 → (爻₁, 爻₂, 爻₃, 爻₄)         "split into 4"
物²: pos → pos                          "make fully substantial"
物² ∘ 分: 爻 → (動, 行, 化, 流)         "4 substantial modes"
```

### 9.3 4×4 grid 的算子树命名

每 grid cell = 本_op²(分(爻))[mark_index]：

```
物² ∘ 分 → (動, 行, 化, 流)         在 (幾, 勢, 機, 時) projection
動² ∘ 分 → (萌, 长, 发, 续)         同上
間² ∘ 分 → (緣, 通, 会, 系)         同上
事² ∘ 分 → (兆, 趋, 变, 史)         同上
```

或更精确：每 cell 是 **本算子 × 征算子(爻)** 的复合：

```
動 = 物·幾(爻)        (物 行 with 幾 column)
行 = 物·勢(爻)
化 = 物·機(爻)
流 = 物·時(爻)

萌 = 動·幾(爻)
长 = 動·勢(爻)
发 = 動·機(爻)
续 = 動·時(爻)

緣 = 間·幾(爻)
通 = 間·勢(爻)
会 = 間·機(爻)
系 = 間·時(爻)

兆 = 事·幾(爻)
趋 = 事·勢(爻)
变 = 事·機(爻)
史 = 事·時(爻)
```

16 个 cell 总和 —— 这是 4×4 grid 的精确算子树命名（详 [layer-axis-graph.md §11](layer-axis-graph.md)）。

### 9.4 微积分 dual

```
分 ≈ d (导数 / 微分)
物² ≈ ∫ (积分)
动² ≈ d∫ ≈ id 但 phase shift
```

8 个 ontological 算子在 yao 上的 "calculus reading"：

| 算子 | calculus 类比 | 应用结果 |
|---|---|---|
| 物 | ∫ at peak | 累积到极值 (实在) |
| 事 | ∫ at trough | 累积到极反 (虚事) |
| 動 | ∫∂² | 二阶微分累积 (过程性) |
| 間 | ∫(-1)ⁿ ∂ | 离散希尔伯特变换 (关系性) |
| 幾 | d at start | 起点微分 (微入) |
| 勢 | d sustained | 持续微分 (推势) |
| 機 | δ-burst | 瞬时冲量 (机发) |
| 時 | step / Heaviside | 阶跃累积 (时序) |

---

### 9.5 完整算子规律：四组核心定律

把 §9.2-9.4 的零散观察整合为系统的**完整代数律**。

#### 律 I — 本算子迭代律（Substrate Iteration Law）

对**每一个** 本 N ∈ {物, 動, 間, 事}：

```
N⁰(爻) = 爻                                ← 零次迭代 = 恒等
N¹(爻) = (N, 幾)-cell                     ← 一次迭代 = N 之"幾面"
N²(爻) = N 自身                            ← 二次迭代 = N 之"实"
N²(分(爻)) = N-row in 4×4 grid (4 modes)   ← 二次迭代 + 分 = N 之四模
```

**直觉**：N¹ 是"刚开始 N"，N² 是"完整 N"，N²(分) 是"N 的 4 个细分模式"。

#### 律 II — 征算子迭代律（Mark Iteration Law）

对**每一个** 征 M ∈ {幾, 勢, 機, 時}：

```
M⁰(爻) = 爻
M¹(爻) = (物, M)-cell
M²(爻) = M 自身
M²(分(爻)) = M-column in 4×4 grid (4 modes)
```

**律 I 与律 II 是 dual** —— 4×4 grid 的行算子（律 I）和列算子（律 II）合作生成全 grid。

#### 律 III — 复合律（Composition Law）

本算子 与 征算子 复合 = 4×4 grid 的具体 cell：

```
∀ N ∈ 本, M ∈ 征:    N ∘ M (爻) = (N, M)-cell ∈ 4×4 grid
```

#### 律 IV — 对偶律（Duality Law）

```
N(M(爻)) ≅ M(N(爻))  (mod cuo/zong/hu equivalence)
```

复合算子在 cuo / zong / hu 等价之下交换 —— 这是 **本征对偶 (substrate-mark duality)** 的代数版。

#### 律 V — 12 grid 阶段复合律

对 N ∈ {物, 動, 間} 与 阶段 S ∈ {差, 识, 间, 事}：

```
N ∘ S (爻) = (N, S)-cell ∈ 12 grid

完整表（3 × 4 = 12 entries）:
                    差(爻)    识(爻)    间(爻)    事(爻)
        物 ∘    ─→  物         注意      模        文
        動 ∘    ─→  生         心        理        价值
        間 ∘    ─→  人         审校      证明      真理
```

详见 [sanben-sijieduan-grid.md](sanben-sijieduan-grid.md)。

#### 律 VI — 高阶迭代收敛律（Saturation Law）

```
∀ k ≥ 2: N^k(爻) ≡ N (mod isomorphism)
```

**N²(爻) 是 N 的 fixpoint** —— 二次迭代后 saturates。

#### 律 VII — 算子 involution / 周期律

| 算子 | 迭代律 | 类型 |
|---|---|---|
| 易 (yao flip) | 易² = id | involution (Z/2) |
| 错 (cuo) | 错² = id | involution (Z/2) |
| 综 (zong) | 综² = id | involution (Z/2) |
| 改 / 化 / 变 / 临 / 主 / 极 | flip² = id | each Z/2 |
| 印 (yìn) | 印² = id | involution (Z/2) |
| 投 (tóu) | 投² = id | involution (Z/2) |
| 印 ⊕ 投 (= Shi.cuo) | (印⊕投)² = id | involution (Z/2) |
| 互 (hu) | 互^? — 多步收敛到 4 attractor | converges (not Z/k) |
| 分 / 合 (Lift / Project) | 合 ∘ 分 = id (left inv only) | left-adjoint |
| 乘 (chong) | 不可逆 (one-way) | mono (R₃ × R₃ → R₆) |
| 置 (set Shi on R₈) | 置 ∘ 置 = 置 (idempotent on shi) | retraction |
| N 本算子 | N² 饱和 | saturating |
| M 征算子 | M² 饱和 | saturating |

注：v3 之 V₄ Shi 是 Klein 4-group，每元自逆 —— `Shi.next` (从 v1 之 Z/3 cycle 升级) 现在是 Shi.cuo involution（period 2），不再是 period-3 cycle。

#### 律 VIII — 分配律（Distribution Law）

```
N(分(P, Q)) = 分(N(P), N(Q))         ← 本算子 分配于 分
```

#### 律 IX — Shi 独立律（Shi Independence Law）

```
对 hex 算子 Op (改/化/变/临/主/极/错/综/互):
  Op ∘ 印 = 印 ∘ Op       ← 任何 hex 算子与 印 (yin) 交换
  Op ∘ 投 = 投 ∘ Op       ← 同样

∴ Cell256 = Hexagram × Shi 是 direct product
```

R₈ direct product 结构在 commit 7de5064 之 algebraic spine 之后是 **AddCommGroup-strict**：Cell256 现在是 (Z/2)⁸ abelian 群之 Cayley regular representation 的 carrier（详 [cell256-algebra.md](cell256-algebra.md)）。

#### 律 X — 同源律（Common Origin Law）

```
∀ position P in system:
  ∃ 算子树 T:  P = T(爻)
  且 T uses only ~32 atomic operators

∴ 爻 是系统唯一原子
∴ 整个系统是 (~32 算子)* 应用于 爻 的封闭代数
```

---

### 9.6 完整规律 cheat-sheet

```
律 I    本迭代:    N¹(爻) = N之幾面;  N²(爻) = N;  N²(分(爻)) = N-row
律 II   征迭代:    M¹(爻) = M之物面;  M²(爻) = M;  M²(分(爻)) = M-column
律 III  本征复合:  N ∘ M (爻) = (N, M)-cell of 4×4 grid (= R₄ Mian)
律 IV   对偶:      N(M(爻)) ≅ M(N(爻)) (mod cuo/zong/hu)
律 V    12 grid:   N ∘ S (爻) = (N, S)-cell of 3×4 grid
律 VI   饱和:      N^(k≥2)(爻) ≡ N
律 VII  周期:      算子各自的 involution / cycle / saturation
律 VIII 分配:      N(分(P,Q)) = 分(N(P), N(Q))
律 IX   独立:      hex 算子 与 印/投 commute (R₈ = R₆ × Shi V₄ direct product)
律 X    同源:      ∀ P. ∃T. P = T(爻), T 使用 ≤32 原子算子
```

---

## 10. 12 grid (3 本 × 4 阶段) 的算子树

12 grid 的每 cell = 本_op × 阶段_op (爻)：

```
(物, 差) = 物·差(爻) = 物 (粗实)
(物, 识) = 物·识(爻) = 注意
(物, 间) = 物·间(爻) = 模
(物, 事) = 物·事(爻) = 文

(動, 差) = 動·差(爻) = 生
(動, 识) = 動·识(爻) = 心
(動, 间) = 動·间(爻) = 理
(動, 事) = 動·事(爻) = 价值

(間, 差) = 間·差(爻) = 人
(間, 识) = 間·识(爻) = 审校
(間, 间) = 間·间(爻) = 证明
(間, 事) = 間·事(爻) = 真理
```

详 [sanben-sijieduan-grid.md](sanben-sijieduan-grid.md)。

---

## 11. 名册线 (M-line) 的算子树

名册线 (Face / CoreAtom / AtomName) 是另一个轴的算子化。

### 11.1 Face

```
12 Face = SanBen × SiJieduan = (3 本) × (4 阶段)  -- 待重构 (与 main @ 1c76a55 上 Face 12-inductive 并存)
```

每 Face 是 12 grid 的一个 cell，详 §10。

具体 12 Face 的算子树（候选 mapping）：

```
文面     = (物, 事)·爻        (物 in event = recorded text)
物面     = (物, 差)·爻        (substantive in raw distinction)
生面     = (動, 差)·爻        (process in raw distinction)
理面     = (動, 间)·爻        (process in structure = logic)
心面     = (動, 识)·爻        (process being identified = perception)
人面     = (間, 差)·爻        (relation in raw form = inter-being)
模面     = (物, 间)·爻        (substantive in structure)
审校面   = (間, 识)·爻        (relation being identified = audit)
价值面   = (動, 事)·爻        (process in event = valuation)
证明面   = (間, 间)·爻        (relation in structure = proof)
注意面   = (物, 识)·爻        (substantive being identified)
真理面   = (間, 事)·爻        (relation in event = eternal truth)
```

### 11.2 CoreAtom (44 个)

每 CoreAtom 是一个被 register 为 hash key 的 yao-algebra position。它们在 [`MonadRoot.lean`](../../formal/SSBX/Foundation/Core/MonadRoot.lean) 内是 inductive 枚举。

每 CoreAtom 的算子树 = 它在 12 Face × 算子链 上的 unique address。

### 11.3 AtomName (333 个)

每 AtomName 是被 register 为 surface 字面的 position。它们的算子树是 (CoreAtom × specifier)·爻。

详细 333 字的算子树超出本文范围，详 [`Roster.lean`](../../formal/SSBX/Roster.lean)。

---

## 12. 完整位置清单 — 算子树 summary（v3 R₀..R₈）

按 layer 总数：

| Layer | 算子树形 | 数 |
|---|---|---|
| R₀ 太极 | ε (空算子) | 1 |
| R₁ 爻 / 两仪 | 易⁰(爻), 易¹(爻) | 2 |
| R₂ 四象 | 分²(爻, 爻) | 4 |
| R₃ 八卦 | 分³(爻³) | 8 |
| **R₄ 面 (Mian)** | 分⁴(爻⁴) = (Ben, Zheng) | **16** |
| **R₅ 五爻 (Wuyao)** | 分⁵(爻⁵) = (Mian, Bool) | **32** |
| R₆ 六十四卦 | 乘(分³, 分³) | 64 |
| **R₇ 因卦 (Cell128)** | (Hex, YinBit), 印 加底 | **128** |
| **R₈ 果卦 (Cell256)** | (Hex, Shi V₄), 投 加底 | **256** |
| ontological 4×4 grid | 本·征·爻 (= R₄ Mian) | 16 |
| 12 Face / 阶段 grid | 本·阶·爻 | 12 |
| L0 BaguaWen 12 instr | 12 个 VM 算子 | 12 |
| 三显 (位場際) | 显(本·爻) | 3 |
| 三征 (幾勢機) | 征(本·爻) | 3 |
| 闸口 (開閉) | 2 | 2 |
| 合成 (網體流) | 3 | 3 |

**核心 R-line 累计 (R₀..R₈)**: 1 + 2 + 4 + 8 + 16 + 32 + 64 + 128 + 256 = **511 R-line positions**（v2.1 strict uniform total）

加 ontological / Face / Atom 字根：

| 层 | 数 |
|---|---|
| 4 本 | 4 |
| 4 征 | 4 |
| 4 阶段 | 4 |
| 12 Face (= 4×3 grid) | 12 |
| 16 grid cell (4×4 = R₄ Mian) | 16（与 R₄ 重合）|
| 44 CoreAtom | 44 |
| 333 AtomName | 333 |

**ontological / 名册累计**: 4 + 4 + 4 + 12 + 44 + 333 = **401 named positions**

**总位置数 (可命名 + 算子树可达)**: ~912 unique positions，全部从单一 yao 通过算子组合到达。

---

## 13. 算子树的递归形式

整个系统是一个 **recursive operator algebra**：

```
Position ::= 爻
           | 易(Position)                    -- yao flip
           | Lift_n(Position, Yao)           -- vertical extend (n=0..7)
           | Project_n(Position)             -- vertical reduce (n=0..7)
           | flip_i(Position)                -- horizontal flip at position i (i=1..8)
           | 错(Position) | 综(Position) | 互(Position)  -- whole-trigram/hex V₄ outer
           | 印(Position) | 投(Position)     -- R₇ / R₈ atom (toggle 因 / 果)
           | 乘(Position, Position)          -- chong (R₃ × R₃ → R₆)
           | 置_shi(Position)                -- temporal annotation on R₈
           | 本(Position)                    -- ontological projection (4 species)
           | 征(Position)                    -- ontological mark (4 species)
           | 阶段(Position)                  -- developmental stage (4)

Ontology base:
  本 ::= 物 | 動 | 間 | 事
  征 ::= 幾 | 勢 | 機 | 時
  阶段 ::= 差 | 识 | 间 | 事
  Shi (V₄) ::= 道 | 已 | 今 | 未    -- v3 升级 (旧 v1 是 Z/3 {ji, jin, wei})
  Yao ::= 阳 (= o = false) | 阴 (= x = true)
```

这是一个**完整的 type-theoretic grammar** —— 所有命名位置都是这个 grammar 的某个 derivation tree。

每个 position 有：
- **名** (其字面 name)
- **算子树** (其 grammar derivation)
- **代数等价类** (cuo / zong / hu 之下的 equivalence)
- **layer** (R 几 / M 几 / 阶段 / phase)

---

## 14. 简化记号 vs 完整算子树

为了实用性，常用 surface notation 替代算子树：

| Surface | 算子树 | OX 字面 |
|---|---|---|
| 阳 | 爻 | (single bit) |
| 阴 | 易(爻) | (single bit) |
| 太阳 | 分²(阳, 阳) | — |
| 乾 | 分³(阳, 阳, 阳) | — |
| 1乾 (R₆) | 乘(乾, 乾) | — |
| (1乾, 道) | OX["oooooooo"] | `oooooooo` |
| (1乾, 已) | 印 OX["oooooooo"] | `ooooooxo` |
| (1乾, 未) | 投 OX["oooooooo"] | `ooooooox` |
| (1乾, 今) | (印 ⊕ 投) OX["oooooooo"] | `ooooooxx` |
| 健 | 物·虚(乾) (= virtue char of 乾) | — |

详 [ox-notation.md](ox-notation.md) (sibling, v3) 关于 `OX["..."]` macro。

### 命名优先级（系统内）

1. 单字 surface name（最常用）
2. 双字（必要时）
3. 算子树（精确，machine-readable）
4. OX 字面（256-cell 场景，machine-readable）

例：
- 在 surface text 写 "乾" — 读者直接懂
- 在 type theory paper 写 "⊤" — 形式清楚
- 在 Lean code 写 `Trigram.qian` — 程序锚定
- 在底层证明中可展开为 `分³(阳, 阳, 阳)` — 结构透明
- 在 R₈ cell 处理写 `OX["oooooooo"]` — bit-level 精确

---

## 15. 算子树 = system 的 minimum self-description

这个算子树框架的关键特性：

1. **完备性**：所有命名位置（约 912 个）都能由 ~32 个原子算子有限组合得到。
2. **唯一性**：每个 position 在 cuo/zong/hu 等价之下有唯一最简算子树。
3. **代数性**：组合规则形成代数（结合律、commute、群结构 — R₈ 是 Cayley regular representation）。
4. **可计算性**：每个算子在 Lean 内是 `def` 或 `theorem`，可 `native_decide`。
5. **递归性**：grammar 是 recursive — 任意深度算子嵌套都合法。
6. **有限基**：原子算子集是 minimum complete generator。
7. **R₈ 闭合**：(Z/2)⁸ Cayley fusion 在 R₈ 之 self-action 严格成立 (Theorem 5.1 of [yi-RO-hierarchy.md](yi-RO-hierarchy.md))。

这是为什么这个 framework 能完整表达任何形式系统 —— 因为它是 **Lawvere fixed-point**（self-describing system）的具体 instantiation。

---

## 16. 关键示例：从爻到一切

```
爻
└─ 易(爻) = 阴

分(爻, 爻) = 太阳
分(爻, 易(爻)) = 少阴
分(易(爻), 爻) = 少阳
分(易(爻), 易(爻)) = 太阴

分(分(爻, 爻), 爻) = ⟨阳,阳,阳⟩ = 乾 = 物 = 健
分(分(爻, 爻), 易(爻)) = ⟨阳,阳,阴⟩ = 兑 = 機 = 悦
... (8 trigrams)

乘(乾, 乾) = ⟨阳⁶⟩ = 1乾
乘(坤, 坤) = ⟨阴⁶⟩ = 2坤
... (64 hexagrams)

R₈ (Cell256) atomic 应用:
  OX["oooooooo"]                      = (1乾, 道) = 道-anchor
  印 OX["oooooooo"]   = OX["ooooooxo"] = (1乾, 已)
  投 OX["oooooooo"]   = OX["ooooooox"] = (1乾, 未)
  (印⊕投) OX["oooooooo"] = OX["ooooooxx"] = (1乾, 今)
... (256 cells)

物²(爻) = 实在
物²(分(爻)) = 動 ∪ 行 ∪ 化 ∪ 流  ← 4 substantial modes
動²(分(爻)) = 萌 ∪ 长 ∪ 发 ∪ 续  ← 4 process modes
間²(分(爻)) = 緣 ∪ 通 ∪ 会 ∪ 系  ← 4 relation modes
事²(分(爻)) = 兆 ∪ 趋 ∪ 变 ∪ 史  ← 4 event modes
```

每一行都是一个**精确的算子构造** —— 从单一原子 "爻" 出发，通过有限算子组合，到达系统中**任意**命名位置。

---

## 17. 与 Lean code 的对接

| 算子 | Lean 实现 |
|---|---|
| 易 | [`Yao.neg`](../../formal/SSBX/Foundation/Yi/Yi.lean) |
| Lift_n / Project_n (R₀..R₈ pairs) | [`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) |
| 乘 (chong) | [`chong`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) |
| R₃ 改 / 化 / 变 (inner) | [`dong / hua / bian`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) |
| R₆ 临 / 主 / 极 (outer) | flip4..6, [`Hierarchy/Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) |
| 错 / 综 / 互 / 错综 (V₄ outer) | [`Hierarchy/Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) |
| 印 (yìn, R₇ atom) | [`Cell128.yin`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) |
| 投 (tóu, R₈ atom) | [`Cell256.tou`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) |
| Shi V₄ {道, 已, 今, 未} | [`Cell256.Shi`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) |
| `OX["xxxxxxxx"]` macro | [`OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) |
| Cayley ι/ε | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) (Phase A) |
| 4-quadrant invariants (BenZheng / Mian) | [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) |
| R₀..R₈ umbrella | [`RHierarchy.lean`](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean) |
| 本 / 征 / 阶段 algebra | TODO（详 [sanben-sijieduan-grid.md](sanben-sijieduan-grid.md) §8 重构方案）|

---

## 18. 待办

- [ ] 把 §13 的 grammar 形式化为 Lean inductive `Position`
- [ ] 把 §9 的 calculus dual 加为 theorem (e.g., `物_iter_2_yao_eq_full_substance`)
- [ ] 把 §14 的 surface-to-tree map 加为 `def positionToTree : Position → OperatorTree`
- [ ] 12 grid + 16 grid 的 algebraic equivalence (16 = R₄ Mian) 加为 theorem
- [ ] CoreAtom (44) 的算子树 unique address 在 [`MonadRoot.lean`](../../formal/SSBX/Foundation/Core/MonadRoot.lean) 加入 metadata field

---

## 附：所有命名位置 (按 layer 索引, R₀..R₈)

```
R₀       太极 = ε                                        (1)
R₁       阳 = 爻;     阴 = 易(爻)                       (2)
R₂       夏/秋/春/冬 (太阳/少阴/少阳/太阴)                 (4)
R₃ substrate  乾(物)/坤(事)/离(動)/坎(間)               (4)
R₃ mark       震(勢)/艮(時)/巽(幾)/兑(機)               (4)
R₃ total                                                (8)
R₄       16 mian = (Ben × Zheng)                         (16)
R₅       32 wuyao = (Mian × Bool, provisional)           (32)
R₆       64 hexagrams (序卦传 1-64)                       (64)
R₇       128 = 64 × YinBit (Cell128)                     (128)
R₈       256 = 64 × Shi V₄ {道, 已, 今, 未} (Cell256)     (256)
4×4 ontological grid: 動/行/化/流, 萌/长/发/续,
                       緣/通/会/系, 兆/趋/变/史            (16, ≅ R₄ Mian)
12 grid: 物/注意/模/文, 生/心/理/价值,
         人/审校/证明/真理                               (12)
12 Face: 文/物/生/理/心/人/模/审校/价值/证明/注意/真理      (12)
44 CoreAtom: 一/元/之/法/.../子                          (44)
333 AtomName: (Roster.lean enumeration)                  (333)
12 L0 instructions: 静/置/翻/互/错/综/侔/会/跳/推/取/终    (12)
```

总计 **~912 named positions**, all expressible as 算子(爻) trees over ~32 atomic operators.

---

## 19. 一句话总结

> **整个系统的所有命名位置都是 ~32 个原子算子有限组合应用于唯一原子 "爻" 的 derivation tree；R₀..R₈ strict (Z/2)ⁿ uniform spine 在 R₈ 之 256-cell 上闭合（Cayley regular representation + V₄ Shi outer），无 R₉。**

这是 SSBX 系统的 **minimum self-description** —— 它通过这套算子树代数，把全部命名实体表达为同一个起点 ("爻") 的有限构造。

这就是为什么用户的直觉 "爻 → 物(爻) = 几 → 物(物(爻)) = 实在" 是对的 —— **所有位置都是算子作用于爻的结果**，而具体的运算路径就是这个位置的算子树命名。

---

## 形式锚

- [`formal/SSBX/Foundation/Yi/Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) — `Yao` (R₁) + `Trigram` (R₃) + `Hexagram` (R₆) + cuo/zong/hu/Yao.neg
- [`formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) — `SiXiang` (R₂) + dong/hua/bian + chong + Sheng
- [`formal/SSBX/Foundation/Bagua/BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) — `Mian` (R₄) + `Quadrant` invariants
- [`formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean`](../../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean) — `Wuyao` (R₅, Mian × Bool)
- [`formal/SSBX/Foundation/Bagua/Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) — R₇ + `yin` (印, XOR mask)
- [`formal/SSBX/Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) — R₈ + `Shi` V₄ + `tou` (投, XOR mask) + Cayley ι/ε
- [`formal/SSBX/Foundation/Hierarchy/RHierarchy.lean`](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean) — R₀..R₈ umbrella
- [`formal/SSBX/Foundation/Hierarchy/LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) — uniform Lift / Project pairs
- [`formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) — atomic XOR generators
- [`formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) — V₄ Klein outer (zong/cuoZong/hu)
- [`formal/SSBX/Foundation/Notation/OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) — `OX["xxxxxxxx"]` macro
- [`formal/SSBX/Foundation/Bagua/Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) — R₀..R₈ explicit + R8_complete bundle
- [`formal/SSBX/Foundation/Core/MonadRoot.lean`](../../formal/SSBX/Foundation/Core/MonadRoot.lean) — Face 12 + CoreAtom 44 + AtomName 333
- [`formal/SSBX/Roster.lean`](../../formal/SSBX/Roster.lean) — atomName enumeration
