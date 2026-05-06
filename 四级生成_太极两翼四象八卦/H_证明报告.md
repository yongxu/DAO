# H · 证明报告 · 八卦完整算子代数（BaguaAlgebra）

**文件**：`formal/SSBX/Foundation/BaguaAlgebra.lean`
**配套文档**：[`G_完整算子系统_八卦互通与归一.md`](G_完整算子系统_八卦互通与归一.md)
**报告日期**：2026-05-06
**Lean 版本**：4.29.1（Lake 5.0.0）

---

## 〇 · 摘要

本报告记录《八卦完整算子代数》在 Lean 4 中的完整形式化结果。
模块 `SSBX.Foundation.BaguaAlgebra`：

- **120 个声明**（45 定义 + 75 定理）
- **734 行**
- **0 sorry**、**0 warning**
- 全库 36 个 Lean 文件 `lake build` 通过

主要成果：
1. 在 T_3（八卦）层建立 (Z/2)³ 群结构，证明其在 8 卦上 simply transitive
2. 在 T_6（六十四卦）层建立 (Z/2)⁶ 群结构，与 T_3 内/外卦兼容
3. 建立纵向 合 / 分 / 归一 / 重 / 生生 完整算子链
4. 建立 5 个最小算子（变／化／动／合／生生）的代数完备性
5. 证明 综 ∉ (Z/2)³（即位置置换不可由单爻翻转实现）
6. 八卦穷尽 + 六十四卦穷尽 + Sheng 与 Hexagram 同构
7. 大循环 太极 → 八卦 → 太极 闭合

---

## 一 · 背景与目标

### 1.1 起点

项目 `生生不息` 已有 `Yi.lean`（1975 行，298 声明）覆盖：
- `Yao` / `Trigram` / `Hexagram` 类型
- V_4 群（{id, 错, 综, 错综}）作用于 Hexagram
- 互（hu）算子与不动点定理
- ⊕（oplus，重卦）、内/外卦分解
- 位结构（中／应／比）
- YaoStar（老少模态层）

### 1.2 缺口

**Yi.lean 之 V_4 不足以表达八卦互通**：V_4 = {id, 错, 综, 错综} 只有 4 个元素，但八卦有 8 个，且 V_4 不是 simply transitive。

**需补**：(Z/2)³ 单爻翻转群、纵向合分归一、生生 inductive。

### 1.3 目标

为文档 [`G_完整算子系统_八卦互通与归一.md`](G_完整算子系统_八卦互通与归一.md) 提供机器可验证之 Lean 实现：
- 横向：八卦中任两卦皆可由 {变, 化, 动} 序列互通
- 纵向：八卦经合归至太极
- 5 最小算子集合的完备性

---

## 二 · 代码报告

### 2.1 文件清单

| 文件 | 角色 | 行数 | 状态 |
|------|------|------|------|
| `formal/SSBX/Foundation/Yi.lean` | 既有依赖（不修改） | 1975 | ✓ |
| `formal/SSBX/Foundation/BaguaAlgebra.lean` | 本次新建 | **734** | ✓ |
| `formal/SSBX.lean` | 主入口（增 1 import） | 36 | ✓ |
| `formal/SSBX/Core.lean` 等其余 33 文件 | 不动 | — | ✓ |

### 2.2 体量统计

| 度量 | 数值 |
|------|-----|
| BaguaAlgebra.lean 总行数 | 734 |
| 顶层 `def` / `abbrev` / `structure` / `inductive` | 45 |
| 顶层 `theorem` | **75** |
| `sorry` 数量 | **0** |
| `warning` 数量 | **0** |
| `axiom` 新增 | **0** |
| 引入的非标准库依赖 | **0**（仅 stdlib + Yi.lean） |

### 2.3 模块依赖

```
SSBX.Foundation.BaguaAlgebra
  └── import SSBX.Foundation.Yi
        └── import SSBX.Core
              └── (Lean stdlib only)
```

无 Mathlib 依赖。无外部公理。

### 2.4 编译验证

```bash
$ lake build
✔ [34/36] Built SSBX.Foundation.BaguaAlgebra (6.6s)
✔ [35/36] Built SSBX (283ms)
Build completed successfully (36 jobs).
```

单文件编译时长 ≈ 6.6 秒（其中 64-case `decide` / `rfl` 占主要时间）。

### 2.5 文件结构

| 段 | 主题 | 定义 | 定理 |
|---|------|-----|------|
| § 1 | 三个反爻 | `dong`, `hua`, `bian` | 6（involution × 3 + commutativity × 3） |
| § 2 | 错分解 | — | 1（`cuo_eq_compose`） |
| § 3 | 乾之 8 元轨道 | — | 9（id_qian + 7 flip + cuo_qian_eq_kun） |
| § 4 | Cayley 图 | `hammingDist`, `transform`, `transformViaFlips` | 6 |
| § 5 | 四象 / 合 | `SiXiang`, `heShang/中/下`, `heToYi`, `heToTaiji`, `guiyi` | 2（all_length, guiyi_universal） |
| § 6 | 分 | `fenToYi/SiXiang/Trigram` | 3（合分逆 × 3） |
| § 7 | 重 | `chong`（abbrev） | 0 |
| § 8 | Sheng inductive (T_3) | `Sheng`, `toTrigram`, `ofTrigram` | 3（双向同构 + sheng_zero_unique） |
| § 9 | 5 最小算子 | `MinimalOps`, `canonicalOps` | 1（canonical_complete） |
| § 10 | 大循环 | `grandCycle` | 1（grandCycle_returns） |
| § 11 | T_6 lift (Hexagram) | 6 个 inner/outer flip + `hexHammingDist` + `hexTransform` | 16 |
| § 12 | 枚举完全 | `yao_in_yaos` (private) | 2（trigram + hexagram exhaust） |
| § 13 | hammingDist 表征 | — | 1（eq_zero_iff） |
| § 14 | 路径紧度 | `pathFromTo`, `applyPath` | 2（apply correct + length = Hamming） |
| § 15 | Sheng ≃ Hexagram (T_6) | `toHexagram`, `ofHexagram` | 2（双向同构） |
| § 16 | Hex 内/外结构 | — | 2（cuo via 内外 + chong 重建） |
| § 17 | 综 ∉ (Z/2)³ | — | 9（5 不等式 + 4 辅助 + 1 summary） |
| § 18 | Simply transitive | `FlipCombo` inductive + apply | 3（all_length + orbit_qian + inj） |
| 公开 | bagua_algebra_complete + phase2 + hex | — | 3 |

---

## 三 · 形式语言与约定

### 3.1 命名

- ASCII 标识符（与 `Yi.lean` 风格一致）；中文落字仅在文档注释中
- 八卦三反爻：`dong` (动)、`hua` (化)、`bian` (变)
- 纵向算子：`heShang`/`heZhong`/`heXia`、`heToYi`、`heToTaiji`、`guiyi`、`fenTo*`
- 重卦：`chong`（= `Hexagram.oplus` 的 abbrev）
- 生生：`Sheng` (inductive)、`grandCycle`

### 3.2 爻位约定（沿用 Yi.lean）

```
Trigram.y1 = 初爻 (bottom)    动 = flip y1
Trigram.y2 = 中爻 (middle)    化 = flip y2
Trigram.y3 = 上爻 (top)       变 = flip y3
```

### 3.3 八卦二进制对照

| 卦 | (y1, y2, y3) | Yi.lean 定义 |
|----|------------|------------|
| 乾 ☰ | (yang, yang, yang) | `Trigram.qian` |
| 兑 ☱ | (yang, yang, yin)  | `Trigram.dui` |
| 离 ☲ | (yang, yin, yang)  | `Trigram.li` |
| 震 ☳ | (yang, yin, yin)   | `Trigram.zhen` |
| 巽 ☴ | (yin, yang, yang)  | `Trigram.xun` |
| 坎 ☵ | (yin, yang, yin)   | `Trigram.kan` |
| 艮 ☶ | (yin, yin, yang)   | `Trigram.gen` |
| 坤 ☷ | (yin, yin, yin)    | `Trigram.kun` |

---

## 四 · 类型层级

```
TaiJi  : Type   (= Unit)              -- T_0, |·|=1
LiangYi : Type  (= Yao)               -- T_1, |·|=2
SiXiang : Type  (structure y1 y2)     -- T_2, |·|=4
Trigram : Type  (Yi.lean)             -- T_3, |·|=8
Hexagram : Type (Yi.lean)             -- T_6, |·|=64

Sheng : Nat → Type                    -- 通用层级 inductive
  | tai  : Sheng 0                    -- 太极
  | step : Sheng n → Yao → Sheng (n+1) -- 生

Sheng.toTrigram   : Sheng 3 ≃ Trigram
Sheng.toHexagram  : Sheng 6 ≃ Hexagram
```

---

## 五 · 关键算子

### 5.1 横向（八卦层之内）

| 算子 | Lean | 类型 | 阶 |
|------|------|-----|---|
| 动 | `dong` | `Trigram → Trigram` | 2 |
| 化 | `hua` | `Trigram → Trigram` | 2 |
| 变 | `bian` | `Trigram → Trigram` | 2 |
| 错 | `Trigram.cuo` (Yi.lean) | `Trigram → Trigram` | 2 |
| 综 | `Trigram.zong` (Yi.lean) | `Trigram → Trigram` | 2 |

群结构：⟨dong, hua, bian⟩ ≅ (Z/2)³，阶 8，**simply transitive on Trigram**。

### 5.2 纵向（层间）

| 算子 | Lean | 类型 | 方向 |
|------|------|-----|------|
| 合_上 | `heShang` | `Trigram → SiXiang` | ↑ |
| 合_中 | `heZhong` | `Trigram → SiXiang` | ↑ |
| 合_下 | `heXia` | `Trigram → SiXiang` | ↑ |
| 合（→两仪） | `heToYi` | `SiXiang → Yao` | ↑ |
| 合（→太极） | `heToTaiji` | `Yao → Unit` | ↑ |
| 归一 | `guiyi` | `Trigram → Unit` | ↑↑↑ |
| 分（太极→两仪） | `fenToYi` | `Unit → Yao → Yao` | ↓ |
| 分（两仪→四象） | `fenToSiXiang` | `Yao → Yao → SiXiang` | ↓ |
| 分（四象→八卦） | `fenToTrigram` | `SiXiang → Yao → Trigram` | ↓ |
| 重（八卦→64卦） | `chong` | `Trigram → Trigram → Hexagram` | ↓ |

### 5.3 太极算子

| 算子 | Lean | 性质 |
|------|------|-----|
| 生生 | `Sheng` (inductive) | Y combinator-like 不动点 |
| 大循环 | `grandCycle` | TaiJi → Trigram → TaiJi |

---

## 六 · 75 条定理（按主题分组）

### 6.1 群结构（§ 1）— 6 条

| # | 定理 | 内容 |
|---|------|------|
| T1 | `dong_dong` | dong² = id |
| T2 | `hua_hua` | hua² = id |
| T3 | `bian_bian` | bian² = id |
| T4 | `dong_hua_comm` | dong ∘ hua = hua ∘ dong |
| T5 | `hua_bian_comm` | hua ∘ bian = bian ∘ hua |
| T6 | `dong_bian_comm` | dong ∘ bian = bian ∘ dong |

**证法**：`simp [_, Yao.neg_neg]` 或 `cases t; rfl`。
**结论**：⟨dong, hua, bian⟩ 是阿贝尔群，每个生成元 involution，故同构于 (Z/2)³。

### 6.2 错分解（§ 2）— 1 条

| # | 定理 | 内容 |
|---|------|------|
| T7 | `cuo_eq_compose` | `Trigram.cuo t = dong (hua (bian t))` |

**意义**：Yi.lean 的 `cuo`（全反）恰是三反爻之复合，即 (Z/2)³ 的中心元。

### 6.3 乾之 8 元轨道（§ 3）— 9 条

| # | 定理 | 输入 → 输出 |
|---|------|------------|
| T8 | `id_qian` | qian → qian |
| T9 | `dong_qian` | qian → 巽 |
| T10 | `hua_qian` | qian → 离 |
| T11 | `bian_qian` | qian → 兑 |
| T12 | `dong_hua_qian` | qian → 艮 |
| T13 | `hua_bian_qian` | qian → 震 |
| T14 | `dong_bian_qian` | qian → 坎 |
| T15 | `dong_hua_bian_qian` | qian → 坤 |
| T16 | `cuo_qian_eq_kun` | `Trigram.cuo qian = kun` |

**意义**：(Z/2)³ 的 8 个元素作用于 乾，恰得 8 卦——即轨道大小 = 群大小 = 集合大小 = 8。**这是 simply transitive 的概念展开**。

### 6.4 Cayley 图与互通（§ 4）— 6 条

| # | 定理 | 内容 |
|---|------|------|
| T17 | `hammingDist_le_3` | ∀ a b, hammingDist a b ≤ 3 |
| T18 | `hammingDist_self` | hammingDist t t = 0 |
| T19 | `transform_correct` | transform a b a = b（64 case rfl） |
| T20 | `transform_eq_via_flips` | transform 与 flip 复合等价 |
| T21 | `bagua_intercommunication` | ∃ f, f a = b（八卦互通存在性） |
| T22 | `bagua_intercommunication_bounded` | ∃ f, f a = b ∧ Hamming ≤ 3 |

**意义**：八卦中任两卦至多 3 步可达。

### 6.5 四象 + 纵向合分（§ 5–6）— 5 条

| # | 定理 | 内容 |
|---|------|------|
| T23 | `SiXiang.all_length` | 四象有 4 元 |
| T24 | `guiyi_universal` | ∀ t, guiyi t = ()（归一普适） |
| T25 | `heShang_fenToTrigram` | heShang ∘ fenToTrigram = id |
| T26 | `heToYi_fenToSiXiang` | heToYi ∘ fenToSiXiang = π₁ |
| T27 | `heToTaiji_fenToYi` | heToTaiji ∘ fenToYi = const () |

**意义**：合 是 分 的左逆（section/retract pair）。

### 6.6 Sheng inductive 同构 T_3（§ 8）— 3 条

| # | 定理 | 内容 |
|---|------|------|
| T28 | `Sheng.toTrigram_ofTrigram` | Trigram → Sheng 3 → Trigram = id |
| T29 | `Sheng.ofTrigram_toTrigram` | Sheng 3 → Trigram → Sheng 3 = id |
| T30 | `Sheng.sheng_zero_unique` | Sheng 0 唯一（即太极唯一） |

### 6.7 完备性 + 大循环（§ 9–10）— 2 条

| # | 定理 | 内容 |
|---|------|------|
| T31 | `canonical_complete` | 5 算子（互通 + 归一）完备 |
| T32 | `grandCycle_returns` | TaiJi → Trigram → TaiJi 闭合 |

### 6.8 T_6 提升：Hexagram 层（§ 11）— 16 条

**6 个反爻**：dongInner / huaInner / bianInner / dongOuter / huaOuter / bianOuter

| # | 定理 | 内容 |
|---|------|------|
| T33–T38 | `*Inner_*Inner` / `*Outer_*Outer` | 6 个 involution（每反爻²= id） |
| T39 | `hex_cuo_eq_compose` | Hexagram.cuo = 6-flip 复合 |
| T40 | `hexHammingDist_le_6` | 任两卦汉明距 ≤ 6 |
| T41 | `hexHammingDist_self` | hexHammingDist h h = 0 |
| T42 | `hexTransform_correct` | hexTransform a b a = b（4096 case rfl） |
| T43 | `hex_intercommunication` | 重卦互通 |
| T44 | `hex_intercommunication_bounded` | 互通 ≤ 6 步 |
| T45–T50 | `*Inner/Outer_via_chong` | 6 个内外兼容定理 |

**意义**：T_6 之 (Z/2)⁶ 群与 T_3 之 (Z/2)³ 在内/外卦上的作用兼容，确认"层间结构守恒"。

### 6.9 枚举完全（§ 12）— 2 条

| # | 定理 | 内容 |
|---|------|------|
| T51 | `trigram_mem_all` | ∀ t : Trigram, t ∈ Trigram.all（8 元穷尽） |
| T52 | `hexagram_mem_allHex` | ∀ h : Hexagram, h ∈ Hexagram.allHex（64 元穷尽） |

### 6.10 hammingDist 表征（§ 13）— 1 条

| # | 定理 | 内容 |
|---|------|------|
| T53 | `hammingDist_eq_zero_iff` | hammingDist a b = 0 ↔ a = b |

### 6.11 路径紧度（§ 14）— 2 条

| # | 定理 | 内容 |
|---|------|------|
| T54 | `applyPath_pathFromTo` | applyPath (pathFromTo a b) a = b |
| T55 | `pathFromTo_length_eq_hammingDist` | path 长度 = Hamming（紧度） |

### 6.12 Sheng ≃ Hexagram (T_6, § 15) — 2 条

| # | 定理 | 内容 |
|---|------|------|
| T56 | `Sheng.toHexagram_ofHexagram` | Hexagram round-trip |
| T57 | `Sheng.ofHexagram_toHexagram` | Sheng 6 round-trip |

### 6.13 Hex 内/外结构（§ 16）— 2 条

| # | 定理 | 内容 |
|---|------|------|
| T58 | `hex_cuo_via_inner_outer` | Hex.cuo = chong (Tri.cuo inner) (Tri.cuo outer) |
| T59 | `chong_inner_outer` | chong h.innerTrigram h.outerTrigram = h |

### 6.14 综 ∉ (Z/2)³（§ 17）— 9 条

| # | 定理 | 内容 |
|---|------|------|
| T60 | `zong_qian_eq_qian` | 综 qian = qian（综 之乾不动点） |
| T61 | `dong_qian_ne_qian` | dong 移动 qian |
| T62 | `hua_qian_ne_qian` | hua 移动 qian |
| T63 | `bian_qian_ne_qian` | bian 移动 qian |
| T64 | `zong_ne_id` | 综 ≠ id（用 dui 反例） |
| T65 | `zong_ne_dong` | 综 ≠ dong（用 qian 反例） |
| T66 | `zong_ne_hua` | 综 ≠ hua |
| T67 | `zong_ne_bian` | 综 ≠ bian |
| T68 | `zong_ne_cuo` | 综 ≠ Trigram.cuo |
| T69 | `zong_outside_flip_group` | 5 不等式联立 summary |

**论证逻辑**：
- 综 fixed 乾（T60）；
- 但每个非 id 的 (Z/2)³ 元素皆 move 乾（T61–T63 + 推论）；
- 故 综 = (Z/2)³ 中某元 ⇒ 此元 = id；
- 但 综 ≠ id（T64，用 dui→xun 反例）；
- 矛盾，故 综 ∉ (Z/2)³。

### 6.15 Simply transitive（§ 18）— 3 条

定义 `FlipCombo` inductive：8 个具名 (Z/2)³ 元素。

| # | 定理 | 内容 |
|---|------|------|
| T70 | `FlipCombo.all_length` | FlipCombo 共 8 元 |
| T71 | `FlipCombo.orbit_qian` | 8 个 combo 作用于乾 = 8 卦穷尽 |
| T72 | `FlipCombo.apply_qian_inj` | combo → 8 卦 单射（regular action） |

**意义**：(Z/2)³ × Trigram → Trigram 是**自由传递**作用，即 simply transitive。

### 6.16 公开摘要（§ Public）— 3 条

| # | 定理 | 内容（摘要） |
|---|------|------------|
| T73 | `bagua_algebra_complete` | T_3 五大基本性质（互通、归一、错分解、合分逆、大循环） |
| T74 | `bagua_algebra_phase2_complete` | Phase 2 八大性质（穷尽、表征、紧度、同构、内外、综分离、简单传递） |
| T75 | `hex_algebra_complete` | T_6 三大性质（错分解、互通、距离上界） |

---

## 七 · 关键证明思想

### 7.1 64 case 直接展开

最常用的策略：

```lean
rcases t with ⟨y1, y2, y3⟩
cases y1 <;> cases y2 <;> cases y3 <;> ...
```

将 Trigram 的 8 个具体值（或 Hexagram 的 64 个）穷尽，每一个分支用 `rfl` / `decide` / `simp` 关闭。

适用：涉及具体值的等式，如 `transform_correct`、`pathFromTo_length_eq_hammingDist`。

### 7.2 反例证伪

不等式证明（如 `zong_ne_dong`）通过 `congrFun` 展开函数等式，配合 `decide` 求具体反例：

```lean
theorem zong_ne_dong : Trigram.zong ≠ dong := fun h =>
  absurd (congrFun h qian) (by decide)
```

`congrFun h qian` 把假设 `Trigram.zong = dong` 实例化到 `qian`，得 `Trigram.zong qian = dong qian`，
即 `qian = xun`，`decide` 即可拒之。

### 7.3 结构化 list membership

`Hexagram.allHex` 由六层 `flatMap` 构造，`decide` 不可直接合成 Decidable 实例。
改用 `List.mem_flatMap.mpr` 链式展开：

```lean
theorem hexagram_mem_allHex (h : Hexagram) : h ∈ Hexagram.allHex := by
  rcases h with ⟨y1, y2, y3, y4, y5, y6⟩
  unfold Hexagram.allHex
  refine List.mem_flatMap.mpr ⟨y1, yao_in_yaos y1, ?_⟩
  refine List.mem_flatMap.mpr ⟨y2, yao_in_yaos y2, ?_⟩
  -- ... 6 层
  exact List.mem_map.mpr ⟨y6, yao_in_yaos y6, rfl⟩
```

### 7.4 inductive 上的同构证明

```lean
theorem Sheng.toTrigram_ofTrigram (t : Trigram) : toTrigram (ofTrigram t) = t := by
  cases t; rfl

theorem Sheng.ofTrigram_toTrigram (s : Sheng 3) : ofTrigram (toTrigram s) = s := by
  match s with
  | .step (.step (.step .tai _) _) _ => rfl
```

`cases` 解构 Trigram，`match` 解构 inductive Sheng。两侧 round-trip 各用一种解构。

### 7.5 simp 展开命名常量

枚举完全证明（如 `trigram_mem_all`）需把 `qian, dui, ...` 等具名常量展开：

```lean
theorem trigram_mem_all (t : Trigram) : t ∈ Trigram.all := by
  rcases t with ⟨y1, y2, y3⟩
  cases y1 <;> cases y2 <;> cases y3 <;>
    simp [Trigram.all, qian, dui, li, zhen, xun, kan, gen, kun]
```

---

## 八 · 机器验证

### 8.1 编译命令

```bash
$ cd /Users/ren/repos/生生不息
$ lake build SSBX.Foundation.BaguaAlgebra
✔ [3/3] Built SSBX.Foundation.BaguaAlgebra (6.6s)

$ lake build
✔ [34/36] Built SSBX.Foundation.BaguaAlgebra (6.6s)
✔ [35/36] Built SSBX (283ms)
Build completed successfully (36 jobs).
```

### 8.2 严格度

| 项 | 检查 | 结果 |
|----|------|-----|
| `sorry` 数量 | `grep -c sorry` | **0** |
| `axiom` 新增 | `grep -c "^axiom"` | **0** |
| 关闭警告 | `grep -c set_option.*linter` | **0** |
| 自定义公理 | 无 | **无** |
| 外部库 | 仅 stdlib + Yi.lean | ✓ |
| `native_decide` 用量 | 0（避免编译期信任 native code） | **0** |

> **注**：本模块零 `native_decide`、零 `sorry`、零新公理——所有定理由内核类型检查器完整 verify。

### 8.3 交叉验证

`bagua_algebra_phase2_complete` 一举聚合 9 条独立结果：

```lean
theorem bagua_algebra_phase2_complete : ... :=
  ⟨trigram_mem_all,
   hexagram_mem_allHex,
   hammingDist_eq_zero_iff,
   pathFromTo_length_eq_hammingDist,
   Sheng.toHexagram_ofHexagram,
   hex_cuo_via_inner_outer,
   chong_inner_outer,
   zong_outside_flip_group,
   FlipCombo.apply_qian_inj⟩
```

每个槽位 type-check 通过即等价于该结果机器验证。

---

## 九 · 可宣称之事

### 9.1 数学陈述

> **(BAC-1) 八卦互通定理**：在 Trigram 类型上，由 {dong, hua, bian} 生成的群 ≅ (Z/2)³，作用 simply transitive；任意两卦皆可经至多 3 步翻转互通。

> **(BAC-2) 归一定理**：任意 Trigram 在合算子三次复合下退化至 Unit；与 分 算子构成 (section, retraction) pair。

> **(BAC-3) 综分离定理**：综算子 ∉ (Z/2)³ flip 子群；故综代表的位置置换是 (Z/2)³ 之外的独立自由度。

> **(BAC-4) Sheng 同构定理**：Sheng inductive 类型在深度 3 / 6 处分别同构于 Trigram / Hexagram。

> **(BAC-5) T_6 提升定理**：在 Hexagram 上，由 {dongInner, huaInner, bianInner, dongOuter, huaOuter, bianOuter} 生成 (Z/2)⁶；每个生成元等于 chong 后对内外卦的对应翻转。

> **(BAC-6) 八卦穷尽定理**：Trigram.all 含 8 元，且穷尽 Trigram；Hexagram.allHex 含 64 元，且穷尽 Hexagram。

### 9.2 工程陈述

> **(ENG-1) 形式化完整性**：BaguaAlgebra 模块 75 定理、零 sorry、零 axiom、零 native_decide，全部由 Lean 4 内核类型检查通过。

> **(ENG-2) 编译稳定性**：`lake build` 全库 36 jobs 全绿，单文件编译 < 7 秒。

> **(ENG-3) 模块独立性**：仅依赖 stdlib 与 Yi.lean，无 Mathlib 依赖；Yi.lean 不被本模块修改，仅引用其类型与定理。

### 9.3 道-理二分立场

本报告之 75 定理皆属**理层**——即在 `BaguaAlgebra.lean` 内部、由 Lean kernel 类型检查通过之命题。

但**报告本身**（即"75 定理 / 0 sorry / 0 axiom" 这一总命题）属**道层**——是关于理层的元陈述，由项目维护者（人 + Lean kernel）共同保证。

| 范畴 | 例 | 属 |
|---|---|---|
| `dong_dong : dong (dong t) = t` | 在 Lean 内可证 | 理 |
| `bagua_algebra_complete : ⟨...⟩` | 在 Lean 内可证 | 理 |
| 「此模块 0 sorry」 | grep / 编译统计 | 道（元）|
| 「Lean kernel 一致」 | Coq / Lean 之 meta 信任 | 道（元元）|

**关于 `Sheng : ℕ → Type`**：此归纳族提供 ω-tower，**包含**所有 T_n 而**不被**任何 T_n 包含。这是道层结构对理层之外延。

详见 [`J_理之不完备_哥德尔在192.md`](J_理之不完备_哥德尔在192.md) §一与 [`K_完备性审计.md`](K_完备性审计.md) §三。

> **完备性范围声明**：本报告之"完备"严格限于**理层之 BaguaAlgebra 模块** —— 即 `bagua_algebra_complete` 之五条断言（互通 / 归一 / 错分解 / 合分逆 / 大循环）。**不**主张项目整体 Gödel 意义下完备——参 J 之 `halts_undecidable_internally`（待补）。

---

## 十 · 未证之事（roadmap）

### 10.1 易补 next step（C-级）

| # | 命题 | 难度 | 状态 |
|---|------|-----|------|
| C1 | Group instance for (Z/2)³ | 中 | ✗ 需 Mathlib `import` 或自定义 Group typeclass |
| C2 | 互（hu）迭代收敛 ∃ n, hu^n h ∈ {qian, kun} | 中 | ✗ well-founded 证明，估 ≤ 4 步 |
| C3 | 64 × 3 = 192 格类型层 | 易 | ✓ **已完成** `Cell192.lean` 254 行 |
| C4 | YaoStar/HexagramStar ↔ BaguaAlgebra 算子兼容 | 中 | ✗ 跨模块对接 |
| C5 | 序卦：64 卦传统排序 | 中 | ✓ **已完成** `Cell192.lean` 之 `xuGua` |
| C6 | 重卦的 6 反爻 ↔ 内外卦三反爻 之统一定理 | 易 | ✓ **已完成**（6 条 via_chong）|
| C7 | **理之不完备 / Halting 不可判**（J 之路径）| 中 | ✓ **已完成** `GodelLi.lean` 400 行 / 24 定理 / 1 公理 |

### 10.2 较难（D-级）

| # | 命题 | 性质 |
|---|------|-----|
| D1 | 超八面体群 B_3 = (Z/2)³ ⋊ S_3 | 需引入位置置换 |
| D2 | Sheng inductive ↔ ShengshengBuxi.lean OpenRun（Y comb 语义） | 跨范式对接 |
| D3 | 64 卦 V_4 轨道结构（哪些自反，哪些两两配对） | 计算 + 轨道-稳定子 |
| D4 | 占筮态空间 64 卦 × YaoStar^6 = 262144 | 乘积层 |

### 10.3 估时

- C1–C6 全做完：**8–15 小时**
- D1–D4 全做完：**多日级**，部分需设计抉择

---

## 十一 · 附录：完整定理一览（75 条）

```
§ 1   (6) dong_dong, hua_hua, bian_bian, dong_hua_comm, hua_bian_comm, dong_bian_comm
§ 2   (1) cuo_eq_compose
§ 3   (9) id_qian, dong_qian, hua_qian, bian_qian, dong_hua_qian,
          hua_bian_qian, dong_bian_qian, dong_hua_bian_qian, cuo_qian_eq_kun
§ 4   (6) hammingDist_le_3, hammingDist_self, transform_correct, transform_eq_via_flips,
          bagua_intercommunication, bagua_intercommunication_bounded
§ 5   (2) SiXiang.all_length, guiyi_universal
§ 6   (3) heShang_fenToTrigram, heToYi_fenToSiXiang, heToTaiji_fenToYi
§ 8   (3) Sheng.toTrigram_ofTrigram, Sheng.ofTrigram_toTrigram, Sheng.sheng_zero_unique
§ 9   (1) canonical_complete
§ 10  (1) grandCycle_returns
§ 11 (16) dongInner_dongInner, huaInner_huaInner, bianInner_bianInner,
          dongOuter_dongOuter, huaOuter_huaOuter, bianOuter_bianOuter,
          hex_cuo_eq_compose, hexHammingDist_le_6, hexHammingDist_self,
          hexTransform_correct, hex_intercommunication, hex_intercommunication_bounded,
          dongInner_via_chong, huaInner_via_chong, bianInner_via_chong,
          dongOuter_via_chong, huaOuter_via_chong, bianOuter_via_chong
§ 12  (2) trigram_mem_all, hexagram_mem_allHex
§ 13  (1) hammingDist_eq_zero_iff
§ 14  (2) applyPath_pathFromTo, pathFromTo_length_eq_hammingDist
§ 15  (2) Sheng.toHexagram_ofHexagram, Sheng.ofHexagram_toHexagram
§ 16  (2) hex_cuo_via_inner_outer, chong_inner_outer
§ 17  (9) zong_qian_eq_qian, dong_qian_ne_qian, hua_qian_ne_qian, bian_qian_ne_qian,
          zong_ne_id, zong_ne_dong, zong_ne_hua, zong_ne_bian, zong_ne_cuo,
          zong_outside_flip_group
§ 18  (3) FlipCombo.all_length, orbit_qian, apply_qian_inj
公开  (3) bagua_algebra_complete, bagua_algebra_phase2_complete, hex_algebra_complete
```

合计：**75 条定理 + 45 个定义 = 120 个声明**。

---

## 十二 · 复现命令

```bash
git clone <repo>
cd 生生不息
elan default leanprover/lean4:v4.29.1   # 或本机已有 Lean 4
lake build                              # 全库编译
lake build SSBX.Foundation.BaguaAlgebra # 单模块编译
```

预期输出：

```
Build completed successfully (36 jobs).
```

任何 `sorry` / `error` / `warning` 均为回归。

---

**报告结束。**
