# I · 八卦全集 · 字 · 符 · 爻 · 算子一一对应

**配套形式化**：[`formal/SSBX/Foundation/Yi.lean`](../formal/SSBX/Foundation/Yi.lean) · [`formal/SSBX/Foundation/BaguaAlgebra.lean`](../formal/SSBX/Foundation/BaguaAlgebra.lean)
**配套报告**：[`H_证明报告.md`](H_证明报告.md)
**修订日期**：2026-05-06

> 「无极生太极，太极生两仪，两仪生四象，四象生八卦，八卦相重而成六十四。」
>
> 本表为 75 条 Lean 定理（零 sorry）所确立之核结构对照册。

---

## 〇 · 总览

| 层 | Lean 类型 | |·| | 道家名 | 几何 |
|---|---|---|---|---|
| T₀ | `TaiJi` (`= Unit`) | 1 | 太极 | 点 |
| T₁ | `LiangYi` (`= Yao`) | 2 | 两仪 | Σ |
| T₂ | `SiXiang` | 4 | 四象 | Σ² |
| T₃ | `Trigram` | 8 | 八卦 | Σ³ |
| T₆ | `Hexagram` | 64 = 8 × 8 | 重卦 | Σ⁶ = Σ³ ⊕ Σ³ |

形式根：`Yao = {阳, 阴}`；`Trigram = ⟨y₁, y₂, y₃⟩`，y₁ = 初爻 (下)，y₃ = 上爻 (顶)。
枚举闭合：`trigram_mem_all` (8 卦穷举) · `hexagram_mem_allHex` (64 卦穷举)。

---

## 一 · 原子层 `Yao` (爻)

| Lean | 字 | 符 | 道家义 |
|---|---|---|---|
| `Yao.yang` | 阳 | ⚊ | 刚 · 动 · 施 · 明 |
| `Yao.yin`  | 阴 | ⚋ | 柔 · 静 · 受 · 隐 |

唯一原子算子 `Yao.neg` —— 单爻取反 (「错」之原子)。
对合定理 `Yao.neg_neg : ∀ y, y.neg.neg = y`。

> 注 (Yi.lean §1)：阴 / 阳 不是布尔真假；二者皆「内含倾向其对偶」，故语言之原子本即过程性的。

---

## 二 · 两仪 / 太极

| Lean | 字 | 备 |
|---|---|---|
| `LiangYi := Yao` | 两仪 | 阴阳二态 |
| `TaiJi := Unit`  | 太极 | 唯一性定理 `sheng_zero_unique : ∀ s : Sheng 0, s = .tai` |

---

## 三 · 四象 `SiXiang` (T₂)

| Lean | 字 | 符 | ⟨y₁ y₂⟩ | 时序 | 五行 |
|---|---|---|---|---|---|
| `taiYang`  | **太阳** | ⚌ | ⟨阳, 阳⟩ | 夏 | 火 |
| `shaoYin`  | **少阴** | ⚍ | ⟨阳, 阴⟩ | 秋 | 金 |
| `shaoYang` | **少阳** | ⚎ | ⟨阴, 阳⟩ | 春 | 木 |
| `taiYin`   | **太阴** | ⚏ | ⟨阴, 阴⟩ | 冬 | 水 |

`SiXiang.all = [taiYang, shaoYin, shaoYang, taiYin]` · `all_length : 4`。

---

## 四 · 八卦 `Trigram` (T₃) 全表

### 4.1 八卦总册

| Lean | 卦 | 符 | ⟨y₁ y₂ y₃⟩ | 自然 | 家庭 | 性 | 后天方位 | 五行 | 自乾出发的 (Z/2)³ 组合 | 先天序 |
|---|---|---|---|---|---|---|---|---|---|---|
| `qian` | **乾** | ☰ | ⟨阳, 阳, 阳⟩ | 天 | 父 | 健 | 西北 | 金 | id | 1 |
| `dui`  | **兑** | ☱ | ⟨阳, 阳, 阴⟩ | 泽 | 少女 | 悦 | 西 | 金 | `bian` | 2 |
| `li`   | **离** | ☲ | ⟨阳, 阴, 阳⟩ | 火 | 中女 | 丽 | 南 | 火 | `hua` | 3 |
| `zhen` | **震** | ☳ | ⟨阳, 阴, 阴⟩ | 雷 | 长男 | 动 | 东 | 木 | `hua ∘ bian` | 4 |
| `xun`  | **巽** | ☴ | ⟨阴, 阳, 阳⟩ | 风 | 长女 | 入 | 东南 | 木 | `dong` | 5 |
| `kan`  | **坎** | ☵ | ⟨阴, 阳, 阴⟩ | 水 | 中男 | 陷 | 北 | 水 | `dong ∘ bian` | 6 |
| `gen`  | **艮** | ☶ | ⟨阴, 阴, 阳⟩ | 山 | 少男 | 止 | 东北 | 土 | `dong ∘ hua` | 7 |
| `kun`  | **坤** | ☷ | ⟨阴, 阴, 阴⟩ | 地 | 母 | 顺 | 西南 | 土 | `dong ∘ hua ∘ bian` (= 错) | 8 |

> **形式 / 传统分判**：Lean 列（卦名 / 符 / 爻 / 组合）严格机器验证；自然 / 家庭 / 方位 / 五行 / 先天序为传统映射，仅作语义注解。

> **家庭对应规则**：六子卦由「少数爻位置」标记 ——
> 男为「孤阳所在」（震 = y₁ 长 · 坎 = y₂ 中 · 艮 = y₃ 少），
> 女为「孤阴所在」（巽 = y₁ 长 · 离 = y₂ 中 · 兑 = y₃ 少）。

> **先天序**：邵雍 / 伏羲先天八卦次序（乾兑离震巽坎艮坤），恰为 `Trigram.all` 之枚举次序，等价于以 `y₃` 为最高位、阳=1 阴=0 的二进制递降。

`Trigram.all_length : 8` · `trigram_mem_all : ∀ t : Trigram, t ∈ Trigram.all`。

### 4.2 错 / 综 配对

| 卦 | 错 (三爻全反) | 综 (上下倒置) |
|---|---|---|
| 乾 ☰ | 坤 ☷ | **乾 ☰** (回文不动) |
| 兑 ☱ | 艮 ☶ | 巽 ☴ |
| 离 ☲ | 坎 ☵ | **离 ☲** (回文不动) |
| 震 ☳ | 巽 ☴ | 艮 ☶ |
| 巽 ☴ | 震 ☳ | 兑 ☱ |
| 坎 ☵ | 离 ☲ | **坎 ☵** (回文不动) |
| 艮 ☶ | 兑 ☱ | 震 ☳ |
| 坤 ☷ | 乾 ☰ | **坤 ☷** (回文不动) |

四「自反综卦」**乾 · 离 · 坎 · 坤** 即 T₃ 中位序回文者（$y_1 = y_3$），亦即四正卦。

> **错综分判**（重要）：
> - **错** $: \langle y_1, y_2, y_3 \rangle \mapsto \langle \neg y_1, \neg y_2, \neg y_3 \rangle$ —— 改值不改位，属 (Z/2)³
> - **综** $: \langle y_1, y_2, y_3 \rangle \mapsto \langle y_3, y_2, y_1 \rangle$ —— 改位不改值，**不**属 (Z/2)³
> - **错综** = cuo ∘ zong $: \langle y_1, y_2, y_3 \rangle \mapsto \langle \neg y_3, \neg y_2, \neg y_1 \rangle$ —— 既改值又反位，亦不属 (Z/2)³
> 
> 故 cuo ∘ zong 属于扩张群 $(\mathbb{Z}/2)^3 \rtimes \langle \text{综} \rangle$（阶 16），不可还原为 (Z/2)³ 之内的 flip 复合。
> 形式见证：[`zong_outside_flip_group`](../formal/SSBX/Foundation/BaguaAlgebra.lean) 之 5 条不等式。

---

## 五 · 横向算子 (Cayley action)

### 5.1 T₃ 三反爻 —— `(Z/2)³` 的生成元

| Lean | 字 | 翻位 | 道家义 |
|---|---|---|---|
| `dong` | **动** | y₁ (初/下) | 始动 · 萌生 |
| `hua`  | **化** | y₂ (中)   | 中变 · 转质 |
| `bian` | **变** | y₃ (上)   | 终成 · 显化 |

对合：`dong_dong / hua_hua / bian_bian`。
两两交换：`dong_hua_comm / hua_bian_comm / dong_bian_comm`（**阿贝尔**）。

### 5.2 (Z/2)³ 的 8 元 (`FlipCombo`)

| Lean | 组合 | 自乾→ |
|---|---|---|
| `id`  | e (恒) | 乾 ☰ |
| `d`   | dong | 巽 ☴ |
| `h`   | hua | 离 ☲ |
| `b`   | bian | 兑 ☱ |
| `dh`  | dong ∘ hua | 艮 ☶ |
| `hb`  | hua ∘ bian | 震 ☳ |
| `db`  | dong ∘ bian | 坎 ☵ |
| `dhb` | dong ∘ hua ∘ bian | 坤 ☷ |

定理：
- `cuo_eq_compose : 错 = dong ∘ hua ∘ bian` —— 「错」是 (Z/2)³ 的中心元
- `FlipCombo.apply_qian_inj` —— **simply transitive**：(Z/2)³ ↪ Trigram 在乾轨道为双射
- `bagua_intercommunication` —— 任两卦皆有变换互通
- `bagua_intercommunication_bounded` —— 互通距离 ≤ 3
- `pathFromTo_length_eq_hammingDist` —— 显式路径长度 = Hamming 距离 (**最短**)

### 5.3 T₆ 六反爻 —— `(Z/2)⁶ = (Z/2)³_内 × (Z/2)³_外`

| Lean | 字 | 翻位 |
|---|---|---|
| `dongInner` | 内·动 | y₁ |
| `huaInner`  | 内·化 | y₂ |
| `bianInner` | 内·变 | y₃ |
| `dongOuter` | 外·动 | y₄ |
| `huaOuter`  | 外·化 | y₅ |
| `bianOuter` | 外·变 | y₆ |

定理：
- 六对合 (`*_*` 各自)
- `hex_cuo_eq_compose : 错_hex = dongInner ∘ huaInner ∘ bianInner ∘ dongOuter ∘ huaOuter ∘ bianOuter`
- `*_via_chong` (六条) —— 每个翻分解为「`chong (内动) 外`」等结构
- `hex_intercommunication_bounded` —— 重卦互通 ≤ 6 步

> **「一在不同层面不同」**：T₃ 是 (Z/2)³，T₆ 是 (Z/2)⁶；原理同形，维度递升。

---

## 六 · 纵向算子

### 6.1 合 (he) —— 层降 / 投影

| Lean | 类型 | 字义 |
|---|---|---|
| `heShang` | T₃ → T₂ | 舍上爻 |
| `heZhong` | T₃ → T₂ | 舍中爻 |
| `heXia`   | T₃ → T₂ | 舍下爻 |
| `heToYi` | T₂ → T₁ | 四象 → 两仪 |
| `heToTaiji` | T₁ → T₀ | 两仪 → 太极 |
| `guiyi` | T₃ → T₀ | **归一** (三步合到底) |

`guiyi_universal : ∀ t, guiyi t = ()` —— 万物归一。

### 6.2 分 (fen) —— 层升 / 生发

| Lean | 类型 | 字义 |
|---|---|---|
| `fenToYi` | TaiJi → Yao → LiangYi | 太极 → 两仪 |
| `fenToSiXiang` | LiangYi → Yao → SiXiang | 两仪 → 四象 |
| `fenToTrigram` | SiXiang → Yao → Trigram | 四象 → 八卦 |

合分逆 (section / retract)：`heShang_fenToTrigram` · `heToYi_fenToSiXiang` · `heToTaiji_fenToYi`。

### 6.3 大循环 (grandCycle)

```
grandCycle y₁ y₂ y₃ : TaiJi
  := guiyi (fenToTrigram (fenToSiXiang (fenToYi () y₁) y₂) y₃)
```

`grandCycle_returns : ∀ y₁ y₂ y₃, grandCycle y₁ y₂ y₃ = ()` —— **太极 → 八卦 → 太极** 闭合。

---

## 七 · 重卦 `Hexagram` (T₆) 关键卦

`Hexagram = ⟨y₁..y₆⟩`：y₁..y₃ = 内卦 (下)，y₄..y₆ = 外卦 (上)。
**内卦** 承：本 · 源 · 自身 · 起；**外卦** 承：用 · 显 · 对境 · 应。

### 7.1 Lean 中显式定义之卦

| Lean | 卦 | 内 | 外 | 全爻 | 涵 |
|---|---|---|---|---|---|
| `Hexagram.qian` | **乾 ䷀** | 乾 ☰ | 乾 ☰ | ⟨阳⁶⟩ | 互不动点；纯阳 |
| `Hexagram.kun`  | **坤 ䷁** | 坤 ☷ | 坤 ☷ | ⟨阴⁶⟩ | 互不动点；纯阴 |
| `Hexagram.tai`  | **泰 ䷊** | 乾 ☰ | 坤 ☷ | ⟨阳³ 阴³⟩ | 地上天下，通泰 |
| `Hexagram.pi`   | **否 ䷋** | 坤 ☷ | 乾 ☰ | ⟨阴³ 阳³⟩ | 天上地下，闭塞 |

`pi_ne_tai` —— 内外不可交换之具体见证；`oplus_not_comm` —— 一般陈述。

### 7.2 重 (chong / oplus)

| Lean | 字 | 类型 | 义 |
|---|---|---|---|
| `Hexagram.oplus` | ⊕ | T₃ × T₃ → T₆ | 内 ⊕ 外 → 六爻卦 |
| `chong` | **重** | T₃ × T₃ → T₆ | `oplus` 别名 (BaguaAlgebra) |

`chong_inner_outer : chong h.innerTrigram h.outerTrigram = h` —— 重之逆构原。
`hex_cuo_via_inner_outer : Hexagram.cuo h = chong (cuo innerTrigram) (cuo outerTrigram)` —— 错算子内外因式分解。

---

## 八 · 对称算子 (V₄ 群与互卦)

T₆ 上的 **Klein 四元群 V₄**：

| Lean | 字 | 作用 | 在 (Z/2)⁶ 中？ |
|---|---|---|---|
| `id` | 恒 | h ↦ h | ✓ |
| `Hexagram.cuo` | **错** | ⟨a..f⟩ ↦ ⟨¬a..¬f⟩ | ✓（六单翻复合）|
| `Hexagram.zong` | **综** | ⟨y₁..y₆⟩ ↦ ⟨y₆..y₁⟩ | ✗ |
| `Hexagram.cuoZong` | **错综** | cuo ∘ zong | ✗ |
| `Hexagram.hu` | **互** | ⟨y₂, y₃, y₄, y₃, y₄, y₅⟩ | ✗ (维度降) |

定理：`cuo_cuo` · `zong_zong` · `cuoZong_cuoZong` · `cuo_zong_comm` · `v4_orders`。

### 8.1 互卦不动点定理

`hu_fixed_point : h.hu = h ↔ h = qian ∨ h = kun`

—— **「互卦不动点恰为乾、坤」**，证「乾坤为易之门」之代数形。

### 8.2 错综分离定理（`zong_outside_flip_group`）

T₃ 层 5 条小定理捆绑 ——「综」严格 **不属于 (Z/2)³**：

- `zong_ne_id` (兑 ↦ 巽 见证)
- `zong_ne_dong / hua / bian` (乾不动 见证)
- `zong_ne_cuo` (乾不动 vs 乾 ↦ 坤 见证)

> **哲学涵义**：**错** 是「相反」（阴阳互换），属 (Z/2)ⁿ 比特群；**综** 是「相对」（视角倒转），在群外。两者本质不同维度。

---

## 九 · 生生 (Sheng) 层级

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

> **生生 = 归纳类型 step 的迭代**；六步即重卦。

---

## 十 · 五最小算子完备性

```lean
structure MinimalOps where
  dong, hua, bian : Trigram → Trigram   -- 横向：(Z/2)³
  he              : Trigram → SiXiang   -- 纵向：归一
  sheng           : Nat → Type          -- 生生层级
```

`canonical_complete` —— 五算子联合实现：
1. **横向 simply transitive 互通**（八卦皆可达）；
2. **纵向归一**（万物归太极）。

---

## 十一 · 距离 / 路径

| Lean | 义 |
|---|---|
| `hammingDist : T₃ × T₃ → Nat` | 八卦间差爻数 (≤ 3) |
| `hexHammingDist : T₆ × T₆ → Nat` | 六十四卦间差爻数 (≤ 6) |
| `transform / hexTransform` | 直接连接变换 |
| `pathFromTo` | 显式 `[dong / hua / bian]` 路径 |
| `applyPath` | 顺序施用路径 |

定理：`hammingDist_eq_zero_iff` · `pathFromTo_length_eq_hammingDist` · 互通 ≤ 距离。

---

## 十二 · 位 (位次结构) — `Yi.lean`

| Lean | 字 | 义 |
|---|---|---|
| `atPos` | 位 | h 在第 i (Fin 6) 爻的取值 |
| `isYangPos` / `isYinPos` | 阳位 / 阴位 | i % 2 = 0 / 1 |
| `wellPos` | **当位** (得正) | 阳爻居阳位 ∨ 阴爻居阴位 |
| `isZhongPos` | **中** | i = 1 (二爻) 或 i = 4 (五爻) |
| `yingResponds` | **应** | 初/四、二/五、三/六 阴阳异 |
| `biAdj` | **比** | 相邻爻对 |

---

## 十三 · 占筮模态层 — `YaoStar / HexagramStar`

| Lean | 字 | 义 |
|---|---|---|
| `YaoStar.laoYang` ⚊⊙ | **老阳 9** | 阳之极，将变 |
| `YaoStar.shaoYang` ⚊ | 少阳 7 | 阳之常 |
| `YaoStar.shaoYin` ⚋ | 少阴 8 | 阴之常 |
| `YaoStar.laoYin` ⚋⊙ | **老阴 6** | 阴之极，将变 |
| `proj` | 投影 | YaoStar → Yao（取本相）|
| `delta` | 变 | YaoStar → Yao（老变少不变）|
| `isOld / isYoung` | 老 / 少 | 模态判定 |
| `HexagramStar` | 卦象 | 6 个 YaoStar 组 |
| `benGua` | **本卦** | proj 投影 → Hexagram |
| `bianGua` | **变卦** | delta 投影 → Hexagram |

定理：`old_or_young` · `not_both_old_young` · `delta_young_eq_proj` · `delta_old_eq_neg_proj` · `benGua_eq_bianGua_of_all_young` (无老即不变) · `allLaoYang_benGua = qian` ∧ `allLaoYang_bianGua = kun` (六老阳本乾变坤)。

---

## 十四 · 终极对应总图

```
                       ┌──────────────┐
                       │ 太极  TaiJi   │ 1   * = ()
                       └──────┬───────┘
                              │ fen ↓↑ he
                       ┌──────┴───────┐
                       │ 两仪 LiangYi │ 2   {阳, 阴}
                       └──────┬───────┘
                              │ fen ↓↑ he
                       ┌──────┴───────┐
                       │ 四象 SiXiang │ 4   太阳/少阴/少阳/太阴
                       └──────┬───────┘
                              │ fen ↓↑ he
                       ┌──────┴───────┐  动 (y₁)  ┐
                       │ 八卦 Trigram │ 8 ← 化 (y₂) ─→ (Z/2)³ simply transitive
                       │  T_3 = Σ³    │   变 (y₃)  ┘   错=动∘化∘变 ; 综 ∉ (Z/2)³
                       └──────┬───────┘
                              │ chong (内 ⊕ 外)，不可交换
                ┌─────────────┴─────────────┐  内·动/化/变 ┐
                │ 重卦 Hexagram               │ 64 ← 外·动/化/变 → (Z/2)⁶
                │  T_6 = Σ⁶ = 8 × 8           │           错_hex = 六单翻复合
                │                            │           V₄: id/错/综/错综
                │                            │           互(hu) 不动点 = {乾, 坤}
                └─────────────┬──────────────┘
                              │ 占筮：HexagramStar (老少模态)
                              │  proj → 本卦 ; delta → 变卦
                              ▼
                          ⟨彖 / 象 / 爻辞⟩
```

---

## 十五 · 全集单字算子合表

合并 G（横纵群代数 11 字）+ 数与算术（12 字）+ 形式逻辑（25 字）+ 统计（27 字）= **总 75 个声明，去重后约 60 单字算子**。

### 15.1 按文件分类

| 文件 | 数 | 单字 |
|---|---:|---|
| **G** | 11 | 变 / 化 / 动 / 错 / 综 / 合 / 分 / 重 / 生生 / 不(静) / 一(抱) |
| **数与算术** | 12 | 生 / 合 / 损 / 重 / 除 / 空 / 一 / 反(负) / 份 / 趋 / 极 / 完 |
| **形式逻辑** | 25 | 是 / 非 / 疑 / 不 / 並 / 或 / 若(则) / 即 / 凡 / 有 / 莫(无) / 必 / 可 / 故 / 致 / 必(小故) / 者 / 也 / 所 / 于 / 同四 / 异四 / 式 / 法 / 证 / 保 / 洽 |
| **统计** | 27 | 域 / 事 / 度 / 率 / 一(归一) / 因 / 占 / 观 / 演 / 兆 / 期 / 离 / 正 / 玄(熵) / 信 / 似 / 先 / 后 / 极(似然) / 验 / 拒 / 悬(待) / 归 / 链 / 平 |

### 15.2 跨文件去重表

| 单字 | 出现位 | 是否同义 |
|---|---|---|
| **合** | G（合分对）/ 数（加）/ 测（additivity）| 同根（"合一"）|
| **一** | G（归一）/ 数（壹）/ 测（归一概率）| 同根 |
| **分** | G（split）/ 测（σ-代数构造）| 同根 |
| **重** | G（八卦相重）/ 数（乘法）| 同根（"叠加复合"）|
| **不** | G（静 / id）/ 推（否定）| 异义（保留两字）|
| **极** | 数（sup）/ 测（argmax）| 同根（"取顶"）|
| **归** | G（归一）/ 测（LLN 收敛）| 同根（"还原至本"）|
| **反** | G（错爻）/ 数（负）| 异义（前者 (Z/2) flip，后者 ℤ neg）|
| **生** | G（分之单字）/ 数（succ）| 异义（前者升维，后者 +1）|
| **疑** | 推（U 三值）/ 测（悬 待） | 同根（"未决"）|

去重后**约 60 单字算子**完整覆盖集合所需。

### 15.3 按层级与作用域归类

| 算子族 | 单字（去重） | 作用层 |
|---|---|---|
| **群作用（横向）** | 变 / 化 / 动 / 错 / 综 | T₃ 之 (Z/2)³ |
| **纵向（升降）** | 合 / 分 / 重 / 一 / 归 | T₀–T₆ 链 |
| **太极（不动点）** | 生生 / 一(抱) | 元层 / Y comb |
| **算术** | 生 / 损 / 除 / 空 / 反(负) / 份 / 趋 / 极 / 完 | ℕ → ℤ → ℚ → ℝ |
| **真值** | 是 / 非 / 疑 | Bool / U |
| **联结词** | 不 / 並 / 或 / 若 / 即 | Prop² → Prop |
| **量词** | 凡 / 有 / 莫 | (A → Prop) → Prop |
| **模态** | 必 / 可 | Prop → Prop |
| **推理** | 故 / 致 / 必(小故) | ⊢ |
| **元逻辑** | 式 / 法 / 证 / 保 / 洽 | meta |
| **句法承字** | 者 / 也 / 所 / 于 | term/prop binders |
| **墨经四** | 同四（重/体/合/类）/ 异四（二/不体/不合/不类）| equivalence |
| **测度** | 域 / 事 / 度 / 率 | (Ω, Σ, μ) |
| **事件之关** | 因 | conditional |
| **观验** | 占 / 观 / 演 | system → info |
| **统计量** | 兆 / 期 / 离 / 正 / 信 | random vars |
| **熵** | 玄 | $-\sum p \log p$ |
| **推断** | 似 / 先 / 后 / 验 / 拒 / 悬(待) | inference |
| **过程** | 链 / 平 | Markov |

---

## 十六 · 道-理二分与 192 之关系

> 此 I 文件之全部内容皆属**理层**（八卦 / 64 卦 / 192 之 r.e. 形式系统）；
> 但**生生 (Sheng)** 算子与 **完备性陈述** 属**道层**（元理论 / Lean kernel 之 ω-tower）。

详见 [`J_理之不完备_哥德尔在192.md`](J_理之不完备_哥德尔在192.md) §一。

| 本文之 | 属 | 例 |
|---|---|---|
| `Trigram` 类型与全部具名卦 | 理 | `qian, dui, li, ...` |
| `dong / hua / bian` 算子及其 75 定理 | 理 | `dong_dong : dong ∘ dong = id` |
| `Sheng : ℕ → Type` 归纳族 | 道 | 类型族层 (kind level) |
| `bagua_algebra_complete` 主定理 | 道 | 关于理之元命题 |
| 此 I 文件作为文档 | 同时属 | 理（作为字符串存在）∧ 道（关于全集之陈述）|

**故 I 既是理之总册（八卦字符整全枚举），亦是道之文（关于此整全之陈述）**——属于"道理二分"在文档层之自指（参 [`K_完备性审计.md`](K_完备性审计.md) §六之结尾）。

---

## 闭合状态

- 文件：`formal/SSBX/Foundation/{Yi,BaguaAlgebra}.lean` （共 2709 行）
- **75 条定理 · 0 sorry · 0 axiom · 0 warning · `lake build` 通过**
- 五重完备：横向 (Z/2)ⁿ simply transitive · 纵向合分归一 · 错综分离 · Sheng 同构 · 枚举完全
- 单字算子约 **60 字** 完整承担数 / 推 / 测三衍 + 群代数（详 §十五）
- 道理二分：本文档既属理（具体形式系统）亦属道（元陈述）——参 §十六 + J + K
