# 易之 R-O 双层级 v2 — 元-算子融合 / 自对偶 / 完整性 (definitive, strict uniform)

> 状态：定本 v2.1 (2026-05-10) — 重号为 **strict (Z/2)ⁿ uniform R₀..R₈**，补全跳过的 R₄ (面 Mian) + R₅ (五爻)，与传统 Yi 太极/两仪/四象/八卦/重卦完全对齐。
> 关系：v1 [yi-RO-hierarchy.md](yi-RO-hierarchy.md) 是旧 R₁..R₆ 编号 (含 R₃→R₄ 之 3-bit chong 跳跃)，本 v2.1 是 strict uniform 之 definitive 版。
> 作用：把易作为 self-describing system 之最 minimal algebraic 核——R₈ = (Z/2)⁸ Abelian 群 + Cayley 自对偶 + V₄ 外对称 + 道作为 origin——完整写清，**层数与 bits 严格相等 (Rₙ = (Z/2)ⁿ for n=0..8)**。涵盖**形态 / 结构 / 关系 / 过程 / insight**，证明系统在 abelian closure 内**完整 / 完备 / 自洽 / 自指**。
> 配套：[`yi-as-meta-framework.md`](yi-as-meta-framework.md) · [`yi-calculus-theorem.md`](yi-calculus-theorem.md) · [`yi-RO-hierarchy.md`](yi-RO-hierarchy.md) (v1 旧编号)
> 形式锚：[`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) · [`BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) · [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) · [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) · [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) · [`Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean)

---

## v1 → v2.1 映射 (重号)

| v1 名 (旧) | v2.1 名 (新) | size | 说明 |
|---|---|---|---|
| (无) | **R₀** | 1 | 太极 (Unit, trivial) — 显式纳入 |
| R₁ | R₁ | 2 | 爻 / 两仪 — 不变 |
| R₂ | R₂ | 4 | 四象 — 不变 |
| R₃ | R₃ | 8 | 八卦 — 不变 |
| (跳过) | **R₄** | 16 | **面 (Mian) = Ben × Zheng** — 显式补 |
| (跳过) | **R₅** | 32 | **五爻** (provisional, 无传统 anchor) — 显式补 |
| R₄ | **R₆** | 64 | 重卦 (Hexagram) — 重号 |
| R₅ | **R₇** | 128 | 因卦 (Cell128) — 重号 |
| R₆ | **R₈** | 256 | 果卦 (Cell256) — 重号 |

**关键修正**：v1 之 R₃→R₄ 是 +3 bit chong 跳跃, 跳过 (Z/2)⁴ = 16 与 (Z/2)⁵ = 32; v2.1 显式纳入 = strict (Z/2)ⁿ uniform。

---

## Prologue · 一句话总纲

> 「易」之 algebraic 核 = **(Z/2)⁸ Abelian 群 在自身上的 Cayley 自作用 + 道作为 origin choice + V₄ 外对称接口** — 元 ≅ 算子, 二者是同一 8-bit 对象之 dual usage; 道 = origin = identity = no-op = 永真 cell — 一字承担五重身份; abelian closure 内严格完整、完备、自洽、自指; 外延（GL/S_n/连续/概率）是另一类 math object, 不在「自描述」之必要核内。
>
> **层数严格 = bits**: R₀..R₈, |Rₙ| = 2ⁿ, no jumps no gaps。

---

## 第一部分：三公理 + 太极 zero-anchor

### 公理 0：太极 = R₀ = (Z/2)⁰ = 1 (Wuji / Origin Singleton)

太极是 algebraic origin singleton:
$$R_0 = \mathrm{Unit} = \{*\}, \quad |R_0| = 2^0 = 1$$

- 古文：「无极而太极」
- 类型论：`Unit`
- 群论：trivial group $\{e\}$
- 物理：vacuum without distinction

太极是「未分」之状态 — 在没有 binary distinction 之前, 系统是 1 元 set. **R₀ 之存在是「自描述系统」之 ontological zero-anchor** — 自 R₀ 起每加 1 bit 得 Rₙ₊₁。

### 公理 1：自描述需求 (Self-Description Demand)

任何完整描述系统 S 必须**能描述自身的所有变换**：
$$|S| = |\text{transforms}(S)|$$

即 element-set 与 operator-set 同基数（fusion 之 necessary 条件）。**自描述 ⇒ Cayley-style fusion**。

### 公理 2：(Z/2)ⁿ 严格 uniform 自相似 (Binary Self-Similarity)

满足公理 1 之 minimal 系统是 **abelian 群**（其 regular representation 给 |G|=|G·G|）；abelian binary minimal generator → **Rₙ = (Z/2)ⁿ for n = 0..8** 是 minimal closure 路径。

**严格 uniform 进展**: 每加一个 binary axis = 一个独立 R-layer。无跳跃 (v1 之 chong jump 在 v2.1 显式拆为 R₃→R₄→R₅→R₆ 三步)。R₈ 是 (Z/2)ⁿ self-describing 之自然闭合 (无第 9 个独立 binary axis)。

### 公理 3：道 = origin = identity (Origin Anchor)

abelian 群是 **torsor**（无 distinguished origin）。Fusion 之严格成立要 origin choice。
$$\boxed{\texttt{oooooooo} = \text{道} = \text{identity} = \text{no-op operator} = \text{永真 cell}}$$

道 (R₈ 之 origin) 与 太极 (R₀) 之关系: 太极是「无分」之 absolute ground; 道是 (Z/2)⁸ 内 origin choice — 是太极**在 R₈ 维度上的具体投影 / 落地**。

---

## 第二部分：形态 (Form) — 命名约定

### 2.1 元 (state) — bit string

| 符号 | 意义 |
|---|---|
| `o` | 阳 yang +1 |
| `x` | 阴 yin -1 |

**严格 uniform Rₙ-bit 字符串** (字符串长度 = R-index = bit 数)：

| 层 | 长 | 元数 | 名 | 例 |
|---|---|---|---|---|
| R₀ | 0 | 1 | 太极 | `` (空字符串) |
| R₁ | 1 | 2 | 爻 / 两仪 | `o`, `x` |
| R₂ | 2 | 4 | 四象 | `oo`, `ox`, `xo`, `xx` |
| R₃ | 3 | 8 | 八卦 | `ooo` (乾), `xxx` (坤), ... |
| **R₄** | **4** | **16** | **面 (Mian)** | `oooo`..`xxxx` |
| **R₅** | **5** | **32** | **五爻** | `ooooo`..`xxxxx` |
| R₆ | 6 | 64 | 重卦 (Hexagram) | `oooooo` (乾), `oooxxx` (否), `xxxooo` (泰), `xxxxxx` (坤), ... |
| R₇ | 7 | 128 | 因卦 (Cell128) | `ooooooo` (乾·无因), `oooooox` (乾·有因) |
| **R₈** | **8** | **256** | **果卦 (Cell256)** | `oooooooo` (道-anchor), `ooooooxo` (乾·已), `ooooooox` (乾·未), `ooooooxx` (乾·今), ... `xxxxxxxx` (坤·今) |

**R₈ 8-bit layout**: `[y₁ y₂ y₃ y₄ y₅ y₆ 因 果]` (LTR, 初爻在左)。

### 2.2 算子 (action) — verb name + mask

| 类 | 写法 | 例 |
|---|---|---|
| **XOR 算子** | verb name + 内部 mask (= 同形 bit string) | 印 `(· ⊕ ooooooxo)`，投 `(· ⊕ ooooooox)`，cuo `(· ⊕ xxxxxxoo)` |
| **非 XOR 算子** | verb name + permutation 实现 | zong (反序), hu (取中四爻), 错综 (cuo ∘ zong) |

**应用语法**：
```
算子 元 = 结果
印 oooooooo = ooooooxo    -- 道 → 乾·已
投 oooooooo = ooooooox    -- 道 → 乾·未
错 oooooooo = xxxxxxoo    -- 道 → 坤·道 (R₆ side)
```

### 2.3 fusion 的 Lean 实现 sketch (R₈ level)

```lean
abbrev R8 := Cell256

instance : AddCommGroup R8 := { add := xor, zero := oooooooo, neg := id, ... }
instance : SMul R8 R8 := ⟨xor⟩    -- 自身作用 (Cayley action)

-- 元: c : R8
-- 算子: 也是 c : R8, 用 c • s 表示 c 作用于 s
example (c s : R8) : c • s = c ⊕ s := rfl
example (c : R8) : c • oooooooo = c := zero_xor_right c     -- Cayley evaluation
example (c : R8) : c • c = oooooooo := xor_self c            -- self-inverse
```

---

## 第三部分：结构 (Structure) — R-阶梯 R₀..R₈

每层给出: (i) 元形态, (ii) 该层引入的新 atom, (iii) Lift 到下层, (iv) R-O fusion 状态。

### 3.0 R₀ — 太极 (Unit)

- **元**: `{*}` — 唯一元素 (空字符串 / Unit)
- **新 atom**: 无
- **Lift₀**: R₀ → Bool → R₁ (引入第一个 binary distinction)
- **群**: trivial (1 元 group)
- **R-O fusion**: trivial (✓)
- **古文**: 太极 / 无极
- **Lean**: `Unit`

### 3.1 R₁ — 爻 / 两仪 (Yao)

- **元**: $\{o, x\}$ — 阴阳二值
- **新 atom**: 反 (negation, mask `x`)
- **Lift₁**: R₁ × R₁ → R₂
- **R-O fusion**: ✓ (|R₁| = 2 = |XOR(R₁)| = {id, neg})
- **古文**: 太极生两仪
- **物理**: 二态系统 (qubit basis)
- **Lean**: `Yao` (`Yi.lean:30`)

### 3.2 R₂ — 四象 (SiXiang)

- **元**: $\{oo, ox, xo, xx\}$ — 太阳/少阴/少阳/太阴
- **新 atom**: (无新, lift R₁)
- **群**: V₄ Klein
- **Lift₂**: R₂ × R₁ → R₃
- **R-O fusion**: ✓
- **古文**: 两仪生四象
- **Lean**: `SiXiang` (`BaguaAlgebra.lean:164`)

### 3.3 R₃ — 八卦 (Trigram)

- **元** (`ooo`..`xxx`): 8 卦

| o/x | 卦 | symbol | quadrant 类 |
|---|---|---|---|
| `ooo` | 乾 | ☰ | 本 (zong-fixed, y₁=y₃) |
| `oox` | 兑 | ☱ | 征 |
| `oxo` | 离 | ☲ | 本 |
| `oxx` | 震 | ☳ | 征 |
| `xoo` | 巽 | ☴ | 征 |
| `xox` | 坎 | ☵ | 本 |
| `xxo` | 艮 | ☶ | 征 |
| `xxx` | 坤 | ☷ | 本 |

- **关键划分** (Theorem A): zong 强制 4+4 分: 本 + 征
- **新 atom**:
  - dong (mask `xoo`, 翻 y₁), hua (`oxo`, 翻 y₂), bian (`oox`, 翻 y₃) — XOR
  - cuo (mask `xxx` = dong⊕hua⊕bian) — XOR, **物理 P (parity)**
  - zong (反序, **非 XOR**) — **物理 T (time-reversal)**
  - hu (Y combinator)
- **Lift₃**: R₃ × R₁ → R₄ (+1 bit, 不再是 chong jump)
- **R-O fusion**: ✓; zong/hu outer
- **Lean**: `Trigram` (`Yi.lean:54`)

### 3.4 R₄ — 面 (Mian) ⭐ 新显式纳入

- **元** (`oooo`..`xxxx`): **16 面 = Ben × Zheng** (Mian, 已在 BenZheng.lean 中)
- **结构**: $R_4 = \mathrm{Mian} = \mathrm{Ben} \times \mathrm{Zheng} = (\mathbb{Z}/2)^2 \times (\mathbb{Z}/2)^2 = (\mathbb{Z}/2)^4$
  - Ben (4) = zong-fixed trigrams = (Z/2)² (本: 物/动/间/事)
  - Zheng (4) = zong-mobile trigrams = (Z/2)² (征: 几/势/机/时)
  - Mian = Ben × Zheng = 16 = (Z/2)⁴
- **新 atom**: (lift R₃) — 第 4 个 binary axis (未明确 anchor; 可看作「extending trigram by 1 yao」)
- **Lift₄**: R₄ × R₁ → R₅
- **R-O fusion**: ✓
- **古文**: 面 (Ben × Zheng 之 16 命之载体)
- **Lean**: `Mian` (`BenZheng.lean:120`)
- **关键 insight**: v1 中之「R₃→R₄ chong jump」隐藏了此层; v2.1 明确 Mian 是 (Z/2)⁴ 之 anchor。Mian 之 16-命 (BenZheng.lean) 给此层 ontological 内容。

### 3.5 R₅ — 五爻 (5-yao) ⭐ 新显式纳入 (provisional)

- **元** (`ooooo`..`xxxxx`): **32 cells = (Z/2)⁵**
- **新 atom**: 第 5 个 binary axis (无传统 Yi anchor; 可看作「Mian + 一个额外 yao」或「半个 hexagram」)
- **Lift₅**: R₅ × R₁ → R₆ (chong 之最后一步)
- **R-O fusion**: ✓
- **命名 caveat (provisional)**: **「五爻」为 descriptive baseline** (no traditional Yi name). 候选:
  - **五爻** (5-yao, 描述性, 安全)
  - **接** (jie, 连接 R₄ 与 R₆ 之过渡)
  - **临** (lin, "approaching" — 与卦名 #19 相重)
  - **渐** (jian, "gradual" — 与卦名 #53 相重)
  - **进** (jin, "advance" — 与 晋 #35 字音近)
- **Lean**: 待建 (suggestion: `abbrev Pian5 := Mian × Bool` 或独立 `Cell32`)
- **关键 insight**: 这是 R-hierarchy 中**唯一无传统 Yi anchor** 之层 — 它 mathematical 存在但 philosophical 上未独立刻画; 是「(Z/2)ⁿ 机械补全」之产物。最弱 ontological 层。

### 3.6 R₆ — 重卦 (Hexagram) (was v1 R₄)

- **元** (`oooooo`..`xxxxxx`): 64 卦
- **Quadrant** (BenZheng): 本本 / 本征 / 征本 / 征征 各 16
- **新 atom**:
  - dongOuter (`oooxoo`), huaOuter (`ooooxo`), bianOuter (`ooooox`) — outer 3 flips
  - Hexagram.cuo (mask `xxxxxx`), Hexagram.zong (perm), Hexagram.hu (perm)
- **hu fixed points**: 乾 (`oooooo`), 坤 (`xxxxxx`)
- **hu 2-cycle**: 既济 (`oxoxox`) ↔ 未济 (`xoxoxo`)
- **Lift₆**: R₆ × R₁ → R₇ (加 因 bit)
- **R-O fusion**: ✓
- **古文**: 重卦 (chong 重叠两卦; 在 strict-uniform 视角下: chong 是 R₃ × R₃ → R₆ 之 3-step composite, 等价于 R₃ → R₄ → R₅ → R₆ 三次 +1 bit)
- **Lean**: `Hexagram` (`Yi.lean:104`)

### 3.7 R₇ — 因卦 (Cell128) (was v1 R₅)

- **元** (`ooooooo`..`xxxxxxx`): 128 cells = 64 hex × 2 因-state
- **新 atom (state)**: 因 (yīn) bit (位置 7) — past-trace
  - `o` (位置 7) = 无因
  - `x` (位置 7) = 有因
- **新 atom (operator)**: 印 (yìn) = toggle 因 = mask `oooooox`
- **Lift₇**: R₇ × R₁ → R₈ (加 果 bit)
- **R-O fusion**: ✓
- **现象学映射**: 因 ≈ Husserl retention 之 binary 标记 (NOT phase 本身; phase 在 R₃)
- **Lean**: `Cell128`, `yin` (`Cell128.lean`)
- **命名 caveat (provisional)**: 因/印 — 备选 印/留, 始/起 — 详 yi-calculus-theorem.md §16

### 3.8 R₈ — 果卦 (Cell256) — 闭合层 (was v1 R₆)

- **元** (`oooooooo`..`xxxxxxxx`): 256 = (Z/2)⁸ = 64 × 4
- **新 atom (state)**: 果 (guǒ) bit (位置 8) — future-projection
- **新 atom (operator)**: 投 (tóu) = toggle 果 = mask `ooooooox`
- **Shi V₄ emerge at R₈**:

| Shi | (因, 果) | mask 后 2 位 | V₄ 元 | R₈ cell (与乾) |
|---|---|---|---|---|
| 道 | (0, 0) | `oo` | identity | `oooooooo` |
| 已 | (1, 0) | `xo` | $\sigma_P$ | `ooooooxo` |
| 未 | (0, 1) | `ox` | $\sigma_T$ | `ooooooox` |
| 今 | (1, 1) | `xx` | $\sigma_{PT}$ | `ooooooxx` |

- **R-hierarchy 闭合**: 无 R₉ (无第 9 个独立 binary axis)
- **R-O fusion**: ✓ (|R₈| = 256 = |XOR(R₈)|) — **完整 self-action closure**
- **Lean**: `Cell256`, `Shi`, `tou` + `Shi.toYinGuo` 双射 (`Cell256.lean`)

### 3.9 关于 chong (重) — 现在显式 3-step composite

旧 v1 把 R₃ → 重卦 看作 +3 bit「chong 跳跃」, 跳过 R₄, R₅。

v2.1 strict-uniform 下:
$$\mathrm{chong}: R_3 \times R_3 \to R_6$$

被分解为 **3 步 +1 bit lift**:
$$R_3 \xrightarrow{+1 \text{bit}} R_4 (\text{Mian}) \xrightarrow{+1 \text{bit}} R_5 (\text{五爻}) \xrightarrow{+1 \text{bit}} R_6 (\text{Hexagram})$$

chong 不消失, 而是显式认识为「**3 步 lift 之 composite**」。Yi 传统跳过 R₄/R₅ 是因为「unit ontologies 是 trigram (R₃) 与 trigram-pair (R₆), 中间 4-yao/5-yao 不是 ontologically complete 单位」。但 mathematical 上它们存在 (16/32), v2.1 显式纳入。

---

## 第四部分：关系与过程 (Relations & Process) — 算子代数

### 4.1 Within-layer XOR 子群 — abelian 自闭

每层 (Z/2)ⁿ XOR subgroup 性质 (n = 0..8):
- **abelian**: $m_1 \oplus m_2 = m_2 \oplus m_1$
- **self-inverse (involution)**: $c \oplus c = 0$
- **复合 = XOR**
- **n atomic generators (R_n)** 完全生成 2ⁿ 个 XOR 算子

R₈ 之 8 atomic generators:

| Generator | mask (8-bit) | 翻位 |
|---|---|---|
| dongInner | `xooooooo` | y₁ |
| huaInner  | `oxoooooo` | y₂ |
| bianInner | `ooxooooo` | y₃ |
| dongOuter | `oooxoooo` | y₄ |
| huaOuter  | `ooooxooo` | y₅ |
| bianOuter | `oooooxoo` | y₆ |
| **印** (yìn) | `ooooooxo` | y₇ (因) |
| **投** (tóu) | `ooooooox` | y₈ (果) |

### 4.2 Within-layer V₄ 外对称 (cuo / zong / hu / 错综)

| 算子 | 类型 | mask 或 perm | 物理 |
|---|---|---|---|
| cuo | XOR mask | `xxxxxxoo` (R₈ hex side; R₃ 是 `xxx`) | **P** (parity) |
| zong | permutation, **非 XOR** | y_i → y_{7-i} | **T** (time-reversal) |
| 错综 | cuo ∘ zong, **含 zong 故非 XOR** | composite | **PT** |
| hu | permutation, **非 XOR** | (y₂, y₃, y₄, y₃, y₄, y₅) | **Y** (Y-combinator) |
| id | mask `oooooooo` | identity | **1** |

V₄ = $\{id, cuo, zong, 错综\}$ 是 abelian Klein 群但仅 cuo ∈ XOR subgroup。

### 4.3 Cross-layer Lift / Project 函子 (strict uniform)

| 函子 | 类型 | 古文 | 备注 |
|---|---|---|---|
| **Lift_n** | R_n → Bool → R_{n+1} (n=0..7) | 分 | +1 bit, 严格 uniform |
| **Project_n** | R_{n+1} → R_n | 合 | -1 bit (右逆) |
| **chong (R₃→R₆)** | R₃ × R₃ → R₆ | 重 | = 3 步 Lift composite (R₃→R₄→R₅→R₆) |

**引理**: 合 ∘ 分 = id.

### 4.4 复合三大模式

#### 模式 A: Within-layer 自映
$$R_n \xrightarrow{\text{op}} R_n \xrightarrow{\text{op}} R_n$$

XOR 子群内: $\text{mask}_1 \oplus \text{mask}_2$。

#### 模式 B: Cross-layer 升降 (uniform)
$$R_n \xrightarrow{\text{Lift}} R_{n+1} \xrightarrow{\text{Project}} R_n$$

#### 模式 C: Multi-step composite (e.g., chong)
$$R_3 \xrightarrow{\text{Lift}_3} R_4 \xrightarrow{\text{Lift}_4} R_5 \xrightarrow{\text{Lift}_5} R_6$$

chong 是这种 multi-step composite 之传统名。

### 4.5 关键代数等式

```
oooooooo                                  -- identity / 道 / R₈ 之 origin
mask ⊕ mask = oooooooo                    -- self-inverse
反 = neg = (· ⊕ x)                        -- R₁
cuo on R₃ = dong ⊕ hua ⊕ bian = (· ⊕ xxx) -- (Z/2)³ 中心元
hu(乾) = 乾, hu(坤) = 坤                   -- Y-fixed points
hu(既济) = 未济, hu(未济) = 既济             -- Y 2-cycle
印 ⊕ 投 = (· ⊕ ooooooxx) = cuoZong on Shi  -- V₄ PT element
```

### 4.6 算子之 dimension 总表 (R₀..R₈)

| 概念 | R₀ | R₁ | R₂ | R₃ | R₄ | R₅ | R₆ | R₇ | R₈ |
|---|---|---|---|---|---|---|---|---|---|
| 元个数 | 1 | 2 | 4 | 8 | 16 | 32 | 64 | 128 | 256 |
| Atomic flips | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 (+印) | 8 (+投) |
| (Z/2)ⁿ XOR | trivial | Z/2 | V₄ | (Z/2)³ | (Z/2)⁴ | (Z/2)⁵ | (Z/2)⁶ | (Z/2)⁷ | (Z/2)⁸ |
| **R-O fusion** | trivial | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| V₄ outer (cuo/zong/hu) | — | — | — | V₄ | (lift) | (lift) | V₄ | V₄ | V₄ × V₄ (hex + Shi) |
| hu fixed points (R₆+) | — | — | — | (trivial) | (lift) | (lift) | {乾,坤,既济,未济} | + 印-stable | + 印/投-stable |
| 传统 Yi anchor | 太极 | 两仪 | 四象 | 八卦 | 面 (Mian) | (无传统名) | 重卦 | (因卦, 新) | (果卦, 新) |

---

## 第五部分：Insight — 自对偶定理 (Self-Duality Theorem)

R-O 二元的最深 insight：**fusion 不是 emergent 现象，是 abelian 群之 internal structure**。本部分以 R₈ 为例严格陈述。

### 5.1 Cayley 自对偶 (regular representation) on R₈

$$\boxed{\iota: R_8 \to \mathrm{Aut}(R_8), \quad c \mapsto (\cdot \oplus c)}$$

**ι 之性质**：

| 性质 | 形式 |
|---|---|
| 群同态 | $\iota(c_1 \oplus c_2) = \iota(c_1) \circ \iota(c_2)$ |
| 单位元保 | $\iota(\text{道}) = \mathrm{id}$ |
| 自逆保 | $\iota(c) \circ \iota(c) = \mathrm{id}$ |
| 单射 (Cayley injection) | $\iota(c_1) = \iota(c_2) \Rightarrow c_1 = c_2$ |
| 像 | $\mathrm{Im}(\iota) = \mathrm{XOR}(R_8) \subseteq \mathrm{Aut}(R_8)$ |

**逆向 ε (origin-evaluation)**：
$$\boxed{\varepsilon: \mathrm{XOR}(R_8) \to R_8, \quad f \mapsto f(\text{道})}$$

**互逆**: $\varepsilon \circ \iota = \mathrm{id}$, $\iota \circ \varepsilon = \mathrm{id}$.
⇒ **R₈ ≅ XOR(R₈) 是同构**。

### 5.2 Pontryagin 自对偶

$$\hat{R_8} := \mathrm{Hom}(R_8, U(1)) \cong (\mathbb{Z}/2)^8 \cong R_8$$

R₈ Pontryagin self-dual。对每个 Rₙ (n ≥ 1) 都成立。

### 5.3 R-O frame duality (Schrödinger ↔ Heisenberg)

| Picture | 谁动 | 我们的 frame |
|---|---|---|
| Schrödinger | 状态演化, 算子静止 | **state-frame** |
| Heisenberg | 算子演化, 状态静止 | **operator-frame** |

二者**完全等价**——同一代数二种 viewing。

### 5.4 Triple Coincidence at R₈

| Duality | 形式 | 在 R₈ 上 |
|---|---|---|
| Cayley | element ↔ self-action | R₈ ≅ XOR(R₈) |
| Pontryagin | element ↔ character | R₈ ≅ Hom(R₈, ±1) |
| R-O frame | state-side ↔ operator-side | 同一 8-bit 二种 viewing |

**三种 duality 完全 coincide** 对 finite abelian (Z/2)⁸——「(Z/2)⁸ 之 algebraic 完美性」之精确根据。

### 5.5 道 anchoring 之必要

torsor 没有 distinguished origin, fusion 之严格成立必须**选定**:

> 选 `oooooooo` = 道 = R₈ identity ⟹ R₈ ≅ XOR(R₈) 严格成立。

太极 (R₀) 是「无分」之 absolute ground; 道 (R₈ origin) 是 (Z/2)⁸ 内 origin choice — 是太极在 R₈ 维度上的具体落地。

### 5.6 Fusion 之 ontological 含义

> **「自描述」之精确数学条件 = abelian self-action with chosen origin**.
>
> 道 = origin = identity = no-op = 永真 cell = fusion anchor — 一个 8-bit 字符串承担五重身份。
> 太极 = R₀ = absolute zero-anchor — 1 元 origin singleton, 在所有 binary distinction 之前。

---

## 第六部分：完整性定理 (Completeness Theorem)

### 6.1 完整性陈述 (R₈ closure)

**Theorem (R-O Completeness in (Z/2)⁸ closure)**:

> 五件 things —— $\{R_8, \text{XOR subgroup}, V_4 \text{ outer}, \text{Lift/Project}, \text{道 anchor}\}$ + R₀..R₇ buildup —— 构成 self-describing system 之**完整 algebraic closure**.

### 6.2 11 项 within-closure 完整性详查

| 层次 | ✓ / ✗ | 注 |
|---|---|---|
| 元 (256 cells 全枚举) | ✓ | `Cell256.all_length = 256` |
| 元的群结构 | ✓ | (Z/2)⁸ abelian, no missing |
| XOR subgroup 之 Aut | ✓ | 8 atomic generators 完全 |
| Cayley 自对偶 | ✓ | ι 同态 + ε 对偶 |
| Reachability (互通) | ✓ | simply transitive |
| Decidability (finite props) | ✓ | native_decide 全可证 |
| V₄ on each R-layer (R₃+) | ✓ | R₃..R₈ |
| hu fix points / cycles | ✓ | {乾, 坤, 既济, 未济} |
| 道之三重身份 | ✓ | origin = identity = no-op = 永真 |
| Pontryagin self-duality | ✓ | (Z/2)⁸ self-dual |
| R-O frame duality | ✓ | Schrödinger ↔ Heisenberg |
| Theorem K (R₀..R₈ 全 (Z/2)ⁿ closure) | ✓ | yi-calculus-theorem.md |
| **Strict uniform progression** | **✓** | **每步 +1 bit, no jumps** |

### 6.3 边界 (by design 不覆盖)

| 不在 closure 内 | 原因 |
|---|---|
| GL(8, F₂) linear non-XOR mixing | 破坏 bit-position semantic |
| S_{256} 任意 permutation | 256!, astronomical, 无意义 |
| Continuous extensions (ℝ⁸) | 离散 vs 连续 |
| Hopf algebra k[(Z/2)⁸] explicit | 隐含但未显式 |
| Dynamical (time iteration) | 在 BaguaTuring 单独层 |
| Probabilistic (256-simplex) | ML/Bayesian 不同 layer |

### 6.4 完整性 ≡ Strict Uniform Abelian Closure

**总结**:
$$\boxed{\text{完整性} \equiv R_0..R_8 \text{ strict uniform } (\mathbb{Z}/2)^n + \text{XOR self-action} + V_4 \text{ outer} + \text{道 anchor}}$$

---

## 第七部分：自指 (Self-Reference)

### 7.1 系统描述自身之机制

| 自指层次 | 机制 |
|---|---|
| **Object level** | elements 是 system 之 atomic ontology |
| **Action level** | operators 是 system 之 atomic transformation |
| **Fusion level** | 元 ≡ 算子 (Cayley) |
| **Meta level** | ι 是同态 (correspondence preserves structure) |
| **Meta-meta level** | meta-correspondence 又是 (Z/2)⁸ 自身 (self-similar at all meta levels) |
| **Origin level** | 道 anchor identifies 所有 levels |
| **Zero level** | 太极 (R₀) 是 absolute ground — 「无分」之 anchor |

### 7.2 Y-combinator (hu) 之 algebraic 自指

V₄ outer 中之 hu (R₆+):
- Fixed points: hu(乾) = 乾, hu(坤) = 坤
- 2-cycle: hu(既济) = 未济, hu(未济) = 既济

**不动点之存在 = self-reference 之 algebraic 见证**。

### 7.3 静/动分界

| 静态 R-O closure (本文 R₀..R₈) | 动态层 (BaguaTuring) |
|---|---|
| 全 finite, 全 decidable | 引入 unbounded iteration → halting undecidability |
| 自指 = hu fixed point + Cayley fusion | 自指 = quine + universal interpreter |
| 0 sorry / 0 axiom | 1 axiom (kleene_recursion_axiom) |

**完整 / 不完整之精确分界 = 静态/动态界面**。

### 7.4 Insight — 自指之 ontological 必要

> 「自描述」⟹ 「自指」. Algebraic 实现:
> - **元 = 算子** (Cayley fusion)
> - **道 anchor** (fusion origin)
> - **太极 R₀** (absolute zero ground)
> - **Y-combinator (hu)** (fixed-point generator)
>
> 四者合一 = 完整 self-referential closure. (Z/2)⁸ 系统对 Lawvere/Gödel/Y 三个经典自指原理之 minimal 离散统一实现。

---

## 第八部分：跨语言对应总表 (R₀..R₈)

### 8.1 R-hierarchy (元层)

| Rₙ | 古文 | o/x | Type Theory | Group | Physics |
|---|---|---|---|---|---|
| R₀ | 太极 | `` | Unit | trivial | vacuum |
| R₁ | 爻/两仪 | `o`/`x` | Bool | ℤ/2 | qubit |
| R₂ | 四象 | 2-char | Bool² | V₄ | 2-qubit |
| R₃ | 八卦 | 3-char | Bool³ | (ℤ/2)³ | 3-qubit |
| **R₄** | **面 Mian** | 4-char | Bool⁴ | (ℤ/2)⁴ | Ben×Zheng decomposition |
| **R₅** | 五爻 (provisional) | 5-char | Bool⁵ | (ℤ/2)⁵ | (transitional) |
| R₆ | 重卦 | 6-char | Bool⁶ | (ℤ/2)⁶ | 6-qubit + V₄ |
| R₇ | 因卦 | 7-char | Bool⁷ | (ℤ/2)⁷ | + past-cone marker |
| R₈ | 果卦 | 8-char | Bool⁸ | (ℤ/2)⁸ | + future-cone, Shi V₄ |

### 8.2 O-hierarchy 之新增 atomic 算子

| Oₙ atomic op | 古文 | mask (XOR) | 物理 |
|---|---|---|---|
| O₀ | (无) | trivial | trivial |
| O₁ | 反 | `x` | charge conjugation 影 |
| O₂ | (lift) | 2-char | 2-qubit Pauli |
| O₃ | dong/hua/bian + zong/hu | 3-char | P + T + PT + Y |
| O₄ | (lift to Mian-axis) | 4-char | (lift) |
| O₅ | (lift to 5-yao) | 5-char | (lift) |
| O₆ | + outer 3 flips | 6-char | 6-qubit + V₄ |
| **O₇** | **印** | `ooooooox` | toggle past-cone |
| **O₈** | **投** | `ooooooox` (8-bit) | toggle future-cone |

### 8.3 V₄ Klein 四群之多重 instantiation

V₄ 在易系统中**至少**出现 4 次:

| 层 | V₄ 实例 | 元素 |
|---|---|---|
| R₂ Aut | V₄ on SiXiang | id (`oo`), σ₁ (`xo`), σ₂ (`ox`), σ₁σ₂ (`xx`) |
| R₃ V₄ subgroup | {id, cuo₃, zong₃, 错综₃} | id (`ooo`), cuo (`xxx`), zong/错综 (perm) |
| R₆ V₄ subgroup | {id, cuo₆, zong₆, 错综₆} | id (`oooooo`), cuo (`xxxxxx`), zong/错综 (perm) |
| R₈ Shi V₄ | {道, 已, 今, 未} | mask 后 2 位 `oo`/`xo`/`xx`/`ox` |

---

## 第九部分：Lean 形式化映射

### 9.1 文件 → R/O 范围 (R₀..R₈)

| Lean 文件 | R/O 范围 | 关键定义 |
|---|---|---|
| (Unit type, Lean stdlib) | R₀ | `Unit` |
| [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) | R₁/R₃/R₆ + 部分 O | `Yao`, `Trigram`, `Hexagram`, `cuo/zong/hu` |
| [`BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) | O₁..O₆ 主体 | `dong/hua/bian`, `FlipCombo`, `Sheng`, `chong` |
| [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) | **R₄ (Mian)** + R₃ 4+4 + R₆ quadrant | `Ben/Zheng/Mian/Quadrant` — **Mian = R₄ anchor** |
| (待建) | **R₅ (五爻)** | `abbrev Pian5 := Mian × Bool` 候选 |
| [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) | R₇ + O₇.印 | `Cell128`, `yin` (= 印) |
| [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) | R₈ + O₈.投 + Shi V₄ | `Cell256`, `Shi`, `yin/tou` + 双射 |
| [`Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) | R₀..R₈ explicit + R8_complete | R-hierarchy abbrevs + parity/timeReversal/PT/yComb + bundle |

### 9.2 Lean abbrev 重号 (待落)

```lean
abbrev R0 := Unit                        -- 太极
abbrev R1 := Yao                          -- 爻/两仪
abbrev R2 := SiXiang                      -- 四象
abbrev R3 := Trigram                      -- 八卦
abbrev R4 := Mian                         -- 面 (= Ben × Zheng), 16
abbrev R5 := Mian × Bool                  -- 五爻 (provisional), 32
abbrev R6 := Hexagram                     -- 重卦, 64
abbrev R7 := Cell128                      -- 因卦, 128
abbrev R8 := Cell256                      -- 果卦, 256

-- R8_complete bundle (was R6_complete)
theorem R8_complete : ... := ⟨...⟩
```

### 9.3 Fusion 实现 (proposed)

```lean
abbrev R8 := Cell256

instance : AddCommGroup R8 := { ... }
instance : SMul R8 R8 := ⟨xor⟩

theorem cayley_inj : Function.Injective (fun c : R8 => (· ⊕ c)) := ...
def ι (c : R8) : R8 → R8 := (c ⊕ ·)
def ε (f : R8 → R8) : R8 := f oooooooo
theorem ε_ι (c : R8) : ε (ι c) = c := ...
```

### 9.4 Lean implementation map (post-Cell256 / Hierarchy refactor, 2026-05-10)

定本的 R-hierarchy 与 V₄ Shi 已全部 Lean 落地, 本节给出 doctrine concept ↔ source file 之精确 map.

- **R₀..R₈ (Z/2)ⁿ uniform layers**:
  - R₀ Taiji = `Unit` (implicit, Lean stdlib)
  - R₁ Yao = `Bool`, in [`formal/SSBX/Foundation/Yi/Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean)
  - R₂ SiXiang in [`formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean)
  - R₃ Trigram in [`formal/SSBX/Foundation/Yi/Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean)
  - R₄ Mian = Ben × Zheng (16 = (Z/2)⁴) in [`formal/SSBX/Foundation/Bagua/BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean)
  - R₅ Wuyao = Mian × Bool (32 = (Z/2)⁵) in [`formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean`](../../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean)
  - R₆ Hexagram (64 = (Z/2)⁶) in [`formal/SSBX/Foundation/Yi/Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean)
  - R₇ Cell128 = Hexagram × YinBit (128 = (Z/2)⁷) in [`formal/SSBX/Foundation/Bagua/Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean)
  - R₈ Cell256 = Hexagram × Shi (256 = (Z/2)⁸) in [`formal/SSBX/Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean)

- **Algebraic spine** (Phase A): `Cell{128,256}` carry Add/Zero/Neg/Sub + SMul,
  with origin = (qian, dao) = V₄ identity, plus Cayley `ι/ε` homomorphism.

- **Operators inner/outer**:
  - Atomic XOR-subgroup ops in [`Foundation/Hierarchy/Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean)
  - V₄ outer permutations (`zong` / `hu` / `cuoZong`) in [`Foundation/Hierarchy/Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean)

- **Lift/Project uniform API**: [`Foundation/Hierarchy/LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) (8 R-layer pairs, each with `proj_lift_id_Rn` retract lemma)

- **OX notation**: [`Foundation/Notation/OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) provides `OX["xxxxxxxx"]` macro
  (8-char `o`/`x` string → Cell256 literal; `o` = yang/false, `x` = yin/true; positions 7/8 encode YinBit/GuoBit → Shi)

- **Self-description witness**: [`formal/SSBX/Truth/SelfDescription.lean`](../../formal/SSBX/Truth/SelfDescription.lean)
  `Cell256OperatorComplete` theorem (V₄ extension of legacy 192-cell version)

- **R₈ closure bundle**: `R8_complete` in [`Foundation/Bagua/Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean)
  depends only on `propext` + `native_decide` axes (no project axioms).

---

## 第十部分：哲学结 + 开放方向

### 10.1 essence 一句话

> 「易」之 algebraic 核 = **(Z/2)⁸ Abelian 群之 Cayley 自作用 + 道作为 origin choice + V₄ 外对称接口 + 太极作为 absolute zero-anchor** —— 9 层 strict uniform R₀..R₈ (each Rₙ = (Z/2)ⁿ) 完整闭合; 元 ≅ 算子之 fusion 是「自描述」之 algebraic 本质;道之 anchoring 是「立心」之 ontological 必要; abelian closure 内严格完整、完备、自洽、自指。

### 10.2 v2.1 vs v1 之关键区别

| Aspect | v1 (yi-RO-hierarchy.md) | v2.1 (本文) |
|---|---|---|
| R 编号 | R₁..R₆ (含 R₃→R₄ chong jump) | **R₀..R₈ strict uniform (no jumps)** |
| Mian 之地位 | 在 BenZheng 内, 不在 R-hierarchy 主线 | **R₄ first-class** |
| (Z/2)⁵ = 32 | 跳过 | **R₅ 显式 (五爻 provisional)** |
| 太极 R₀ | 隐含 (Unit) | **R₀ 显式纳入** |
| Hexagram | R₄ | R₆ |
| Cell128 | R₅ | R₇ |
| Cell256 | R₆ | R₈ |
| chong (重) | "3-bit jump" | "3-step composite" |

### 10.3 完整 vs 不完整之精确分界 (与 v1 同)

| 范围 | 完整性 |
|---|---|
| R₀..R₈ + XOR + V₄ + Lift/Project + 道 (本文 closure) | ✅ 完整完备自洽自指 strict uniform |
| GL(8, F₂) non-XOR linear automorphisms | ❌ by design 不入 |
| S_{256} 任意 permutation | ❌ astronomical |
| Continuous (ℝ⁸ + measure) | ❌ different math object |
| Probabilistic (Δ²⁵⁵ simplex) | ❌ different math layer |
| Dynamical (time iteration) | ⚠ 在 BaguaTuring 之上 |

### 10.4 开放问题

- **R₅ 命名 final 定**: 五爻 (descriptive) vs 接/临/渐/进 (philosophical anchor)
- **R₅ Lean type**: `Mian × Bool` vs 独立 `Cell32`
- 印 / 投 atomic vs fancy (state-modifying)
- R₃ phenomenology 三相 vs R₇/R₈ 二元之精确映射
- 命名 final 定 (因/果/印/投 vs 印/投/始/终/持/期)
- R₉+ 是否存在 (无 candidate, 但 strict uniform 视角下 (Z/2)⁹ 数学存在)
- Outer non-XOR 算子族之深化研究

### 10.5 三句话总论

1. **Algebraic**: R₀..R₈ strict (Z/2)ⁿ uniform; (Z/2)⁸ at R₈ 完成 Cayley regular representation; 元 ≅ 算子 严格同构, abelian closure 内完整。

2. **Ontological**: 太极 = R₀ = absolute zero-anchor; 道 = R₈ origin = identity = no-op = 永真 cell, 一字承担五重身份, anchor 整个 fusion。

3. **Self-referential**: hu (Y-combinator) 之不动点 + Cayley fusion + 道 anchor + 太极 ground 四者合一 = 完整 self-referential closure.

---

## 附录 A：v1 → v2.1 重号表 (再次显示)

| v1 名 (旧) | v2.1 名 (新) | size | 类型 |
|---|---|---|---|
| (无) | **R₀** | 1 | Unit (太极) |
| R₁ | R₁ | 2 | Yao |
| R₂ | R₂ | 4 | SiXiang |
| R₃ | R₃ | 8 | Trigram |
| (跳过) | **R₄** | 16 | Mian (Ben × Zheng) |
| (跳过) | **R₅** | 32 | (provisional 五爻) |
| R₄ | **R₆** | 64 | Hexagram |
| R₅ | **R₇** | 128 | Cell128 |
| R₆ | **R₈** | 256 | Cell256 |

## 附录 B：术语对照

| 术语 | 在易 | 在抽象代数 | 在物理 |
|---|---|---|---|
| 太极 (R₀) | 无极 / 未分 | trivial group / Unit | vacuum (no distinction) |
| 元 | cell, state | group element | state vector |
| 算子 | operator, action | group automorphism | observable |
| 道 (R₈ origin) | 永真 anchor | identity element | reference vacuum |
| 因 / 果 | binary attribute | bit position | causal half-cone marker |
| 印 / 投 | atomic operator | Z/2 generator | toggle operator |
| 错 (cuo) | parity flip | XOR with all-1 | P (parity) |
| 综 (zong) | reverse permutation | non-XOR involution | T (time-reversal) |
| 互 (hu) | Y-combinator | fixed-point operator | Y / self-reference |
| (Z/2)⁸ Cayley | fusion | regular representation | wave-particle duality 离散版 |
| Pontryagin self-dual | (隐含) | character ≅ element | Fourier 自共轭 |
| Mian (R₄) | 面 = Ben × Zheng | (Z/2)² × (Z/2)² = (Z/2)⁴ | (BenZheng 16-命) |

## 附录 C：与其它 doctrine 文档之关系

| 文档 | 主题 | 与本文关系 |
|---|---|---|
| [yi-as-meta-framework.md](yi-as-meta-framework.md) | 哲学层 | 上层哲学 anchor (待 R₀..R₈ 重号同步) |
| [yi-calculus-theorem.md](yi-calculus-theorem.md) | Theorems A–K | § 6 完整性定理之严格证明 (待 R₅→R₇/R₆→R₈ 重号同步) |
| [yi-RO-hierarchy.md](yi-RO-hierarchy.md) (v1) | 旧编号 R₁..R₆ | bottom-up buildup; 本 v2.1 是 strict uniform definitive |
| [`Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) | R8_complete bundle (待重号) | § 9 之 Lean 落地 |
| [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) | Mian = R₄ first-class | R₄ 之 type 已存在 |
