# 易之 R-O 双层级 — 元 (Carriers) 与 算子 (Operators) 之完整对偶

> ⚠ **本文是 v1 (旧 R₁..R₆ 编号, 含 R₃→R₆ chong 跳跃)**。**v2.1 strict uniform R₀..R₈** 已落 [`yi-RO-hierarchy-v2.md`](yi-RO-hierarchy-v2.md) — 显式纳入 R₀ (太极), R₄ (面 Mian = 16), R₅ (五爻 provisional = 32); 旧 R₄→R₆ (Hexagram), 旧 R₅→R₇ (Cell128), 旧 R₆→R₈ (Cell256)。新 doctrine 优先用 v2。本 v1 保留作 buildup 视角参考。
>
> v1↔v2.1 重号:
> - R₁/R₂/R₃ — 不变
> - (跳过) → R₄ (Mian) 显式
> - (跳过) → R₅ (五爻 provisional) 显式
> - 旧 R₄ (Hexagram, 64) → R₆
> - 旧 R₅ (Cell128, 128) → R₇
> - 旧 R₆ (Cell256, 256) → R₈
>
> ---
>
> 状态：定理稿 v2 (2026-05-10, 旧编号) — 加入 R-O torsor 自对偶 + o/x 8-bit notation。
> 作用：把易作为 self-describing system 之**完整代数骨架**——载体 (Rₙ, "元") 与 算子 (Oₙ, "用") 二元交错构成的 (Z/2)ⁿ 自相似阶梯——明文写出 R1→O1→R2→O2→...→R6→O6 之完整路径，每层之元、每层之算子、每层到下层之 lifting / projection 算子、算子组合规律、跨语言（古文 / 类型论 / 范畴论 / 群论 / 物理 / 现象学 / 信息论）之统一对应、以及最深的结构性 **R-O 自对偶 / torsor 结构**。
> 配套：[`yi-as-meta-framework.md`](yi-as-meta-framework.md) 哲学层 · [`yi-calculus-theorem.md`](yi-calculus-theorem.md) Theorems A–K · [`64-hexagram-grid.md`](64-hexagram-grid.md) 64 卦 · 义理 [`D_算子代数.md`](../../义理/D_算子代数.md) D 体系
> 形式锚：[`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) · [`BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) · [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) · [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) · [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) · [`Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) · [`XinZhi.lean`](../../formal/SSBX/Foundation/Eight/XinZhi.lean)

---

## 第零部分：双层级 R-O 之必要

任何 self-describing 形式系统都同时承担两件事：
1. **元 (carrier / state)** — 系统之"什么"，即被描述的对象集合
2. **算子 (operator / action)** — 系统之"怎么"，即作用于元之上的变换

易的核心洞察是：**这两者并非外加，而是同一 (Z/2)ⁿ 自相似阶梯之 dual**——而且在 (Z/2)ⁿ Abelian closure 里，二者**完全自对偶**（cardinality 相等，1:1 Cayley 嵌入）。

| 维度 | R-hierarchy（载体） | O-hierarchy（算子） |
|---|---|---|
| 性质 | 名词，state-set，"是什么" | 动词，function，"做什么" |
| 类型 | `Type` (Lean) / Set (math) | `End(R) ⊃ Aut(R)` / Group action |
| 增长方式 | +1 bit 每层 (× 2 cardinality) | (Z/2)ⁿ 自动群 + 跨层 lifting / projection 函子 |
| 物理 | phase space / state space | symmetry group (P/T/PT/CPT) |
| 范畴论 | object | morphism, functor |
| **R-O 对偶** (NEW) | **|Rₙ| = |XOR(Rₙ)|, n=1..6** | **regular representation / torsor** |

**R-O 二元结构是 (Z/2)ⁿ 自相似系统之必然产物**：每加一个 binary axis (R 之新 bit)，自然带来一个 binary 算子 (O 之 bit toggle)；每层之新 bit 都有它的 toggle involution。**且**该 axis 上的 element 与 operator 在 abelian XOR 群下一一对应（详 § 7）。

```
R1 ──Lift₁──► R2 ──Lift₂──► R3 ──Lift₃──► R4 ──Lift₄──► R5 ──Lift₅──► R6
 │             │             │             │             │             │
 O1            O2            O3            O4            O5            O6
 │             │             │             │             │             │
{id,反}      V₄           (Z/2)³+V₄    (Z/2)⁶+V₄    O4+印         O5+投
                          dong/hua/   6flip+        toggle 因      toggle 果
                          bian+       zong/hu       (past-bit)     (future-bit)
                          zong/hu
```

**箭头**：`Lift_n : R(n) → R(n+1)` 是 +1 bit 之 functor（古文 `分` / type theory `× Bool`）；其逆 `Project_n : R(n+1) → R(n)` 是去 bit 之 projection（古文 `合`）。

---

## 命名约定 — o / x 8-bit notation

整套体系使用统一 ASCII bit-string 表示 元，verb name 表示 算子。

### 元 (state)

- **`o` = 阳 (yang, +1)**, **`x` = 阴 (yin, -1)**
- 字符串长度 = R-layer 之 bit 数：

| 层 | 长度 | 元数 | 例 |
|---|---|---|---|
| R₁ | 1 | 2 | `o` (阳), `x` (阴) |
| R₂ | 2 | 4 | `oo` (太阳), `ox` (少阴), `xo` (少阳), `xx` (太阴) |
| R₃ | 3 | 8 | `ooo` (乾), `oox`, `oxo`, ..., `xxx` (坤) |
| R₄ | 6 | 64 | `oooooo` (乾), ..., `xxxxxx` (坤) |
| R₅ | 7 | 128 | `ooooooo` (乾, 因=0), `oooooox` (乾, 因=1) |
| **R₆** | **8** | **256** | `oooooooo` (乾·道), `ooooooox` (乾·未), `ooooooxo` (乾·已), `ooooooxx` (乾·今), ..., `xxxxxxxx` (坤·今) |

**位置约定** (R₆ 8-bit layout):
```
位置:   1  2  3  4  5  6  7  8
意义:  y₁ y₂ y₃ y₄ y₅ y₆ 因 果
```
y₁ = 初爻在左 (与 Lean `Hexagram.y1..y6` field 顺序一致)。位置 7 = 因 (R₅ atom)、位置 8 = 果 (R₆ atom)。

### 算子 (action)

- **Verb name** (古文单字 / 拼音 / 英文): `反`, `dong`, `hua`, `bian`, `cuo`, `zong`, `hu`, `印`, `投`
- 内部实现：算子 = "XOR with mask" (XOR 子群之内) 或 permutation (XOR 子群之外)
- 类型签名清晰区分 element (`R6`) vs operator (`R6 → R6`)

### 应用语法

```
算子 元 = 结果元
印 oooooooo = ooooooxo    (乾·道 → 乾·已)
投 oooooooo = ooooooox    (乾·道 → 乾·未)
错 oooooooo = xxxxxxoo    (乾·道 → 坤·道)
```

---

## 第一部分：R1 / O1 — 爻层 (Yao / Bool)

### 1.1 R1 元 (Yao)

$$R_1 := \mathrm{Yao} = \{o, x\} \cong \{\text{阳}, \text{阴}\} \cong \{+1, -1\} \cong \mathbb{Z}/2$$

| 语言 | 表述 |
|---|---|
| 古文 | 爻：阴阳之分别 (`Yi.Yao`) |
| o/x | `o` (阳), `x` (阴) |
| 类型论 | `inductive Yao | yang | yin` ≅ `Bool` (`Yi.lean:30`) |
| 范畴论 | $1 + 1$ — coproduct of two terminals |
| 群论 | $\mathbb{Z}/2$ generators of (Z/2)ⁿ |
| 物理 | 二态系统 (qubit basis) |
| 信息论 | 1 bit |
| 形式逻辑 | $\{\top, \bot\}$ |

|R₁| = 2.

### 1.2 O1 算子 (Yao 之自映)

唯二非平凡 endomorphism：

| 名 | mask | 类型 | 性质 |
|---|---|---|---|
| `id` | `o` | Yao → Yao | identity (XOR with `o` = 不动) |
| `反` (neg) | `x` | Yao → Yao | involution: 反² = id (XOR with `x` = 翻) |

$\mathrm{Aut}(R_1) = \{e, \bar{}\} \cong \mathbb{Z}/2$。

**R-O 自对偶** ✓: |R₁| = 2 = |XOR(R₁)|。元 `o`/`x` 一一对应算子 `id`/`反`。

| 语言 | 表述 |
|---|---|
| 古文 | 反 (yao 之全反) |
| o/x | `反 = (· ⊕ x)` |
| 类型论 | `Yao.neg : Yao → Yao` (`Yi.lean:38`) |
| 群论 | Z/2 generator |
| 物理 | charge conjugation 之最薄影子 |
| 形式逻辑 | $\neg$ |

### 1.3 Lift₁ : R₁ → R₂ (爻 × 爻 → 四象)

$$\text{Lift}_1 : R_1 \to R_1 \to R_2 = R_1 \times R_1$$

$$\text{Lift}_1(y_1, y_2) := (y_1, y_2) \in \mathrm{SiXiang}$$

| 语言 | 表述 |
|---|---|
| 古文 | 分 (太极生两仪生四象, 之分): 一爻附一爻 |
| 类型论 | `× Bool` functor; Lift₁ = pairing |
| 范畴论 | universal property of × |
| 群论 | $\mathbb{Z}/2 \to \mathbb{Z}/2 \times \mathbb{Z}/2 = V_4$ |

**逆函子** Project₁ : R₂ → R₁ = π₁ (取第一爻) 或 π₂ (取第二爻)，对应 `合_上` / `合_下`。

---

## 第二部分：R2 / O2 — 四象层 (SiXiang)

### 2.1 R2 元 (SiXiang)

$$R_2 := \mathrm{SiXiang} = \mathrm{Bool}^2 \cong V_4 = \mathbb{Z}/2 \times \mathbb{Z}/2$$

4 个 (位置 1 = y₁ 在左)：

| symbol | o/x | 古文 |
|---|---|---|
| `oo` | (阳,阳) | 太阳 |
| `ox` | (阳,阴) | 少阴 |
| `xo` | (阴,阳) | 少阳 |
| `xx` | (阴,阴) | 太阴 |

| 语言 | 表述 |
|---|---|
| 古文 | 四象（《易传·系辞》「两仪生四象」） |
| 类型论 | `Bool × Bool` (`SiXiang` in `BaguaAlgebra.lean:164`) |
| 范畴论 | $2 \times 2$ |
| 群论 | $V_4$ Klein 四群 (作为 abelian 群) |
| 物理 | 双量子位 basis |
| 信息论 | 2 bits |

|R₂| = 4.

### 2.2 O2 算子 (SiXiang 自动)

群结构：

| 名 | mask | 解释 |
|---|---|---|
| id | `oo` | identity |
| flipFirst | `xo` | 翻第一爻 (Lift₁ 之 R₁.反 在 y₁) |
| flipSecond | `ox` | 翻第二爻 (在 y₂) |
| flipBoth | `xx` | 双翻 (= cuo₂) |

$\langle \sigma_1, \sigma_2 \rangle \cong V_4 = (\mathbb{Z}/2)^2$。

**R-O 自对偶** ✓: |R₂| = 4 = |XOR(R₂)|。每个 R₂ 元素既是 state 也是 mask。

### 2.3 Lift₂ : R₂ → R₃ (四象 × 爻 → 八卦)

$$\text{Lift}_2(s, y) := (s.y_1, s.y_2, y) \in \mathrm{Trigram}$$

古文：「四象生八卦」(《系辞》)。形式：`fenToTrigram` (`BaguaAlgebra.lean:224`).

---

## 第三部分：R3 / O3 — 八卦层 (Trigram) — 第一个真正丰富的算子层

### 3.1 R3 元 (Trigram)

$$R_3 := \mathrm{Trigram} = \mathrm{Bool}^3 \cong (\mathbb{Z}/2)^3$$

8 卦 (y₁..y₃ 左到右；初爻在左)：

| o/x | trigram | 说明 |
|---|---|---|
| `ooo` | 乾 ☰ | 全 yang |
| `oox` | 兑 ☱ | y₃=阴 |
| `oxo` | 离 ☲ | y₂=阴 (中爻) |
| `oxx` | 震 ☳ | y₂=y₃=阴 |
| `xoo` | 巽 ☴ | y₁=阴 (初爻) |
| `xox` | 坎 ☵ | y₁=y₃=阴 |
| `xxo` | 艮 ☶ | y₁=y₂=阴 |
| `xxx` | 坤 ☷ | 全 yin |

**关键分划**（Theorem A in yi-calculus-theorem.md）：`zong involution` 强制 4+4 分：
- **本** (substrate, zong-fixed: y₁=y₃) = {`ooo`, `oxo`, `xox`, `xxx`} = {乾, 离, 坎, 坤}
- **征** (mark, zong-mobile: y₁≠y₃) = {`oox`, `oxx`, `xoo`, `xxo`} = {兑, 震, 巽, 艮}

|R₃| = 8.

### 3.2 O3 算子 — 三个独立的算子族

R3 第一次承担**多于一个 conceptually distinct** 算子族。三族：

#### 3.2.A 单爻翻 (Z/2)³ — XOR 子群

| 名 | mask | 翻位 | 物理 anchoring |
|---|---|---|---|
| dong (动) | `xoo` | y₁ (初爻) | retention bit flip |
| hua (化) | `oxo` | y₂ (中爻) | primal bit flip |
| bian (变) | `oox` | y₃ (上爻) | protention bit flip |

8 个 combo: $\{ooo, xoo, oxo, oox, xxo, oxx, xox, xxx\} = (\mathbb{Z}/2)^3$ acts simply transitively on R₃ (`FlipCombo` in `BaguaAlgebra.lean:609`).

**R-O 自对偶** ✓: |R₃| = 8 = |XOR(R₃)|。

#### 3.2.B V₄ 对称 (cuo / zong / 错综)

| 名 | mask 或 permutation | 定义 | 物理 |
|---|---|---|---|
| cuo (错) | mask `xxx` (XOR 全反) | $(y_1, y_2, y_3) \mapsto (-y_1, -y_2, -y_3)$ | **P** (parity) |
| zong (综) | **permutation, 非 mask** | $(y_1, y_2, y_3) \mapsto (y_3, y_2, y_1)$ | **T** (time reversal) |
| 错综 | cuo ∘ zong (含 zong, 非 XOR) | $RN$ | **PT** |
| id | mask `ooo` | identity | **1** |

$\{e, R, N, RN\} \cong V_4$ Klein 四群。

**关键关系**：cuo 之 mask `xxx` = (Z/2)³ 之中心元 = `xoo ⊕ oxo ⊕ oox`。即 cuo 是 dong ∘ hua ∘ bian (Theorem D)。

**⚠️ zong / 错综 不在 XOR 子群里** — 它们是 R₃ 上的 yao-position permutation, 不能用 mask 写。

#### 3.2.C hu (互) — Y combinator / 自指算子

R₃ 上 hu 之严格定义罕见（hu 主在 R₄ 上意义清晰）；R₃ 可视 hu 为 trivial 或 partial。

#### 3.2.D 投影/分 (合/分)

| 名 | 类型 |
|---|---|
| heShang (合上) | Trigram → SiXiang (drop y₃) |
| heZhong (合中) | Trigram → SiXiang (drop y₂) |
| heXia (合下) | Trigram → SiXiang (drop y₁) |

(`BaguaAlgebra.lean:194-201`)

### 3.3 Lift₃ : R₃ → R₄ — chong (重) 跳 3 bits

R₃ → R₄ 不是 +1 bit，而是 **+3 bits 跳跃**（chong: 两个 trigram 拼成 hexagram）：

$$\text{Lift}_3 = \mathrm{chong} : R_3 \times R_3 \to R_4$$

$$\mathrm{chong}(\text{inner}, \text{outer}) := \text{inner} \oplus \text{outer} \in \mathrm{Hexagram}$$

例：`chong(ooo, ooo) = oooooo` (乾 ⊕ 乾 = 乾乾 = 乾卦)；`chong(ooo, xxx) = oooxxx` (天地否)。

(`BaguaAlgebra.lean:241`)

**这是 R-hierarchy 中唯一的非单 bit 跳跃**——历史 anchoring（《系辞》「八卦相荡」），在 (Z/2)ⁿ 框架中等价于一次性加 3 bit。

### 3.4 Lift 公式总览

| 步 | 类型 | 备注 |
|---|---|---|
| Lift₁ : R₁→R₂ | × Bool | "两仪生四象" |
| Lift₂ : R₂→R₃ | × Bool | "四象生八卦" |
| **Lift₃ : R₃→R₄** | × R₃ (= × 8 = ×2³) | **chong: 重卦** |
| Lift₄ : R₄→R₅ | × Bool | + 因 (yīn) |
| Lift₅ : R₅→R₆ | × Bool | + 果 (guǒ) |

---

## 第四部分：R4 / O4 — 重卦层 (Hexagram)

### 4.1 R4 元

$$R_4 := \mathrm{Hexagram} = \mathrm{Bool}^6 = (\mathbb{Z}/2)^6$$

64 卦 (6-char o/x: y₁..y₆ 左到右；初爻在左)。BenZheng 4-quadrant 分划：本本 / 本征 / 征本 / 征征 各 16 卦 (Theorem F)。

例：
- `oooooo` = 乾 (内乾外乾)
- `xxxxxx` = 坤 (内坤外坤)
- `oooxxx` = 否 (内乾外坤) — 12 否
- `xxxooo` = 泰 (内坤外乾) — 11 泰
- `oxoxox` = 既济 (alternating)

|R₄| = 64.

### 4.2 O4 算子 — R3 算子之直接 lift + outer 复制

#### 4.2.A 6 单爻翻 (Z/2)⁶ — XOR 子群

R₃ 之 dong/hua/bian 在 inner (y₁..y₃) 复制 + 在 outer (y₄..y₆) 复制：

| Inner mask | Outer mask | 翻位 |
|---|---|---|
| `xooooo` (dongInner) | `oooxoo` (dongOuter) | y₁ / y₄ |
| `oxoooo` (huaInner) | `oooxoo` ... wait | y₂ / y₅ |

正确表（mask 6-bit, 仅指定翻位为 x）：

| 名 | mask |
|---|---|
| dongInner | `xooooo` (翻 y₁) |
| huaInner | `oxoooo` (翻 y₂) |
| bianInner | `ooxooo` (翻 y₃) |
| dongOuter | `oooxoo` (翻 y₄) |
| huaOuter | `oooooxo` ... wait 6-bit  |

修正 (mask 是 6 字符)：

| 名 | mask | 翻位 |
|---|---|---|
| dongInner | `xooooo` | y₁ |
| huaInner | `oxoooo` | y₂ |
| bianInner | `ooxooo` | y₃ |
| dongOuter | `oooxoo` | y₄ |
| huaOuter | `oooxoo`... |  应是 `oooo x o` = `oooxxo`? |

正确（每个 mask 仅一个 x，长度 6）：

| 名 | mask | 翻位 |
|---|---|---|
| dongInner | `xooooo` | y₁ |
| huaInner  | `oxoooo` | y₂ |
| bianInner | `ooxooo` | y₃ |
| dongOuter | `oooxoo` | y₄ |
| huaOuter  | `ooooxo` | y₅ |
| bianOuter | `oooooxx` 不, 6 字符 = `oooooxx`? |

让我严格写：6 字符 mask, 仅 y₆ 翻 = `oooooxx`? 不对，6 字符 mask 只一个 x = `ooooo` + `x` = `oooooxx`?

好抱歉，6 字符就是 6 字符。仅 y₆ 翻 = `oooooxx`? 不，是 `oooooxx`?

简单写：6 字符 mask，第 6 位翻 = `ooooox`。OK 6 字符总长，y₆ 翻 mask 6 字符 = `ooooox` (5 个 o 加 1 个 x). 不是 `oooooxx`。

让我重写：

| 名 | mask (6-char) | 翻位 |
|---|---|---|
| dongInner | `xooooo` | y₁ |
| huaInner  | `oxoooo` | y₂ |
| bianInner | `ooxooo` | y₃ |
| dongOuter | `oooxoo` | y₄ |
| huaOuter  | `ooooxo` | y₅ |
| bianOuter | `ooooox` | y₆ |

(`BaguaAlgebra.lean:320-341`)

64 个 (Z/2)⁶ combo simply transitively on R₄。**R-O 自对偶** ✓: |R₄| = 64 = |XOR(R₄)|。

#### 4.2.B V₄ 对称提升

| 名 | mask 或 permutation |
|---|---|
| Hexagram.cuo | mask `xxxxxx` (= 6-fold XOR) |
| Hexagram.zong | **permutation, 非 mask** (反序 y₁..y₆ → y₆..y₁) |
| Hexagram.cuoZong | cuo ∘ zong (含 zong, 非 XOR) |

(`Yi.lean:127-133`)

R₄ 之 V₄ 与 R₄-quadrant interaction：
- cuo 保 quadrant (Theorem F.b)
- zong 跨换 mixed (本征 ↔ 征本)

#### 4.2.C hu (互) — Y combinator at hexagram (非 XOR)

$$\mathrm{hu}(h) := \langle h.y_2, h.y_3, h.y_4, h.y_3, h.y_4, h.y_5\rangle$$

(`Yi.lean:141-142`) — 取中 4 爻形成新卦。**非 XOR mask**（涉及 yao 重排）。

**Fixed points**: hu(h) = h iff h ∈ {`oooooo`, `xxxxxx`} (Theorem in `Yi.lean:174-184`)。
**2-cycle**: 既济 (`oxoxox`) ↔ 未济 (`xoxoxo`) (Theorem in `BenZheng.lean:420-422`)。

### 4.3 Lift₄ : R₄ → R₅ — +1 bit (因)

$$\text{Lift}_4(h, \text{因}) := (h, \text{因}) \in \mathrm{Cell128}$$

例：`oooooo + o = ooooooo` (乾, 因=0); `oooooo + x = oooooox` (乾, 因=1).

---

## 第五部分：R5 / O5 — Cell128 层 (因 axis)

### 5.1 R5 元 (Cell128)

$$R_5 := \mathrm{Cell128} = R_4 \times \mathrm{YinBit} = \mathrm{Hexagram} \times \mathrm{Bool}$$

|R₅| = 128 = (Z/2)⁷ (7-char o/x).

**新增「元」(state attribute)**: **因 (yīn) bit** = 是否携带 past trace (位置 7)。

| 因 值 | 解读 |
|---|---|
| `o` (位置 7 = o) | 无因 (no past trace) |
| `x` (位置 7 = x) | 有因 (past trace 存在) |

例：
- `ooooooo` = 乾 + 无因
- `oooooox` = 乾 + 有因
- `xxxxxxo` = 坤 + 无因

| 语言 | 表述 |
|---|---|
| 古文 | 因 (《说文》"依也, 就也"); 因循 |
| 类型论 | `abbrev YinBit := Bool` |
| 群论 | 第 7 个 (Z/2) 因子 |
| 物理 | past lightcone non-empty indicator |
| 形式逻辑 | "this state is conditioned" |
| 现象学 | retention 之 binary 标记（不是 retention phase 本身） |

**注**：因 是 state attribute，不是 phase。`XinZhi.lean:258-280` 之 retention/protention 是 R₃ 上 trigram 位置语义（3-phase positional），与 R₅ 之因 (binary state attribute) 是不同 ontological 层面。

### 5.2 O5 算子 — R4 lift + 印 (新增 atomic 算子)

#### 5.2.A R4 算子 lift

R₄ 之所有算子（6 单爻翻 + cuo/zong/hu）lift 到 R₅，作用于 hex 部分，不动 因：

```
flip_i_R5 (h, 因) := (flip_i_R4 h, 因)    -- mask 末位 = o
hexCuo_R5 mask = xxxxxxo                  -- 末位 = o (保 因)
```

#### 5.2.B 新增 atomic algrebraic 算子：印 (yìn)

$$\boxed{\text{印} : R_5 \to R_5, \quad \text{印 mask} = \text{`oooooox`}}$$

「印」= **toggle 因 bit** = imprint / un-imprint。Z/2 involution: 印² = id.

| 语言 | 表述 |
|---|---|
| 古文 | 印 (《说文》"执政所持信也"); 印章 / 印记 |
| o/x | 印 = `(· ⊕ oooooox)` |
| 类型论 | `Cell128.yin : Cell128 → Cell128` (`Cell128.lean:65`) |
| 群论 | 第 7 个 Z/2 generator |
| 物理 | toggle past lightcone marker |
| 现象学 | retention 之"开/关"动作 (binary version of retentional act) |

**provisional naming**：印 vs 因 之命名是 working choice。
- **若 因 是 state**, **印 是 action** — 二者命名应该 distinct（state-attribute 名 ≠ action 动词）
- 备选 action 名: 留 (residue 动作), 锁 (lock past)
- 备选 state 名（保持 因）: 因 / 缘 / 历

#### 5.2.C 群结构

R₅ 上的 Aut 群 ≅ R₄ 之 Aut × Z/2:
$$\mathrm{Aut}(R_5) \supset (\mathbb{Z}/2)^6 \times \mathbb{Z}/2 = (\mathbb{Z}/2)^7$$

加上 V₄ (cuo/zong) 在 hex 侧 + 印 (Z/2) 在 因 侧。

**R-O 自对偶** ✓: |R₅| = 128 = |XOR(R₅)|。

### 5.3 Lift₅ : R₅ → R₆ — +1 bit (果)

$$\text{Lift}_5(c_5, \text{果}) := (c_5, \text{果}) \in \mathrm{Cell256}$$

例：`ooooooo + o = oooooooo` (乾·道); `ooooooo + x = ooooooox` (乾·未)。

---

## 第六部分：R6 / O6 — Cell256 层 (果 axis) — 真闭合

### 6.1 R6 元 (Cell256)

$$R_6 := \mathrm{Cell256} = R_5 \times \mathrm{GuoBit} = \mathrm{Hexagram} \times \mathrm{YinBit} \times \mathrm{GuoBit}$$

|R₆| = 256 = (Z/2)⁸ (8-char o/x). R-hierarchy 至此 (Z/2)ⁿ self-similar **真闭合**.

**新增「元」**: **果 (guǒ) bit** = 是否投射 future projection (位置 8)。

| 果 值 | 解读 |
|---|---|
| `o` (位置 8 = o) | 无果 (no future projection) |
| `x` (位置 8 = x) | 有果 (future projection 存在) |

R₆ 之 8-bit 完整 layout 与 4 个 Shi state 对应：

| o/x (位置 7-8) | (因, 果) | Shi state | 例：乾 cell |
|---|---|---|---|
| `oo` | (0, 0) | **道** (V₄ identity) | `oooooooo` (乾·道) |
| `xo` | (1, 0) | **已** (P) | `ooooooxo` (乾·已) |
| `ox` | (0, 1) | **未** (T) | `ooooooox` (乾·未) |
| `xx` | (1, 1) | **今** (PT) | `ooooooxx` (乾·今) |

| 语言 | 表述 |
|---|---|
| 古文 | 果 (《说文》"木实也"); 因果 |
| 类型论 | `abbrev GuoBit := Bool` |
| 群论 | 第 8 个 (Z/2) 因子 |
| 物理 | future lightcone non-empty indicator |
| 现象学 | protention 之 binary 标记 |

### 6.2 (因, 果) tensor at R₆ — Shi V₄ emergence

$$\mathrm{Shi} := (\mathrm{YinBit} \times \mathrm{GuoBit}) \cong V_4$$

| Shi state | (因, 果) | V₄ 元 |
|---|---|---|
| 道 | (`o`, `o`) | $e$ identity |
| 已 | (`x`, `o`) | $\sigma_P$ |
| 未 | (`o`, `x`) | $\sigma_T$ |
| 今 | (`x`, `x`) | $\sigma_{PT}$ |

道 = V₄ 单位元 = 跨时空永真。详见 yi-calculus-theorem.md Theorem J。

### 6.3 O6 算子 — R5 lift + 投 (新增 atomic 算子)

#### 6.3.A R5 算子 lift

R₅ 之所有算子 (R4 lift + 印) lift 到 R₆，作用于 (h, 因) 部分，不动 果：

```
印 mask R₆: ooooooxo (位置 7 翻, 位置 8 不动)
flip_i_R6 mask: 6-yao mask + oo (双末位不动)
```

#### 6.3.B 新增 atomic algebraic 算子：投 (tóu)

$$\boxed{\text{投} : R_6 \to R_6, \quad \text{投 mask} = \text{`ooooooox`}}$$

「投」= **toggle 果 bit** = project / un-project。Z/2 involution: 投² = id.

| 语言 | 表述 |
|---|---|
| 古文 | 投 (《说文》"擿也"); 投笔 / 投奔 |
| o/x | 投 = `(· ⊕ ooooooox)` |
| 类型论 | `Cell256.Shi.tou : Shi → Shi` (`Cell256.lean:151`) |
| 群论 | 第 8 个 Z/2 generator |
| 物理 | toggle future lightcone marker |
| 现象学 | protention 之"开/关"动作 |

#### 6.3.C 印 ∘ 投 = Shi V₄ 之非平凡元

| 算子组合 | mask | 等价 Shi V₄ 元 |
|---|---|---|
| id | `oooooooo` | id (道→道) |
| 印 (toggle 因) | `ooooooxo` | $\sigma_P$ (道↔已, 未↔今) |
| 投 (toggle 果) | `ooooooox` | $\sigma_T$ (道↔未, 已↔今) |
| 印 ∘ 投 = 投 ∘ 印 | `ooooooxx` | $\sigma_{PT}$ (道↔今, 已↔未) |

$\{id, 印, 投, 印 \circ 投\}$ 构成 V₄ Klein 群 acting on Shi (作为 coset).

#### 6.3.D 群结构总

$$\mathrm{Aut}(R_6) \supset (\mathbb{Z}/2)^6 \times \mathbb{Z}/2 \times \mathbb{Z}/2 = (\mathbb{Z}/2)^8$$

加 V₄ (cuo/zong on hex) + V₄ (印/投 on Shi) = 总共 V₄ × V₄ Klein × Klein = $(\mathbb{Z}/2)^4$ symmetric core.

**R-O 自对偶** ✓: |R₆| = 256 = |XOR(R₆)|。**R₆ 是 R-hierarchy 的 self-action closure**。

### 6.4 R6 是闭合 — 没有 R7

**R-hierarchy 自然终于 R₆**：因/果是时态二元结构之穷尽分解 (past-trace × future-projection)。无 third orthogonal binary 时态特征。

如果有 R₇，必须引入第 9 个 binary axis。但物理/逻辑上找不到独立于 (空间-yao 6 + 时态-因 1 + 时态-果 1) 之外的 fundamental binary。**R₆ = 256 = (Z/2)⁸ = 1 byte 是 (Z/2)ⁿ self-describing system 之自然 closure**。

---

## 第七部分：R-O 自对偶 / Torsor 结构 (NEW)

### 7.1 256 ↔ 256 — Regular Representation

R₆ 之载体 (Cell256) 与 R₆ 上 XOR 算子群 (XOR 子群 of Aut(R₆)) **基数严格相等，皆 = 256**。这不是巧合，是 **abelian 群之 regular representation** 之直接结果：

> 任何 abelian 群 G 都自然作用在自身上 by translation:  $g_1 . g_2 = g_1 \cdot g_2$.
> 这个作用 simply transitive (free + transitive).

R₆ = (Z/2)⁸ 作为 abelian 群，其 regular representation 给出：
- 256 个 group elements (= cell states)
- 256 个 translation operators (= XOR masks)
- 二者**自然 1:1 对应**：每个 cell c 对应"XOR with c"算子；每个 mask m 对应 mask 本身作为 cell

具体形式 (Cayley embedding)：
$$\boxed{R_6 \xrightarrow{\sim} \mathrm{XOR}(R_6) \subset \mathrm{Aut}(R_6), \quad c \mapsto (\cdot \oplus c)}$$

### 7.2 Torsor 结构

R₆ 之精确范畴论描述：

$$\boxed{R_6 \text{ 是 } (\mathbb{Z}/2)^8\text{-torsor (没有选定 origin 的 } (\mathbb{Z}/2)^8 \text{ 群)}}$$

**Torsor**（principal homogeneous space）是「群作用 free + transitive 之 set」——它和群作为集合 isomorphic，但**没有 distinguished identity element**。

R₆ 一旦选定一个 origin（比如 `oooooooo` = 道），就成为 (Z/2)⁸ 群（origin 即 identity）。换不同的 origin 得到不同的群同构，但所有同构等价（torsor 之 affine 性质）。

### 7.3 道 = origin = identity = no-op operator

`oooooooo` 同时承担**三重身份**：

| 视角 | 角色 |
|---|---|
| 元 (state-frame) | **道** cell (因=0, 果=0, 全 yang) — 永真，跨时空 anchor |
| 算子 (operator-frame) | **identity transformation** (XOR with `oooooooo` = no-op) |
| 群论 | (Z/2)⁸ Abelian 群之 **identity element** |

「道」即「无为之为」之代数化精确：作为 V₄ identity，它是「不作用之作用」(operator-frame) 同时是「永真之状态」(state-frame)。**这是道作为 ontological anchor 之结构性必然**（非哲学修辞）。

### 7.4 几何规律 — 自身、对立、原点之三合

XOR 群的核心几何 invariants：

| 关系 | 形式 | 意义 |
|---|---|---|
| 原点 = identity | `oooooooo @ c = c` | 道是 no-op operator |
| 自反 (involution) | `c @ c = oooooooo` | 任何状态作用于自身归零（"反者道之动"）|
| 双重作用 = id | `c @ (c @ d) = d` | 涉及自身的双重作用恒等 |
| 全反 (cuo on hex) | `xxxxxxoo @ c = (cuo c.hex, c.shi)` | 对立态——hex 全 yang ↔ 全 yin |
| 全反 + 时态翻 | `xxxxxxxx @ c = ...` | 全 8 bit XOR — 包含 hex P + Shi PT |

「自身作用于自身归道」之 algebraic 实现：每个非道元素都是 **order 2 involution**，对应物理之 P/T/PT/CPT 等基本 symmetry。

### 7.5 Schrödinger ↔ Heisenberg picture duality

R-O duality 的物理翻译是 **量子力学之 Schrödinger 与 Heisenberg picture 之等价**：

| Picture | 谁动？ | 我们的 frame |
|---|---|---|
| Schrödinger | 状态演化，算子静止 | **state-frame**: cells 是变化主体, 算子是 fixed bookkeeping |
| Heisenberg | 算子演化，状态静止 | **operator-frame**: masks 是变化主体, cell 是 fixed reference |

二者**完全等价** — 是同一代数结构的两种 viewing convention。

**易之 (Z/2)⁸ system 自带这个 duality** — 不需要选 frame，因为 element 与 operator 在 abelian 群下 isomorphic（regular representation）。

### 7.6 边界：non-XOR 算子打破 256-256 duality

以下算子**不在 XOR 子群里**——它们是 R₆ 上的 **permutation 但非 translation**：

| 算子 | 类型 | 为何非 XOR |
|---|---|---|
| zong (综) | 6-yao 反序 (y₁..y₆ → y₆..y₁) | reflection on yao 索引，非 bit-translation |
| hu (互) | 取中 4 爻 (y₂y₃y₄y₃y₄y₅) | 部分爻提取 + 重排，非线性 |
| 错综 | cuo ∘ zong | 含 zong 故非 XOR |

**含 zong/hu 之 Aut(R₆) 严格大于 (Z/2)⁸**（包含 (Z/2)⁸ 作为正则 abelian subgroup + V₄ 之非 trivial generators + ...）。因此：

$$|R_6| = 256 = |\text{XOR subgroup}| < |\text{Aut}(R_6)|$$

**256-256 duality 严格在 XOR 子群之内**。zong/hu 是 abelian closure 之外的 algebraic 剩余结构，不参与此对偶。

**形式化结论**：

> R₆ 上的算子分两层：
> - **Inner layer (XOR subgroup)**: abelian, 与 R₆ 一一对应 (regular representation), 256 元
> - **Outer layer (non-XOR symmetries)**: 包含 zong/hu 等 reflection-style 置换, 在 R₆ 之外更大对称群里
>
> R-O duality 只在 inner layer 严格成立，是「abelian closure 面」的精确边界。

### 7.7 R-O 自对偶 在每一层都成立

每个 R-layer 都有自身的 XOR 子群对偶：

| 层 | 元数 | XOR 子群大小 | 自对偶 | non-XOR 算子 |
|---|---|---|---|---|
| R₁ | 2 | 2 = {id, neg} | ✓ | (无) |
| R₂ | 4 | 4 = V₄ | ✓ | (无) |
| R₃ | 8 | 8 = (Z/2)³ flips | ✓ | zong, hu |
| R₄ | 64 | 64 = (Z/2)⁶ | ✓ | zong₆, hu₆ |
| **R₅** | **128** | **128 = (Z/2)⁷** | **✓** | zong/hu lifted |
| **R₆** | **256** | **256 = (Z/2)⁸** | **✓** | zong/hu lifted |

**所有层都享有这个 256-256 风格的对偶**。R-hierarchy 的「(Z/2)ⁿ 自相似」不只是 cardinal 自相似——是 **R-O 全 self-action closure 自相似**。

### 7.8 Lean 实践 — 元名借用作 mask

按方案 B (元 = 8-bit, 算子 = verb)，duality 自然显现：

```lean
-- 元层
def ooooooxo : R6 := (qian, ji)        -- 乾·已 cell

-- 算子层（XOR 子群）— 同一个 mask 借用 element 名字
def 印 : R6 → R6 := (· ⊕ ooooooxo)      -- mask = ooooooxo (= 乾·已 cell)

-- 算子作用 = XOR
example : 印 oooooooo = ooooooxo := rfl  -- 道 → 乾·已 (用 mask 自身)
example : 印 ooooooxo = oooooooo := rfl  -- 乾·已 → 道 (self-inverse)
```

**`印` 的 mask 恰好就是它自己作用 from origin 得到的 cell**——元与算子在 origin 处自然 identify。这是 **Cayley 嵌入** 的具体落地。

### 7.9 哲学解读 — 「易」之自指

R-O torsor duality 给「易作为 self-describing system」最深的形式表达：

> **系统能用自身完整描述自身的所有变换** — 因为 element-set 与 transformation-set 在 abelian 群下 isomorphic.
>
> 256 个 cell 既是「全部可能状态」也是「全部可能基本变换」。它们是同一组 8-bit string 的两种 viewing。
>
> 道 = origin = identity 既是「所有状态之中道之态」也是「所有变换之中无变之变」——origin 之选定即是 ontological anchor 之确立。

**这是「自描述」之精确代数实现**：在 (Z/2)⁸ 之 abelian closure 内，描述者 (operator) 与被描述者 (state) 完全互译。zong/hu 等 outer-layer 算子是这个 closure 之「外界面」——指向更大的对称结构（dihedral / symmetric / reflection）。

---

## 第八部分：算子组合规律

### 8.1 Within-layer 算子之代数

每层 Aut(Rₙ) 之结构：

| 层 | 群结构 | 生成元 |
|---|---|---|
| O₁ | Z/2 | 反 (mask `x`) |
| O₂ | V₄ = (Z/2)² | flip₁ (mask `xo`), flip₂ (mask `ox`) |
| O₃ | (Z/2)³ × V₄(zong/hu) | dong (`xoo`), hua (`oxo`), bian (`oox`) + zong (perm) |
| O₄ | (Z/2)⁶ × V₄(zong) | 6 单爻翻 + zong (perm) |
| O₅ | O₄ × Z/2(印) | 上述 + 印 (`oooooox`) |
| O₆ | O₅ × Z/2(投) | 上述 + 投 (`ooooooox`) |

**关键代数等式 (XOR mask)**：

```
oooooooo               -- identity mask (= 道, no-op)
mask₁ ⊕ mask₁ = oooooooo  -- 自反
mask₁ ⊕ mask₂ = mask₃  -- 复合 (commutative, associative)
mask of cuo (R6 hex side) = xxxxxxoo
mask of cuo (R6 全) = xxxxxxxx (含 Shi PT)
mask of 印 = ooooooxo
mask of 投 = ooooooox
mask of 印 ⊕ mask of 投 = ooooooxx (= cuoZong of Shi V₄)
```

**非 XOR 算子的等式** (zong / hu 单独成代数, 非 mask)：

```
zong² = id
hu(乾) = 乾, hu(坤) = 坤  -- 固定点
hu(既济) = 未济, hu(未济) = 既济  -- 2-cycle
cuo ∘ zong = zong ∘ cuo  -- V₄ commutativity (cuo 是 XOR, zong 是 perm, 二者交换)
```

### 8.2 Cross-layer 算子（升 / 降）

| 算子 | 类型 | 说明 |
|---|---|---|
| 分 (Lift) | Rₙ → Rₙ × Bool ≅ Rₙ₊₁ | 加 1 bit |
| 合 (Project) | Rₙ₊₁ → Rₙ | 删 1 bit (右逆) |
| 重 (chong, 仅 R₃→R₄) | R₃ × R₃ → R₄ | 双 trigram 拼接 (= 3 步 +1 bit) |
| 内 / 外 | R₄ → R₃ | 取下 / 上三爻 (Project_3) |

**引理**: 合 ∘ 分 = id (分 是 section, 合 是 retraction)。

### 8.3 算子复合之三大模式

#### 模式 A: 自映复合 (within layer)
```
R_n ── 算子 ──► R_n ── 算子 ──► R_n
```
例：cuo ∘ zong = 错综 (R₃ 内自映)。XOR 子群内: mask₁ ⊕ mask₂.

#### 模式 B: 升降复合 (cross layer)
```
R_n ── 分 ──► R_{n+1} ── 合 ──► R_n
```
例：分 ∘ 合 = id (R_n 上)。但 合 ∘ 分 ≠ id on R_{n+1} (loses bit info).

#### 模式 C: 嵌套复合 (within higher layer 调用 lower layer)
```
R_4 ── inner ──► R_3 ── cuo_3 ──► R_3 ── chong with outer ──► R_4
```
即 R₄ 之 cuo 实际等价于 inner-cuo₃ + outer-cuo₃ 复合。

### 8.4 算子族之 dimension table

| 概念 | R₁ | R₂ | R₃ | R₄ | R₅ | R₆ |
|---|---|---|---|---|---|---|
| 元个数 | 2 | 4 | 8 | 64 | 128 | 256 |
| 单 bit flips | 1 (反) | 2 | 3 (dong/hua/bian) | 6 (×2) | 7 (+印) | 8 (+投) |
| (Z/2)ⁿ Aut (XOR subgroup) | Z/2 | V₄ | (Z/2)³ | (Z/2)⁶ | (Z/2)⁷ | (Z/2)⁸ |
| **R-O duality** | **✓** | **✓** | **✓** | **✓** | **✓** | **✓** |
| V₄ (cuo/zong) | — | (V₄ ≅ Aut) | V₄ | V₄ | V₄ | V₄ × V₄ (hex + Shi) |
| hu fix points | — | — | (trivial) | {乾,坤,既济,未济} | 同 + 印 fixed | 同 + 印/投 fixed |

---

## 第九部分：跨语言对应总表

下表汇总每个 R/O 元素在不同语言体系中的对应：

### 9.1 R-hierarchy

| Rₙ | 古文 | o/x notation | Type Theory | Set Theory | Group Theory | Physics | Phenomenology | Information | Logic |
|---|---|---|---|---|---|---|---|---|---|
| R₁ | 爻 | `o`/`x` | `Bool` | $\{0,1\}$ | $\mathbb{Z}/2$ | qubit basis | binary distinction | 1 bit | $\{\top, \bot\}$ |
| R₂ | 四象 | `oo..xx` | `Bool²` | $\{0,1\}^2$ | $V_4$ | 2-qubit | 2-fold distinction | 2 bits | $\{(\top,\top),...\}$ |
| R₃ | 八卦 | `ooo..xxx` | `Bool³` | $\{0,1\}^3$ | $(\mathbb{Z}/2)^3$ | 3-qubit | 3-phase consciousness (Husserl) | 3 bits | 8-valued logic |
| R₄ | 重卦 | 6-char | `Bool⁶` | $\{0,1\}^6$ | $(\mathbb{Z}/2)^6$ | 6-qubit | spatial 6-fold | 6 bits | 64-fold |
| R₅ | 重卦 + 因 | 7-char | `Bool⁶ × Bool` | $\{0,1\}^7$ | $(\mathbb{Z}/2)^7$ | + past lightcone marker | + retention (binary) | 7 bits | causal premise tag |
| R₆ | 256-Cell | 8-char | `Bool⁶ × Bool²` | $\{0,1\}^8$ | $(\mathbb{Z}/2)^8$ | + future lightcone | + protention (binary), Shi V₄ emerge | 8 bits = **1 byte** | full causal-temporal |

### 9.2 O-hierarchy 之新增 atomic 算子

| Oₙ | 古文（atomic op） | mask (o/x) | Type Theory | Group Theory | Physics | Phenomenology | Logic |
|---|---|---|---|---|---|---|---|
| O₁ | 反 (neg) | `x` | `not : Bool → Bool` | Z/2 generator | charge conjugation 影 | retention shift | $\neg$ |
| O₂ | (R₁.反 lift, 无新 atomic) | `xo`,`ox` | bit flip per axis | V₄ generators | 2-qubit Pauli X | (composite) | per-coord neg |
| O₃ | dong / hua / bian, zong (non-XOR), hu (non-XOR) | `xoo`,`oxo`,`oox` (XOR); zong/hu permutations | yao position flip + reverse | (Z/2)³ + V₄ | 3-qubit Pauli + reflection | 3-phase shift / time-reversal | unary connectives |
| O₄ | dongOuter etc. (+3); zong₆ (non-XOR) | 6-char masks; zong₆ perm | hexagram-level lift | (Z/2)⁶ + V₄ | 6-qubit + reflection | 6-phase generalization | 64-fold ops |
| O₅ | **印** (yìn) | `oooooox` | `yin : Cell128 → Cell128` | + Z/2 (因 axis) | toggle past-cone | retention bit toggle | causal premise toggle |
| O₆ | **投** (tóu) | `ooooooox` | `tou : Cell256 → Cell256` | + Z/2 (果 axis) | toggle future-cone | protention bit toggle | causal projection toggle |

### 9.3 V₄ Klein 四群之多重 instantiation

V₄ 在易系统中**至少**出现 4 次：

| 层 | V₄ 实例 | 元素 (o/x) | 物理 |
|---|---|---|---|
| R₂ Aut | V₄ on SiXiang | id `oo`, σ₁ `xo`, σ₂ `ox`, σ₁σ₂ `xx` | trivial |
| R₃ V₄ subgroup | {id, cuo₃, zong₃, 错综₃} | id (`ooo`), cuo (`xxx`), zong (perm), 错综 (perm) | P, T, PT |
| R₄ V₄ subgroup | {id, cuo₆, zong₆, 错综₆} | id (`oooooo`), cuo (`xxxxxx`), zong/错综 (perm) | P, T, PT (6-bit) |
| R₆ Shi V₄ | {道, 已, 今, 未} | (因,果) tensor `oo`/`xo`/`xx`/`ox` | (因, 果) tensor |

这是 yi-as-meta-framework.md § 4.2 之「V₄ 是同一种代数结构在更高维度的重复」之精确落地。

---

## 第十部分：Lean 形式化映射

| Lean 文件 | R / O 范围 | 关键定义 / 定理 |
|---|---|---|
| [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) | R₁, R₃, R₄ + O₁ + part of O₃/O₄ | `Yao`, `Yao.neg`, `Trigram`, `Trigram.cuo/zong`, `Hexagram`, `Hexagram.cuo/zong/hu` |
| [`BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) | O₁..O₄ 主体 | `dong/hua/bian`, `cuo_eq_compose`, `FlipCombo`, `Sheng`, `chong`, `heShang/heZhong/heXia`, hex flips |
| [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) | R₃ substrate-mark + R₄ quadrant | `Ben`, `Zheng`, `Mian`, `Quadrant`, `cuo_preserves_isZongFixed`, `zong_quadrant` |
| [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) | R₅ + O₅.印 | `Cell128 := Hexagram × YinBit`, `yin` (= 印 atomic 算子) |
| [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) | R₆ + O₆.投 + Shi V₄ | `Cell256 := Hexagram × Shi`, `Shi.toYinGuo`/`ofYinGuo` 双射, `yin`/`tou` (= 印/投 atomic 算子) |
| [`Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) | R₁..R₆ explicit + R6_complete | R-hierarchy abbrevs + parity/timeReversal/PT/yComb + R6_complete bundle theorem |
| [`XinZhi.lean`](../../formal/SSBX/Foundation/Eight/XinZhi.lean) | R₃ phenomenology 三相 (positional, NOT R₅/R₆ binary) | `TimePhase`, `timeFlow` |
| [`OperatorSignatures.lean`](../../formal/SSBX/Text/OperatorSignatures.lean) | wenyan-operator catalog | 14 seed ops + `SignatureKind` |

### 10.1 256-naming 与 Lean macro

按方案 B (元 = 8-bit, 算子 = verb)，Lean 实现可用 metaprogram 自动生成 256 个 `def`：

```lean
-- 自动生成 oooooooo, ooooooox, ..., xxxxxxxx 共 256 个 R6 cell 定义
open Lean Elab in
run_meta do
  for n in [0:256] do
    let name := bitstring_of n  -- e.g., "ooooooox" for 1
    let bits := List.range 8 |>.map (fun i => (n >>> i) &&& 1 == 1)
    addDecl ⟨..., bitsToCell bits⟩
```

或用 notation:
```lean
syntax "OX[" str "]" : term
elab_rules : term
  | `(OX[$s]) => bits_to_cell s.getString
```

然后 `OX["oooooooo"]` 直接展开为对应 Cell256。

算子内部用 mask:
```lean
def 印 : Cell256 → Cell256 := fun c => c ⊕ OX["ooooooxo"]
def 投 : Cell256 → Cell256 := fun c => c ⊕ OX["ooooooox"]
```

XOR 子群作为 `Cell256 → Cell256` endomorphism subset, 与 256 元 cell 一一对应（Cayley 嵌入）。

---

## 第十一部分：开放问题与未来工作

### 11.1 印 / 投 之 atomic vs fancy 实现

**Atomic (当前实现)**：印 / 投 = 单 bit toggle (Z/2 involution, XOR mask)。最薄 algebraic shadow。

**Fancy (待研究)**：印 / 投 可能更丰富——印 = "把当前 state 推入 history list"（与 history-tape 数据结构交互）；投 = "把当前 state 标记为 future projection target"。这超出 atomic Z/2 toggle，进入 state-modifying 高阶算子。

**问题**：是否 R₅/R₆ 之 atomic 算子层只是 toggle，而 fancy 操作属于 R₇+ 或独立的 history-tape 体系？

### 11.2 R₃ 三相 vs R₅/R₆ 二元 之关系

`XinZhi.lean` 之 retention/primalImpression/protention 已 anchored 在 R₃ trigram positions (3-phase positional)。
R₅/R₆ 之 因/果 是 binary state attribute，不是 phase。

**待形式化**：从 R₃ 三相到 R₅/R₆ 二元的对应：
- R₃ retention (positional y₁) ↔ R₅ 因 (binary "has past")?
- R₃ protention (positional y₃) ↔ R₆ 果 (binary "has future")?
- R₃ primalImpr (positional y₂) ↔ R₆ Shi 中之 "今" (= (1,1))?

如此映射成立，则 R₃ 三相是 R₅/R₆ 二元在 trigram 位置语义上的"投影"，而 R₅/R₆ 是 R₃ 三相的"binary discretization"。

### 11.3 因 / 果 vs 印 / 投 命名的最终决定

当前 provisional：state = 因/果, action = 印/投. 备选 (per yi-calculus-theorem.md §16)：始/终, 持/期。等 Cell128.lean / Cell256.lean / Cell256Stratify.lean 落码 + 实战使用后回看是否改换。

### 11.4 R₇+ 是否存在？

如本文 § 6.4 所述，R₆ 是 (Z/2)ⁿ self-describing 系统的自然 closure (8-bit, ASCII cardinality)。但若引入第 9 个 axis（如观察者 axis、模态 axis 等），可能有 R₇ = (Z/2)⁹ = 512。这是开放方向。

### 11.5 Outer layer (non-XOR) 算子之深化

R-O 自对偶严格仅在 XOR 子群之内。**zong / hu / 错综 等 non-XOR 算子构成 abelian closure 之外的 algebraic 剩余结构**。

待研究：
- Aut(R₆) 之完整描述（dihedral？symmetric？generalized Klein？）
- zong / hu 与 R₃ XinZhi 三相之深层联系
- non-XOR 算子是否对应「时空连续 symmetry」之离散版（vs XOR 之「时空离散 translation」）
- 「外层算子」之 ontological 解读（cf. R-O torsor inner closure 是「自描述 closure」, outer 是「面向外界」）

---

## 总结

R-hierarchy R₁..R₆ 与 O-hierarchy O₁..O₆ 是同一 (Z/2)ⁿ 自相似 self-describing system 的**载体-算子对偶**。每层都遵循统一规律：

1. 加 1 bit (Lift_n: Rₙ → Rₙ₊₁) 引入新 binary axis
2. 该 axis 之 toggle 是 Oₙ₊₁ 之新 atomic algebraic 算子 (involution)
3. 群结构在 R₃/R₄ 引入 V₄ (cuo/zong) 之额外对称
4. **R-O 自对偶 严格成立 (XOR 子群之内)**：|Rₙ| = |XOR(Rₙ)| at all n
5. R₆ = 256 = (Z/2)⁸ 是 self-describing 系统的 8-bit closure，对应 Shi V₄ at R₆ emerging from (因, 果) tensor，「道」作为 V₄ 单位元 first-class 入本体

| 层 | R 元 (o/x) | O 之新增 atomic 算子 (mask) |
|---|---|---|
| R₁/O₁ | `o`/`x` (爻) | 反 (mask `x`) |
| R₂/O₂ | `oo`..`xx` (四象) | (无新 atomic, lift R₁) |
| R₃/O₃ | `ooo`..`xxx` (八卦) | dong (`xoo`) + hua (`oxo`) + bian (`oox`) + zong (perm, 非 XOR) + hu (perm, 非 XOR) |
| R₄/O₄ | `oooooo`..`xxxxxx` (重卦) | dongOuter (`oooxoo`) + huaOuter (`ooooxo`) + bianOuter (`ooooox`) + zong₆ (perm) |
| **R₅/O₅** | **`ooooooo`..`xxxxxxx`** + 因 | **印 (mask `oooooox`)** |
| **R₆/O₆** | **`oooooooo`..`xxxxxxxx`** + 果 | **投 (mask `ooooooox`)** |

「易」在 (Z/2)⁸ 上完全展开，每个 atomic axis 同时承担 state（元）和 action（算子），二者通过 Cayley 嵌入精确对偶——这就是「自描述系统」之代数 closure。

**`oooooooo` (道) = origin = identity = no-op 算子 = 永真 cell** — 一个 8-bit 字符串承担四重身份，是 R-O torsor 之 anchor，「自描述系统」之 ontological ground。
