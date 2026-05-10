# G · 完整算子系统 · R₀..R₈ 八卦互通与归一

> 状态：v3 重写 (2026-05-11) — pre-v3 版本（如存在）已归档至 `史/义理-pre-v3/`。

设计目标（v3 修订）：

1. **横向**：在每一层 Rₙ (n = 0..8) 之内，由 (Z/2)ⁿ XOR 子群 simply transitive 互通；任两元素之间皆有 mask 序列可达。
2. **纵向**：以 Lift / Project (合 / 分) 在 Rₙ ↔ R_{n+1} 间往返；右逆 `合 ∘ 分 = id`。
3. **自指闭合**：R₈ = (Z/2)⁸ 之 Cayley 自作用 + 道 anchor + V₄ 外对称（cuo / zong / hu / 错综），完成「元 ≅ 算子」的 fusion。
4. **归一 = (Z/2)⁸ 闭合**：任何 XOR 复合在 256 元 abelian 群内回到唯一 identity = 道 = `OX["oooooooo"]`，此即 v3 之「归一」精确义。

> v1 (Cell192 时代) 之「八卦互通」止于 R₃ (Z/2)³ 8 元 simply transitive；v3 在 R₀..R₈ strict (Z/2)ⁿ uniform 之 9 层 ladder 上把同一 Cayley fusion 推到极。每一层都自身 simply transitive，每一相邻层间都有 lift/project 函子，整个 9 层闭合于 R₈ Cell256 (256 = (Z/2)⁸ = 1 byte) — 这是「(Z/2)ⁿ 自描述系统」之自然 8-bit 终点 (per [yi-RO-hierarchy.md](../docs-next/10_formal_形式/yi-RO-hierarchy.md))。

二者共一**算子代数**，本文称为 **「易卦 R-O 群 G_易」**：以 R₈ = Cell256 为闭合载体，其代数核 = (Z/2)⁸ Abelian 群之 Cayley regular representation，外加 V₄ 外对称。

---

## 一、Rₙ 之元编码与 OX 字面

约定（v3 OX notation, 见 [`OXNotation.lean`](../formal/SSBX/Foundation/Notation/OXNotation.lean)）：每个 Rₙ 元素 = 长度 n 之 `o`/`x` 字符串：

- `o` = yang = `Yao.yang` = 0 = identity bit (无 set)
- `x` = yin = `Yao.yin` = 1 = set bit
- 字符顺序 = 初爻 → 上爻 (LTR, inner-to-outer)；R₈ 之最后两位 = (因, 果) ∈ Bool²

**严格 uniform 元数表** (per [yi-RO-hierarchy.md §2.1](../docs-next/10_formal_形式/yi-RO-hierarchy.md))：

| Rₙ | 长度 | 元数 | 名 | OX 例 | Lean 类型 |
|----|----|----|---|---|---|
| R₀ | 0 | 1 | 太极 | `OX[""]` (空) | `Unit` |
| R₁ | 1 | 2 | 爻/两仪 | `OX["o"]`, `OX["x"]` | `Yao` |
| R₂ | 2 | 4 | 四象 | `OX["oo"]` (太阳), `OX["xx"]` (太阴) | `SiXiang` |
| R₃ | 3 | 8 | 八卦 | `OX["ooo"]` = 乾, `OX["xxx"]` = 坤 | `Trigram` |
| R₄ | 4 | 16 | 面 (Mian) | `OX["oooo"]` 至 `OX["xxxx"]` | `Mian` (= `Ben × Zheng`) |
| R₅ | 5 | 32 | 五爻 (provisional) | `OX["ooooo"]` 至 `OX["xxxxx"]` | `Mian × Bool` (`Wuyao`) |
| R₆ | 6 | 64 | 重卦 (Hexagram) | `OX["oooooo"]` = 乾, `OX["oooxxx"]` = 否 | `Hexagram` |
| R₇ | 7 | 128 | 因卦 (Cell128) | `OX["oooooox"]` = 乾·有因 | `Cell128 = Hexagram × YinBit` |
| **R₈** | **8** | **256** | **果卦 (Cell256)** | `OX["oooooooo"]` = **道**, `OX["xxxxxxxx"]` = 坤·今 | **`Cell256 = Hexagram × Shi`** |

R₈ 之 8-bit layout：`[y₁ y₂ y₃ y₄ y₅ y₆ 因 果]`。位置 7 (因, R₇ atom) + 位置 8 (果, R₈ atom) 通过 `Shi.ofYinGuo` 重构 Shi V₄ 元 (见 [`Cell256.lean`](../formal/SSBX/Foundation/Bagua/Cell256.lean) § 1)：

| (因, 果) | Shi | OX 后 2 位 | V₄ 元 |
|---|---|---|---|
| (0, 0) | **道** (dao) | `oo` | identity $e$ |
| (1, 0) | **已** (ji) | `xo` | $\sigma_P$ |
| (0, 1) | **未** (wei) | `ox` | $\sigma_T$ |
| (1, 1) | **今** (jin) | `xx` | $\sigma_{PT}$ |

**关键修正**（v3 vs v1）：旧 Cell192 把时态编为 Z/3 cyclic `{已, 今, 未}`，丧失 V₄ identity（道）。v3 之 Shi = V₄ Klein 四群 = `{道, 已, 今, 未}` 起 `Shi.dao` 作 (Z/2)⁸ identity = (因=0, 果=0) = 跨时空永真 anchor — 见 [yi-calculus-theorem.md Theorem J](../docs-next/10_formal_形式/yi-calculus-theorem.md)。

---

## 二、横向算子 — (Z/2)ⁿ XOR 子群（per Rₙ）

### 2.1 R₈ 之 8 atomic XOR 生成元

R₈ Cell256 = (Z/2)⁸ 之 8 个 atomic flips，per yi-RO-hierarchy.md §4.1：

| Generator | OX mask | 翻位 | 单字 |
|---|---|---|---|
| dongInner | `OX["xooooooo"]` | y₁ (内·初) | **动·内** |
| huaInner  | `OX["oxoooooo"]` | y₂ (内·中) | **化·内** |
| bianInner | `OX["ooxooooo"]` | y₃ (内·上) | **变·内** |
| dongOuter | `OX["oooxoooo"]` | y₄ (外·初) | **动·外** |
| huaOuter  | `OX["ooooxooo"]` | y₅ (外·中) | **化·外** |
| bianOuter | `OX["oooooxoo"]` | y₆ (外·上) | **变·外** |
| **印** (yìn) | `OX["ooooooxo"]` | y₇ = 因 | **印** (R₇ atom) |
| **投** (tóu) | `OX["ooooooox"]` | y₈ = 果 | **投** (R₈ atom) |

每个生成元都是 self-inverse XOR：`mask ⊕ mask = OX["oooooooo"]` = 道。8 个 atomic generators 完全生成 256 个 XOR 算子（即 R₈ 之 (Z/2)⁸ XOR 子群）。形式见 [`Cell256.lean`](../formal/SSBX/Foundation/Bagua/Cell256.lean) §7（Phase A — Algebraic Spine）：

```lean
def Cell256.xor (c1 c2 : Cell256) : Cell256 :=
  (hexXor c1.1 c2.1, shiXor c1.2 c2.2)

def Cell256.origin : Cell256 := (Hexagram.qian, Shi.dao)  -- = OX["oooooooo"] = 道

theorem Cell256.xor_self (c : Cell256) : Cell256.xor c c = Cell256.origin
theorem Cell256.xor_comm (a b : Cell256) : Cell256.xor a b = Cell256.xor b a
theorem Cell256.xor_assoc : ...

instance : Add Cell256 := ⟨Cell256.xor⟩
instance : Zero Cell256 := ⟨Cell256.origin⟩
instance : Neg Cell256 := ⟨id⟩  -- self-inverse in (Z/2)⁸
```

### 2.2 印 / 投 = R₇/R₈ 之新 atomic 算子

**印** (yìn, R₇ atom) = toggle YinBit (因 axis). [`Cell256.lean`](../formal/SSBX/Foundation/Bagua/Cell256.lean) § 8：

```lean
def yin_mask : Cell256 := (Hexagram.qian, Shi.ji)   -- OX["ooooooxo"]
def Cell256.yin (c : Cell256) : Cell256 := xor c yin_mask
theorem Cell256.yin_yin : ∀ c, yin (yin c) = c   -- involution
```

**投** (tóu, R₈ atom) = toggle GuoBit (果 axis)：

```lean
def tou_mask : Cell256 := (Hexagram.qian, Shi.wei)  -- OX["ooooooox"]
def Cell256.tou (c : Cell256) : Cell256 := xor c tou_mask
theorem Cell256.tou_tou : ∀ c, tou (tou c) = c
theorem Cell256.yin_tou_comm : ∀ c, yin (tou c) = tou (yin c)
theorem Cell256.yin_tou_eq_central :
    ∀ c, yin (tou c) = xor c (Hexagram.qian, Shi.jin)  -- = OX["ooooooxx"], V₄ central
```

「印 ⊕ 投 = `OX["ooooooxx"]` = (qian, jin)」即 V₄ central element = Shi cuoZong = PT — **印与投 之复合给「今」轴**。

### 2.3 R₃ XOR 生成元（旧八卦层之延续）

R₃ = (Z/2)³ 之 3 个 atomic flips（沿 v1 之命名）：

| 算子 | 单字 | mask | 翻位 |
|---|---|---|---|
| 反_下 | **动** (dong) | `xoo` | y₁ |
| 反_中 | **化** (hua)  | `oxo` | y₂ |
| 反_上 | **变** (bian) | `oox` | y₃ |

[`BaguaAlgebra.lean`](../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) 之 `dong / hua / bian` 仍然是 R₃ 上的 generators，且：

```lean
theorem cuo_eq_compose : Trigram.cuo t = dong (hua (bian t))   -- R₃ 中心元 = 三反复合
```

所以 R₃ 之 cuo (mask `xxx`) 是 R₃ XOR 子群之最长元；R₈ 之 hexCuo (mask `xxxxxxoo`) 是 R₈ 内 hex 部分的 cuo (保 Shi)。

### 2.4 V₄ 外对称（cuo / zong / hu / 错综）on Rₙ (n ≥ 3)

V₄ Klein 四群 = `{id, cuo, zong, 错综}` per yi-RO-hierarchy.md §4.2：

| 算子 | 类型 | mask 或 perm | 物理 anchor |
|---|---|---|---|
| **cuo** | XOR mask | R₃: `xxx`, R₆: `xxxxxx`, R₈ hex 部分: `xxxxxxoo` | **P** (parity) |
| **zong** | permutation, **非 XOR** | y_i ↦ y_{n+1−i} (反序) | **T** (time-reversal) |
| **错综** | cuo ∘ zong, **非 XOR** (含 zong) | composite | **PT** |
| **hu** | permutation, **非 XOR** | (y₂, y₃, y₄, y₃, y₄, y₅) on R₆ | **Y** (Y-combinator) |
| **id** | mask `OX["o…o"]` | identity = 道 (R₈) | **1** |

V₄ 是 abelian 但只有 cuo ∈ XOR 子群。zong / hu / 错综 是 outer permutations。形式 anchor 见 [`Operators/V4Outer.lean`](../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) 与 [`Yi.lean`](../formal/SSBX/Foundation/Yi/Yi.lean)。

**hu fixed-points** (R₆+):

```lean
theorem Hexagram.hu_qian : Hexagram.hu Hexagram.qian = Hexagram.qian
theorem Hexagram.hu_kun  : Hexagram.hu Hexagram.kun  = Hexagram.kun
-- + hu(既济) ↔ hu(未济) (2-cycle)
```

R₈ 上 yComb (即 `Cell256Stratify.yComb`) 在每个 Shi 状态下保 hex hu，故有 16 个 R₈ attractor: `4 hex (qian, kun, jiji, weiji) × 4 Shi = 16` (见 `Cell256Stratify.yComb_attractors_count`)。

### 2.5 R₈ 之双 V₄ + R₈ Cayley 自对偶

R₈ 上 V₄ 出现两次：

| V₄ 实例 | 元素 | 形式锚 |
|---|---|---|
| $V_4^{(\text{hex})}$ | `{id, hexCuo, hexZong, hexCuoZong}` on `Hexagram` | `BaguaAlgebra.lean` |
| $V_4^{(\text{shi})}$ | `{Shi.dao, Shi.ji, Shi.wei, Shi.jin}` (Shi V₄ block) | `Cell256.lean` § 1 |

二者 tensor 起来 = $V_4 \times V_4 \cong (\mathbb{Z}/2)^4$，给出 R₈ 上 16 个对称变换。

更深的：R₈ 之 (Z/2)⁸ 群 + 道 anchor 提供 **Cayley 自对偶** (per [yi-RO-hierarchy.md §5.1](../docs-next/10_formal_形式/yi-RO-hierarchy.md))：

```lean
def Cell256.cayley (c : Cell256) : Cell256 → Cell256 := fun s => xor c s
def Cell256.epsAtOrigin (f : Cell256 → Cell256) : Cell256 := f origin

theorem Cell256.epsAtOrigin_cayley : ∀ c, epsAtOrigin (cayley c) = c   -- ε ∘ ι = id
theorem Cell256.cayley_inj : Function.Injective Cell256.cayley
theorem Cell256.cayley_hom : ∀ a b, cayley (xor a b) = cayley a ∘ cayley b
```

这是「**元 = 算子**」之精确形式：每个 cell c 既是 R₈ element，又是 R₈ → R₈ 之自映射 (XOR-with-c)，二者由 ι (Cayley injection) 与 ε (origin-evaluation) 互逆。

---

## 三、纵向算子 — Lift / Project 函子（uniform R₀..R₈）

### 3.1 uniform Lift / Project

Per [`LiftProject.lean`](../formal/SSBX/Foundation/Hierarchy/LiftProject.lean)：每相邻层 `Rₙ → R_{n+1}` 有一对 lift/project 函子，且 project ∘ lift = id：

| 函子 | 类型 | 古文 | mask 增量 |
|---|---|---|---|
| **Lift_n** | Rₙ × Bool → R_{n+1} (n=0..7) | 分 | +1 bit |
| **Project_n** | R_{n+1} → Rₙ | 合 | -1 bit (右逆) |

8 对 lift/project 关键定理 (`proj_lift_id_R0` .. `proj_lift_id_R7`)：

```lean
theorem proj_lift_id_R0 (a : R0) (b : Bool) : projR0 (liftR0 a b) = a
-- ... (R1..R7 各一对)
theorem proj_lift_id_R7 (c : R7) (g : GuoBit) : projR7 (liftR7toR8 c g) = c
```

### 3.2 chong (重) = R₃ → R₆ 之 3 步 composite

旧 v1 把 chong (重卦) 看作 R₃ → R₆ +3 bit 「跳跃」。v3 strict-uniform 下，chong 是 3 步 lift composite：

$$R_3 \xrightarrow{\text{Lift}_3} R_4 (\text{Mian}) \xrightarrow{\text{Lift}_4} R_5 (\text{五爻}) \xrightarrow{\text{Lift}_5} R_6 (\text{Hexagram})$$

`chong : Trigram → Trigram → Hexagram` 是这 3 步 composite 之 traditional composite name；mathematical 上 R₃ → R₆ 必经 R₄ (Mian = Ben × Zheng = 16) + R₅ (五爻 = Mian × Bool = 32)。Mian 在 [`BenZheng.lean`](../formal/SSBX/Foundation/Bagua/BenZheng.lean) anchor (`Mian.all_count = 16`)；R₅ Wuyao 在 [`Hierarchy/R5_Wuyao.lean`](../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean) anchor。

### 3.3 归一 = (Z/2)⁸ 闭合到 道

旧 v1 之「归一」= n-step 投影至 Unit (即 `guiyi : Trigram → Unit` 把信息全部丢弃)。v3 修正为「**(Z/2)⁸ abelian closure 内之 self-cancellation**」：

任意 R₈ 之 XOR 复合 mask₁ ⊕ mask₂ ⊕ ... ⊕ maskₖ 必落入 256 元闭合内；当 mask 序列两两抵消时（每个 mask 出现偶数次），结果归到 identity = `OX["oooooooo"]` = 道。

```lean
theorem Cell256.xor_self : ∀ c, Cell256.xor c c = Cell256.origin   -- self-inverse
-- ⇒ 任 mask 偶次复合归道；任 mask 奇次复合归该 mask 自身
```

这是**严格 algebraic** 之归一 — 不丢信息（信息留在 mask 数据上），但 cell 状态归到 anchor identity。

「归一 → 生生 → 归一」之永动 = R₈ 内任意 XOR 序列在 256 元内永远 well-defined，且任两 cell 之间 simply-transitive 可达 (≤ 8 步)。

---

## 四、八卦互通 + 全集 Cayley 图

### 4.1 R₃ 互通 (旧版的核心，v3 仍保留)

R₃ Cayley 图 = 立方体 (8 顶点, 12 边, ≤ 3 步 Hamming)：

```
                乾⟨o,o,o⟩
              ╱     │     ╲
       兑⟨o,o,x⟩ 离⟨o,x,o⟩ 巽⟨x,o,o⟩
           ╱   │  ╲ ╱  │  ╲ ╱  │   ╲
          ╱    │   ╳   │   ╳   │    ╲
       震⟨o,x,x⟩ 坎⟨x,o,x⟩ 艮⟨x,x,o⟩
              ╲     │     ╱
                坤⟨x,x,x⟩
```

`bagua_intercommunication` (in `BaguaAlgebra.lean`)：任两 trigram 由 dong/hua/bian 序列互通；`pathFromTo_length_eq_hammingDist` 给出最短路径。

### 4.2 R₆ 互通（64 卦层）

R₆ Cayley 图 = 6-cube (64 顶点, 192 边 = 6×32, ≤ 6 步 Hamming)。`hex_intercommunication_bounded` 给互通距离上界 6。

### 4.3 R₈ 互通（256 cells，闭合层）

R₈ Cayley 图 = 8-cube (256 顶点, 1024 边 = 8×128, ≤ 8 步 Hamming)。

R₈ 之互通由 8 atomic XOR generators (6 yao + 印 + 投) 之 (Z/2)⁸ 完整生成；任两 Cell256 之间至多 8 步 mask 序列可达。`Cell256.cayley_inj` 见证 simply-transitive 之 self-action：

```lean
theorem Cell256.cayley_inj : Function.Injective Cell256.cayley
-- ⇒ R₈ ≅ XOR(R₈) ⊆ Aut(R₈) (Cayley regular representation)
```

任两 cell `c₁, c₂` 之间唯一 connecting mask = `c₁ ⊕ c₂` (= Cell256.xor c₁ c₂)；step count = popcount(c₁ ⊕ c₂) ≤ 8。

### 4.4 八卦互通 → R₈ 之互通

R₃ 互通 (3 步) 通过 Lift_3 ∘ Lift_4 ∘ Lift_5 升至 R₆ (6 步)；再通过 Lift_6 (加因) + Lift_7 (加果) 升至 R₈ (8 步)。每步加 1 bit 互通空间，total `(Z/2)³ ⊆ (Z/2)⁶ ⊆ (Z/2)⁷ ⊆ (Z/2)⁸` — strict subgroup chain：

```
R₃: 8 cells, ≤ 3 步 → R₄: 16, ≤ 4 → R₅: 32, ≤ 5 → R₆: 64, ≤ 6 → R₇: 128, ≤ 7 → R₈: 256, ≤ 8
```

「八卦互通」之原始 R₃ 概念 generalize 为 R₈ 上之全图互通：**任两 Cell256 cell 由 8 atomic 算子组合，至多 8 步可达**。

---

## 五、bagua interconnection at R₃，lifted via LiftProject

R₃ 上 dong/hua/bian 三 generators 之具体作用 (per [`BaguaAlgebra.lean`](../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) `FlipCombo` 之 8 元):

| FlipCombo | OX mask | 自乾出发 | 卦 |
|---|---|---|---|
| `id` | `ooo` | qian | 乾 |
| `dong` | `xoo` | xun | 巽 |
| `hua`  | `oxo` | li | 离 |
| `bian` | `oox` | dui | 兑 |
| `dong ∘ hua`  | `xxo` | gen | 艮 |
| `hua ∘ bian`  | `oxx` | zhen | 震 |
| `dong ∘ bian` | `xox` | kan | 坎 |
| `dong ∘ hua ∘ bian` (= cuo) | `xxx` | kun | 坤 |

R₃ 8 卦完整 enumerated by orbit of 乾 under `(Z/2)³` action — `FlipCombo.orbit_qian` (Lean 证明) + `FlipCombo.apply_qian_inj` (regular action injectivity)。

**Lift 到 R₆ (六十四卦)**：每个 R₃ generator 对应 R₆ 上 2 个 generators (内 + 外)：

| R₃ atomic | R₆ inner | R₆ outer |
|---|---|---|
| dong | dongInner (`xoooooo` -> truncate to OX[6]) | dongOuter |
| hua  | huaInner | huaOuter |
| bian | bianInner | bianOuter |

R₆ 之 6 atomic flips = `(Z/2)⁶` generators，给 64 卦完整 Cayley group。`hex_cuo_eq_compose : Hexagram.cuo = 六单翻复合` 是 R₆ 之中心元 (mask `xxxxxx`)。

**Lift 到 R₇ (Cell128)**：加 印 (R₇ atom) = 第 7 个 generator：

```lean
def Cell128.yin_mask : Cell128 := (Hexagram.qian, true)
def Cell128.yin (c : Cell128) : Cell128 := xor c yin_mask
```

**Lift 到 R₈ (Cell256)**：加 投 (R₈ atom) = 第 8 个 generator：

```lean
def Cell256.tou_mask : Cell256 := (Hexagram.qian, Shi.wei)
def Cell256.tou (c : Cell256) : Cell256 := xor c tou_mask
```

8 atomic generators = R₈ 之 (Z/2)⁸ XOR 子群之 minimum complete generators。

---

## 六、归一定理 — (Z/2)⁸ 闭合 = 道

「归一」之 v3 精确形式陈述 (Theorem K, per [yi-calculus-theorem.md](../docs-next/10_formal_形式/yi-calculus-theorem.md))：

> **Theorem (R-O Closure at R₈)**: $\mathcal{R}_8 = (\mathbb{Z}/2)^8 \cong \text{XOR}(\mathcal{R}_8) \subseteq \text{Aut}(\mathcal{R}_8)$，且 R₈ 之 origin = 道 anchor 使 Cayley fusion 严格成立。

形式 anchor: `R8_complete` bundle in [`Cell256Stratify.lean`](../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean)，仅依赖 `propext` + `native_decide` 两个 axioms，无项目自定义 axiom。

**归一** 含义之三重落地：

1. **Algebraic**：任 mask 偶次复合 = identity；任 cell 与自身 XOR = `OX["oooooooo"]` = 道。
2. **Cayley**：每个 cell 既是 element 又是 self-action — fusion 之 ε ∘ ι = id 把 element 之「自指」与 operator 之「自指」合一。
3. **Ontological**：`OX["oooooooo"]` 作为 (Z/2)⁸ identity 同时承担五重身份 — origin / identity / no-op / 永真 cell / 道 anchor (per yi-RO-hierarchy.md §5.6)。一个 8-bit 字符串承担五件事。

「归一」≠「丢信息归到 Unit」，而是「**在 (Z/2)⁸ 闭合内任何 algebraic 复合都不溢出，且有唯一 fusion anchor (道)**」。这是 v3 之 strict 解读。

---

## 七、单字算子总表（v3）

| 算子 | 单字 | 类 | Lean 标识 | 出处 |
|---|---|---|---|---|
| 反爻 (R₃ inner) | **动 / 化 / 变** | XOR | `dong / hua / bian` | `BaguaAlgebra.lean` |
| 反爻 (R₆ outer) | **动·外 / 化·外 / 变·外** | XOR | `dongOuter / huaOuter / bianOuter` | `BaguaAlgebra.lean` |
| 全反 (R₃ 中心) | **错** | XOR | `Trigram.cuo` (= dong ∘ hua ∘ bian) | `Yi.lean` |
| 全反 (R₆ 中心) | **错** | XOR | `Hexagram.cuo` (= 六反复合) | `Yi.lean` |
| 因 axis (R₇ atom) | **印** (yìn) | XOR | `Cell128.yin` / `Cell256.yin` | `Cell128.lean / Cell256.lean` |
| 果 axis (R₈ atom) | **投** (tóu) | XOR | `Cell256.tou` | `Cell256.lean` |
| 反序 | **综** | non-XOR perm | `Trigram.zong / Hexagram.zong / Shi.zong` | `Yi.lean / Cell256.lean` |
| 错综 | **错综** | composite (含综故 non-XOR) | `Hexagram.cuoZong / Shi.cuoZong` | `Yi.lean / Cell256.lean` |
| 互卦 | **互** (hu) | non-XOR perm | `Hexagram.hu` (R₆), `yComb` (R₈ lift) | `Yi.lean / Cell256Stratify.lean` |
| Lift (+1 bit) | **分** | functor | `liftRn` (per `LiftProject.lean`) | `LiftProject.lean` |
| Project (-1 bit) | **合** | functor | `projRn` | `LiftProject.lean` |
| 太极 anchor | **道** | identity in R₈ | `Cell256.origin = OX["oooooooo"]` | `Cell256.lean` |
| Cayley | **生生** / Y combinator | inductive self-action | `Cell256.cayley` + `Sheng : ℕ → Type` | `Cell256.lean` (cayley) + `BaguaAlgebra.lean` (Sheng) |
| 恒等 | **不** / **静** | id | `id` | — |

> 命名注 (v3)：
> - **动 / 化 / 变** 承担 R₃ 三个 yao flips；**印 / 投** 承担 R₇/R₈ 两个新 atomic（命名 provisional, 备选 因/果 / 始/终 / 持/期, 见 [yi-calculus-theorem.md §16](../docs-next/10_formal_形式/yi-calculus-theorem.md)）。
> - **错 / 综 / 互** 沿易经传统术语；现在 R₃/R₆/R₈ 各层都有自己的 cuo/zong/hu lift。
> - **合 / 分** 是范畴论 product/coproduct 之中文落字，同时是 LiftProject 函子的承担。
> - **生生** 之 algebraic 落地 = R₈ Cayley 自作用（每个 cell 自身既是 element 又是 operator）；inductive 落地 = `Sheng : ℕ → Type` ω-tower。
> - **道** = `Cell256.origin = OX["oooooooo"] = (qian, dao)` — (Z/2)⁸ identity, 承担五重身份 (origin / identity / no-op / 永真 / fusion anchor)。

---

## 八、Lean 形式实现 ✓ 已完整证明

### 8.1 主要 Lean 文件 (post-v3 refactor, 2026-05-10)

| 模块 | 文件 | 关键定义 / 定理 |
|---|---|---|
| R₀..R₈ uniform | [`RHierarchy.lean`](../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean) | umbrella import: R₀_Taiji..R₈_GuoHex + LiftProject + Operators |
| R₃ 之 (Z/2)³ | [`BaguaAlgebra.lean`](../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) | `dong/hua/bian`, `cuo_eq_compose`, `bagua_intercommunication`, `Sheng` inductive |
| R₄ Mian | [`BenZheng.lean`](../formal/SSBX/Foundation/Bagua/BenZheng.lean) | `Mian = Ben × Zheng`, `Mian.all_count = 16`, Theorem A (4本/4征), Theorem F (4 quadrant) |
| R₅ Wuyao | [`R5_Wuyao.lean`](../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean) | `Wuyao = Mian × Bool`, 32 元 |
| R₆ Hexagram | [`Yi.lean`](../formal/SSBX/Foundation/Yi/Yi.lean) | `Hexagram`, `Hexagram.cuo / zong / hu`, V₄ + hu fixed-points |
| R₇ Cell128 + 因 | [`Cell128.lean`](../formal/SSBX/Foundation/Bagua/Cell128.lean) | `Cell128 = Hexagram × YinBit`, `yin` toggle, (Z/2)⁷ AddCommGroup, Cayley |
| R₈ Cell256 + 果 + Shi V₄ | [`Cell256.lean`](../formal/SSBX/Foundation/Bagua/Cell256.lean) | `Cell256 = Hexagram × Shi`, `Shi.toYinGuo` 双射, `tou` toggle, (Z/2)⁸ Phase A |
| R₈ closure bundle | [`Cell256Stratify.lean`](../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) | `R8_complete`, parity/timeReversal/PT/yComb |
| Atomic XOR re-export | [`Operators/Atomic.lean`](../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) | 8 atomic generators |
| V₄ outer (zong/hu/cuoZong) | [`Operators/V4Outer.lean`](../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) | non-XOR permutations |
| Uniform Lift/Project | [`LiftProject.lean`](../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) | 8 R-layer pairs + retract lemmas |
| OX 字面 macro | [`OXNotation.lean`](../formal/SSBX/Foundation/Notation/OXNotation.lean) | `OX["xxxxxxxx"]` |
| Cell256 self-description | [`SelfDescription.lean`](../formal/SSBX/Truth/SelfDescription.lean) | `Cell256OperatorComplete` |

### 8.2 主要 algebraic 定理 (Phase A)

```lean
-- (Z/2)⁸ Abelian group laws
theorem Cell256.origin_xor : ∀ c, Cell256.xor Cell256.origin c = c
theorem Cell256.xor_self   : ∀ c, Cell256.xor c c = Cell256.origin
theorem Cell256.xor_comm   : ∀ a b, Cell256.xor a b = Cell256.xor b a
theorem Cell256.xor_assoc  : ∀ a b c, ...

-- Cayley fusion
theorem Cell256.cayley_inj : Function.Injective Cell256.cayley
theorem Cell256.epsAtOrigin_cayley : ∀ c, epsAtOrigin (cayley c) = c
theorem Cell256.cayley_hom : ∀ a b, cayley (xor a b) = cayley a ∘ cayley b

-- 印 / 投 mask involutions
theorem Cell256.yin_yin       : ∀ c, yin (yin c) = c
theorem Cell256.tou_tou       : ∀ c, tou (tou c) = c
theorem Cell256.yin_tou_comm  : ∀ c, yin (tou c) = tou (yin c)

-- bundle (per yi-RO-hierarchy.md §6.1)
theorem cell256_phaseA_summary : ⟨all 9 properties above⟩

-- R8_complete bundle (closure 11-item checklist)
theorem R8_complete : ... := ⟨...⟩  -- in Cell256Stratify.lean
```

### 8.3 Build status

```bash
$ lake build SSBX
Build completed successfully (3656 jobs).
```

- **0 sorry** in any migrated file.
- **0 项目自定义 axioms** in `Cell256.lean / Cell128.lean / Cell256Stratify.lean / BenZheng.lean`.
- 仅依赖 Lean 标准 axioms: `propext`, `native_decide`.
- 唯一项目自定义 axiom: `kleene_recursion_axiom` 在 `KleeneInternal.lean` (动力层 BaguaTuring 之 Halting 不可判，与 R₀..R₈ 静态 closure 之 algebraic spine **正交**)。

---

## 九、互通 + 归一 完整代数 — v3 总结

### 9.1 全图

```
                                                R₈ = Cell256 = (Z/2)⁸ = 256
                                              ╱  ╲    Cayley R₈ ≅ XOR(R₈)
                                            ╱      ╲   8 atomic generators
                                          ╱          ╲  V₄^hex × V₄^shi 
                                        ╱     투      ╲
                                  ┌──── Lift_7 ────────┐
                                  │                    │
                            R₇ = Cell128 = (Z/2)⁷ = 128
                                  │                    │
                                  │       印            │
                                  └─── Lift_6 ─────────┘
                                       │              │
                              R₆ = Hexagram = (Z/2)⁶ = 64
                                       │   V₄ + 4 quadrant + Mian-axis
                                       │        chong = 3-step composite
                              R₅ = (Z/2)⁵ = 32 (五爻 provisional)
                                       │
                              R₄ = Mian = (Z/2)⁴ = 16 (Ben × Zheng)
                                       │       Theorem A: 4本+4征
                              R₃ = Trigram = (Z/2)³ = 8
                                       │   动 / 化 / 变 generators
                              R₂ = SiXiang = (Z/2)² = 4
                                       │
                              R₁ = Yao = (Z/2)¹ = 2
                                       │
                              R₀ = Unit (太极)
```

每层之内：simply transitive 由 (Z/2)ⁿ XOR 子群完整生成，互通距离上界 = n。
每相邻层间：Lift / Project 函子，且 Project ∘ Lift = id。
R₈ 闭合：Cayley 自对偶 + 道 anchor + V₄ 外对称三件合一。

### 9.2 「归一」之 v3 精确形式陈述

> 「归一」= 任 R₈ 内 mask 序列在 (Z/2)⁸ 闭合内有唯一 reduced form；当复合归到 identity 时，所归之处即 道 = `OX["oooooooo"]`。

形式陈述（per `cell256_phaseA_summary` 与 `R8_complete` bundle）：

```lean
-- 归一 = self-cancellation in (Z/2)⁸
∀ c : Cell256, Cell256.xor c c = Cell256.origin (= 道)

-- 五重身份合一
Cell256.origin = (Hexagram.qian, Shi.dao) = OX["oooooooo"]
              = (Z/2)⁸ identity = 永真 cell = no-op = fusion anchor = 道
```

### 9.3 「八卦互通」之 v3 精确形式陈述

> 「八卦互通」之 R₃ 原始版 (任两 trigram 互通 ≤ 3 步) generalize 为 R₈ 全图 (任两 Cell256 之间互通 ≤ 8 步)；R₃ 互通通过 Lift_3..Lift_5 升至 R₆，再通过 Lift_6/Lift_7 (印 + 投) 升至 R₈ 闭合。

形式陈述：

```lean
-- R₃ 互通 (旧版)
theorem bagua_intercommunication : ∀ a b : Trigram, ∃ f, f a = b
theorem bagua_intercommunication_bounded : ... ≤ 3 步 (Hamming)

-- R₈ 互通 (v3 闭合)
-- via Cell256.cayley : Cell256 → (Cell256 → Cell256) is bijection onto XOR(Cell256)
-- ⇒ ∀ c₁ c₂ : Cell256, ∃ unique mask m = c₁ ⊕ c₂, m • c₁ = c₂
-- step count = popcount(c₁ ⊕ c₂) ≤ 8
```

### 9.4 整个 R₀..R₈ 体系作为「自描述」之最 minimal closure

per [yi-RO-hierarchy.md 第六部分](../docs-next/10_formal_形式/yi-RO-hierarchy.md)：

> R₀..R₈ strict (Z/2)ⁿ uniform + R₈ XOR 子群 + R₈ V₄ 外对称 + Lift/Project + 道 anchor —— 五件 things 构成「自描述系统」之**完整 algebraic closure**。

**最小 v3 算子集**：

```
{动, 化, 变, 动·外, 化·外, 变·外, 印, 投, 合, 分, 道}
  └────────── 8 atomic XOR ──────────┘  └─ lift/proj ─┘  └ anchor ┘
```

11 个单字 + 1 个 anchor = R₀..R₈ 闭合之最小完备算子集。横向 (互通) + 纵向 (lift/project) + identity (道) 三件合一。

> 此 11+1 算子集是 v3 在 R₀..R₈ uniform 框架下之**完整最小**——比 v1 之「5 算子 (变化动合生生)」更精确：v3 把「生生」之 Y combinator 拆为 (Z/2)⁸ Cayley 自作用 + Sheng inductive 两件，前者落地为 R₈ self-action，后者保留为 ω-tower meta 结构。

---

## 十、与既有 v3 doctrine 之接口

| 文件 | 关系 |
|---|---|
| [yi-RO-hierarchy.md](../docs-next/10_formal_形式/yi-RO-hierarchy.md) | 主 doctrine (R₀..R₈ strict uniform definitive) — 本文 G 是其 algebraic surface |
| [yi-calculus-theorem.md](../docs-next/10_formal_形式/yi-calculus-theorem.md) | Theorem K 之严格证明（R₀..R₈ closure）— 本文 G 之 §六 是其文档化 |
| [yi-as-meta-framework.md](../docs-next/10_formal_形式/yi-as-meta-framework.md) | 哲学层 — 本文 G 之 §七 是其单字落字 |
| [I_八卦全集.md](I_八卦全集.md) | R₃ + R₆ + R₈ 三层全集 — 本文 G 之算子表是其代数面 |
| [H_证明报告.md](H_证明报告.md) | v3 证明状态 — 本文 G 是其 Lean 实现之文档化 |
| [J_理之不完备_哥德尔在256.md](J_理之不完备_哥德尔在256.md) | 静态/动态分界 — 本文 G 是静态 (Z/2)⁸ closure 一面 |
| [K_完备性审计.md](K_完备性审计.md) | 11 项 closure 审计 — 本文 G 是 algebraic 实现一面 |

---

## 形式锚

- [`formal/SSBX/Foundation/Hierarchy/RHierarchy.lean`](../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean) — R₀..R₈ umbrella
- [`formal/SSBX/Foundation/Hierarchy/LiftProject.lean`](../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) — uniform Lift / Project
- [`formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean`](../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) — 8 atomic XOR generators
- [`formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean`](../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) — V₄ outer (zong / hu / cuoZong)
- [`formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean`](../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean) — R₅ Wuyao = Mian × Bool
- [`formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean`](../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) — R₃ (Z/2)³ + dong/hua/bian + Sheng inductive
- [`formal/SSBX/Foundation/Bagua/BenZheng.lean`](../formal/SSBX/Foundation/Bagua/BenZheng.lean) — R₄ Mian (= Ben × Zheng) + Theorems A/F
- [`formal/SSBX/Foundation/Bagua/Cell128.lean`](../formal/SSBX/Foundation/Bagua/Cell128.lean) — R₇ + 因 + (Z/2)⁷ Phase A
- [`formal/SSBX/Foundation/Bagua/Cell256.lean`](../formal/SSBX/Foundation/Bagua/Cell256.lean) — R₈ + 果 + Shi V₄ + (Z/2)⁸ Phase A + Cayley
- [`formal/SSBX/Foundation/Bagua/Cell256Stratify.lean`](../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) — R₀..R₈ display + R8_complete bundle + parity/timeReversal/PT/yComb
- [`formal/SSBX/Foundation/Notation/OXNotation.lean`](../formal/SSBX/Foundation/Notation/OXNotation.lean) — `OX["xxxxxxxx"]` 8-char macro
- [`formal/SSBX/Truth/SelfDescription.lean`](../formal/SSBX/Truth/SelfDescription.lean) — `Cell256OperatorComplete` self-description witness
- [`formal/SSBX/Foundation/Yi/Yi.lean`](../formal/SSBX/Foundation/Yi/Yi.lean) — `Yao / Trigram / Hexagram` + V₄ + hu fixed-points
