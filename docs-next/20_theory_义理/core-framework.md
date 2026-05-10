# 核心框架

> 状态：v3 定本 (2026-05-11) — Cell256 / V₄ Klein Shi / 严格-uniform R₀..R₈
> 作用：把不同义理文档与现 Lean 形式化层指向同一生成骨架；本页是义理层入口，**形式定本以 [`../10_formal_形式/yi-RO-hierarchy.md`](../10_formal_形式/yi-RO-hierarchy.md) 为准**。
> 配套：[`../00_start/final-theory.md`](../00_start/final-theory.md)（v3 速览） · [`../10_formal_形式/yi-calculus-theorem.md`](../10_formal_形式/yi-calculus-theorem.md)（Theorems A–K） · [`../10_formal_形式/yi-as-meta-framework.md`](../10_formal_形式/yi-as-meta-framework.md)（meta-framework）

---

## 1. 一句话总纲

**易之 algebraic 核 = 严格 uniform (Z/2)ⁿ R₀..R₈ 阶梯 + (Z/2)⁸ Cayley 自作用 + V₄ Klein Shi 在 R₈ emerge + 道 = (0,0) = V₄ identity = origin = no-op = 永真 cell**。

「四级生成 (太极→两仪→四象→八卦)」是这条阶梯的下半段（R₀..R₃），不是骨架顶层。骨架顶层是 R₈ = Cell256 = (Z/2)⁸ — 这是 self-describing 系统在 binary 上的最小完备闭合，与 ASCII 8-bit cardinality 同构。

---

## 2. R-hierarchy 阶梯（义理读法）

旧 `义理/A_经典易传.md` 给出经典二分读法：太极、一分为二、再成四象、再成八卦。它适合作为传统入口，但 **它是 R₀..R₃ 段，并非全部骨架**。完整骨架是九层 (Z/2)ⁿ uniform：

| R-index | size | 名（中） | 该层新原子 | 传统 Yi 锚 |
|---|---|---|---|---|
| R₀ | 1 | 太极 | (Unit) | 无极而太极 |
| R₁ | 2 | 爻 / 两仪 | 反 (neg) | 太极生两仪 |
| R₂ | 4 | 四象 | (lift R₁) | 两仪生四象 |
| R₃ | 8 | 八卦 | dong/hua/bian + cuo/zong/hu | 四象生八卦 |
| R₄ | 16 | 面 (Mian = Ben × Zheng) | (4 axis) | 面 / 16 命 |
| R₅ | 32 | 五爻 (provisional) | (5 axis) | (无传统锚) |
| R₆ | 64 | 重卦 (Hexagram) | outer 3 flips + 外 V₄ | 重卦 |
| R₇ | 128 | 因卦 (Cell128) | 因 (yīn) bit + 印 toggle | (新, post-traditional) |
| R₈ | 256 | 果卦 (Cell256) | 果 (guǒ) bit + 投 + Shi V₄ emerge | (新, post-traditional) |

**严格 uniform**: |Rₙ| = 2ⁿ for n=0..8, no jumps no gaps。旧版本所谓「R₃→R₄ chong jump」（直接 +3 bit 到 hexagram）已被显式拆为 R₃ → R₄ → R₅ → R₆ 三步 +1 bit lift composite。

形式锚: [`Foundation/Hierarchy/RHierarchy.lean`](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean) (umbrella) · 各层 [`R0_Taiji.lean`](../../formal/SSBX/Foundation/Hierarchy/R0_Taiji.lean) .. [`R8_GuoHex.lean`](../../formal/SSBX/Foundation/Hierarchy/R8_GuoHex.lean)。

---

## 3. 六征体系（M-axis 内容层）

旧 `义理/B_六征体系.md` 是项目主用语义层。三对征为：

| 征对 | 两极 | 中态读法 |
|---|---|---|
| 显隐 | 显 / 隐 | 玄 |
| 限许 | 限 / 许 | 可禁可通之前 |
| 实虚 | 实 / 虚 | 几、妙 |

三对征全取二态时形成 `2^3 = 8` 个八卦位。它与 `Bool^3` 形式同构，但**三轴语义不同**，不应把三爻混作同一类阴阳。

**v3 定位**：六征体系坐 **M-axis (内容层)**；R₃ 坐 **R-axis (结构层 / 群轴)**。两者共享 (Z/2)³ = 8 cardinality 但服务不同——R-axis 给 algebraic 群作用，M-axis 给 semantic content。 这是**轴的并存**，不是替代。

---

## 4. 实虚史真（高层 modal frame）

旧 `义理/C_实虚史真.md` 与 `六表_实虚史真/` 提供三轴/四轴审校读法：实虚、史维、真假。它适合判断一个命题在事实、历程、认识三方面的位置。

**v3 定位**：modal frame 坐高层（R₆ 之上 / R₇/R₈ Shi 流），与 R-hierarchy 形成 layer-axis 网格。详见 [`../10_formal_形式/yi-as-meta-framework.md`](../10_formal_形式/yi-as-meta-framework.md)。新版 docs-next 中，六表作为参考资料，不在义理正文重复展开。

---

## 5. 算子代数（O-hierarchy）

每层 (Z/2)ⁿ 内有两类算子，外层有 V₄ Klein 外对称：

### 5.1 Within-layer XOR 子群

每层 Rₙ 上 (Z/2)ⁿ XOR 子群是 abelian self-action：
- abelian: `m₁ ⊕ m₂ = m₂ ⊕ m₁`
- self-inverse: `c ⊕ c = 0`
- 复合 = XOR
- n 个 atomic generators 完全生成 2ⁿ 个 XOR 算子

R₈ 的 8 个 atomic generators (原子 XOR mask)：

| 生成元 | mask | 翻位 | 说明 |
|---|---|---|---|
| dongInner | `xooooooo` | y₁ | 内卦 1 爻 |
| huaInner | `oxoooooo` | y₂ | 内卦 2 爻 |
| bianInner | `ooxooooo` | y₃ | 内卦 3 爻 |
| dongOuter | `oooxoooo` | y₄ | 外卦 1 爻 |
| huaOuter | `ooooxooo` | y₅ | 外卦 2 爻 |
| bianOuter | `oooooxoo` | y₆ | 外卦 3 爻 |
| **印 (yìn)** | `ooooooxo` | y₇ (因) | toggle 因 axis |
| **投 (tóu)** | `ooooooox` | y₈ (果) | toggle 果 axis |

[`Foundation/Hierarchy/Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean)

### 5.2 V₄ 外对称

| 算子 | 类型 | 物理 anchoring |
|---|---|---|
| **cuo** (错) | XOR mask 全反 | P (parity) |
| **zong** (综) | permutation 反序 (非 XOR) | T (time-reversal) |
| **错综** | cuo ∘ zong | PT |
| **hu** (互) | permutation 取中四爻 (非 XOR) | Y (Y-combinator) |
| id | mask `oooooooo` | identity |

V₄ = {id, cuo, zong, 错综} 是 abelian Klein 群但仅 cuo ∈ XOR 子群。[`Foundation/Hierarchy/Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean)

### 5.3 Cayley 自对偶 (R₈ regular representation)

$$\iota: R_8 \to \mathrm{Aut}(R_8), \quad c \mapsto (\cdot \oplus c)$$

ε(f) := f(道) 是逆向 origin-evaluation。$\varepsilon \circ \iota = \mathrm{id}$，$\iota \circ \varepsilon = \mathrm{id}$，故 **R₈ ≅ XOR(R₈) 同构**。

这是「自描述」的精确数学条件 — abelian self-action with chosen origin。**道 = `oooooooo` = identity = origin = no-op = 永真 cell** — 一个 8-bit 字符串承担五重身份。

---

## 6. Shi V₄ — R₇ ⊗ R₈ 双层 emergent

**Shi {道, 已, 今, 未} 不是 R₇ 或 R₈ 单层 atom**，而是 R₇ (因 axis) 与 R₈ (果 axis) 双层之 V₄ Klein emergence：

| Shi | (因, 果) | V₄ 元素 | 物理 |
|---|---|---|---|
| **道** | (0, 0) | identity | 跨时空永真 |
| **已** | (1, 0) | $\sigma_P$ | 过去封闭 |
| **未** | (0, 1) | $\sigma_T$ | 未来开放 |
| **今** | (1, 1) | $\sigma_{PT}$ | 现在 |

**关键修正**：旧 Cell192 把时态编为 Z/3 cyclic {已, 今, 未} — 丧失「道」V₄ 单位元，丧失「描述者本身之恒在 anchor」。v3 Cell256 让道 first-class 进入本体，是「自描述」之形式落地。

---

## 7. 完整算子系统：生 / 互通 / 归一

旧 `义理/G_完整算子系统_八卦互通与归一.md` 把横向互通与纵向生成合在一处。在 v3 框架下读作三件事：

- **生成**：从 R₀ 到 R₈，每层 +1 bit 的 Lift 函子（[`Foundation/Hierarchy/LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean)）。
- **互通**：每层 (Z/2)ⁿ XOR 子群 simply-transitive 自作用，加 V₄ 外对称 — 任何 cell 之间皆可达。
- **归一**：Project 函子右逆 Lift（合 ∘ 分 = id）；道 = origin = identity 是归宿 anchor。

相关旧入口：`义理/A_经典易传.md`、`义理/B_六征体系.md`、`义理/C_实虚史真.md`、`义理/D_算子代数.md`、`义理/G_完整算子系统_八卦互通与归一.md`、`义理/算子别名总表.md`、`义理/道桥接_ProcessAligned_Dao_ShengshengBuxi.md`。

---

## 8. 形式锚总表

| 概念 | 形式文件 |
|---|---|
| R₀..R₈ R-index 命名 | [`Foundation/Hierarchy/RHierarchy.lean`](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean) (umbrella) |
| R₄ Mian = Ben × Zheng | [`Foundation/Bagua/BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) |
| R₇ Cell128 + 因 / 印 | [`Foundation/Bagua/Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) |
| R₈ Cell256 + 果 / 投 + Shi V₄ | [`Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) |
| R₈ closure bundle | [`Foundation/Bagua/Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) (`R8_complete`) |
| 8 R-layer Lift / Project pairs | [`Foundation/Hierarchy/LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) |
| Atomic XOR-subgroup 算子 | [`Foundation/Hierarchy/Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) |
| V₄ outer 算子 (zong / hu / cuoZong) | [`Foundation/Hierarchy/Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) |
| OX 8-char literal macro | [`Foundation/Notation/OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) |
| Self-description witness | [`Truth/SelfDescription.lean`](../../formal/SSBX/Truth/SelfDescription.lean) (`Cell256OperatorComplete`) |

---

## 9. 自动生成索引

自动生成索引若存在，可对照 `../_generated/` 中的文件索引与术语索引；以 `../_generated/lean-index.md`、`../_generated/claim-index.md`、`../_generated/trust-boundary.md` 为权威 build/claim/trust 事实。
