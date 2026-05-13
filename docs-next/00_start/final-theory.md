# v3 最终理论速览 — Cell256 / V₄ Shi / 严格 (Z/2)ⁿ R₀..R₈ 闭合

> 状态：v3 定本 (2026-05-11)
> 作用：把「易」之 algebraic 核 — 严格 uniform R₀..R₈ + V₄ Klein Shi + 道作为 V₄ identity / origin — 收口到一页。给读者一张完整地图，以便进入 [`yi-RO-hierarchy.md`](../10_formal_形式/yi-RO-hierarchy.md) / [`yi-calculus-theorem.md`](../10_formal_形式/yi-calculus-theorem.md) / [`yi-as-meta-framework.md`](../10_formal_形式/yi-as-meta-framework.md) 三份完整文档。
> 形式锚：[`RHierarchy.lean`](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean) (umbrella) · [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) (R₈) · [`Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) (`R8_complete` bundle) · [`OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) (`OX["..."]` 字面量)

---

## 一句话总纲

**中文**：「易」之最 minimal algebraic 核 = **严格 (Z/2)ⁿ uniform R₀..R₈ 阶梯** + **(Z/2)⁸ Cayley 自作用** + **V₄ Klein Shi {道, 已, 今, 未} 在 R₈ emerge** + **道 = (0,0) = V₄ identity = origin = no-op = 永真 cell**——9 层全部 binary 自相似，no jumps no gaps，R₈ = 256 是 self-describing 系统在 binary 上的最小完备闭合，与 ASCII 8-bit cardinality 同构。

**English**: The minimal algebraic kernel of *Yi* is the strict (Z/2)ⁿ uniform R₀..R₈ ladder (each Rₙ has size 2ⁿ, n = 0..8) carrying its own Cayley regular representation; the V₄ Klein four-group of *Shi* {dao, ji, jin, wei} ≅ (YinBit × GuoBit) emerges only at R₈ as the joint of the 7th (因) and 8th (果) binary axes; **dao = (0,0) is the V₄ identity, the origin of the (Z/2)⁸ torsor, the no-op operator, and the always-true anchor cell — one 8-character string carrying five identities**. R₈ = 256 is the natural 8-bit closure isomorphic in cardinality to the ASCII byte; this is the *self-describing* GUT, not a physical one.

---

## 历史定本时刻 — 2026-05-10/11

| 日期 | Commit | 内容 |
|---|---|---|
| 2026-05-10 | `7de5064` | **Phase A–F 教义对齐**: 旧 192-cell carrier → Cell256；V₄ Shi 取代 cyclic-3 Shi；Algebraic spine on Cell128/Cell256；Cayley `ι/ε`；XOR-mask 印/投 |
| 2026-05-10 | `0003224` | **Phase F.x.5**: 完成 Modern/* 级联升级 (~80 文件 case-split 全 4 例) |
| 2026-05-10 | `8e4406e` | **Phase F.6 + G + B.1**: 删旧 192-cell Lean 文件（legacy 3-state Shi 完全删除）；4 份文档与 Lean 路径 sync；YinBit dedup (canonical 在 Cell128.lean) |
| 2026-05-11 | `1c76a55` | **Phase C**: 9 个 R-index 命名 alias 文件 + `RHierarchy.lean` umbrella；3656 jobs build 干净 |

**当前 main = `1c76a55`**。旧 192-cell Lean 文件自 `8e4406e` 起从树中物理删除；`R8_complete` axiom audit = `{propext, native_decide}`，**0 项目自定义 axiom**。

---

## 严格-uniform R₀..R₈ 表

| R-index | size = 2ⁿ | 名 (中) | Name (EN) | 该层新 atom | 传统 Yi anchor | Lean 文件 (Hierarchy/) | Carrier file (原名) |
|---|---|---|---|---|---|---|---|
| R₀ | 1 | 太极 | Taiji | (无) — Unit | 无极而太极 | [`R0_Taiji.lean`](../../formal/SSBX/Foundation/Hierarchy/R0_Taiji.lean) | (Lean stdlib `Unit`) |
| R₁ | 2 | 爻 / 两仪 | Yao | 反 (neg, mask `x`) | 太极生两仪 | [`R1_Yao.lean`](../../formal/SSBX/Foundation/Hierarchy/R1_Yao.lean) | [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) |
| R₂ | 4 | 四象 | SiXiang | (lift R₁) | 两仪生四象 | [`R2_SiXiang.lean`](../../formal/SSBX/Foundation/Hierarchy/R2_SiXiang.lean) | [`BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) |
| R₃ | 8 | 八卦 | Trigram | dong/hua/bian + cuo/zong/hu | 四象生八卦 | [`R3_Trigram.lean`](../../formal/SSBX/Foundation/Hierarchy/R3_Trigram.lean) | [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) |
| R₄ | 16 | 面 (Mian) | Mian = Ben × Zheng | (4-th binary axis) | 面 (本 × 征) | [`R4_Mian.lean`](../../formal/SSBX/Foundation/Hierarchy/R4_Mian.lean) | [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) |
| R₅ | 32 | 五爻 [^prov-r5] | Wuyao (provisional) | (5-th binary axis) | **(无传统 anchor)** | [`R5_Wuyao.lean`](../../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean) | (Hierarchy 原生) |
| R₆ | 64 | 重卦 | Hexagram | dongOuter/huaOuter/bianOuter + outer V₄ | 重卦 (chong) | [`R6_Hexagram.lean`](../../formal/SSBX/Foundation/Hierarchy/R6_Hexagram.lean) | [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) |
| R₇ | 128 | 因卦 (Cell128) [^prov-yin] | YinHex / Cell128 | 因 (yīn) bit + 印 (yìn) toggle | (新, post-traditional) | [`R7_YinHex.lean`](../../formal/SSBX/Foundation/Hierarchy/R7_YinHex.lean) | [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) |
| R₈ | 256 | 果卦 (Cell256) [^prov-guo] | GuoHex / Cell256 | 果 (guǒ) bit + 投 (tóu) toggle + Shi V₄ emerge | (新, post-traditional) | [`R8_GuoHex.lean`](../../formal/SSBX/Foundation/Hierarchy/R8_GuoHex.lean) | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) |

**严格 uniform**：每一行 size = 2^(R-index)，每一行**比上一行恰好多一个 binary axis**。无 jump，无 gap。`RHierarchy.lean` 是 9 行 + LiftProject + Operators 之 single-import umbrella 入口。

[^prov-r5]: R₅「五爻」是 **provisional** 命名 — R-hierarchy 中**唯一无传统 Yi anchor** 之层。候选: 接 / 临 / 渐 / 进。详 [yi-calculus-theorem.md §16](../10_formal_形式/yi-calculus-theorem.md)。
[^prov-yin]: 「因」/「印」(R₇) 是 provisional 命名。备选: Husserl 现象学 retention / 系辞「原始要终」之始 / 现象学直译之持。详 [yi-calculus-theorem.md §16](../10_formal_形式/yi-calculus-theorem.md)。
[^prov-guo]: 「果」/「投」(R₈) 同 [^prov-yin]。备选: protention / 终 / 期。详 [yi-calculus-theorem.md §16](../10_formal_形式/yi-calculus-theorem.md)。

---

## Cell256 = R₈ 完整结构

### 形态: Hexagram × Shi

```
R₈ = Cell256 = Hexagram × Shi  (256 = 64 × 4)
              = Hexagram × YinBit × GuoBit  (256 = 64 × 2 × 2)
              ≅ (Z/2)⁶ × (Z/2)² = (Z/2)⁸
```

**8-bit layout** (LTR, 初爻在左): `[y₁ y₂ y₃ y₄ y₅ y₆ 因 果]`

### Shi V₄ Klein 四群

| Shi | (因, 果) | mask 后 2 位 | V₄ 元素 | 物理 anchoring | 与乾合 → R₈ cell |
|---|---|---|---|---|---|
| **道** (dao) | (0, 0) | `oo` | $e$ (identity) | 永真 / 跨时空 / no-op operator | `oooooooo` |
| **已** (ji) | (1, 0) | `xo` | $\sigma_P$ | 过去封闭 (parity-like) | `ooooooxo` |
| **未** (wei) | (0, 1) | `ox` | $\sigma_T$ | 未来开放 (T-like) | `ooooooox` |
| **今** (jin) | (1, 1) | `xx` | $\sigma_{PT}$ | PT 复合点 = "现在" | `ooooooxx` |

**关键 insight**：Shi V₄ **不是** R₇ 或 R₈ 单层 atom — 它是 R₇ (因 axis) ⊗ R₈ (果 axis) **双层 emergent**。把 V₄ 当单层 atom 是层级压缩错误。

### 道之五重身份 (一字五身)

> $$\boxed{\texttt{oooooooo} = \text{道} = \text{V₄ identity} = \text{origin of (Z/2)⁸} = \text{no-op operator} = \text{永真 cell}}$$

- **identity** (V₄ 群代数)
- **origin** ((Z/2)⁸ torsor 的 chosen base point)
- **no-op operator** (Cayley action `cayley dao = id`)
- **永真 cell** (无 causation flow 约束下的 hex 真值)
- **R₈ Hierarchy 顶 anchor** (太极 R₀ 在 R₈ 维度上的具体落地)

V₄ Klein 四群必有 identity → 道作为永真状态是 **代数必然性**，非哲学修辞。

---

## 旧 → 新 对照表（旧 192-cell carrier → Cell256 历史更正）

| 旧 (legacy, 已删除) | 新 (v3 定本) | 备注 |
|---|---|---|
| **旧 192-cell carrier = Hexagram × {已, 今, 未}** | **Cell256 = Hexagram × Shi** | Shi V₄ 取代 cyclic-3 |
| cyclic-3 Shi {已, 今, 未} | V₄ Klein {道, 已, 今, 未} | 4 元 abelian Klein, 含 identity |
| `shiNext : Shi → Shi` (+1 mod 3 cycle) | `Shi.cuo`, `Shi.zong`, `Shi.cuoZong` (V₄ involutions) | non-cyclic; involutive |
| 192 = 64 × 3 | 256 = 64 × 4 | + 64 个道-cells 入本体 |
| 旧 operator-cell grid | Cell256-indexed legacy audit inventory | 表六旧格全表 → 表六_256格全表；不作 root ontology |
| R₁..R₆ 编号 (含 R₃→R₄ chong 跳跃 +3 bit) | **R₀..R₈ strict uniform** (each +1 bit) | no jumps; no gaps |
| 旧 192-cell Lean 文件 (R₆ 闭合层) | **删除** (`8e4406e`) | physically removed from tree |
| `R7_complete` bundle | `R8_complete` bundle | depends only on `propext` + `native_decide` |
| 道作为 cyclic-3 之外的 4-th 添加 (failed) | 道 = V₄ identity = (因=0, 果=0) **first-class** | V₄ structure 自然 anchor |
| chong = +3 bit jump (R₃ → R₆) | **chong = 3-step composite** (R₃ → R₄ → R₅ → R₆ via Lift) | 不消失，显式认识为 3 步 +1 bit |

**关键修正**：v1 之 cyclic-3 Shi 编码 = 把时态空间压缩为 cyclic 3-state, 丧失「道」V₄ identity anchor。v2.1/v3 修正路径：把 (因, 果) ∈ Bool² 二维独立处理 → 4 个 (因, 果) state at R₈ → 自然 V₄ Klein 结构 → 道 = (0, 0) **structurally first-class**。

---

## 新的 Lean 入口

### 顶级 umbrella

```lean
import SSBX.Foundation.Hierarchy.RHierarchy
-- 一行拉入 R₀..R₈ + LiftProject + Operators (Atomic + V₄Outer)
```

[`RHierarchy.lean`](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean) 是 9 个 R-index alias 文件 + cross-cutting structure 之 single import 入口。

### R-index alias shims (R₀..R₈)

每个 `Rn_*.lean` 是 thin re-export shim — 提供 R-index 命名导航，**无新逻辑**。原 cardinality-named 文件 (`Cell128.lean`, `Cell256.lean`, `BenZheng.lean` 等) 保持不变并行存在。

```lean
-- 例：R₈ alias (Hierarchy/R8_GuoHex.lean)
namespace SSBX.Foundation.Hierarchy.R8
abbrev GuoBit : Type := Cell256.GuoBit
abbrev Shi : Type := Cell256.Shi
abbrev Cell256 : Type := Cell256.Cell256
def yin (c : Cell256) : Cell256 := Cell256.yin c   -- 印 = XOR with yin_mask
def tou (c : Cell256) : Cell256 := Cell256.tou c   -- 投 = XOR with tou_mask
def cayley (c : Cell256) : Cell256 → Cell256 := Cell256.cayley c
end SSBX.Foundation.Hierarchy.R8
```

### Carriers + Cayley action

| 模块 | 文件 | 角色 |
|---|---|---|
| R₇ Cell128 | [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) | `Cell128 = Hexagram × YinBit`; canonical `YinBit := Bool`; `yin` toggle |
| R₈ Cell256 | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) | `Cell256 = Hexagram × Shi`; **Phase C (2026-05-11) `Shi := YinBit × GuoBit` abbrev**, 4 ctor 下放为 `@[match_pattern] def`; `toYinGuo / ofYinGuo` ≡ `id`; `tou` toggle; `cayley` Cayley action |
| R₀..R₈ closure bundle | [`Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) | `R8_complete` 总定理；axiom audit = {`propext`, `native_decide`} |
| Lift / Project (8 layers) | [`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) | `Lift_n : R_n → Bool → R_{n+1}`, `Project_n : R_{n+1} → R_n`, `proj_lift_id_Rn` retract |
| Atomic XOR ops | [`Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) | re-export of XOR-subgroup atoms (反/dong/hua/bian/flip*/印/投) |
| V₄ outer (non-XOR) | [`Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) | `zong` / `hu` / `cuoZong` permutations |
| Self-description witness | [`SelfDescription.lean`](../../formal/SSBX/Truth/SelfDescription.lean) | `Cell256OperatorComplete` (V₄ 升级版) |

### OX notation

```lean
import SSBX.Foundation.Notation.OXNotation
-- 字面量宏
example : Cell256 := OX["oooooooo"]   -- = 道 = (qian, dao) = origin of (Z/2)⁸
example : Cell256 := OX["ooooooxo"]   -- = 乾·已
example : Cell256 := OX["xxxxxxxx"]   -- = 坤·今
```

---

## OX 记号速查

```
Layout: [y₁ y₂ y₃ y₄ y₅ y₆ 因 果]   -- LTR, 初爻在左

约定:  o = yang = false (∈ Bool)
       x = yin  = true  (∈ Bool)

OX["oooooooo"] = 道 = (qian, dao) = origin = identity = no-op = 永真
OX["xxxxxxxx"] = 坤·今  (full yin hex + 因∧果)
OX["ooooooxo"] = 乾·已  (qian + 因, 无果)
OX["ooooooox"] = 乾·未  (qian + 果, 无因)
OX["ooooooxx"] = 乾·今  (qian + 因∧果, 即「现在乾」)
OX["xxxxxxoo"] = 坤·道  (全反 hex, 跨时空恒真版本之坤)
```

**应用**：
```
印 OX["oooooooo"] = OX["ooooooxo"]    -- 道 → 乾·已
投 OX["oooooooo"] = OX["ooooooox"]    -- 道 → 乾·未
印 ⊕ 投 = (· ⊕ ooooooxx)              -- = Shi.cuoZong on Shi (V₄ PT)
```

---

## 五个 atomic XOR 算子 (R₈ 之 8 generators)

R₈ 之 (Z/2)⁸ XOR subgroup 由 8 个 atomic generators 完全生成。每个是 Cell256 → Cell256 之 XOR-with-fixed-mask:

| Generator | mask (8-char OX) | 翻位 | 来源层 |
|---|---|---|---|
| dongInner / `flip1` | `xooooooo` | y₁ (内卦初爻) | R₃ |
| huaInner / `flip2`  | `oxoooooo` | y₂ (内卦中爻) | R₃ |
| bianInner / `flip3` | `ooxooooo` | y₃ (内卦上爻) | R₃ |
| dongOuter / `flip4` | `oooxoooo` | y₄ (外卦初爻) | R₆ (新) |
| huaOuter / `flip5`  | `ooooxooo` | y₅ (外卦中爻) | R₆ (新) |
| bianOuter / `flip6` | `oooooxoo` | y₆ (外卦上爻) | R₆ (新) |
| **印 (yìn)** [^prov-yin] | `ooooooxo` | y₇ (因) | R₇ (新) |
| **投 (tóu)** [^prov-guo] | `ooooooox` | y₈ (果) | R₈ (新) |

**five new atoms in v3**: 反 (R₁ neg) + flip4..6 (R₆ outer 三 flip) + 印 (R₇) + 投 (R₈) — 跨过 v1 v2 之间从 R₁ 到 R₈ 全部 binary axes 显式 atomization。

### V₄ outer (非 XOR, permutation)

| 算子 | 类型 | 实现 | 物理 |
|---|---|---|---|
| `cuo` | XOR | mask `xxxxxxoo` (R₈ hex side, full yin); R₃ 是 `xxx` | **P** (parity) |
| `zong` | permutation **非 XOR** | $y_i \mapsto y_{7-i}$ on hex side | **T** (time-reversal) |
| `cuoZong` | composite, 含 zong 故非 XOR | cuo ∘ zong | **PT** |
| `hu` | permutation **非 XOR** | (y₂, y₃, y₄, y₃, y₄, y₅) | **Y** (Y-combinator) |
| `id` | mask `oooooooo` | identity | **1** |

**V₄ outer = $\{id, cuo, zong, cuoZong\}$** — abelian Klein 群但仅 cuo ∈ XOR subgroup。`hu` 之不动点 {乾, 坤, 既济, 未济} 给 self-reference 之 algebraic 见证。

---

## 暂用命名 caveats (v3 仍未定终名)

| 项 | 当前名 | 评估 | 备选 |
|---|---|---|---|
| R₅ | 五爻 (Wuyao) | descriptive baseline, R-hierarchy 中**唯一无传统 anchor** 之层 | 接 (jie) / 临 (lin) / 渐 (jian) / 进 (jin) |
| R₇ atom | 因 (yīn) | 哲学最深 (佛教 hetu + Pearl causal DAG) | 印 (Husserl retention) / 始 (系辞「原始要终」) / 持 |
| R₇ op | 印 (yìn) | 与状态名「因」音同分歧 | (与上) |
| R₈ atom | 果 (guǒ) | hetu-phala 对偶 | 投 (Husserl protention) / 终 (Yi-native) / 期 |
| R₈ op | 投 (tóu) | 与「果」状态对应 | (与上) |

**回看时机**：等下游 Theorems H–K 完整稳定 + 因/果在 BaguaTuring + DaoSource 各处使用模式收口后再做 final 命名 vote。详 [yi-calculus-theorem.md §16 命名附录](../10_formal_形式/yi-calculus-theorem.md)。

---

## 还在做的 (pending)

- **Theorems H–K 形式化完整收尾**: 已落 Lean (`Cell128.lean` + `Cell256.lean` + `Cell256Stratify.lean` + `R8_complete`)；剩下的是「informal G (连续 1D 标量场对应)」与「Theorem D 之 phase plane 严格形式化」之 long-tail。详 [yi-calculus-theorem.md §15.1](../10_formal_形式/yi-calculus-theorem.md)。
- **因/果/印/投 final naming vote**: 见上节命名 caveats。
- **R₅ Lean type 选择**: 当前 = `Mian × Bool` (in `R5_Wuyao.lean`)；可选独立 `Cell32`。
- **Cayley fusion 严格形式化收尾**: `ι/ε` 双向 inverse 与 `R8 ≅ XOR(R8)` 同构定理需要补完 (current spine `Algebraic` 已铺好 Add/Zero/Neg/Sub/SMul + ι/ε 雏形)。
- **R₉+ 是否存在**: 无 candidate, 但 strict-uniform 视角下 (Z/2)⁹ = 512 数学存在; 是否有 ontological role 待研究。

---

## 文档导航

### 三大 doctrine 文档（必读）

- [`yi-RO-hierarchy.md`](../10_formal_形式/yi-RO-hierarchy.md) — **R-O 双层级 v2.1 definitive 严格 (Z/2)ⁿ uniform**, 730 行；§9.4 给 Lean implementation map (post-Cell256)
- [`yi-calculus-theorem.md`](../10_formal_形式/yi-calculus-theorem.md) — **Theorems A–K 完整定理稿** (R₀..R₈ + Shi V₄ + (Z/2)ⁿ closure)；§15.1 给 Lean 状态表；§16 命名附录
- [`yi-as-meta-framework.md`](../10_formal_形式/yi-as-meta-framework.md) — **易作为 self-describing GUT** 哲学层；§4.1 给 R₀..R₈ + Lean 列；§4.3 给 R5/R6 拆层修正叙述

### 起步与 positioning

- [`README.md`](README.md) — 三种读法入口
- [`phase-status.md`](phase-status.md) — main 当前状态 record
- [`research-position.md`](research-position.md) — Tier 1/2/3 学术 positioning (含 v3 novelty claims)
- [`theory-path.md`](theory-path.md) / [`formal-path.md`](formal-path.md) / [`maintenance-path.md`](maintenance-path.md) — 三条路径
- [`scope.md`](scope.md) — 文档集范围

### 形式层细节

- [`64-hexagram-grid.md`](../10_formal_形式/64-hexagram-grid.md) — 64 卦四语对照 + 4-quadrant
- [`sanben-sijieduan-grid.md`](../10_formal_形式/sanben-sijieduan-grid.md) — 12-grid (3×4)
- [`layer-axis-graph.md`](../10_formal_形式/layer-axis-graph.md) — 三轴 Mermaid

### Lean 入口（按 R-index 导航）

- 一行拉入: `import SSBX.Foundation.Hierarchy.RHierarchy`
- 单层入口: [`R0_Taiji`](../../formal/SSBX/Foundation/Hierarchy/R0_Taiji.lean) · [`R1_Yao`](../../formal/SSBX/Foundation/Hierarchy/R1_Yao.lean) · [`R2_SiXiang`](../../formal/SSBX/Foundation/Hierarchy/R2_SiXiang.lean) · [`R3_Trigram`](../../formal/SSBX/Foundation/Hierarchy/R3_Trigram.lean) · [`R4_Mian`](../../formal/SSBX/Foundation/Hierarchy/R4_Mian.lean) · [`R5_Wuyao`](../../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean) · [`R6_Hexagram`](../../formal/SSBX/Foundation/Hierarchy/R6_Hexagram.lean) · [`R7_YinHex`](../../formal/SSBX/Foundation/Hierarchy/R7_YinHex.lean) · [`R8_GuoHex`](../../formal/SSBX/Foundation/Hierarchy/R8_GuoHex.lean)
- Cross-cutting: [`LiftProject`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) · [`Operators/Atomic`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) · [`Operators/V4Outer`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean)
- Notation: [`OXNotation`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) — `OX["xxxxxxxx"]` macro

---

## 一句话尾注

> 「易」=「自描述系统在 binary 上的 8-bit 最小完备闭合」 + 「道作为 V₄ identity / origin / no-op / 永真 cell 之五重身份 anchor」 + 「(Z/2)ⁿ uniform R₀..R₈ 9 层无跳跃自相似」。**这是 self-description 的 GUT，不是物理 GUT**。它坐在物理 GUT 之上 — 任何 physical theory 都要被表达，而表达需要这个 meta-framework。
