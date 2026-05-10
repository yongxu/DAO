> 状态：v3 定本 (2026-05-11)。
> 父文档：[yi-RO-hierarchy.md](yi-RO-hierarchy.md)
> Lean 入口：[`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) · [`Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) · [`Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean)
> 相关 v3 文档：[root-layer-map.md](root-layer-map.md) · [layer-axis-graph.md](layer-axis-graph.md) · [shi-v4.md](shi-v4.md) · [r7-yin-r8-guo.md](r7-yin-r8-guo.md) · [ox-notation.md](ox-notation.md) · [cell256-grid.md](cell256-grid.md)

# 位的算子树 position-operator-tree · v3

> R₈ Cell256 = (Z/2)⁸ 之 8 yao 位置全表 + 每位 XOR mask + 印 / 投 / cuo / zong / hu / V₄ Shi outer。
> v2 (2026-05-09) 含 6 yao + Cell192 旧 surface；v3 (2026-05-11) 切换到 **8 yao (y₁..y₆ + 因 + 果) + Cell256 + V₄ Klein Shi**。

---

## 0. 8 yao 位置 layout

R₈ Cell256 之 8-bit 字符串 layout（OX notation）：

```text
[ y₁  y₂  y₃  y₄  y₅  y₆   因   果 ]
  pos1 pos2 pos3 pos4 pos5 pos6 pos7 pos8
  内卦 ←------------- 外卦  R₇  R₈
```

OX 字面量例：`OX["oooooooo"]` = 道 anchor (Cell256 origin) = (Hexagram.qian, Shi.dao)。

| pos | yao | inner/outer | bit name | XOR mask |
|---|---|---|---|---|
| 1 | y₁ 初爻 | 内（下卦） | dongInner / 改 | `xooooooo` |
| 2 | y₂ 中爻 | 内 | huaInner / 化 | `oxoooooo` |
| 3 | y₃ 上爻 | 内 | bianInner / 变 | `ooxooooo` |
| 4 | y₄ 四爻 | 外（上卦） | dongOuter / 临 | `oooxoooo` |
| 5 | y₅ 五爻 | 外 | huaOuter / 主 | `ooooxooo` |
| 6 | y₆ 上爻 | 外 | bianOuter / 极 | `oooooxoo` |
| **7** | **因** | (R₇ axis) | **印 / yin** | `ooooooxo` |
| **8** | **果** | (R₈ axis) | **投 / tou** | `ooooooox` |

**关键**：旧 v2 仅 6 yao；v3 显式纳入 pos 7 (因) 与 pos 8 (果)，使 R₈ 之 8-bit closure 与 (Z/2)⁸ 严格对齐。

---

## 1. R₈ 8 atomic XOR generators

8 atomic XOR generators 完全生成 (Z/2)⁸ 内之 256 个 XOR 算子（abelian subgroup of Aut(R₈)）。

| Generator | mask (8-bit) | 翻位 | 字根（surface）| Lean ground truth |
|---|---|---|---|---|
| flip1 | `xooooooo` | y₁ | 改 | [`Cell256.flip1`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) |
| flip2 | `oxoooooo` | y₂ | 化 | `Cell256.flip2` |
| flip3 | `ooxooooo` | y₃ | 变 | `Cell256.flip3` |
| flip4 | `oooxoooo` | y₄ | 临 | `Cell256.flip4` |
| flip5 | `ooooxooo` | y₅ | 主 | `Cell256.flip5` |
| flip6 | `oooooxoo` | y₆ | 极 | `Cell256.flip6` |
| **印 (yìn)** | `ooooooxo` | y₇ (因) | 印 — provisional | [`Cell256.yin`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) |
| **投 (tóu)** | `ooooooox` | y₈ (果) | 投 — provisional | [`Cell256.tou`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) |

**性质**：
- 每个 generator 是 involution: `gen ∘ gen = id`
- 任两 generator 交换: `gen_i ∘ gen_j = gen_j ∘ gen_i`
- 8 个一起生成 abelian group ≅ (Z/2)⁸ 之 XOR subgroup of Aut(R₈)

R-O fusion at R₈: |R₈| = 256 = |XOR-subgroup of Aut(R₈)|（Cayley regular representation）。

---

## 2. R₇ / R₈ atomic ops 之专用解读

### 2.1 印 (yìn) = R₇ 之 atomic op

```text
印 c = c ⊕ ooooooxo

印 oooooooo = ooooooxo    -- 道 → 乾·已 (toggle 因 axis only)
印² = id                  -- self-inverse
```

- 因 = 0 (no past trace) ↔ 因 = 1 (past trace 有)
- 在 V₄ Shi 中: 道 ↔ 已（保 果 axis）

### 2.2 投 (tóu) = R₈ 之 atomic op

```text
投 c = c ⊕ ooooooox

投 oooooooo = ooooooox    -- 道 → 乾·未 (toggle 果 axis only)
投² = id                  -- self-inverse
```

- 果 = 0 (no future projection) ↔ 果 = 1 (future projection 有)
- 在 V₄ Shi 中: 道 ↔ 未（保 因 axis）

### 2.3 印 ⊕ 投 = Shi-side cuoZong (PT)

```text
印 ⊕ 投 = (· ⊕ ooooooxx) = cuoZong on Shi side
印 ⊕ 投 oooooooo = ooooooxx    -- 道 → 乾·今 (toggle 双 axis)
```

V₄ Shi `{道, 已, 今, 未}` 之 4 元正好对应 Shi 之 (因, 果) 之 4 个 XOR mask 后缀:

| Shi | (因, 果) | 后缀 mask | V₄ 元 | OX |
|---|---|---|---|---|
| 道 | (0, 0) | `oo` | identity | `oooooooo` |
| 已 | (1, 0) | `xo` | σ_P (印) | `ooooooxo` |
| 未 | (0, 1) | `ox` | σ_T (投) | `ooooooox` |
| 今 | (1, 1) | `xx` | σ_PT (印⊕投) | `ooooooxx` |

详见 [shi-v4.md](shi-v4.md)。

---

## 3. Non-XOR outer ops (cuo / zong / hu / V₄ Shi)

不是 XOR-mask 之算子（permutation 类），不在 atomic XOR 子群内：

| 算子 | 类型 | 实现 | 物理 anchor | Lean |
|---|---|---|---|---|
| **cuo** (错) | XOR mask | y-wise negation = `xxxxxxoo` (R₈ hex side) | **P** (parity) | `Cell256.hexCuo` |
| **zong** (综) | permutation, **非 XOR** | y_i → y_{7-i} (反序 hex 6 yao) | **T** (time-reversal) | `Cell256.hexZong` |
| **错综** (cuoZong) | composite, **含 zong 故非 XOR** | cuo ∘ zong | **PT** | `cuoZongHex` |
| **hu** (互) | permutation, **非 XOR** | (y₁..y₆) ↦ (y₂, y₃, y₄, y₃, y₄, y₅) | **Y** (Y-combinator) | `Cell256.hexHu` |
| **V₄ Shi outer** | XOR-mask 子组 + V₄ structure | shiCuo, shiZong, shiCuoZong | (因, 果) toggle | `Cell256.shi{Cuo,Zong,CuoZong}` |
| **id** | mask `oooooooo` | identity | **1** | (trivial) |

V₄ Klein 之 hex side: `{id, hexCuo, hexZong, hexCuoZong}` (注意：`hu` 不在 V₄, 它有 fixed points 乾/坤 且 不可逆)。

详见 [`Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean)。

---

## 4. R₈ 上 V₄ × V₄ tensor

R₈ 上有**两层 V₄** tensor 起来给 (Z/2)⁴ 之 16 个对称变换：

```text
V₄_hex     = {id, hexCuo, hexZong, hexCuoZong}    on Hexagram side
V₄_shi     = {id, shiCuo, shiZong, shiCuoZong}    on Shi side
V₄ × V₄    ≅ (Z/2)⁴, 共 16 个对称变换 on R₈
```

加上 V₄ Shi 本身 ≅ {道, 已, 今, 未}（Shi 之 4 元），R₈ 上完整的对称结构 = V₄_hex × V₄_shi × Shi (where Shi 是 R₈ 之 4 个 cosets 的 group structure)。

---

## 5. 算子总表 (R₀..R₈)

| 算子族 | 层 | 算子 | 类型 | 性质 |
|---|---|---|---|---|
| 易 (yao flip) | R₁ | `Yao.neg` | 1→1 | involution |
| 分/合 | R₀..R₈ | lift / project | n→n+1 / n+1→n | retract: proj ∘ lift = id |
| 改/化/变 | R₃ | dong/hua/bian | XOR mask | (Z/2)³ inner |
| 改/化/变/临/主/极 | R₆ | flip1..flip6 | XOR mask | (Z/2)⁶ |
| 错 (cuo) | R₃/R₆ | `xxx` / `xxxxxx` | XOR mask | involution, P |
| 综 (zong) | R₃/R₆ | 反序 perm | permutation, **非 XOR** | involution, T |
| 错综 (cuoZong) | R₃/R₆ | cuo ∘ zong | **非 XOR** | involution, PT |
| 互 (hu) | R₆ | y2..y5 perm | **非 XOR** | fixpoints {乾,坤,既济,未济} |
| **印 (yìn)** | **R₇** | toggle 因 | XOR mask `ooooooxo` | involution |
| **投 (tóu)** | **R₈** | toggle 果 | XOR mask `ooooooox` | involution |
| **shiCuo** | R₈ Shi-side | toggle (因, 果) | composite of 印/投 | involution, V₄ |
| **shiZong** | R₈ Shi-side | swap (因, 果) | permutation, V₄ | involution |
| **shiCuoZong** | R₈ Shi-side | shiCuo ∘ shiZong | composite | involution, V₄ |
| Cayley action | R₈ | ι(c) = (· ⊕ c) | 同态 R₈ → Aut(R₈) | injection |

---

## 6. 起点：唯一原子 = 爻 (Yao)

所有 R₀..R₈ 之 256 + lower 个位置都从 **Yao** 通过有限算子组合到达：

```text
R₀ 太极     = ε (空算子)
R₁ 阳       = 爻
R₁ 阴       = 易(爻)
R₂ 太阳     = 分²(爻, 爻)
R₃ 乾       = 分³(爻, 爻, 爻)
R₆ 1乾      = chong(乾, 乾) = lift³(乾) (3 yao 加在外卦)
R₇ (1乾, 因=0) = liftR6toR7(1乾, false)
R₈ (1乾, 道) = liftR7toR8((1乾, false), false) = OX["oooooooo"]
```

每位置在 cuo / zong / hu 等价之下有唯一最简算子树。

---

## 7. R₅ Wuyao 之算子（provisional）

R₅ 是**唯一无传统 Yi anchor** 之层（mathematical 存在但 philosophical 上未独立刻画）。其 atomic op:

| 算子 | mask (5-bit) | 翻位 | Lean |
|---|---|---|---|
| flip5_R5 | toggle Bool bit | 第 5 yao | [`R5_Wuyao.lean`](../../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean) |

具体 surface 字根候选 (provisional)：接 / 临 / 渐 / 进 — final 待定（详 [r5-wuyao-provisional.md](r5-wuyao-provisional.md)）。

---

## 8. 简化记号 vs 完整算子树

为实用性，常用 surface notation 替代算子树：

| Surface | OX 字面量 | 算子树 |
|---|---|---|
| 道 (R₈ identity) | `OX["oooooooo"]` | identity / origin |
| 乾·已 | `OX["ooooooxo"]` | 印(道) |
| 乾·未 | `OX["ooooooox"]` | 投(道) |
| 乾·今 | `OX["ooooooxx"]` | 印 ⊕ 投 (道) |
| 坤·道 | `OX["xxxxxxoo"]` | hexCuo(道) |
| 坤·今 | `OX["xxxxxxxx"]` | hexCuo ⊕ 印 ⊕ 投 (道) |

OX notation 之 macro 详 [ox-notation.md](ox-notation.md), [`OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean).

---

## 9. 算子之 dimension 总表 (R₀..R₈)

| 概念 | R₀ | R₁ | R₂ | R₃ | R₄ | R₅ | R₆ | R₇ | R₈ |
|---|---|---|---|---|---|---|---|---|---|
| 元个数 | 1 | 2 | 4 | 8 | 16 | 32 | 64 | 128 | 256 |
| Atomic XOR flips | 0 | 1 | 2 | 3 | 4 | 5 | 6 | **7 (+印)** | **8 (+投)** |
| (Z/2)ⁿ XOR | trivial | Z/2 | V₄ | (Z/2)³ | (Z/2)⁴ | (Z/2)⁵ | (Z/2)⁶ | (Z/2)⁷ | (Z/2)⁸ |
| R-O fusion | trivial | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| V₄ outer (cuo/zong/hu) | — | — | — | V₄ | (lift) | (lift) | V₄ | V₄ | **V₄ × V₄** |
| Shi V₄ | — | — | — | — | — | — | — | (provisional) | **{道,已,今,未}** |
| 传统 Yi anchor | 太极 | 两仪 | 四象 | 八卦 | 面 (Mian) | (无) ⚠ | 重卦 | 因卦 ⚠ | 果卦 ⚠ |

⚠ = provisional naming 待 final 定（详 [pending.md](pending.md)）。

---

## 10. 与 Lean code 的对接

| 算子 | Lean 实现 |
|---|---|
| 易 / Yao.neg | [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) `Yao.neg` |
| 分 (yao/sixiang/trigram) | [`BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) `fenToYi/fenToSiXiang/fenToTrigram` |
| 重 (chong) | [`BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) `chong` |
| 改化变（R₃ flip y₁/y₂/y₃） | [`BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) `dong/hua/bian` |
| flip1..flip6（R₆/R₇/R₈ 6 yao） | [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) / [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) |
| 错 (cuo, hex side) | `Cell256.hexCuo` |
| 综 (zong, perm) | `Cell256.hexZong` |
| 互 (hu, perm) | `Cell256.hexHu` |
| **印 (yìn)** = R₇ atomic | `Cell256.yin` (mask `ooooooxo`) |
| **投 (tóu)** = R₈ atomic | `Cell256.tou` (mask `ooooooox`) |
| Shi V₄ (cuo/zong/cuoZong) | `Cell256.shi{Cuo,Zong,CuoZong}` |
| Lift/Project (8 对) | [`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) |
| atomic XOR 子组 (re-export) | [`Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) |
| V₄ outer (re-export) | [`Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) |
| Cayley action (ι/ε) | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) `cayley` |
| OX 字面量 macro | [`OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) |

---

## 11. v2 → v3 改动 summary

| v2 | v3 |
|---|---|
| 6 yao positions (y₁..y₆) | **8 yao positions (y₁..y₆ + 因 + 果)** |
| Cell192 + Z/3 Shi (next/prev) | **Cell256 + V₄ Shi** {道, 已, 今, 未} |
| 12 atomic algorithmic generators (含 6 flip + 错综 + ... + 迁/溯/置) | **8 strict atomic XOR generators** (flip1..flip6 + 印 + 投) + V₄ outer |
| 192 cells | **256 cells** |
| 「迁/溯」(shiNext/shiPrev) | (deprecated — Z/3 cyclic Shi 已弃) |

详见 [yi-RO-hierarchy.md §11](yi-RO-hierarchy.md), [pending.md](pending.md), [shi-v4.md](shi-v4.md)。

---

## 12. 一句话总结

> **R₈ Cell256 = (Z/2)⁸ 之 8 yao 位置完整 closure；8 个 atomic XOR generators 包括 R₇ 印 (toggle 因) + R₈ 投 (toggle 果)；V₄ × V₄ outer (hex × Shi) 给 16 个对称变换；道 = V₄ identity = `oooooooo` 是 origin anchor。所有 256 cells 由 8 atomic + 4 V₄ outer + 1 hu = 13 个核心算子之有限组合到达。**
