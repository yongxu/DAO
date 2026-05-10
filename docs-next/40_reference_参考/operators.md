> 状态：v3 (2026-05-11) — 算子参考。已加入 v3 first-class 算子 印 / 投，V₄ Shi 之 cuo / zong / cuoZong，Cell128 / Cell256 lifted hexZong / hexHu，并明确 Atomic（XOR 子群）vs V4Outer（Klein-four permutation 群）二分。

# 算子参考

本页是算子系统的人读入口。机器事实以 `../_generated/operator-index.md` 和 Lean 源为准；本页不维护总数、分组数量或完整表格。

## 主要来源

| 来源 | 用途 |
|---|---|
| `../_generated/operator-index.md` | 当前算子索引、分组和 code/id |
| `wenyan-operators.md` | 人工长表与文字说明 |
| [`formal/SSBX/Text/WenyanOperators.lean`](../../formal/SSBX/Text/WenyanOperators.lean) | 算子数据源 |
| [`formal/SSBX/Text/OperatorReadings.lean`](../../formal/SSBX/Text/OperatorReadings.lean) | 读法登记 |
| [`formal/SSBX/Text/OperatorSignatures.lean`](../../formal/SSBX/Text/OperatorSignatures.lean) | 签名和形态 |
| [`formal/SSBX/Text/OperatorCellMap.lean`](../../formal/SSBX/Text/OperatorCellMap.lean) | 单元映射（已迁 Cell256 anchor） |
| [`formal/SSBX/Text/OperatorAnchors.lean`](../../formal/SSBX/Text/OperatorAnchors.lean) | 文言算子到八卦系统的锚点（已迁 Cell256） |
| [`formal/SSBX/Foundation/Wen/Operators.lean`](../../formal/SSBX/Foundation/Wen/Operators.lean) | Wen 层算子接口 |
| [`formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) | XOR-mask atomic 算子（v3 入口） |
| [`formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) | V₄ Klein outer permutation 算子（v3 入口） |

## v3 算子分类（核心二分：Atomic vs V4Outer）

v3 把基础算子（在 Cell128 / Cell256 / Hexagram 上的）严格分为两组，按代数性质区分：

| 类别 | 代数性质 | 群结构 | 典型算子 | Lean 文件 |
|---|---|---|---|---|
| **Atomic** | XOR with fixed mask | (Z/2)ⁿ abelian subgroup；each involution；all pairs commute | 印 / 投（at Cell256），flip1..flip6 / 印 / hexCuo（at Cell128） | [`Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) |
| **V4Outer** | non-XOR permutation | `{id, cuo, zong, cuoZong}` ≅ V₄ Klein-four；含 sibling `hu`（**不在** V₄，有 `{乾, 坤}` 不动点） | hex_zong / hex_cuoZong / hex_hu / cell128_zong / hu / cell256_zong / hu | [`Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) |

> 注：`cuo` 本身是 XOR-mask（with all-yin / kun mask），代数上是 atomic；但其 V₄ **结构**作用与 `zong` / `cuoZong` 不可分割，故在 V4Outer.lean 中亦作 V₄ 生成元出现。

## v3 first-class 算子表（精选）

| 算子 | 类别 | 类型 | 定义 | 锚 |
|---|---|---|---|---|
| **印 (yìn)** at Cell256 | Atomic | `Cell256 → Cell256` | XOR with `yin_mask = (qian, ji) = OX["ooooooxo"]`（toggle YinBit / 因 axis） | `Cell256.lean § 8`, `Operators/Atomic.lean § 1` |
| **投 (tóu)** at Cell256 | Atomic | `Cell256 → Cell256` | XOR with `tou_mask = (qian, wei) = OX["ooooooox"]`（toggle GuoBit / 果 axis） | `Cell256.lean § 8`, `Operators/Atomic.lean § 1` |
| **印** at Cell128 | Atomic | `Cell128 → Cell128` | toggle YinBit；mask 形与直接形等价（`yinM_eq_yin`） | `Cell128.lean § 7`, `Operators/Atomic.lean § 2` |
| **flip1..flip6** at Cell128 | Atomic | `Cell128 → Cell128` | 单爻 toggle（dongInner / huaInner / bianInner / dongOuter / huaOuter / bianOuter）；保 YinBit | `Cell128.lean § 4`, `Operators/Atomic.lean § 2` |
| **hexCuo** at Cell128 | Atomic | `Cell128 → Cell128` | yao-wise negation（XOR with kun mask）；保 YinBit | `Cell128.lean § 4`, `Operators/Atomic.lean § 2` |
| **cuo (错)** at Hexagram | Atomic（XOR） | `Hexagram → Hexagram` | XOR with kun（all-yin）；物理 P (parity) | `Yi.lean`, `Operators/V4Outer.lean § 1` |
| **zong (综)** at Hexagram | V4Outer | `Hexagram → Hexagram` | yao 序反转 perm；非 XOR；involution；物理 T (time-reversal) | `Yi.lean`, `Operators/V4Outer.lean § 1` |
| **cuoZong (错综)** at Hexagram | V4Outer | `Hexagram → Hexagram` | `cuo ∘ zong`；involution；物理 PT | `Operators/V4Outer.lean § 1` |
| **hu (互)** at Hexagram | sibling outer（非 V₄） | `Hexagram → Hexagram` | 取中四爻 perm；非 XOR；非 involution；fixed pts = `{乾, 坤}`，2-cycle = `{既济, 未济}`；物理 Y / Y-combinator | `Yi.lean`, `Operators/V4Outer.lean § 1, § 6` |
| **hexZong** at Cell128 | V4Outer (lift) | `Cell128 → Cell128` | `(Hexagram.zong h, b)` — 保 YinBit | `Cell128.lean § 4`, `Operators/V4Outer.lean § 2` |
| **hexHu** at Cell128 | sibling outer (lift) | `Cell128 → Cell128` | `(Hexagram.hu h, b)` — 保 YinBit | 同上 |
| **hexZong** at Cell256 | V4Outer (lift) | `Cell256 → Cell256` | `(Hexagram.zong h, s)` — 保 Shi V₄ component | `Cell256.lean § 3`, `Operators/V4Outer.lean § 3` |
| **hexHu** at Cell256 | sibling outer (lift) | `Cell256 → Cell256` | `(Hexagram.hu h, s)` — 保 Shi | 同上 |
| **shiCuo** at Cell256 | V4Outer (Shi-side) | `Cell256 → Cell256` | toggle YinBit only on Shi part；与 Cell256 atomic `cell256_yin` 等价（XOR-mask 形） | `Cell256.lean § 3` |
| **shiZong** at Cell256 | V4Outer (Shi-side) | `Cell256 → Cell256` | toggle GuoBit only on Shi part；与 `cell256_tou` 等价 | 同上 |
| **shiCuoZong** at Cell256 | V4Outer (Shi-side) | `Cell256 → Cell256` | toggle 两 bits；V₄ central element 之 toggle；= `(· ⊕ (qian, jin))` | 同上 |

## 印 / 投 / Shi V₄ 之关系（v3 总图）

```
Cell256 = Hexagram × Shi,   Shi = V₄ Klein = {道, 已, 今, 未}
Shi ≅ (因, 果) ∈ Bool²:       道=(0,0)  已=(1,0)  未=(0,1)  今=(1,1)

印 (Atomic)   = XOR with (qian, 已) = toggle 因   ↔ Shi.cuo (V₄ generator 1)
投 (Atomic)   = XOR with (qian, 未) = toggle 果   ↔ Shi.zong (V₄ generator 2)
印 ⊘ 投       = XOR with (qian, 今) = V₄ central  ↔ Shi.cuoZong (V₄ central element)
道            = Shi.dao = V₄ identity = R₈ origin = no-op operator = 永真 cell
```

`cuo` / `zong` 在 R₃/R₆ Hexagram 上是 V₄ outer permutation；在 Shi V₄ 上 `Shi.cuo` / `Shi.zong` 是 V₄ generator；二者**不要混淆**：同名不同 layer，统一在 V₄ 之代数 family 中。

## 群关系（已 machineChecked）

| 关系 | 形式 | 锚 |
|---|---|---|
| Atomic 算子皆 involution（10 件） | `op (op c) = c` | `Operators/Atomic.lean § 5` `atomic_all_involutive` |
| 印 / 投 commute | `yin (tou c) = tou (yin c)` | `Cell256.lean § 8` `yin_tou_comm`, `Operators/Atomic.lean § 4` |
| 印 ∘ 投 = `(· ⊕ (qian, jin))` | `yin (tou c) = c ⊕ (qian, jin)` | `Cell256.lean § 8` `yin_tou_eq_central` |
| `{id, cuo, zong, cuoZong}` Hexagram 上 = V₄ Klein | involutivity + commute + composite | `Operators/V4Outer.lean § 7` `v4_outer_summary` |
| `hu` 不动点 = `{乾, 坤}` | `hu h = h ↔ h = qian ∨ h = kun` | `Operators/V4Outer.lean § 6` `hu_fixed_iff` |
| Cell128 / Cell256 zong involution | lift to product carrier 保持 involution | `Operators/V4Outer.lean § 5` |

## 读表方法

每个算子至少有四个层面：

| 层面 | 问题 | 审计入口 |
|---|---|---|
| 文字 | 这个字或短语如何写 | `wenyan-operators.md` |
| code/id | 它在表中如何定位 | `../_generated/operator-index.md` |
| 签名 | 它怎样接收和产生结构 | `OperatorSignatures.lean` |
| 语义 | 它在候选 cell 或 family 中怎样解释 | `Operator*Semantics.lean` |
| 群结构（v3 新加） | 它属于 Atomic 还是 V4Outer；involution / non-involution | `Operators/Atomic.lean` / `Operators/V4Outer.lean` |

## 分组口径

算子分组是阅读与审计工具，不是宣称传统文献天然如此分类。常见组别包括关系、容纳、转化、流动、起止、量词、因果、模态、否定、同异、句法、核心义理、墨经、名家、时间副词等。完整 group 列表以生成索引为准。

生成索引同时给出三种定位字段：

| 字段 | 用途 |
|---|---|
| `Group` | 稳定机器分组，例如 `R`、`T`、`LIJ` |
| `Key` | 人读助记码，例如 `REL`、`TRN`、`RIT` |
| `Action Position` | 中文作用位，例如「结构关系位」「状态变换位」「礼制角色位」 |
| `Signature` / `Sig Key` / `Arity` | 形态层编码，说明它是一元映射、二元关系、抽取、构造、量化等 |
| `Action Bit` | 效果位，说明这个形态落到哪类操作位置，例如关联位、变换位、抽取位 |
| `Operator Mode` | 该效果位允许的 operator 模式，例如 `relate`、`transform`、`extract` |
| `Effect` | 该模式的保守效果说明；这是账本语义，不等于完整可执行解释 |
| `Full Code` | 全路径码：`GroupKey.SignatureKeyArity.ActionKey.Code`，例如 `REL.REL2.LINK.R-1` |

引用定理或代码时仍用 `Code`/`Id`；面向阅读、讨论和图示时可显示 `Full Code`，它把分组、形态、效果位、原始编号合成一个可读定位。

`Action Bit` 是比 `Signature` 再低一层的索引：`Signature` 回答「它长成什么形」，`Action Bit` 回答「它能当什么 operator 用、作用后产生什么类型的效果」。能执行到 **`Cell256 → Cell256`** 的效果以 `OperatorInstructionSemantics.lean` 里的证明为准（v3 已迁；旧 `Cell192 → Cell192` 表述见 [`../30_crosswalk_互证/old-to-new.md`](../30_crosswalk_互证/old-to-new.md) #22）。

## 与义理的关系

- `义理/D_算子代数.md` 和 `义理/G_完整算子系统_八卦互通与归一.md` 是旧解释入口。
- 新版义理只摘要结构，不复制长表。
- 若旧别名表与生成索引冲突，先信任生成索引，再回到 Lean 源确认。
- 算子出现于图或 claim 时，仍需查对应 theorem 或 registry 状态。
- v2 期之「印 / 投 仅作 Shi 三态 (Z/3) 算子」已被 v3 的 first-class XOR-mask 算子取代；旧叙述见 [`../30_crosswalk_互证/old-to-new.md`](../30_crosswalk_互证/old-to-new.md) #15。

## 维护规则

- 不在本页手写完整算子清单。
- 不把同字复用自动解释为同一语义；复用要看 id、group 和 reading。
- 不把 operator table complete 误读成所有自然语言句子可解析。
- 新增算子后应重新生成 `../_generated/operator-index.md`，再检查本页是否需要补充入口。
- v3 之 Atomic / V4Outer 分类是结构性约束；新增算子若属此二分应在相应 Lean 文件中归类。

## 形式锚

- [`formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) — XOR-mask atomic 算子
- [`formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) — V₄ Klein outer permutation 算子
- [`formal/SSBX/Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) — Cell256 / Shi V₄ / 印 / 投 mask
- [`formal/SSBX/Foundation/Bagua/Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) — Cell128 / 印 / flip1..flip6
- [`formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) — `dong/hua/bian`, `FlipCombo`
- [`formal/SSBX/Foundation/Yi/Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) — `Hexagram.cuo / zong / hu`
- [`formal/SSBX/Text/OperatorAnchors.lean`](../../formal/SSBX/Text/OperatorAnchors.lean) — 文言算子到八卦系统的锚点
- [`formal/SSBX/Text/OperatorCellMap.lean`](../../formal/SSBX/Text/OperatorCellMap.lean) — 单元映射
- [`formal/SSBX/Text/WenyanOperators.lean`](../../formal/SSBX/Text/WenyanOperators.lean) — 算子数据源
