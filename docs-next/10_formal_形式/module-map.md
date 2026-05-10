> 状态：v3 定本 (2026-05-11)。
> 父文档：[yi-RO-hierarchy.md](yi-RO-hierarchy.md)
> Lean 入口：[`formal/SSBX/README.md`](../../formal/SSBX/README.md) (canonical foundation tree, updated in commit 8e4406e)
> 相关 v3 文档：[foundation-core.md](foundation-core.md) · [root-layer-map.md](root-layer-map.md) · [layer-axis-graph.md](layer-axis-graph.md) · [pending.md](pending.md)

# 模块地图 module-map · v3

模块地图把读者从主题带到 Lean 文件。完整列表见 [`formal/SSBX/README.md`](../../formal/SSBX/README.md) (canonical foundation tree) 与 [../_generated/lean-index.md](../_generated/lean-index.md)；本页只描述模块簇的职责。

v2 (2026-05-09) → v3 (2026-05-11) 主要改动：新增 `Foundation/Hierarchy/` 与 `Foundation/Notation/` 子目录；删除 `Foundation/Bagua/Cell192.lean`（commit 8e4406e）。

---

## 0. 顶层入口

- **`formal/SSBX.lean`** 是聚合入口。
- **`formal/SSBX/Core.lean`** 给出基础枚举、三值、开闭与若干共用结构。
- **`formal/SSBX/Roster.lean`** 维护字根、生成项、primitive、recursive 与 pending 名册。
- **`formal/SSBX/README.md`** — canonical foundation tree（**更新于 commit 8e4406e**），所有目录布局以此为 ground truth。

这些文件是阅读全局结构的入口，但不应把「被导入」误读成「所有 claim 已证明」。

---

## 1. 主要簇

| 簇 | 子目录 | 职责 | 读法 |
|---|---|---|---|
| **`Foundation/Core`** | `Foundation/Core/` | 单根 / 构造 / 价值 / 注意 / 人对齐 | 看结构性 theorem 与 DAG 口径 |
| **`Foundation/Yi`** | `Foundation/Yi/` | 易核心：Yao / Trigram / Hexagram + cuo/zong/hu | R₁ / R₃ / R₆ 主载体 |
| **`Foundation/Bagua`** | `Foundation/Bagua/` | 八卦代数 / Cell128 (R₇) / Cell256 (R₈) / BaguaTuring / 不完备 | 看 R₈ closure + 计算边界 + `kleene_recursion_axiom` |
| **`Foundation/Hierarchy`** ⭐ NEW | `Foundation/Hierarchy/` | R₀..R₈ uniform 基础设施: 9 alias + LiftProject + Operators | R-index 导航；strict (Z/2)ⁿ uniform |
| **`Foundation/Notation`** ⭐ NEW | `Foundation/Notation/` | 符号 / surface 编码 (OX 字面量 macro) | 解析 `OX["xxxxxxxx"]` |
| **`Foundation/Wen`** | `Foundation/Wen/` | 文 / 文言微核 / 自释 / 自举 / quine 路线 | 看语法 / 求值 / 封装 witness 与路线层次 |
| **`Foundation/Jian`** | `Foundation/Jian/` | 间 / 本体 / 模式核 / STLC / 易桥 | 看「关系间隔」如何进入形式对象 |
| **`Foundation/Eight`** | `Foundation/Eight/` | 八衍：动理 / 逻辑 / 数算 / 统计 / 形位 / 类应 / 心智 / 物相 | 专题中层接口，不读作经验充分性 |
| **`Foundation/Modern`** | `Foundation/Modern/` | 现代数学 / 概率 / 逻辑 / 物理 / 神经 | 形式桥接与局部定理 |
| **`Text`** | `Text/` | glyph / 义位 / 算子 / 覆盖性 / `LayerCharacterMap.lean` (字根 ground truth) | 文字账本与算子表完备性 |
| **`Truth`** | `Truth/` | claim ledger / 语义 / 体系内真理 / `SelfDescription.lean` (V₄ 升级版 Cell256 self-description witness) | claim status，而不是只看名称 |
| **`Model`** | `Model/` | adequacy 与 concrete ledger | 模型充分性表述 |
| **`Pending`** | `Pending/` | 经验接口与示例 | 未闭合边界 |

---

## 2. ⭐ NEW: `Foundation/Hierarchy/` (R₀..R₈ 基础设施)

2026-05-10 新增的 R-hierarchy 统一基础设施：

```text
Foundation/Hierarchy/
├── RHierarchy.lean              umbrella import (9 aliases + LiftProject + Operators)
├── R0_Taiji.lean                R₀ = Unit (1)
├── R1_Yao.lean                  R₁ = Yao (2)
├── R2_SiXiang.lean              R₂ = SiXiang (4)
├── R3_Trigram.lean              R₃ = Trigram (8)
├── R4_Mian.lean                 R₄ = Mian = Ben × Zheng (16)
├── R5_Wuyao.lean                R₅ = Mian × Bool (32, provisional carrier)
├── R6_Hexagram.lean             R₆ = Hexagram (64)
├── R7_YinHex.lean               R₇ = Cell128 = Hex × YinBit (128)
├── R8_GuoHex.lean               R₈ = Cell256 = Hex × Shi (256)
├── LiftProject.lean             8 对 Lift/Project + retract lemma proj_lift_id_Rn
└── Operators/
    ├── Atomic.lean              XOR 子群 (atomic involutions, abelian re-export)
    └── V4Outer.lean             V₄ 外对称 (zong / hu / cuoZong, non-XOR re-export)
```

**职责**：
- 9 个 R{n}_*.lean 是**纯 alias shim**，只提供 R-index 导航，不引入新 logic
- LiftProject 给所有 8 对 (Rₙ, R_{n+1}) 之 lift/project 函子 + 严格 retract 证明
- Operators/Atomic 与 Operators/V4Outer 是从 Cell128/Cell256/BaguaAlgebra 之 re-export，统一 R-hierarchy 接口

详见 [foundation-core.md](foundation-core.md) §1, [`RHierarchy.lean`](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean)。

---

## 3. ⭐ NEW: `Foundation/Notation/` (符号编码)

2026-05-10 新增：

```text
Foundation/Notation/
└── OXNotation.lean              OX["xxxxxxxx"] 8-char Cell256 字面量 macro
```

**职责**：把 8 字符 `o`/`x` 字符串编译期解析为 Cell256 元素：
- chars 0..5 = 6 yao（内→外）：`o` = yang, `x` = yin
- char 6 = YinBit (因 axis, R₇ atom)
- char 7 = GuoBit (果 axis, R₈ atom)

例：`OX["oooooooo"]` = `(Hexagram.qian, Shi.dao)` = Cell256.origin（道 anchor）。

详见 [ox-notation.md](ox-notation.md), [`OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean)。

---

## 4. ⚠ DELETED: `Foundation/Bagua/Cell192.lean`

`Cell192.lean` (Z/3 cyclic Shi {已, 今, 未}) **已删除** in commit 8e4406e。

原因：Z/3 是层级压缩错误。正确 Shi 结构是 V₄ Klein 四群 `{道, 已, 今, 未}` ≅ YinBit × GuoBit ≅ (Z/2)²，由 Cell256 落地。

迁移路径：
- `Cell192` 类型 → `Cell256`
- `Shi.{ji, jin, wei}` (3 case) → `Shi.{dao, ji, jin, wei}` (4 case, V₄)
- `setShi` Z/3 cyclic → `Shi.toYinGuo / ofYinGuo` bijection
- 所有下游 case-split (BaguaTuring, MetaInterp, DaoSource, GodelLi, OperatorCellMap) 已迁移

详见 [foundation-core.md](foundation-core.md) §1, [pending.md](pending.md)。

---

## 5. R₈ closure bundle

最重要的 R-hierarchy 闭合性定理（替代之前 R6_complete / R7_complete）：

```lean
-- in Foundation/Bagua/Cell256Stratify.lean
theorem R8_complete : ...
```

**依赖**: 只依 `propext` + `native_decide`（**无项目自定义 axiom**）。

bundles: `Cell256.all_length = 256`, (Z/2)⁸ Cayley regular representation, V₄ Shi structure, R₀..R₈ explicit cardinality, Lift/Project retract chain.

---

## 6. 索引优先

人工模块图会过期。核对时优先使用：

- [`formal/SSBX/README.md`](../../formal/SSBX/README.md) — **canonical foundation tree** (commit 8e4406e 更新)
- [../_generated/lean-index.md](../_generated/lean-index.md) — 模块 / 导入 / 声明 / 行数
- [../_generated/crossrefs.md](../_generated/crossrefs.md) — 文档与 Lean 路径 / 符号互证
- [../_generated/registry-index.md](../_generated/registry-index.md) — 名册 kind 与 pending / recursive 项
- [../_generated/claim-index.md](../_generated/claim-index.md) — claim 状态

---

## 7. 阅读原则

先从模块簇判断「这页在证明什么」，再看 theorem 名称和依赖。不要只凭文件名推断强度：例如 truth 相关文件可以记录 ledgerDependent claim，Bagua 不完备路线仍依赖唯一 axiom (`kleene_recursion_axiom`)，Pending 文件明确是接口边界。

`Foundation/Hierarchy/` 内的 R{n}_*.lean alias shim 不引入新 logic — 它们仅提供 R-index 导航；真实 algebraic content 仍在 `Foundation/Yi/` + `Foundation/Bagua/` + `Foundation/Hierarchy/R5_Wuyao.lean`。

---

## 8. v2 → v3 改动 summary

| Aspect | v2 (2026-05-09) | v3 (2026-05-11) |
|---|---|---|
| `Foundation/Hierarchy/` | (无) | **新增**：9 alias + LiftProject + Operators/ |
| `Foundation/Notation/` | (无) | **新增**：OXNotation.lean |
| `Foundation/Bagua/Cell192.lean` | 主体 | **DELETED** (commit 8e4406e) |
| Bagua 簇职责 | 192 / V₄ Shi | 128 / 256 / V₄ Klein Shi {道, 已, 今, 未} |
| Hexagram | R₄ | **R₆** |
| 顶层 hierarchy | R₁..R₆ | **R₀..R₈** strict uniform |
| 字根 ground truth | 部分散落 | `Text/LayerCharacterMap.lean` (统一查表 + 往返定理) |
| Self-description witness | 192 版 (旧) | `Truth/SelfDescription.lean` 升级为 `Cell256OperatorComplete` (V₄ 扩展) |

详见 [foundation-core.md](foundation-core.md), [yi-RO-hierarchy.md](yi-RO-hierarchy.md), [pending.md](pending.md)。
