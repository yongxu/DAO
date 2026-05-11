# 模块地图

> 状态：v3 (2026-05-11) — 与当前工作树对齐。Cell192 已删；Hierarchy/、Notation/、Squaring/ 是 v3 新增簇；R₀..R₈ strict (Z/2)ⁿ uniform 是 spine。

模块地图把读者从主题带到 Lean 文件。完整列表由 `python3 scripts/docs_next.py build` 生成到 `docs-next/_generated/lean-index.md`；本页只描述模块簇的职责。

## 顶层入口

- [`formal/SSBX.lean`](../../formal/SSBX.lean) — 聚合入口；当前工作树 `lake build SSBX` = **3686 / 3686 jobs**
- [`formal/SSBX/Core.lean`](../../formal/SSBX/Core.lean) — 基础枚举、三值、开闭与若干共用结构
- [`formal/SSBX/Roster.lean`](../../formal/SSBX/Roster.lean) — 字根、生成项、primitive、recursive、pending 名册

被导入不等于 claim 已证明。

## 主要簇

| 簇 | 路径 | 职责 | 读法 |
|---|---|---|---|
| `Foundation/Core` | [`Foundation/Core/`](../../formal/SSBX/Foundation/Core/) | 单根、构造、价值、注意、人对齐 (13 文件) | 看结构性 theorem 与 DAG 口径 |
| `Foundation/Wen` | [`Foundation/Wen/`](../../formal/SSBX/Foundation/Wen/) | 文 / 文言微核 / 自释 / 自举 / quine 路线 | 看语法、求值、封装 witness 与路线层次 |
| `Foundation/Jian` | [`Foundation/Jian/`](../../formal/SSBX/Foundation/Jian/) | 间、本体、模式核、STLC、易桥 | 看「关系间隔」如何进入形式对象 |
| `Foundation/Yi` | [`Foundation/Yi/`](../../formal/SSBX/Foundation/Yi/) | 易核心：Yao / Trigram / Hexagram | 看八卦/重卦的最小单 |
| `Foundation/Bagua` | [`Foundation/Bagua/`](../../formal/SSBX/Foundation/Bagua/) | 八卦代数、BenZheng (R₄)、**Cell128 (R₇)、Cell256 (R₈)、Cell256Stratify** (R₀..R₈ bundle)、BaguaTuring、KleeneInternal、GodelLi、Newman、ChunkedDecide、CuoInvariance、FuelDiscipline | 看计算边界与 `kleene_recursion_axiom` |
| **`Foundation/Hierarchy`** ⭐新 | [`Foundation/Hierarchy/`](../../formal/SSBX/Foundation/Hierarchy/) | **R₀..R₈ index alias 文件 (R0_Taiji..R8_GuoHex) + RHierarchy umbrella + LiftProject + Operators/{Atomic, V4Outer}** | 一处 import 即得 R-index 命名 + 算子 inner/outer 拆分 |
| **`Foundation/Notation`** ⭐新 | [`Foundation/Notation/`](../../formal/SSBX/Foundation/Notation/) | **`OX["xxxxxxxx"]` 8-char Cell256 字面 macro** | 给 256-cell 一个可读的字面 |
| **`Foundation/Squaring`** ⭐新 | [`Foundation/Squaring/`](../../formal/SSBX/Foundation/Squaring/) | **L-tower / V₄ tensor / L₁ / retract tower / Stream carrier / L∞ final coalgebra** | 看 R₈ 闭合后的正交 squaring tower，不读作 R₉ |
| `Foundation/Eight` | [`Foundation/Eight/`](../../formal/SSBX/Foundation/Eight/) | 八衍：动理、逻辑、数算、统计、形等 | 看专题中层接口，不读作经验充分性 |
| `Foundation/Modern` | [`Foundation/Modern/`](../../formal/SSBX/Foundation/Modern/) | 现代数学、概率、逻辑、物理、神经科学 | 看形式桥接与局部定理；Cell256 cascades 已 0003224 落地 |
| `Text` | [`Text/`](../../formal/SSBX/Text/) | glyph、义位、算子、覆盖性 | 看文字账本与算子表完备性；OperatorAnchors / OperatorCellMap / LayerCharacterMap 在 Cell256 之上 |
| `Truth` | [`Truth/`](../../formal/SSBX/Truth/) | claim ledger、语义、体系内真理、**SelfDescription** | 看 claim status；`Cell256OperatorComplete` theorem |
| `Model` | [`Model/`](../../formal/SSBX/Model/) | adequacy 与 concrete ledger | 看模型充分性如何被表述 |
| `Pending` | [`Pending/`](../../formal/SSBX/Pending/) | 经验接口与示例 | 看未闭合边界 |

## v3 新增 / 删除

**删除（commit 8e4406e）**：
- ~~`Foundation/Bagua/Cell192.lean`~~ — 已删（旧 192 = 64 hex × 3 Shi {ji, jin, wei} 之 carrier）

**新增（v3 base + current worktree）**：

`Foundation/Hierarchy/`（11 文件 + 1 子目录）：

```
R0_Taiji.lean      R1_Yao.lean        R2_SiXiang.lean
R3_Trigram.lean    R4_Mian.lean       R5_Wuyao.lean      ← 真实新载体 (32 = (Z/2)⁵)
R6_Hexagram.lean   R7_YinHex.lean     R8_GuoHex.lean
RHierarchy.lean    LiftProject.lean   Operators/{Atomic.lean, V4Outer.lean}
```

`Foundation/Notation/`：

```
OXNotation.lean    -- OX["xxxxxxxx"] 8-char Cell256 字面 macro
```

`Foundation/Squaring/`：

```
V4Tensor.lean       -- Cell256 ≃+ V₄⁴ + Mathlib Fintype/AddCommGroup bridge
L1.lean             -- L₁ = Cell256 × Cell256 + swap/diag/octant classifier
RetractTower.lean   -- R₀..R₈ retracts lifted into L₁
StreamCarrier.lean  -- Stream' Cell256 coalgebra carrier + unfold/bisim wrapper
ProfiniteLimit.lean -- L∞ coherent prefixes ≃+ Stream' Cell256 + final coalgebra
```

`Foundation/Bagua/` 新增（commit 7de5064）：

```
Cell128.lean       -- R₇ = Hexagram × YinBit, 128 cells, 印 (yin) XOR atom
Cell256.lean       -- R₈ = Hexagram × Shi V₄, 256 cells, 投 (tou) XOR atom
Cell256Stratify.lean -- R₀..R₈ explicit bundle + R8_complete
```

`Foundation/Bagua/BenZheng.lean`：在 v2 (commits 73c94a3 + 172487c) 已存在，作 R₃ 4本/4征 + R₄ Mian + R₆ Quadrant；v3 没有变更。

## 一处入口：RHierarchy umbrella

```lean
import SSBX.Foundation.Hierarchy.RHierarchy
-- 现在 R0..R8、liftR{n}toR{n+1}/projR{n+1}toR{n}、
-- 8 atomic XOR ops + V₄ outer 都在 namespace 内可用
```

## 索引优先

人工模块图会过期。核对时优先使用：

- `docs-next/_generated/lean-index.md`：模块、导入、声明、行数
- `docs-next/_generated/crossrefs.md`：文档与 Lean 路径/符号互证
- `docs-next/_generated/registry-index.md`：名册 kind 与 pending/recursive 项
- `docs-next/_generated/claim-index.md`：claim 状态

## 阅读原则

先从模块簇判断「这页在证明什么」，再看 theorem 名称和依赖。不要只凭文件名推断强度：

- Truth 相关文件可记录 ledgerDependent claim
- Bagua 不完备路线（BaguaTuring / KleeneInternal）仍依赖唯一 axiom（`kleene_recursion_axiom`，4 件具名原子）
- Pending 文件明确是接口边界
- Hierarchy / Notation 是 navigation / surface 层（无独立证明）

## 形式锚

- [`formal/SSBX.lean`](../../formal/SSBX.lean)
- [`formal/SSBX/Foundation/Hierarchy/RHierarchy.lean`](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean)
- [`formal/SSBX/Foundation/Hierarchy/LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean)
- [`formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean)
- [`formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean)
- [`formal/SSBX/Foundation/Notation/OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean)
- [`formal/SSBX/Foundation/Squaring/V4Tensor.lean`](../../formal/SSBX/Foundation/Squaring/V4Tensor.lean)
- [`formal/SSBX/Foundation/Squaring/L1.lean`](../../formal/SSBX/Foundation/Squaring/L1.lean)
- [`formal/SSBX/Foundation/Squaring/RetractTower.lean`](../../formal/SSBX/Foundation/Squaring/RetractTower.lean)
- [`formal/SSBX/Foundation/Squaring/StreamCarrier.lean`](../../formal/SSBX/Foundation/Squaring/StreamCarrier.lean)
- [`formal/SSBX/Foundation/Squaring/ProfiniteLimit.lean`](../../formal/SSBX/Foundation/Squaring/ProfiniteLimit.lean)
- [`formal/SSBX/Foundation/Bagua/Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean)
- [`formal/SSBX/Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean)
- [`formal/SSBX/Foundation/Bagua/Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean)
