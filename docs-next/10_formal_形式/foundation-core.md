# Foundation/Core + Foundation/Bagua

> 状态：v3 (2026-05-11) — 与 main @ 1c76a55 对齐。Cell256 (R₈) 是闭合层；Cell192 已删；Hierarchy/ 提供 R-index 命名 + uniform Lift/Project + inner/outer 算子拆分。

`Foundation/Core` 是从基础词汇走向单根、构造、价值、注意与人对齐的主干。`Foundation/Bagua` 是「易」的代数核 + R₆ / R₇ / R₈ 三层之 carrier 与定理。两者在 v3 上的连接点是：BenZheng 提供 R₃ 4本/4征 拆分（即 R₄ Mian 之 anchor），Cell128/Cell256 给 R₇/R₈ 之闭合，Cell256Stratify 把 R₀..R₈ 显式 bundling 起来。

完整文件列表以 [../_generated/lean-index.md](../_generated/lean-index.md) 为准。

## 1. Foundation/Core 主线

[`SSBX/Foundation/Core/`](../../formal/SSBX/Foundation/Core/) 内的 13 个文件：

| 文件 | 一句 |
|---|---|
| [`Yuan.lean`](../../formal/SSBX/Foundation/Core/Yuan.lean) | 元层与起点词汇；`TaiJi ≅ Unit`、R₀ 之 anchor |
| [`Li.lean`](../../formal/SSBX/Foundation/Core/Li.lean) | 「理」与生生不息相关桥接 |
| [`Monism.lean`](../../formal/SSBX/Foundation/Core/Monism.lean) | Construction DAG 与构造充分性 |
| [`MonadRoot.lean`](../../formal/SSBX/Foundation/Core/MonadRoot.lean) | 单根回归 + Monad DAG + **`Face` 12 inductive** + CoreAtom (44) + AtomName (333) + DirectEdge |
| [`AtomDerivation.lean`](../../formal/SSBX/Foundation/Core/AtomDerivation.lean) | 字根派生与登记规则 |
| [`Renlei.lean`](../../formal/SSBX/Foundation/Core/Renlei.lean) | 人类（共同体）形式证：三轴 model + iff 充要 |
| [`ShengshengBuxi.lean`](../../formal/SSBX/Foundation/Core/ShengshengBuxi.lean) | 「生生不息」命题的形式接口 |
| [`EvolutionDao.lean`](../../formal/SSBX/Foundation/Core/EvolutionDao.lean) | 进化与道的接口 |
| [`HumanAlignment.lean`](../../formal/SSBX/Foundation/Core/HumanAlignment.lean) | 人对齐 |
| [`Alignment.lean`](../../formal/SSBX/Foundation/Core/Alignment.lean) | 一般 alignment 接口 |
| [`MathAxiomMap.lean`](../../formal/SSBX/Foundation/Core/MathAxiomMap.lean) | 数学公设映射 |
| [`MissingGlyphs.lean`](../../formal/SSBX/Foundation/Core/MissingGlyphs.lean) | 缺字检测与登记 |
| [`Sincerity.lean`](../../formal/SSBX/Foundation/Core/Sincerity.lean) | 信诚相关结构 |
| [`Attention.lean`](../../formal/SSBX/Foundation/Core/Attention.lean) | 注意 / 聚焦与子结构 |

**注**：`Face` 12 inductive 在 v3 的 main @ 1c76a55 上**仍然存在**，与 BenZheng 的 4 本 / 4 征 / 16-Mian 并存（详 [phase-status.md](../00_start/phase-status.md) §2.6）。Mian = R₄ 是 v2.1 doctrine 之 first-class layer；Face 是 M-line 之 M1 层（atom 的 12-面分类），二者维度不同、并不冲突。

## 2. Foundation/Bagua（R₃..R₈ 的 carrier 与算子）

[`SSBX/Foundation/Bagua/`](../../formal/SSBX/Foundation/Bagua/) 内的 13 个文件（**Cell192.lean 已删**，commit 8e4406e）：

| 文件 | R 范围 | 一句 |
|---|---|---|
| [`BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) | R₂..R₃ + 部分 R₆ | SiXiang / dong/hua/bian / FlipCombo / Sheng / chong / cuo/zong/hu |
| [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) | **R₄ (Mian)** + R₃ 4+4 + R₆ quadrant | `Ben / Zheng / Mian = Ben × Zheng / Quadrant` — Mian 是 R₄ first-class anchor |
| [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) | **R₇** | `Cell128 = Hexagram × YinBit`、`yin / 印` XOR atom、AddCommGroup spine |
| [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) | **R₈** (闭合) | `Cell256 = Hexagram × Shi`、`Shi = V₄ {dao, ji, jin, wei}`、`tou / 投` XOR atom、Cayley ι/ε、`Shi.toYinGuo` 双射 |
| [`Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) | R₀..R₈ explicit | R-hierarchy abbrevs + parity / timeReversal / PT / yComb + `R8_complete` bundle（仅依赖 propext + native_decide）|
| [`BaguaTuring.lean`](../../formal/SSBX/Foundation/Bagua/BaguaTuring.lean) | dynamics on R₈ | unbounded iteration → halting layer |
| [`BaguaWenSpec.lean`](../../formal/SSBX/Foundation/Bagua/BaguaWenSpec.lean) | spec | 八卦文 spec / IL 层 |
| [`KleeneInternal.lean`](../../formal/SSBX/Foundation/Bagua/KleeneInternal.lean) | dynamics | Kleene 内部表 |
| [`GodelLi.lean`](../../formal/SSBX/Foundation/Bagua/GodelLi.lean) | dynamics | Gödel-style incompleteness on Bagua |
| [`ChunkedDecide.lean`](../../formal/SSBX/Foundation/Bagua/ChunkedDecide.lean) | proof infra | 分块 decide 工艺 |
| [`CuoInvariance.lean`](../../formal/SSBX/Foundation/Bagua/CuoInvariance.lean) | invariant | cuo 之等变性 |
| [`FuelDiscipline.lean`](../../formal/SSBX/Foundation/Bagua/FuelDiscipline.lean) | proof infra | fuel-bounded recursion |
| [`Newman.lean`](../../formal/SSBX/Foundation/Bagua/Newman.lean) | rewriting | Newman 引理 (local confluence + termination → confluence) |

## 3. R₀..R₈ 一处入口

[`Foundation/Hierarchy/RHierarchy.lean`](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean) umbrella 文件一处导入即得 R₀..R₈ + LiftProject + Operators/Atomic + Operators/V4Outer。

```lean
import SSBX.Foundation.Hierarchy.RHierarchy
-- 现在 R0..R8 abbrevs、liftR{n}toR{n+1}/projR{n+1}toR{n}、
-- 8 atomic XOR ops 与 V₄ outer 都可用
```

R-index alias 与 carrier 的对应：

| R | abbrev (Hierarchy) | 真实 carrier (Bagua / Yi) |
|---|---|---|
| R₀ | `Unit` | (Lean stdlib) |
| R₁ | `Yao` | [`Yi/Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) |
| R₂ | `SiXiang` | [`Bagua/BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) |
| R₃ | `Trigram` | [`Yi/Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) |
| R₄ | `Mian = Ben × Zheng` | [`Bagua/BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) |
| R₅ | `Wuyao = Mian × Bool` | [`Hierarchy/R5_Wuyao.lean`](../../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean) |
| R₆ | `Hexagram` | [`Yi/Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean) |
| R₇ | `Cell128 = Hex × YinBit` | [`Bagua/Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) |
| R₈ | `Cell256 = Hex × Shi` | [`Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) |

## 4. 算法骨架（Phase A algebraic spine）

`Cell128 / Cell256` 在 commit 7de5064（Phase A）之后：

- **AddCommGroup 风格**：`Add` (= XOR), `Zero` (= origin = (qian, dao) for Cell256 / (qian, false) for Cell128), `Neg` (= identity, 因 self-inverse), `Sub`
- **SMul 自身作用**：`(c : Cell256) • (s : Cell256) := c ⊕ s` — Cayley regular representation
- **Cayley homomorphism ι**: `ι c := (· ⊕ c) : Cell256 → Cell256`
- **Origin evaluation ε**: `ε f := f origin = f (qian, dao)`
- **互逆**: `cayley_inj`, `epsilon_iota`, `iota_epsilon` 三件 (在 Cell256.lean)

R₈ 同构：`R₈ ≅ XOR(R₈) ⊆ Aut(R₈)`。

## 5. 三种强度（沿用 v2 框架）

Foundation/Core 与 Foundation/Bagua 的 theorem 大致有三种读法：

- **结构性**：DAG、rank、根、覆盖、依赖关系、群结构、(Z/2)ⁿ 闭合
- **定义性**：把项目内部术语（Mian / Quadrant / Shi / Cell128 / Cell256）转为形式对象
- **桥接性**：把 Core 结构连接到 claim ledger、Text 或 Model

桥接性 theorem 要回看目标 claim 的状态；结构性 theorem 不应被扩大成经验判断。

## 6. 单根、构造、Mian、Quadrant

| 问题 | 由谁回答 |
|---|---|
| 登记项是否回到「一」？ | `MonadRoot.lean` |
| 内容如何从 Γ 经过构造关系走向总论？ | `Monism.lean` |
| 8 trigram 之 4 本 / 4 征 zong-orbit 拆分？ | `BenZheng.lean` |
| R₄ Mian 之 16 命载体？ | `BenZheng.lean`（`Mian = Ben × Zheng`）|
| 64 卦之 4-quadrant 分类？ | `BenZheng.lean`（`Quadrant`）+ [64-hexagram-grid.md](64-hexagram-grid.md) |
| R₈ 256 cell 之 V₄ Shi 闭合？ | `Cell256.lean`（`Shi V₄ {dao, ji, jin, wei}`）|
| R₀..R₈ 之 strict uniform 闭合 bundle？ | `Cell256Stratify.lean`（`R8_complete`）|
| 经验真值与阈值校准？ | ledger / model / pending 层 |

## 7. 与生成索引

- 文件是否被导入、声明数或行数：[../_generated/lean-index.md](../_generated/lean-index.md)
- 相关 claim 是否 machineChecked：[../_generated/claim-index.md](../_generated/claim-index.md)

## 形式锚

- [`formal/SSBX/Foundation/Core/Yuan.lean`](../../formal/SSBX/Foundation/Core/Yuan.lean)
- [`formal/SSBX/Foundation/Core/MonadRoot.lean`](../../formal/SSBX/Foundation/Core/MonadRoot.lean)
- [`formal/SSBX/Foundation/Core/Monism.lean`](../../formal/SSBX/Foundation/Core/Monism.lean)
- [`formal/SSBX/Foundation/Core/Renlei.lean`](../../formal/SSBX/Foundation/Core/Renlei.lean)
- [`formal/SSBX/Foundation/Core/ShengshengBuxi.lean`](../../formal/SSBX/Foundation/Core/ShengshengBuxi.lean)
- [`formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean)
- [`formal/SSBX/Foundation/Bagua/BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean)
- [`formal/SSBX/Foundation/Bagua/Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean)
- [`formal/SSBX/Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean)
- [`formal/SSBX/Foundation/Bagua/Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean)
- [`formal/SSBX/Foundation/Hierarchy/RHierarchy.lean`](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean) — 一处导入即得 R₀..R₈
