> 状态：v3 (2026-05-11) — 从义理表述定位到 Lean 模块的口径页。已更新到 Cell256 + V₄ Klein Shi + R₀..R₈ strict-uniform。

# 义理 → Lean 定位

本页说明如何从义理叙述寻找形式层对应。目标是降低误读：不是每个义理句子都应有 theorem，也不是每个 theorem 都能承载完整旧文论证。

## 三步定位

1. 先看义理页所属类别：核心框架、形式与证明、传统、现代对齐或八衍专题。
2. 再查 `../_generated/crossrefs.md`，寻找文档中已有 Lean path mention 与 symbol hit。
3. 最后查 `../_generated/lean-index.md` 和 `../_generated/claim-index.md`，确认对应模块与 claim 状态。

## 类别对应

| 义理类别 | 首查位置 | 读法 |
|---|---|---|
| 四级生成、根源、开闭 | `Foundation/Core`、`Roster` | 看构造与名册登记，不直接推断价值结论 |
| 六征、实虚史真、256 格 | `Foundation/Bagua`、`Text` | 看有限表、算子空间与 Cell256 / Cell128 / RHierarchy 模块 |
| R₀..R₈ 层级 / 升降 / 对齐 | `Foundation/Hierarchy/`（umbrella + LiftProject） | 看 R-index 命名 + lift/project + `proj_lift_id_R{n}` retract 引理 |
| 算子代数（XOR vs V₄ outer） | `Foundation/Hierarchy/Operators/Atomic.lean` + `V4Outer.lean`、`Foundation/Bagua/`、`Text/WenyanOperators` | 区分 XOR atomic 子群 与 V₄ Klein outer permutation 群 |
| 印 / 投 / 道 / 因 / 果（v3 first-class） | `Foundation/Bagua/Cell256.lean § 1, § 8`；`Cell128.lean`；`Foundation/Notation/OXNotation.lean` | 印 / 投 = XOR-with-mask 算子；道 = (qian, dao) = `OX["oooooooo"]` = R₈ origin |
| 文道一也、自释 | `Foundation/Wen` | 区分解释器、parser、quine 路线和自然语言主张；base-256 dispatch re-derivation pending |
| 对齐、共同体、失败模式 | `Foundation/Core`、`Foundation/Wen`、`Truth` | 多数是 formal interface 或案例层，不宜扩成经验定律 |
| 传统义理 | `Foundation/Wen/Kernel.lean` 及 notes | 多为映射与解释，需保留文献口径 |

## R-hierarchy → Lean 模块映射（v3 主轴）

| 层 | 元数 | 概念 | 主 Lean 模块 | R-index 别名 shim |
|---|---|---|---|---|
| R₀ | 1 | 太极 / Unit | `Unit` (Lean stdlib) | `Foundation/Hierarchy/R0_Taiji.lean` |
| R₁ | 2 | 爻 / 两仪 | `Foundation/Yi/Yi.lean` (`Yao`) | `Foundation/Hierarchy/R1_Yao.lean` |
| R₂ | 4 | 四象 | `Foundation/Bagua/BaguaAlgebra.lean` (`SiXiang`) | `Foundation/Hierarchy/R2_SiXiang.lean` |
| R₃ | 8 | 八卦 | `Foundation/Yi/Yi.lean` (`Trigram`) | `Foundation/Hierarchy/R3_Trigram.lean` |
| R₄ | 16 | 命 / 面 (Mian) = Ben × Zheng | `Foundation/Bagua/BenZheng.lean` (`Mian`) | `Foundation/Hierarchy/R4_Mian.lean` |
| R₅ | 32 | 五爻 (provisional) | `Foundation/Hierarchy/R5_Wuyao.lean` (`Wuyao = Mian × Bool`) | (本身就是 R-index 文件) |
| R₆ | 64 | 重卦 (Hexagram) | `Foundation/Yi/Yi.lean` (`Hexagram`) | `Foundation/Hierarchy/R6_Hexagram.lean` |
| R₇ | 128 | 因卦 (Cell128) = Hexagram × YinBit | `Foundation/Bagua/Cell128.lean` (`Cell128`) | `Foundation/Hierarchy/R7_YinHex.lean` |
| R₈ | 256 | 果卦 (Cell256) = Hexagram × Shi | `Foundation/Bagua/Cell256.lean` (`Cell256`) | `Foundation/Hierarchy/R8_GuoHex.lean` |

R₀..R₈ 的 umbrella 入口：[`Foundation/Hierarchy/RHierarchy.lean`](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean)。
跨层 lift/project 与 `proj_lift_id_R{n}` retract 引理：[`Foundation/Hierarchy/LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean)。

## 算子位置（XOR atomic vs V₄ outer）

| 类别 | 文件 | 包含 |
|---|---|---|
| XOR-mask atomic（**abelian** subgroup） | [`Foundation/Hierarchy/Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) | `cell256_yin / cell256_tou`、`cell128_flip1..flip6 / yin / hexCuo`；皆 involution，皆交换 |
| V₄ Klein outer（**permutation**，含非 XOR） | [`Foundation/Hierarchy/Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) | `hex_cuo / hex_zong / hex_cuoZong`、`cell128_zong / hu`、`cell256_zong / hu`；`{id, cuo, zong, cuoZong}` ≅ V₄ |
| Cell-level XOR carrier | [`Foundation/Bagua/Cell256.lean § 7`](../../formal/SSBX/Foundation/Bagua/Cell256.lean), [`Foundation/Bagua/Cell128.lean § 6`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) | `xor`、`origin`、Cayley `ι/ε`，`AddCommGroup`-flavor instances |
| Notation surface | [`Foundation/Notation/OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) | `OX["o/x×8"]` literal → `Cell256` |

## 可形式化与不可直接形式化

可优先形式化的对象：

- 明确的枚举、表格、算子签名、状态转移（如 R₀..R₈ 各层基数 + `*_complete` 收口）。
- 有固定输入输出的 parser、evaluator、ledger。
- 可写成 theorem 的闭合性质，例如完备性、保守性、可达性、Cayley `ε ∘ ι = id`、`yin/tou` involution、`proj ∘ lift = id` retract、V₄ Klein 关系。

应留在解释层的对象：

- 历史来源的长段阐释。
- 价值判断的应用语境。
- 经验校准、阈值选择和现实政策判断。
- 仍在 pending interface 中的协议。
- v2 期 192-cell 之结构直觉（如「Z/3 cyclic 是史维三态」）— v3 已用 V₄ Klein 取代。

## 写法约束

义理页映射到 Lean 时，建议使用以下句式：

- 「形式层登记为……」用于名册、算子、字形。
- 「Lean 已检查……」只用于 theorem 或 machineChecked claim。
- 「当前由 ledger 承接……」用于 axiomBacked 或 ledgerDependent claim。
- 「该部分仍是 pending interface……」用于经验、阈值、校准与外部数据。

避免使用「已经证明全部」「彻底解决」「无条件推出」等口径，除非生成索引和 Lean 文件都能支持。

## 写法迁移（v2 → v3 术语）

| 义理旧表述 | v3 重写 |
|---|---|
| 「在 Cell192 上 …」 | 「在 Cell256 上 …」（结构 V₄-extended；旧结论多数仍成立） |
| 「Shi 三态 (Z/3)」 | 「Shi V₄ 四态 = {道, 已, 今, 未}」 |
| 「R₆ 之 192 格」 | 「R₈ 之 256 格」 |
| 「Mian 是 R-hierarchy 顶」 | 「Mian = R₄；R-hierarchy 顶为 R₈ = Cell256」 |

## 维护入口

- 义理导航：`../20_theory_义理/README.md`
- 生成索引：`../_generated/`
- claim 状态：[`claim-status.md`](claim-status.md)
- 旧文迁移：[`old-to-new.md`](old-to-new.md)
- Cell192 → Cell256 操作指引：[`cell192-to-cell256-migration.md`](cell192-to-cell256-migration.md)

## 形式锚

- [`formal/SSBX/Foundation/Hierarchy/RHierarchy.lean`](../../formal/SSBX/Foundation/Hierarchy/RHierarchy.lean) — R₀..R₈ umbrella
- [`formal/SSBX/Foundation/Hierarchy/LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) — `liftProject_summary`
- [`formal/SSBX/Foundation/Bagua/Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) — Cell256 / Shi / 印 / 投 / Cayley
- [`formal/SSBX/Foundation/Bagua/Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) — Cell128 / YinBit
- [`formal/SSBX/Foundation/Bagua/Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) — `R8_complete`
- [`formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) — `atomic_all_involutive`
- [`formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) — `v4_outer_summary`
- [`formal/SSBX/Foundation/Notation/OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) — `OX["o/x×8"]`
