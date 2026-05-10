> 状态：v3 定本 (2026-05-11)。
> 父文档：[yi-RO-hierarchy.md](yi-RO-hierarchy.md)
> Lean 入口：[`formal/SSBX/`](../../formal/SSBX/) · [`README.md`](../../formal/SSBX/README.md) (canonical foundation tree)
> 相关 v3 文档：[module-map.md](module-map.md) · [root-layer-map.md](root-layer-map.md) · [layer-axis-graph.md](layer-axis-graph.md) · [pending.md](pending.md)

# Foundation 主目录概览 foundation-core · v3

`Foundation/` 是 Lean codebase 的主体形式化层。本文件给出主要子目录的职责和关键文件，重点记录 2026-05-10/11 之 R₀..R₈ + V₄ Klein Shi + Cell256 重构后的目录布局。

完整文件列表以 [`README.md`](../../formal/SSBX/README.md) 与 [../_generated/lean-index.md](../_generated/lean-index.md) 为准。

---

## 0. 目录树（v3 重构后）

```text
formal/SSBX/Foundation/
├── Core/                         # 字根 · 注义 · 单根证书
│   ├── Yuan.lean                 元层与起点词汇
│   ├── Li.lean                   理与生生不息桥接
│   ├── MonadRoot.lean            单根回归与 Monad DAG
│   ├── Monism.lean               Construction DAG 与构造充分性
│   ├── ShengshengBuxi.lean       生生不息命题之形式接口
│   ├── Attention.lean            注意 / 聚焦 / 子结构
│   ├── HumanAlignment.lean、Alignment.lean、Renlei.lean
│   ├── Sincerity.lean            信诚相关结构
│   ├── EvolutionDao.lean         进化与道接口
│   └── MathAxiomMap.lean、MissingGlyphs.lean、AtomDerivation.lean
│
├── Yi/                           # 易之代数 (R₁ / R₃ / R₆ 主体)
│   └── Yi.lean                   Yao / Trigram / Hexagram + cuo / zong / hu
│
├── Bagua/                        # 八卦 / 64 / 128 / 256 + 不完备路线
│   ├── BaguaAlgebra.lean         (Z/2)³ + V₄ on R₃/R₆
│   ├── BenZheng.lean             4 本 + 4 征 + Mian = R₄ + 16 命
│   ├── Cell128.lean (R₇)         R₇ = Hexagram × YinBit, 因 / 印
│   ├── Cell256.lean (R₈)         R₈ = Hexagram × Shi, 果 / 投 + V₄ Shi
│   ├── Cell256Stratify.lean      R₀..R₈ explicit + R8_complete bundle
│   ├── BaguaTuring.lean          BaguaWen VM + Halt / Rice
│   ├── BaguaWenSpec.lean         VM spec
│   ├── ChunkedDecide.lean、CuoInvariance.lean、FuelDiscipline.lean
│   ├── GodelLi.lean              理之不完备 (49 定理 / 1 公理 / 0 sorry)
│   ├── KleeneInternal.lean、Newman.lean
│   └── ⚠ Cell192.lean — DELETED in commit 8e4406e (Z/3 Shi 是层级压缩错误)
│
├── Hierarchy/                    # ⭐ NEW (2026-05-10) — R₀..R₈ uniform 基础设施
│   ├── RHierarchy.lean           umbrella import (R₀..R₈ + LiftProject + Operators)
│   ├── R0_Taiji.lean             alias: R₀ = Unit (太极)
│   ├── R1_Yao.lean               alias: R₁ = Yao
│   ├── R2_SiXiang.lean           alias: R₂ = SiXiang
│   ├── R3_Trigram.lean           alias: R₃ = Trigram
│   ├── R4_Mian.lean              alias: R₄ = Mian
│   ├── R5_Wuyao.lean             carrier: R₅ = Mian × Bool = (Z/2)⁵ = 32 (provisional)
│   ├── R6_Hexagram.lean          alias: R₆ = Hexagram
│   ├── R7_YinHex.lean            alias: R₇ = Cell128
│   ├── R8_GuoHex.lean            alias: R₈ = Cell256
│   ├── LiftProject.lean          8 对 Lift/Project + retract lemma proj_lift_id_Rn
│   └── Operators/
│       ├── Atomic.lean           XOR 子群 (atomic involutions, abelian re-export)
│       └── V4Outer.lean          V₄ 外对称 (zong / hu / cuoZong, non-XOR re-export)
│
├── Notation/                     # ⭐ NEW (2026-05-10) — 符号 / surface 编码
│   └── OXNotation.lean           OX["xxxxxxxx"] 8-char Cell256 字面量 macro
│
├── Wen/                          # 古文虚字 · 核 · 自释 · 自举
│   ├── Operators.lean、Kernel.lean
│   ├── WenyanText.lean、WenyanSelfInterp.lean
│   ├── WenSurface/Lex.lean、WenyanParserGeneral.lean
│   └── DaoSource.lean
│
├── Jian/                         # 间之核 (14 字粒子核)
│   ├── JianOntology.lean         三本 / 三显 / 三征 / 開閉 / 網體流 / 自指见证
│   ├── Jian.lean、JianSTLC.lean、JianMinimality.lean
│   ├── JianModeKernel.lean、JianYiBridge.lean
│
├── Eight/                        # 八衍 (八道之展开)
│   ├── ShuSuan.lean、LuoJi.lean、TongJi.lean、XingWei.lean
│   ├── LeiYing.lean、DongLi.lean、XinZhi.lean、WuXiang.lean
│
└── Modern/                       # 现代数学 / 概率 / 逻辑 / 物理 / 神经
```

---

## 1. R₀..R₈ 重构总结（2026-05-10/11）

### 主要改动

1. **新增 `Foundation/Hierarchy/`** 子目录：9 个 alias shim (R0..R8) + LiftProject + Operators/Atomic + Operators/V4Outer。
2. **新增 `Foundation/Notation/OXNotation.lean`**：`OX["xxxxxxxx"]` 8-char Cell256 字面量 macro。
3. **删除 `Foundation/Bagua/Cell192.lean`** (commit 8e4406e)：Z/3 cyclic Shi 是层级压缩错误，由 V₄ Klein Shi 在 Cell256 替代。
4. **`Foundation/Bagua/Cell256.lean`**：R₈ = Hexagram × Shi (256 = (Z/2)⁸) 主载体；引入 `Shi.toYinGuo / ofYinGuo` bijection。
5. **`Foundation/Bagua/Cell256Stratify.lean`**：R₀..R₈ explicit + R8_complete bundle (替代之前 R7_complete / R6_complete 旧版本)。
6. **`Foundation/Bagua/Cell128.lean`**：R₇ 中间层 (Hexagram × YinBit, 128 = (Z/2)⁷)。

### Lean 重号 (definitive)

```lean
abbrev R0 := Unit          -- 太极
abbrev R1 := Yao           -- 爻 / 两仪
abbrev R2 := SiXiang       -- 四象
abbrev R3 := Trigram       -- 八卦
abbrev R4 := Mian          -- 面 = Ben × Zheng (16 = (Z/2)⁴)
abbrev R5 := Wuyao         -- 五爻 = Mian × Bool (32 = (Z/2)⁵, provisional)
abbrev R6 := Hexagram      -- 重卦 (64 = (Z/2)⁶)
abbrev R7 := Cell128       -- 因卦 = Hexagram × YinBit (128 = (Z/2)⁷)
abbrev R8 := Cell256       -- 果卦 = Hexagram × Shi (256 = (Z/2)⁸)
```

详见 [`LiftProject.lean §0`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) (R-layer abbreviations)。

---

## 2. Foundation/Core 主线

`Foundation/Core` 是从基础词汇走向单根、构造、价值、注意与人对齐的主干。

### 主要文件

- **`Yuan.lean`**：元层与起点词汇。
- **`Li.lean`**：理与生生不息桥接。
- **`MonadRoot.lean`**：单根回归与 Monad DAG（M0..M4 名册线）。
- **`Monism.lean`**：Construction DAG 与构造充分性（内容线 Γ → 三本 → 三显 → 三征 → 网体流 → 生生不息论）。
- **`ShengshengBuxi.lean`**：生生不息命题之形式接口。
- **`Attention.lean`**：注意 / 聚焦 / 子结构。
- **`HumanAlignment.lean`、`Alignment.lean`、`Renlei.lean`**：人 / 人类 / 对齐。
- **`Sincerity.lean`**：信诚相关结构。
- **`EvolutionDao.lean`**：进化与道接口。
- **`MathAxiomMap.lean`、`MissingGlyphs.lean`、`AtomDerivation.lean`**：公设映射 / 缺字 / 字根派生。

### 三种强度

这里的 theorem 大致有三种读法：

- **结构性**：DAG / rank / 根 / 覆盖 / 依赖关系。
- **定义性**：把项目内部术语转为形式对象。
- **桥接性**：把 Core 结构连接到 claim ledger / Text / Model。

桥接性 theorem 要回看目标 claim 的状态；结构性 theorem 不应被扩大成经验判断。

### 单根与构造

`MonadRoot.lean` 回答登记项是否回到「一」。`Monism.lean` 回答内容如何从 Γ 经过构造关系走向总论。两者重要但问题不同：

- **单根** 是归属与根性。
- **构造** 是依赖形状与 rank 推进。
- 经验真值与阈值校准仍需 ledger / model / pending 层。

---

## 3. Foundation/Bagua + Hierarchy 核心算子簇

R₀..R₈ 主载体 + 算子在以下文件内：

| 簇 | 主体 | 关键定理 |
|---|---|---|
| R₀..R₆ XOR | [`Yi.lean`](../../formal/SSBX/Foundation/Yi/Yi.lean), [`BaguaAlgebra.lean`](../../formal/SSBX/Foundation/Bagua/BaguaAlgebra.lean) | dong/hua/bian, cuo/zong/hu, V₄ |
| R₃/R₆ 4+4 + Mian (R₄) | [`BenZheng.lean`](../../formal/SSBX/Foundation/Bagua/BenZheng.lean) | ben_count = 4, zheng_count = 4, Mian.all_length = 16 |
| R₅ Wuyao | [`R5_Wuyao.lean`](../../formal/SSBX/Foundation/Hierarchy/R5_Wuyao.lean) | Wuyao.all_length = 32, flip5 involution |
| R₇ Cell128 + 因 | [`Cell128.lean`](../../formal/SSBX/Foundation/Bagua/Cell128.lean) | Cell128 = Hexagram × YinBit; 印 = yin |
| R₈ Cell256 + 果 + Shi V₄ | [`Cell256.lean`](../../formal/SSBX/Foundation/Bagua/Cell256.lean) | Cell256 = Hexagram × Shi; 投 = tou; Shi.toYinGuo bijection |
| R₈ closure bundle | [`Cell256Stratify.lean`](../../formal/SSBX/Foundation/Bagua/Cell256Stratify.lean) | **R8_complete** (依赖只 propext + native_decide) |
| Lift/Project | [`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) | 8 对 + liftProject_summary |
| Atomic XOR re-export | [`Operators/Atomic.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/Atomic.lean) | abelian subgroup |
| V₄ outer re-export | [`Operators/V4Outer.lean`](../../formal/SSBX/Foundation/Hierarchy/Operators/V4Outer.lean) | Klein-four |
| OX 字面量 | [`OXNotation.lean`](../../formal/SSBX/Foundation/Notation/OXNotation.lean) | 8-char macro |

---

## 4. 不完备 + Turing + Gödel 路线

`Foundation/Bagua/` 内之动态层（与静态 R-O closure 在 R₀..R₈ 之外）：

- **`BaguaTuring.lean`**：BaguaWen VM (12 instructions, dispatch + execute) — 引入 unbounded iteration, halting undecidability。
- **`GodelLi.lean`**：理之不完备 (49 定理 / 1 公理 / 0 sorry)。
- **`KleeneInternal.lean`、`Newman.lean`**：Kleene recursion / 终止性。
- **`ChunkedDecide.lean`、`CuoInvariance.lean`、`FuelDiscipline.lean`**：决定性 / 等价性 / fuel 之 discipline。

**1 个项目自定义 axiom**：`kleene_recursion_axiom` 在 `KleeneCarrier.lean` 拆为 4 件具名原子（详 yi-calculus-theorem.md）。

---

## 5. R8_complete 闭合性 bundle

R₀..R₈ 主线之最重要的形式 closure 定理：

```lean
-- in Cell256Stratify.lean
theorem R8_complete : ⟨Cell256.all_length_eq_256, ..., (Z/2)⁸ Cayley closure, V₄ Shi structure, ...⟩
```

**依赖原子**: 只依 `propext` + `native_decide`（**无项目自定义 axiom**）。

是 R-hierarchy 静态完整性之 capstone。

---

## 6. 与生成索引

若需要确认某文件是否被导入、声明数或行数，查 [../_generated/lean-index.md](../_generated/lean-index.md)。
若需要确认相关 claim 是否 machineChecked，查 [../_generated/claim-index.md](../_generated/claim-index.md)。

---

## 7. v2 → v3 改动 quick-ref

| Aspect | v2 | v3 |
|---|---|---|
| 顶层 hierarchy | R₁..R₆ | **R₀..R₈** |
| Cell192 | 主体 | **DELETED** (commit 8e4406e) |
| R₅ 五爻 | 跳过 | **`R5_Wuyao.lean` carrier 显式** |
| R₈ Shi | Z/3 cyclic | **V₄ Klein {道, 已, 今, 未}** |
| 因/果 axes | 隐式 | **R₇ 因 + R₈ 果 显式 atom** |
| Hierarchy/ 子目录 | (无) | **新增** (9 alias + LiftProject + Operators/) |
| Notation/ 子目录 | (无) | **新增** (OXNotation.lean) |
| R₈ closure 定理 | R7_complete (旧 192) | **R8_complete** (256, 0 自定义 axiom) |

详见 [yi-RO-hierarchy.md](yi-RO-hierarchy.md), [pending.md](pending.md)。
