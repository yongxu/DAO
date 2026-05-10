# L-tower 形式化规划 — R₈ 之 squaring 升塔 + algebra/coalgebra 极限合一

> ⚠️ **已被 [v0.2](L-tower-plan-v0.2.md) supersede (2026-05-11)**。
> v0.1 之 4 axiom + 1 元公理估计基于"项目无 Mathlib CT"的悲观假设。
> 实查 Mathlib rev `ea11ccc` 后发现 Profinite.AsLimit / Endofunctor.Algebra (含 Lambek) / Stream'.IsBisimulation 均已可用，**0 axiom 路径可达**。
> v0.1 保留作历史参考；新工作请用 v0.2。

> 状态：草案 v0.1 (2026-05-11) — **superseded by v0.2**
> 关系：[yi-RO-hierarchy-v2.md](yi-RO-hierarchy-v2.md) 已封死 R₀..R₈ 之线性 (Z/2)ⁿ 梯子；本文档规划**正交方向** —— 以 R₈ 为 atom 之 squaring tower L₀ → L₁ → L₂ → ⋯
> 形式锚：尚未实现；本文档同时定义首批文件命名（`Foundation/Squaring/*.lean`）

---

## 0. TL;DR

**核心命题**：R-梯 (Z/2)ⁿ 在 R₈ 处算法关闭，但**张量平方**这条独立轴未被关闭。

```
L₀ := R₈                       (V₄)⁴       = 256
L_{k+1} := L_k ⊗ L_k                                -- group tensor square
|L_k| = 2^(8·2^k)              256, 65536, 4·10⁹, ...
L_∞ := lim_← L_k                                    -- profinite Cantor 群
```

**L_∞ 同时具有**：
1. squaring functor 之 **initial algebra** (μ-fixpoint, algebra side)
2. `F X = R₈ × X` 之 **final coalgebra** (ν-fixpoint, coalgebra side, ≅ Stream R₈)

二者在 L_∞ 处合一 —— 这是 algebra ↔ coalgebra 之 limit-level 桥梁的形式化锚点。

**5 阶段 milestone (M1–M5)**，**总 ~5000 LOC, 4–6 周 calendar**。前 3 阶段 (~1150 LOC, 1 周) 是有限 algebra 自包含 deliverable；M4 跨入 coalgebra；M5 给 duality theorem。

**MVP 路径**（M5 用 axiom 占位）：~2000 LOC, **2 周**。

---

## 1. 数学骨架（前置）

### 1.1 R₈ 的张量分解

[`LiftProject.lean`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) §6 已隐含 R₈ ≅ V₄⁴：

| 轴 | yao 对 | 当前命名 | 备注 |
|---|---|---|---|
| 1 | (y₁,y₂) | Ben | 已命名 |
| 2 | (y₃,y₄) | Zheng | 已命名 |
| 3 | (y₅,y₆) | **匿名** | LiftProject 注释里叫 "extra"；M1 需起名 |
| 4 | (因,果) | Shi | V₄ Klein-four 已命名 |

R₈ = (V₄)⁴ = 256 cells = 4×4×4×4 张量。

### 1.2 Squaring tower

```
L₀ = R₈           = V₄⁴           = (Z/2)⁸          = 256
L₁ = L₀ ⊗ L₀     = V₄⁸           = (Z/2)¹⁶         = 65 536
L₂ = L₁ ⊗ L₁     = V₄¹⁶          = (Z/2)³²         ≈ 4.3·10⁹
⋯
L_k              = V₄^(4·2^k)    = (Z/2)^(8·2^k)
```

每一步 squaring 是 categorical-level 提升，**非** +1-bit 之线性扩展。

### 1.3 极限对偶（核心命题）

projective limit `L_∞ = lim_← (L_k, π_k : L_{k+1} → L_k)` 同时具有：

- (algebra) initial algebra of `F : Group → Group, X ↦ X ⊗ X`
- (coalgebra) final coalgebra of `G : Type → Type, X ↦ R₈ × X` ≅ Stream R₈
- (topology) Cantor 群 `{0,1}^ℕ` 之拓扑加群
- (analysis) 2-adic 测度空间相空间

第 1 与第 2 条**在 L_∞ 处合一** —— 这是本规划要形式证的核心定理 (M5)。

---

## 2. 阶段切分 (M1–M5)

### M1 — V₄⁴ Recast (R₈ 内部张量结构命名)

**目标**：写出 R₈ ≅ (V₄)⁴ 之 explicit group iso，给第三 V₄ 轴起名。

**交付**：
- 新文件：`formal/SSBX/Foundation/Squaring/V4Tensor.lean` (~250 LOC)
- 第三轴命名（建议三选一）：
  - `Wai` (外) — 与 inner Ben/Zheng 对应外卦
  - `Yu`  (域) — 中性 abstract
  - `He`  (合) — Ben/Zheng 之合成
- 形式定理：`Cell256 ≃+ V₄ × V₄ × V₄ × V₄`
- 4 component projection
- native_decide 验证（256 cells 在范围内）

**依赖**：现有 `Bagua/Cell256.lean`、`Hierarchy/LiftProject.lean`

**估时**：1 天

### M2 — L₁ = R₈ ⊗ R₈ 构造

**目标**：L₁ 作为有限 AddCommGroup + swap involution + 8-octant 分解。

**交付**：
- 新文件：`formal/SSBX/Foundation/Squaring/L1.lean` (~500 LOC)
- `abbrev L1 : Type := Cell256 × Cell256`
- `instance : AddCommGroup L1`
- 算子：
  - `L1.swap : L1 → L1` (exchange factor，involution)
  - `L1.diag : Cell256 → L1` (diagonal embedding)
  - `L1.proj1, L1.proj2 : L1 → Cell256`
- 8-octant 划分（沿 R₈ 之 8 atomic flip：flip1..6 + 印 + 投）：
  - 每 octant ⊆ L₁ 应有 |·| = 65 536 / 8 = 8 192
  - `octant_decomp_partition` 定理
- 关键警示：|L₁| = 65 536，**超出 native_decide 舒适区**；从此处起改用 parametric / instance-based proof

**依赖**：M1 + 现有 `Cell256` atomic operators

**估时**：2–3 天

### M3 — Retract 升塔 (L_k 内的 R-shadow)

**目标**：R₀..R₈ 之 lift/project retract pair 升塔到 L₁ 内重复，给出 R₈..R₁₆ retract 链。

**交付**：
- 新文件：`formal/SSBX/Foundation/Squaring/RetractTower.lean` (~400 LOC)
- 通用 squaring retract 引理：若 `(lift_k, proj_k)` 是 R_k → R_{k+1} 之 retract，则 `(lift_k ⊗ lift_k, proj_k ⊗ proj_k)` 是 L 层 retract
- `liftR8toL1`, `projL1toR8` 通过 diag/proj1
- `proj_lift_id_L1` 等 retract 引理
- subhier `R₈ ↪ L₁` 之 faithful embedding 定理

**依赖**：M2 + 现有 LiftProject

**估时**：2 天

### M4 — Stream coalgebra (首次跳出 finite carrier)

**目标**：显式构造 Stream Cell256 之 final coalgebra structure + bisimulation。

**交付**：
- 新文件：`formal/SSBX/Foundation/Squaring/StreamCarrier.lean` (~600 LOC)
- 借 Mathlib `Stream'` (`Mathlib.Data.Stream.Init`)
- `def TrajCell : Type := Stream' Cell256`
- corecursion principle：给 `step : X → Cell256 × X` 产生 `unfold step : X → TrajCell`
- bisimulation 定义：`def Bisim (s t : TrajCell) : Prop := ∀ n, s.get n = t.get n`
- final coalgebra universal property（陈述 + 部分证明）
- 至少 1 个 example：`alwaysReturn dao : TrajCell` 是恒返"道"之 trajectory

**依赖**：Mathlib `Stream'`；M3 不严格依赖

**估时**：3–5 天（Lean coinduction 是首次接触；可能需翻 Mathlib 文档）

**风险**：productivity checking；如卡死，fallback 为 `def TrajCell := ℕ → Cell256` 直接定义不走 codata。

### M5 — Profinite 极限合一定理

**目标**：形式证 `μ(squaring) ≅ ν(R₈ × ·)` at L_∞。

**两路径**：

**(A) 拓扑路径**（Mathlib Profinite，~1500 LOC）
- inverse limit `L_∞ := { (l_k : ∀ k, L_k) // ∀ k, π_k (l_{k+1}) = l_k }`
- topological group instance（compact totally disconnected）
- 主定理：`L_∞ ≃+top TrajCell` (group + topology iso)

**(B) Set-only 阉割版**（~800 LOC，无 topology）
- 直接 `def L_inf := { f : ∀ k, L_k // ∀ k, π_k (f (k+1)) = f k }`
- group iso 不带 topology
- duality theorem 之 set-level 形式

无论哪条，**duality 拆 axiom**（仿 KleeneCarrier 之 4 件具名 + 1 元公理）：
- `axiom L_inf_initial_algebra`
- `axiom L_inf_final_coalgebra`
- `axiom L_inf_iso_to_stream`
- `axiom squaring_alg_coalg_duality` (CT 元公理)

**依赖**：M3, M4；路径 (A) 还需 `Mathlib.Topology.Category.Profinite`

**估时**：1–2 周；real proof 之多数留 sorry / 拆 axiom

**风险**：Mathlib `Profinite` 范畴论基础设施在本项目尚未导入；首次导入可能引入 build 时间显著增加。**默认推路径 (B)**，路径 (A) 留作 followup phase。

---

## 3. 工作量总表

| Milestone | LOC  | Days | 风险           | 自包含？ |
|-----------|------|------|----------------|----------|
| M1        | 250  | 1    | 低              | ✓        |
| M2        | 500  | 3    | 低-中（枚举失效） | ✓        |
| M3        | 400  | 2    | 低              | ✓        |
| M4        | 600  | 5    | 中（coinduction） | 部分     |
| M5 (B)    | 800  | 7    | 中（axiom 设计） | 否       |
| M5 (A)    | 1500 | 14   | 高（Profinite）  | 否       |
| **小计 (M5=B)** | **2550** | **18** | | |
| **小计 (M5=A)** | **3250** | **25** | | |

加 docs / glue / refactor overhead × 1.5：
- M5=B 路径：**~3800 LOC, 4 周 calendar**
- M5=A 路径：**~5000 LOC, 6 周 calendar**

**MVP 路径**（M1–M3 + M4 部分 + M5 statement-only with axioms）：~2000 LOC, **2 周**可达。

---

## 4. 关键风险与对策

### 4.1 native_decide 在 |L_k| ≥ 65 536 失效

L₁ 已超出 native_decide 舒适区；L₂ ≈ 4·10⁹ 完全不可能枚举。

**对策**：
- M2 起所有 L_k 定理用 group-theoretic / instance-based reasoning
- 复用 `BaguaAlgebra` 已有 group lemma
- 不依赖 case split 65k cases；用 universal property + `simp` 链

### 4.2 Lean 4 无原生 codata

M4 必须借 `Stream'`（`def Stream' α := Nat → α`）或 Mathlib coinductive predicate。

**对策**：
- 默认走 `Stream'` 路线（最稳）
- bisim 用 `∀ n, s.get n = t.get n` 表达
- "永远..." 性质均 ∀-量化，避开 productivity checker

### 4.3 Mathlib Profinite 重量

M5 路径 (A) 需要 `Mathlib.Topology.Category.Profinite`，本项目尚未引入。

**对策**：
- 默认走路径 (B) set-only 阉割版
- 路径 (A) 标记为 followup phase

### 4.4 第三 V₄ 轴命名（教义债）

M1 给 (y₅,y₆) 起名是 doctrine 决策，非纯技术。

**对策**：
- Lean 双轨：先用占位 `OuterMian` abbrev；待教义定夺后 alias
- 不阻塞 M2/M3（用占位即可推进）

### 4.5 L_k 子层与 R-index 冲突

L₁ 内有 R₉..R₁₆ 之 retract shadow；命名是否启用 R-index 与 doctrine "R₈ 闭合" 冲突。

**对策**：**不**用 R-index 命名 L 内子层；改用 `L1.subR8`, `L1.subR12` 等 L-prefixed 命名，避开 R-梯之"无 R₉"约束。

---

## 5. 推荐执行路径

### Sprint 1 (Week 1) — M1 + M2 + M3

完成有限 algebra 全部基础。

- 输出 3 个新文件：`V4Tensor.lean`, `L1.lean`, `RetractTower.lean`
- 总 ~1150 LOC
- 验收：`lake build` 全绿；至少 3 个 native_decide / decide 验证 example

### Sprint 2 (Week 2) — M4

首次跨入 coalgebra。

- 输出：`StreamCarrier.lean` (~600 LOC)
- 验收：`alwaysReturn dao` 之 corecursion + bisim equality 通过
- 若 Lean codata 卡死：fallback 到 `ℕ → Cell256` 直接定义

### Sprint 3 (Week 3-4) — M5 (B) statement + axiom

拆 axiom，写 statement，留实际 proof。

- 输出：`ProfiniteLimit.lean` (~800 LOC，多数 axiom)
- 验收：4 件具名 axiom + 1 件 CT 元公理；duality theorem 之 statement compile
- 实际 proof 标记为 `Followup-Phase` 留下次

---

## 6. 第一交付 (Week-1 milestone demo)

完成 M1 后即可 demo 出：

```lean
import SSBX.Foundation.Squaring.V4Tensor

open SSBX.Foundation.Squaring.V4Tensor

-- R₈ ≅ V₄⁴ 之具体见证
example : Cell256 ≃+ (V₄ × V₄ × V₄ × V₄) := V4Tensor.iso

-- 4 轴 projection
example (c : Cell256) : (V4Tensor.iso c).fst = Ben.ofYao₂ c.y1 c.y2 := rfl
```

加上 M2：

```lean
import SSBX.Foundation.Squaring.L1

-- L₁ = R₈ × R₈, swap 是 involution
example (l : L1) : L1.swap (L1.swap l) = l := L1.swap_swap l

-- diag/proj retract
example (c : Cell256) : L1.proj1 (L1.diag c) = c := rfl
```

加上 M3：

```lean
import SSBX.Foundation.Squaring.RetractTower

-- 通用 squaring retract: R₈ ↪ L₁ → R₈ = id
example (c : Cell256) : projL1toR8 (liftR8toL1 c) = c :=
  proj_lift_id_L1 c
```

最小验收：上述 example 全绿 + `lake build` 通过。

---

## 7. 已知未决

- 第三 V₄ 轴命名（doctrine 待定）
- 8-octant 是 axis-flip 派 还是 V₄³-子集 派；M2 默认选 axis-flip
- M5 路径 (A) vs (B) 之最终选择（默认 B）
- 是否依赖 Classical / Choice axiom（路径 (A) 似需要）

---

## 8. 文件结构总览

完成本规划后产生：

```
formal/SSBX/Foundation/Squaring/
├── V4Tensor.lean        (M1, ~250 LOC)
├── L1.lean              (M2, ~500 LOC)
├── RetractTower.lean    (M3, ~400 LOC)
├── StreamCarrier.lean   (M4, ~600 LOC)
└── ProfiniteLimit.lean  (M5, ~800 LOC 路径 B / ~1500 LOC 路径 A)
```

新顶层 namespace `SSBX.Foundation.Squaring`。

---

## 9. 与已有项目对接

- **MetaInterp** Phase A counted-loop = M4 之 fuel-bounded 截断特例。完成 M4 后 counted-loop 之范畴论解读可写 followup doc。
- **KleeneCarrier** 之 4 件具名 + 1 CT 元公理拆分模式 = M5 拆 axiom 之 template。
- **DaoSource** 16-命 受控文言之 generative semantics 自然栖身于 `TrajCell`（M4 产物），可作 M4 完成后之 application demo。
- **YiInstr cuo-equivariance ceiling** 之 «生», «一» 不可达性，可在 M5 完成后形式证为"它们是 ν-constructor，必出 finite ISA"。
