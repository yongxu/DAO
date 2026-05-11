# L-tower 形式化详细规划 v0.2 — Mathlib-加速实现稿

> 状态：v0.2.1 implemented (2026-05-11)，**supersedes** [v0.1 L-tower-plan.md](L-tower-plan.md)
> 关键修订理由：v0.1 基于"项目无 Mathlib CT"假设，提出 4 axiom + 1 元公理；实查 Mathlib rev `ea11ccc` 后确认 `Profinite.AsLimit` / `Endofunctor.Algebra` + `Endofunctor.Coalgebra` (含 Lambek / co-Lambek) / `Stream'.IsBisimulation` 均已存在。
> 净效应：**0 axiom 路径已落地**，无需本地镜像 `Coalgebra.lean`；本轮实现 872 LOC Lean，calendar 从 4-6 周降至单轮完成。
> 关系：[yi-RO-hierarchy.md](yi-RO-hierarchy.md) 描 R₀..R₈ strict (Z/2)ⁿ 梯；本文档延 squaring tower 之正交轴 L₀ → L₁ → L_∞
> 形式锚：[`formal/SSBX/Foundation/Squaring/`](../../formal/SSBX/Foundation/Squaring/) 已实现，并已接入 [`formal/SSBX.lean`](../../formal/SSBX.lean)
> 验证：`lake build SSBX.Foundation.Squaring.ProfiniteLimit` 与 `lake build SSBX` 均通过（3686 / 3686 jobs）

---

## 目录

- §0 [阅读路径](#0-阅读路径)
- §1 [TL;DR](#1-tldr)
- §2 [数学骨架](#2-数学骨架)
- §3 [Mathlib 资源审计](#3-mathlib-资源审计)
- §4 [Milestone 切分](#4-milestone-切分)
- §5 [文件级实现合同](#5-文件级实现合同)
- §6 [Day-by-day sprint plan](#6-day-by-day-sprint-plan)
- §7 [风险登记 + fallback](#7-风险登记--fallback)
- §8 [验收 checklist](#8-验收-checklist)
- §9 [Decision log](#9-decision-log)
- §10 [Future work (M6+)](#10-future-work-m6)
- §11 [Mathlib API cheatsheet](#11-mathlib-api-cheatsheet)

---

## 0. 阅读路径

| 你想看 | 直达 |
|---|---|
| 为什么 v0.1 → v0.2.1 砍了一半工作量 | §1 |
| 数学上发生什么 | §2 |
| Mathlib 哪些定理直接用 | §3, §11 |
| 5 个 milestone 各做什么 | §4 |
| 每个文件长什么样 | §5 |
| 每天具体干什么 | §6 |
| 卡住怎么办 | §7 |
| 怎么算 done | §8 |
| 历史决策 | §9 |
| 之后还能做什么 | §10 |

---

## 1. TL;DR

**核心命题**：R-梯 (Z/2)ⁿ 在 R₈ 算法关闭；张量平方升塔 L₀ → L₁ → ⋯ 是正交独立轴；极限 L_∞ ≅ Cantor 群 ≅ Stream Cell256，**同时**承载 inverse-limit-as-profinite-group 与 Stream-as-final-coalgebra 两种结构。

**v0.1 vs v0.2.1 对比表**：

| 项目 | v0.1 | v0.2.1 |
|---|---|---|
| Axiom (具名工程债) | 4 | **0（已 grep）** |
| Axiom (CT 元公理) | 1 (Smyth–Plotkin) | **0**（命题重述后不需要 SP） |
| 总 LOC | ~5000 | **872 Lean LOC + 文档/入口胶水** |
| Calendar | 4-6 周 | **单轮落地；原计划 8-10 工作日** |
| Mathlib 依赖 | 不引入 | 重度使用 |
| 假设 | 项目无 Mathlib CT | **Mathlib `ea11ccc` 已是依赖** |

**两个让 v0.2.1 变快的关键观察**：
1. **Mathlib 有的比想象多**：`Profinite.AsLimit`（自动 inverse limit）+ `Endofunctor.Algebra` / `Endofunctor.Coalgebra`（含 Lambek / co-Lambek `str_isIso`）+ `Stream'.IsBisimulation`（含 `eq_of_bisim` coinduction）。
2. **honest 命题不需要 Smyth–Plotkin**：v0.1 的"μ(squaring) ≅ ν(R₈ × ·)"是过度戏剧化框架。真正要证的是 "profinite limit ≅ Stream R₈"，是经典拓扑事实，不是 SP。

**本轮已补工程空白**：`V4Tensor.lean` 已把 `Cell256` 的已证枚举与 XOR laws 绑定为 Mathlib `Fintype` / `AddCommGroup` instances；之后 L₁ / L∞ / Stream 的群结构都走 `Prod` / Pi instance。

---

## 2. 数学骨架

### 2.1 R₈ = V₄⁴ 张量分解

[`LiftProject.lean §4-8`](../../formal/SSBX/Foundation/Hierarchy/LiftProject.lean) 已隐含此分解：

| 轴 | yao 对 | 当前命名 | 类型 |
|---|---|---|---|
| 1 | (y₁, y₂) | Ben | V₄ (四象) |
| 2 | (y₃, y₄) | Zheng | V₄ (四象) |
| 3 | (y₅, y₆) | **OuterMian** (占位) | V₄ (四象) |
| 4 | (因, 果) | Shi | V₄ (Klein-four) |

V₄ 之四种实现：四象、Mian sub-axis、Shi {道, 已, 今, 未}—— 在结构上等同（都是 Z/2 × Z/2）。

R₈ = (V₄)⁴ = 4 × 4 × 4 × 4 = 256，**精确等同 4-tensor 张量**。

### 2.2 Squaring tower

```
L₀ := Cell256                              |L₀| = 256
L_{n+1} := L_n × L_n                       |L_n| = 256^(2^n) = 2^(8·2^n)
```

具体：
- L₀ = 256
- L₁ = 65 536
- L₂ ≈ 4.3 · 10⁹
- L₃ ≈ 1.8 · 10¹⁹
- ⋯

projection: π_n : L_{n+1} → L_n 取第一因子（Prod.fst）。这给一个 inverse system。

**注意**：projection 的方向选择不唯一。π_n = Prod.fst 是一个 canonical 选择；π_n = Prod.snd 给出 isomorphic limit；其他 quotient 选择会给出不同对象。本规划固定 π_n = Prod.fst。

### 2.3 极限对偶（重述版）

```
L_∞ := lim_← (L_n, π_n)
     = { f : ∀ n, L_n // ∀ n, π_n (f (n+1)) = f n }
     ≅ Stream Cell256                                  -- 显式双射 §5.5
     ≅ {0, 1}^ℕ as topological group                   -- = Cantor 群
```

L_∞ 同时具有：
- **set-level inverse-limit group structure**（core deliverable；Profinite category 包装列为 optional）
- **final coalgebra of `F X = Cell256 × X` structure**（来自 Stream 的 `(head, tail)` 拆分；`Stream'.IsBisimulation` / `eq_of_bisim` 只提供 coinductive equality，terminality 需在 M5 显式包装）

这两个结构在**同一 carrier** 上**独立可证**；它们的 coincidence 是显式同构传输的推论，而非 SP 元定理。

---

## 3. Mathlib 资源审计

### 3.1 已可用清单（直接 import + instantiate）

| Mathlib 资源 | 文件 | 我们要用什么 |
|---|---|---|
| `Profinite.asLimit` | `Mathlib/Topology/Category/Profinite/AsLimit.lean` | `X ≅ lim X.diagram` 之 `IsLimit` |
| `Endofunctor.Algebra` 范畴 | `Mathlib/CategoryTheory/Endofunctor/Algebra.lean` | F-algebra 类、Hom、Category instance |
| **Lambek 定理已证** | 同上 `Algebra.Initial.str_isIso` | `IsInitial A → IsIso A.str` |
| `Endofunctor.Coalgebra` 范畴 | 同上 `Coalgebra` namespace | F-coalgebra 类、Hom、Category instance |
| **co-Lambek 定理已证** | 同上 `Coalgebra.Terminal.str_isIso` | `IsTerminal A → IsIso A.str` |
| `Stream'` + cons / head / tail | `Mathlib/Data/Stream/Defs.lean` | 基础 API |
| `Stream'.IsBisimulation` | `Mathlib/Data/Stream/Init.lean §Bisim` | bisim 关系 |
| `Stream'.eq_of_bisim` | 同上 | **coinduction principle**（bisim → eq） |
| `Stream'.corec` / `Stream'.corec'` | `Mathlib/Data/Stream/Defs.lean` | corecursion / state-step unfold |
| `Prod.instAddCommGroup` | `Mathlib/Algebra/Group/Prod.lean` | L_n 的 group instance（递归引导） |
| `Limits.IsInitial` / `IsTerminal` | `Mathlib/CategoryTheory/Limits/IsLimit.lean` | universal property 表达 |

### 3.2 缺口清单 + 自给

| 缺口 | 填法 | 工作量 |
|---|---|---|
| `Cell256` 的 Mathlib `Fintype` / `AddCommGroup` instance | M1：复用 `Cell256.all_*` 与 `Cell256.xor_*` 已证 facts，绑定 instances | ~100 LOC |
| Stream 作为 `F X = Cell256 × X` 之 final coalgebra packaging | M5：用 Mathlib `Coalgebra` + `Stream'.corec'` 包装 | ~80 LOC |
| Set-level `L_inf ≃+ Stream' Cell256` 显式构造 | M5：先做 `Nat → Cell256`/prefix block 双射，再加 coherence | ~250 LOC |
| Profinite category 桥接 | M5 optional：set-level 完成后再接 `Profinite.asLimit` | optional ~150 LOC |

**全部填补可走纯 Lean 代码，无需 axiom；本轮不新增 `Coalgebra.lean`。**

### 3.3 Mathlib 版本固定

```
rev: ea11ccc0c5c7c4c562742e918fe2e0b2814a58aa
toolchain: leanprover/lean4:v4.30.0-rc2
```

升级 Mathlib 时需重测本目录所有 `Squaring/*.lean`。

---

## 4. Milestone 切分

总 5 个 milestone（M1–M5），分布在 5 个文件。无需本地 `Coalgebra.lean`：Mathlib `ea11ccc` 已在 `Endofunctor.Algebra.lean` 内提供 `Endofunctor.Coalgebra` 与 co-Lambek。

### M1 — V₄⁴ Recast（R₈ 内部张量结构命名）

| 字段 | 值 |
|---|---|
| 文件 | `formal/SSBX/Foundation/Squaring/V4Tensor.lean` |
| LOC | ~250 |
| 估时 | 1 day (8h) |
| 风险 | 低 |
| 依赖 | 现有 `Cell256` + `LiftProject`；**无 Mathlib** |
| 阻塞下游 | M2, M3, M5 |

**目标**：写出 `Cell256 ≃+ V₄ × V₄ × V₄ × V₄` 之 explicit `AddEquiv`，给第三 V₄ 轴起占位命名 `OuterMian`。

**额外交付**：在首次引入 Mathlib 的 Squaring 层绑定 `Fintype Cell256` 与 `AddCommGroup Cell256` instances；复用 `Cell256.all_length` / `all_nodup` / `mem_all` 与 `Cell256.origin_xor` / `xor_origin` / `xor_self` / `xor_comm` / `xor_assoc`，不改 Foundation-pure 的 `Cell256.lean`。

### M2 — L₁ Group Structure + Octant

| 字段 | 值 |
|---|---|
| 文件 | `formal/SSBX/Foundation/Squaring/L1.lean` |
| LOC | ~500 |
| 估时 | 2-3 days |
| 风险 | 低-中（native_decide 不可用，必须 parametric） |
| 依赖 | M1 + Mathlib `Prod.addCommGroup` |
| 阻塞下游 | M3, M5 |

**目标**：L₁ AddCommGroup + swap involution + 8-octant 分解（沿 8 atomic flips）。

**关键决策**：8-octant 划分沿 R₈ 之 8 atomic flips（flip1..6 + 印 + 投）而非 V₄³ 子集。

### M3 — Retract Tower

| 字段 | 值 |
|---|---|
| 文件 | `formal/SSBX/Foundation/Squaring/RetractTower.lean` |
| LOC | ~400 |
| 估时 | 2 days |
| 风险 | 低 |
| 依赖 | M2 + 现有 LiftProject |
| 阻塞下游 | M5（部分） |

**目标**：把 R₀..R₈ lift/proj retract pair 升塔到 L₁ 内，给出 R₈ ↪ L₁ 之 faithful embedding 链。

### M4 — Stream Coalgebra View

| 字段 | 值 |
|---|---|
| 文件 | `formal/SSBX/Foundation/Squaring/StreamCarrier.lean` |
| LOC | ~200（v0.1 估 600，因 Mathlib bisim 已现成而砍） |
| 估时 | 1-2 days |
| 风险 | 低 |
| 依赖 | Mathlib `Stream'`, `Stream'.IsBisimulation` |
| 阻塞下游 | M5 |

**目标**：Stream Cell256 之 coalgebra 视图（step + unfold） + bisim 应用。

### M5 — Profinite Limit + Stream Iso + Final Coalgebra

| 字段 | 值 |
|---|---|
| 文件 | `formal/SSBX/Foundation/Squaring/ProfiniteLimit.lean` |
| LOC | ~350 |
| 估时 | 2-3 days |
| 风险 | 中（Mathlib Profinite 类型论 dance） |
| 依赖 | M3, M4, Mathlib `Endofunctor.Coalgebra` |
| 阻塞下游 | (terminal) |

**目标**：构造 L_∞ 与 Stream Cell256 之 `AddEquiv` + Mathlib `Endofunctor.Coalgebra` terminal 性质。

### Milestone 依赖图

```
M1 ──┬─→ M2 ──→ M3 ──┐
     │                ├─→ M5
     └─→ M5 (V₄ types)│
                      │
M4 ──────────────────┤
```

---

## 5. 文件级实现合同

本节不是可直接复制的 Lean 源码，而是实现合同：每个文件必须导出哪些名字、依赖哪些现有 API、哪些证明可接受、哪些说法不得越界。这样避免把半成品 Lean 片段误读成已编译代码。

### 5.0 共同约定

- Namespace 根：`SSBX.Foundation.Squaring`；各文件可再开子 namespace。
- 不新增 `axiom`；若某个证明必须暂留 `sorry`，只能是 §7 已登记的风险项，并在验收 checklist 中单独标出。
- `Cell256` 的道 anchor 使用现有 `Cell256.origin = (Hexagram.qian, Shi.dao)`，不要另造 `daoCell` 常量。
- `Cell256` 在 Foundation 层只绑定了 `Add` / `Zero` / `Neg` / `Sub` / `SMul`，并证明了枚举与 XOR laws；`Fintype Cell256` / `AddCommGroup Cell256` instances 在 M1 的 Squaring 层绑定，避免把 Mathlib import 反向塞回 Foundation-pure 文件。
- `Stream' Cell256` 的加群结构走 Pi instance：一旦 `Cell256` 有 `AddCommGroup`，`ℕ → Cell256` 自然继承逐点 `AddCommGroup`。
- Profinite category 桥接是 M5 optional；set-level `L_inf ≃+ Stream' Cell256` 是本轮 core deliverable。

### 5.1 `V4Tensor.lean` (M1)

**Imports**

- `Mathlib.Algebra.Group.Prod`
- `Mathlib.Data.Fintype.Basic`
- `SSBX.Foundation.Bagua.Cell256`
- `SSBX.Foundation.Hierarchy.LiftProject`

**Exports**

| 名字 | 类型 / 作用 | 证明策略 |
|---|---|---|
| `abbrev V4 := Yao × Yao` | generic Klein-4 carrier | 结构定义 |
| `instance instFintypeCell256 : Fintype Cell256` | 把既有 `Cell256.all` 接入 Mathlib | use `Cell256.all`, `all_nodup`, `mem_all` |
| `instance instAddCommGroupCell256 : AddCommGroup Cell256` | 把既有 XOR laws 接入 Mathlib | fields 调用 `Cell256.xor_assoc` / `origin_xor` / `xor_origin` / `xor_self` / `xor_comm` |
| `abbrev OuterMian := V4` | 第三 V₄ 轴占位命名 | doctrine-pending；只作 alias |
| `toV4Quad : Cell256 → V4 × V4 × V4 × V4` | 取 `(y₁,y₂)` / `(y₃,y₄)` / `(y₅,y₆)` / `(因,果)` | `Cell256` 是 `Hexagram × Shi`；用 `c.1.y1` 等字段与 `Shi.toYinGuo c.2` |
| `ofV4Quad : V4 × V4 × V4 × V4 → Cell256` | 反向组装 | `Hexagram.mk` + `Shi.ofYinGuo` |
| `iso : Cell256 ≃+ V4 × V4 × V4 × V4` | 主同构 | `rcases` 四个 V₄；`map_add'` 用现有 XOR 定义或 componentwise cases |
| `v4_tensor_summary` | 打包 `left_inv` / `right_inv` / 道映射 | 供 implementation note 引用 |

**Acceptance**

- `lake build SSBX.Foundation.Squaring.V4Tensor`
- `#check SSBX.Foundation.Squaring.V4Tensor.iso`
- `example : toV4Quad Cell256.origin = ((Yao.yang, Yao.yang), (Yao.yang, Yao.yang), (Yao.yang, Yao.yang), (Yao.yang, Yao.yang)) := rfl`

### 5.2 `L1.lean` (M2)

**Imports**

- `SSBX.Foundation.Squaring.V4Tensor`
- `Mathlib.Data.Fintype.Card`

**Exports**

| 名字 | 类型 / 作用 | 证明策略 |
|---|---|---|
| `abbrev L1 := Cell256 × Cell256` | squaring tower 第一阶 | via `Prod` |
| `instance : AddCommGroup L1` | L₁ 加群 | `inferInstance` from M1 + `Prod` |
| `swap : L1 → L1` | 交换两个 Cell256 factor | by pairs |
| `diag : Cell256 → L1` | 对角嵌入 | `(c,c)` |
| `proj1`, `proj2` | 两个投影 | `Prod.fst` / `Prod.snd` |
| `AtomicFlip` | `f1..f6 | yin | tou` | maps to `Cell256.flip1..flip6` / `Cell256.yin` / `Cell256.tou` |
| `octantIndex : L1 → Fin 8` | 8-octant classifier | 取 `a + b` 的前三个 atomic coordinates；实现时通过 V₄⁴ 投影读前三 bits |
| `octant : Fin 8 → Set L1` | octant fiber | `{ l | octantIndex l = i }` |
| `octant_partition` | 每个 `l` 属于唯一 octant | definitionally by `octantIndex` |
| future `octant_card` | 每个 octant cardinality = 8192 | 非 v0.2.1 core；可在后续用 split-surjection / fiber 等势证明，不 native enumerate 65536 |

**Acceptance**

- `lake build SSBX.Foundation.Squaring.L1`
- `swap_swap`, `swap_diag`, `proj1_diag`, `proj2_diag` 全部无 `sorry`
- `octant_card` 不属于 v0.2.1 core；当前实现以 `octant_partition` 作为验收边界

### 5.3 `RetractTower.lean` (M3)

**Imports**

- `SSBX.Foundation.Squaring.L1`
- `SSBX.Foundation.Hierarchy.LiftProject`

**Exports**

| 名字 | 类型 / 作用 | 证明策略 |
|---|---|---|
| `liftR8toL1 : Cell256 → L1` | R₈ 进入 L₁ | `diag` |
| `projL1toR8 : L1 → Cell256` | L₁ 回 R₈ | `proj1` |
| `proj_lift_id_L1` | `projL1toR8 (liftR8toL1 c) = c` | `rfl` |
| `squareRetract` | `(α → β) → α×α → β×β` | pair map |
| `squareProj` | `(β → α) → β×β → α×α` | pair map |
| `squareProj_squareRetract` | product retract lemma | `intro ⟨a,b⟩; simp [h]` |
| `liftRntoL1` family | R₀..R₇ 进入 L₁ | compose existing `LiftProject` lifts to `R8`, then `diag` |
| `retract_tower_summary` | 打包 R₈ direct retract + generic product retract | conjunction |

**Boundary**

这里不把 L₁ 内的 16-bit shadow 命名为 R₉..R₁₆；所有名字必须带 `L1` 或 `Squaring` 前缀，以守住 canonical doctrine 的"R₈ 闭合，无 R₉"边界。

### 5.4 `StreamCarrier.lean` (M4)

**Imports**

- `Mathlib.Data.Stream.Init`
- `SSBX.Foundation.Squaring.V4Tensor`

**Exports**

| 名字 | 类型 / 作用 | 证明策略 |
|---|---|---|
| `abbrev TrajCell := Stream' Cell256` | trajectory carrier | `Stream'` is `ℕ → Cell256` |
| `step : TrajCell → Cell256 × TrajCell` | coalgebra step | `(s.head, s.tail)` |
| `unfold {X} : (X → Cell256 × X) → X → TrajCell` | state-step corecursion | `Stream'.corec'` |
| `unfold_head` | `(unfold f x).head = (f x).1` | unfold `Stream'.corec'` |
| `unfold_tail` | `(unfold f x).tail = unfold f (f x).2` | `Stream'.ext` over Nat |
| `bisim_eq` | wrapper over `Stream'.eq_of_bisim` | direct call |
| `alwaysReturn` | constant trajectory | `Stream'.const` |
| `shiCycle` | qian fixed, Shi cycles through V₄ | `unfold (fun s => ((Hexagram.qian, s), Shi.cuo s)) Shi.dao` |
| `stream_carrier_summary` | step + unfold + bisim anchors | conjunction of public lemmas |

**Acceptance**

- `lake build SSBX.Foundation.Squaring.StreamCarrier`
- examples for `alwaysReturn` and `shiCycle` compile
- no custom codata or productivity proof; all infinite behavior goes through `Stream'`

### 5.5 `ProfiniteLimit.lean` (M5)

**Imports**

- `Mathlib.CategoryTheory.Endofunctor.Algebra`
- `Mathlib.CategoryTheory.Types.Basic`
- `Mathlib.Algebra.Group.Pi.Basic`
- `Mathlib.Topology.Category.Profinite.AsLimit` only if implementing optional bridge
- `SSBX.Foundation.Squaring.StreamCarrier`

**Core carrier**

`L n` remains recursive product:

```lean
def L : ℕ → Type
  | 0 => Cell256
  | n + 1 => L n × L n
```

Interpretation: `L n` is a block of length `2^n`. The projection `π n : L (n+1) → L n` is first-half projection, not "leftmost cell" projection.

**Exports**

| 名字 | 类型 / 作用 | 证明策略 |
|---|---|---|
| `L : ℕ → Type` | `2^n`-block carrier | recursive product |
| `instance : ∀ n, AddCommGroup (L n)` | block-wise group | induction + `Prod` |
| `pi : ∀ n, L (n+1) → L n` | first-half projection | `Prod.fst` |
| `structure L_inf` | coherent prefix system | fields `toBlock : ∀ n, L n`, `coh : ∀ n, pi n (toBlock (n+1)) = toBlock n` |
| `blockGetNat` | read `Nat` coordinate from `L n`（correctness only used under `k < 2^n`） | recursion on product blocks |
| `blockTake` | first `2^n` entries of a stream as `L n` | recursion: level 0 head; successor splits first and second halves |
| `fromStream : Stream' Cell256 → L_inf` | stream to coherent prefixes | `blockTake`; coherence by first-half lemma |
| `toStream : L_inf → Stream' Cell256` | coherent prefixes to stream | read index `k` from level `k+1`; prove stability by `coh` |
| `toStream_fromStream` | round trip stream | `Stream'.ext`; use `blockGet_blockTake` |
| `fromStream_toStream` | round trip limit | ext on all levels; use prefix stability |
| `isoStream : L_inf ≃+ Stream' Cell256` | additive equivalence | inverse lemmas + pointwise add |
| `coalg : L_inf → Cell256 × L_inf` | transported stream step | `(toStream f).head`, tail transported back through `fromStream` |
| `coalg_toStream_step` | `toStream` respects step | direct from `coalg` + `toStream_fromStream` |
| `coalgebraMorphism`, `coalgebraMorphism_unique` | concrete final-coalgebra map and uniqueness | `Stream'.corec'` plus stream extensionality |
| `funcF : Type ⥤ Type` | `X ↦ Cell256 × X` endofunctor | category-theory packaging |
| `L_inf_coalgebra : Endofunctor.Coalgebra funcF` | carrier + `coalg` | Mathlib `Coalgebra` |
| `L_inf_isFinalCoalgebra` | `Limits.IsTerminal L_inf_coalgebra` | `IsTerminal.ofUniqueHom` from concrete uniqueness |

**Important correction**

`toStream` must not read the leftmost coordinate at each level. That would repeat the first cell forever. It must read coordinate `k` from a sufficiently large coherent block, e.g. level `k+1`, and use coherence to show this is independent of later levels.

**Acceptance**

- `lake build SSBX.Foundation.Squaring.ProfiniteLimit`
- `isoStream.left_inv` and `isoStream.right_inv` compile without `axiom`
- `coalg_toStream_step` and `L_inf_isFinalCoalgebra` compile
- optional `Profinite.asLimit` bridge is not part of the v0.2.1 core acceptance; it can be recorded as M7 work without blocking completion

---

## 6. Day-by-day sprint plan

### Sprint 1 (Week 1) — 有限代数基础

#### Day 1 — M1 V4Tensor

| Hour | Task | Output |
|---|---|---|
| 1 | 设置 `Foundation/Squaring/` namespace + `V4Tensor.lean` imports | empty module |
| 2 | 绑定 `Fintype Cell256` / `AddCommGroup Cell256` instances | ~100 LOC |
| 3 | V4 type + OuterMian abbrev + 第三轴边界注释 | ~40 LOC |
| 4-5 | `toV4Quad` / `ofV4Quad` mutual inverse | ~90 LOC |
| 6 | `iso : Cell256 ≃+ V₄⁴` | ~40 LOC |
| 7 | 4 axis projection convenience + summary theorem | ~40 LOC |
| 8 | acceptance examples + module doc | ~40 LOC |

**Day 1 验收**：`lake build SSBX.Foundation.Squaring.V4Tensor` 全绿；3 个 example 通过。

#### Day 2 — M2 L1 Part 1

| Hour | Task | Output |
|---|---|---|
| 1 | L1 abbrev + AddCommGroup instance via Prod | ~20 LOC |
| 2 | swap, diag, proj1, proj2 | ~30 LOC |
| 3 | swap_swap, swap_diag, proj_diag 引理 | ~40 LOC |
| 4-5 | AtomicFlip enum + apply + applyL1Left/Right | ~80 LOC |
| 6-7 | atomicFlip 之 group-theoretic 性质 | ~60 LOC |
| 8 | partial doc + commit | — |

#### Day 3 — M2 L1 Part 2 + M3 RetractTower Part 1

| Hour | Task | Output |
|---|---|---|
| 1-2 | octantIndex 定义 | ~50 LOC |
| 3 | octant_partition | ~30 LOC |
| 4-5 | octant_card 之 group-theoretic argument | ~80 LOC |
| 6 | L1 final doc + acceptance | ~40 LOC |
| 7-8 | M3 starts: liftR8toL1, projL1toR8, proj_lift_id_L1 | ~30 LOC |

#### Day 4 — M3 RetractTower

| Hour | Task | Output |
|---|---|---|
| 1-2 | squareRetract / squareProj generic | ~60 LOC |
| 3-4 | squareProj_squareRetract 引理 | ~40 LOC |
| 5-7 | R₀..R₇ 各层 lift 升塔到 L₁ | ~150 LOC |
| 8 | retract_tower_summary + doc | ~40 LOC |

#### Day 5 — Buffer + Sprint 1 验收

| Hour | Task |
|---|---|
| 1-3 | 修补前 4 天 sorry / 清理 |
| 4-5 | 跨文件 acceptance examples |
| 6-7 | `lake build` 全绿 + 性能审查 |
| 8 | Sprint 1 review + 文档同步 |

**Sprint 1 验收**：见 §8.1。

### Sprint 2 (Week 2) — Stream + Limit

#### Day 6 — M4 StreamCarrier

| Hour | Task | Output |
|---|---|---|
| 1 | TrajCell, step | ~15 LOC |
| 2-3 | unfold via `Stream'.corec'` + head/tail lemmas | ~60 LOC |
| 4 | bisim_eq wrapper | ~20 LOC |
| 5-6 | alwaysReturn, shiCycle examples | ~50 LOC |
| 7 | 与 ℕ → Cell256 之 trivial 双射 | ~30 LOC |
| 8 | doc + acceptance | ~30 LOC |

#### Day 7 — M5 ProfiniteLimit Part 1

| Hour | Task | Output |
|---|---|---|
| 1 | L : ℕ → Type 递归定义 | ~10 LOC |
| 2 | AddCommGroup, Fintype instances via induction | ~30 LOC |
| 3 | π projection + direct `π_map_add` theorem | ~20 LOC |
| 4-5 | L_inf structure + AddCommGroup instance | ~70 LOC |
| 6-7 | `blockGetNat` / `blockTake` / coherence lemmas | ~110 LOC |
| 8 | partial commit + 验自适应 | — |

#### Day 8 — M5 ProfiniteLimit Part 2

| Hour | Task | Output |
|---|---|---|
| 1 | toStream / fromStream 双向定义 | ~50 LOC |
| 2-4 | toStream_fromStream / fromStream_toStream 互逆证明 | ~100 LOC |
| 5-6 | coalg : L_inf → Cell256 × L_inf + commute lemma | ~50 LOC |
| 7 | `Endofunctor.Coalgebra` packaging | ~30 LOC |
| 8 | L_inf final coalgebra statement + doc | ~30 LOC |

#### Day 9 — M5 完成 + Sprint 2 验收

| Hour | Task |
|---|---|
| 1-2 | 修补 Day 8 卡点 |
| 3-4 | optional: 与 `Profinite.asLimit` 桥接 |
| 5 | 全套 acceptance examples 跑通 |
| 6 | targeted `lake build SSBX.Foundation.Squaring.ProfiniteLimit` + 性能审查 |
| 7 | Sprint 2 review |
| 8 | 文档同步 + commit |

#### Day 10 — Buffer

预留给 `blockGetNat` indexing、typeclass search、或 optional Profinite bridge。若 Day 9 已全绿，Day 10 只做 self-review、`git diff --check`、和 followup notes。

**Sprint 2 验收**：见 §8.2。

---

## 7. 风险登记 + fallback

### 7.1 V₄⁴ 之第三轴命名（M1）

**风险**：(y₅, y₆) 命名是 doctrine 决策；当前用 OuterMian 占位可能与后来的定本命名冲突。

**对策**：
- 用 `abbrev OuterMian := V4` 占位
- 提供一个 `name_alias` namespace，使改名保持局部化
- 不阻塞 M2/M3

### 7.2 native_decide 在 |L₁| ≥ 65536 失效（M2）

**风险**：`octant_card` 无法 native_decide 全枚举。

**对策**：
- **首选**：group-theoretic argument — 证 octant 是 L₁ 之某子群之 coset，从而 |coset| = |L₁| / 8 = 8192
- **次选**：拆 8 octant 分别证 cardinality (each ~30 LOC)
- **fallback**：`octant_card` 可暂标为验收风险，但 M5 不得依赖它；同次提交必须记录精确 theorem 名称与剩余证明义务

### 7.3 Mathlib `Profinite.asLimit` 类型论 dance（M5）

**风险**：Profinite 范畴论 wrappers 与原生 Lean 类型之间需要 coercion；可能引入 universe / typeclass 麻烦。

**对策**：
- **首选**：不用 Profinite category 的 wrap，直接用 set-level inverse limit `{ f : ∀ n, L n // coh }`
- **次选**：先证 set-level，再桥接 Profinite category
- **fallback**：set-level 已是完整 deliverable；Profinite.asLimit 桥接是 bonus

### 7.4 Mathlib Coalgebra packaging（M5）

**风险**：Mathlib 已提供 `Endofunctor.Coalgebra`，但 `F X = Cell256 × X` 必须写成真正的 functor `Type u ⥤ Type u`，不能写成裸函数 `Type → Type`。

**对策**：
- 使用 `Mathlib.CategoryTheory.Endofunctor.Algebra` 中的 `CategoryTheory.Endofunctor.Coalgebra`
- `funcF.map f := fun p => (p.1, f p.2)`，在 Lean 中通过 `TypeCat.ofHom` 包装
- 本轮已闭合：`L_inf_coalgebra`、`coalg_toStream_step`、`L_inf_isFinalCoalgebra` 全部无 `sorry`

### 7.5 Lean 4 codata productivity（M4）

**风险**：自定义 corec 可能触发 termination / productivity checker。

**对策**：
- 用 Mathlib `Stream'.corec'`，不自己写 corec
- 所有 stream 操作走 Stream' API；不直接构造 cons-cons-cons-...

### 7.6 Build time 增长

**风险**：首次 import Profinite + Endofunctor.Algebra 可能显著增加 lake build 时间。

**对策**：
- 仅在 `Squaring/` 子目录 import；不污染 Foundation 主线
- 测量 baseline build time before / after each milestone
- 如增长 > 30%，考虑 `set_option` 减负或拆分

---

## 8. 验收 checklist

### 8.1 Sprint 1 验收（M1 + M2 + M3）

- [x] `lake build SSBX.Foundation.Squaring.V4Tensor` 全绿
- [x] `lake build SSBX.Foundation.Squaring.L1` 全绿
- [x] `lake build SSBX.Foundation.Squaring.RetractTower` 全绿
- [x] V4Tensor.lean 有 `iso` / `origin_toV4Quad` / `v4_tensor_summary` 等命名检查点
- [x] L1.lean 有 `swap_swap` / `proj*_diag` / `octant_partition` 等命名检查点
- [x] RetractTower.lean 有 `proj_lift_id_L1` / `squareProj_squareRetract` / R₀..R₇ lift checks
- [x] M2 之 `octant_card` 未作为 v0.2.1 core；`octant_partition` 已落地且 M5 不依赖 cardinality
- [x] 三个文件合计 387 LOC；比原计划更短，未牺牲 core acceptance
- [x] full `lake build SSBX` 通过（3686 / 3686 jobs）
- [ ] git commit "Sprint 1: M1+M2+M3 — V₄⁴ recast + L₁ + RetractTower"

### 8.2 Sprint 2 验收（M4 + M5）

- [x] `lake build SSBX.Foundation.Squaring.StreamCarrier` 全绿
- [x] `lake build SSBX.Foundation.Squaring.ProfiniteLimit` 全绿
- [x] StreamCarrier.lean 内：`alwaysReturn_head` / `alwaysReturn_tail` / `shiCycle_head` 通过
- [x] ProfiniteLimit.lean 内：`isoStream` + `coalg` + `coalg_toStream_step` 全证（不留 sorry）
- [x] `L_inf_isFinalCoalgebra : Limits.IsTerminal L_inf_coalgebra` 已实际证明
- [x] **0 axiom / 0 sorry / 0 admit 在所有新文件**（grep 确认）
- [x] full `lake build SSBX` 通过（3686 / 3686 jobs）
- [ ] git commit "Sprint 2: M4+M5 — Stream + Profinite Limit"

### 8.3 总体验收

- [x] 所有 5 个文件 lake build 全绿
- [x] 总 LOC 872（比原估算短；实际实现集中在 `ProfiniteLimit.lean` 之证明）
- [x] 0 axiom（无 `axiom` 关键字 in `Foundation/Squaring/`）
- [x] 0 sorry / 0 admit in `Foundation/Squaring/`
- [x] L-tower-plan-v0.2.md 与实际代码一致（Status: Implemented）
- [x] 实现备注内嵌本文件 §9 Decision log 与 §8 checklist；未另开 implementation note

---

## 9. Decision log

### D1 — squaring projection π = Prod.fst（不是 Prod.snd 或 quotient）

**决策**：π_n : L_{n+1} → L_n 选 `Prod.fst`。

**理由**：
- 与 `L_inf → Stream` 之 prefix semantics 对齐：`π` 保留前半 block，`toStream` 通过稳定的 finite prefix 坐标读取第 `k` 项
- π = Prod.snd 给 isomorphic 但 mirror 之 limit；选 fst 与 LiftProject 之 proj 选择一致
- 其他 quotient（如 GroupQuotient）会给 different limit，超出本次范围

### D2 — 8-octant 沿 atomic flips（不是 V₄³ 子集）

**决策**：octant 划分沿 R₈ 之 8 atomic flips（flip1..6 + 印 + 投）。

**理由**：
- 与 Yi 之卦语义对齐（单 yao 移动 + 印/投）
- 与 Cell256 之 atomic generators 对应
- V₄³ 子集划分是 group-theoretic 但与 doctrine 隔阂大

### D3 — 复用 Mathlib Coalgebra（不自建 Coalgebra.lean）

**决策**：不新增 `formal/SSBX/Foundation/Squaring/Coalgebra.lean`。Mathlib rev `ea11ccc` 已在 `Mathlib.CategoryTheory.Endofunctor.Algebra` 中提供 `CategoryTheory.Endofunctor.Coalgebra`、`Coalgebra.Hom`、`Coalgebra.forget` 与 `Coalgebra.Terminal.str_isIso`。

**理由**：
- 减少本仓库维护面，避免复制 Mathlib 已有 API
- 0 axiom 路径更短：M5 只需具体 functor 与 terminal packaging
- 将来若需要上游贡献，应贡献缺失 lemma 或 doc，而不是重复定义 Coalgebra

### D4 — 不引入 Smyth–Plotkin

**决策**：撤回 v0.1 之"μ ≅ ν via SP"框架，重述为 "profinite lim ≅ Stream"。

**理由**：
- v0.1 框架过度戏剧化；honest 命题更简
- profinite-lim 与 Stream 之同构是经典拓扑事实，Mathlib 可直接 instantiate
- SP 是 polynomial functor 在 ω-cocontinuous 条件下的更强陈述，本案不需

### D5 — 不命名 L 内子层为 R₉..R₁₆

**决策**：L₁ 内的 R₉..R₁₆ retract shadow 不用 R-index 命名；改 `L1.subR8` 等 L-prefixed。

**理由**：
- 避免与 doctrine "R₈ 闭合"之"无 R₉"之直接冲突
- L-prefix 明确表明这些是 squaring tower 内部 layer，不是 R-梯延续
- 保留教义清晰

### D6 — 不实现 Profinite category 桥接（optional）

**决策**：M5 之 Profinite category 桥接列为 optional bonus。

**理由**：
- Set-level inverse limit 已是完整 deliverable
- Profinite category 桥接需 universe / typeclass 周旋
- 可作 followup phase

### D7 — 本轮已证明 coalgebra terminality，但仍不做 topological Profinite bridge

**决策**：`ProfiniteLimit.lean` 已证明 `L_inf_isFinalCoalgebra : Limits.IsTerminal L_inf_coalgebra`；§7.3 的 `Profinite.asLimit` / topological group bridge 仍列为 M7。

**理由**：
- `Endofunctor.Coalgebra` terminality 只需 `Stream'.corec'` uniqueness 与 `L_inf ≃+ Stream' Cell256`，类型论成本可控
- `Profinite.asLimit` 涉及拓扑与 `Profinite` wrapper，不是 v0.2.1 core
- 保持本轮 deliverable 为 algebra/coalgebra，不混入拓扑结构

---

## 10. Future work (M6+)

完成 v0.2.1 全部 5 milestone 后，可启动以下：

### M6 — L₂ 与 L_n general 化

将 L₁ 之结构推到任意 L_n。本规划未做（focused on tower limit），但 L₁ 之代码 generic 化即可（~200 LOC）。

### M7 — Profinite topological group structure

把 L_∞ 与 Profinite 范畴 wrappers 桥接，给 topological group instance（Cantor topology）。需 `Mathlib.Topology.Algebra.Group.*`，~400 LOC。

### M8 — 2-adic interpretation

把 L_∞ 视作 F₂[[t]] 之加群（formal power series in F₂），开 algebra-side 之新视角（Witt vectors / formal groups）。需 `Mathlib.RingTheory.WittVector`，可重 ~600 LOC。

### M9 — Counted-loop 之范畴论解读

完成 M4 后，MetaInterp Phase A 之 counted-loop 可形式证为"L_∞ 之 fuel-bounded 投影"。这个连接 lift 到 doc，~150 LOC + 1 篇 followup md。

### M10 — DaoSource generative semantics on TrajCell

DaoSource 之 16-命 受控文言之 generative semantics 自然栖身于 TrajCell。完成 M4 后可 demo `daoSource → TrajCell` 之 unfold，~200 LOC。

### M11 — YiInstr ceiling 之范畴论形式证

完成 M5 后，YiInstr cuo-equivariance ceiling 之 «生», «一» 不可达性可形式证为"它们是 ν-constructor，必出 finite ISA"。需 ~300 LOC + doc。

### M12 — Upstream Stream/Coalgebra lemmas

若 M5 过程中发现 `Stream'.corec'` uniqueness 或 `Coalgebra` packaging 的通用 lemma 缺失，可整理为 mathlib4 PR。注意：不是 PR `Coalgebra.lean` 本身，Mathlib 已有该定义。

---

## 11. Mathlib API cheatsheet

实施过程中频繁使用的 Mathlib API：

### 11.1 Profinite

```lean
-- Mathlib/Topology/Category/Profinite/AsLimit.lean
import Mathlib.Topology.Category.Profinite.AsLimit

#check Profinite.asLimitCone   -- Cone over X.diagram
#check Profinite.asLimit       -- IsLimit X.asLimitCone
#check Profinite.isoAsLimitConeLift  -- X ≅ (limitCone _).pt
```

### 11.2 Endofunctor.Algebra / Coalgebra

```lean
import Mathlib.CategoryTheory.Endofunctor.Algebra

open CategoryTheory.Endofunctor

#check @Algebra              -- structure
#check @Algebra.Hom          -- structure
#check @Algebra.Initial.strInv
#check @Algebra.Initial.str_isIso    -- Lambek

#check @Coalgebra
#check @Coalgebra.Hom
#check @Coalgebra.Terminal.strInv
#check @Coalgebra.Terminal.str_isIso -- co-Lambek
```

### 11.3 Stream'

```lean
import Mathlib.Data.Stream.Init

open Stream'

#check Stream'.corec               -- corecursion
#check Stream'.IsBisimulation      -- bisim 关系
#check Stream'.eq_of_bisim         -- bisim → eq (coinduction)
#check Stream'.head
#check Stream'.tail
#check Stream'.cons
#check Stream'.const
```

### 11.4 Limits

```lean
import Mathlib.CategoryTheory.Limits.IsLimit

open CategoryTheory.Limits

#check IsInitial
#check IsTerminal
#check IsLimit
```

### 11.5 Group / Prod

```lean
import Mathlib.Algebra.Group.Prod

#check Prod.instAddCommGroup    -- L_n via induction on Prod
```

---

## Appendix A — 文件结构总览

v0.2.1 已产生：

```
formal/SSBX/Foundation/Squaring/
├── V4Tensor.lean        (M1, 164 LOC)  -- R₈ ≃+ V₄⁴
├── L1.lean              (M2, 103 LOC)  -- L₁ + swap + 8-octant classifier
├── RetractTower.lean    (M3, 120 LOC)  -- R-梯 升塔到 L₁
├── StreamCarrier.lean   (M4, 74 LOC)   -- Stream Cell256 + bisim/unfold wrapper
└── ProfiniteLimit.lean  (M5, 411 LOC)  -- L_∞ ≃+ Stream + final coalgebra

总: 872 Lean LOC（含 docstrings，不含本计划文档）
```

新顶层 namespace `SSBX.Foundation.Squaring`。

---

## Appendix B — Per-milestone LOC 精算

| Milestone | 估 LOC | 估 days | hours/day | 实际？ |
|---|---|---|---|---|
| M1 V4Tensor | 290 | 1 | 8 | 164 |
| M2 L1 | 500 | 2 | 8 | 103 |
| M3 RetractTower | 400 | 2 | 8 | 120 |
| M4 StreamCarrier | 220 | 1 | 8 | 74 |
| M5 ProfiniteLimit | 350 | 2-3 | 8 | 411 |
| **小计** | **1760** | **8-9** | | **872** |
| Doc / glue | (含) | +2 | | 本文件 + README/module-map + `formal/SSBX.lean` |
| **总** | **~1500-1800** | **~10 工作日** | | **单轮实现** |

---

## Appendix C — 与既有项目接口

| 既有项目 | 接口点 | 完成 v0.2.1 后可做 |
|---|---|---|
| MetaInterp Phase A counted-loop | StreamCarrier 之 fuel-bounded 截断 | M4 完成后即可写 1 篇未来 note：`counted-loop-as-coalgebra.md` |
| KleeneCarrier 4 axiom | 拆分模式 template | 不直接接；本案 0 axiom 不需此模式 |
| DaoSource 16-命 | TrajCell 上之 generative semantics demo | M4 完成后可加 example to StreamCarrier.lean |
| YiInstr ceiling | 不可达性之 categorical 解读 | M5 完成后可启动 M11 |
| BenZheng / Mian / V₄ | V4Tensor 之 instance source | M1 直接复用 |
| LiftProject | Retract pair 之升塔模板 | M3 之 squareRetract 之 source pattern |
| Cell256 atomic operators | L1 atomic flip 之 lift source | M2 直接复用 |

---

## Appendix D — Open questions

仍需 doctrine / 设计决策:

1. **第三 V₄ 轴最终命名**（M1 用 OuterMian 占位）
2. **是否实施 M6（L_n general 化）作为 v0.3**
3. **是否整理 Stream/Coalgebra helper lemmas 回 Mathlib**（M12）
4. **L₁ 内子层是否最终启用 R-index（与 R₈ 闭合冲突）**
5. **Profinite topological structure 是 v0.3 之 core 还是后续 nice-to-have**

---

**End of v0.2.1 plan.**
