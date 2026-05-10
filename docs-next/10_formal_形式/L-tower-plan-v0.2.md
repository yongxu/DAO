# L-tower 形式化详细规划 v0.2 — Mathlib-加速版

> 状态：v0.2 (2026-05-11)，**supersedes** [v0.1 L-tower-plan.md](L-tower-plan.md)
> 关键修订理由：v0.1 基于"项目无 Mathlib CT"假设，提出 4 axiom + 1 元公理；实查 Mathlib rev `ea11ccc` 后确认 `Profinite.AsLimit` / `Endofunctor.Algebra` (含 Lambek) / `Stream'.IsBisimulation` 三件均已存在。
> 净效应：**0 axiom 路径可达**，总 LOC 从 ~5000 降至 ~1700，calendar 从 4-6 周降至 ~2 周。
> 关系：[yi-RO-hierarchy-v2.md](yi-RO-hierarchy-v2.md) 描 R₀..R₈ 线性 (Z/2)ⁿ 梯；本文档延 squaring tower 之正交轴 L₀ → L₁ → L_∞
> 形式锚：尚未实现；本文档定义 `formal/SSBX/Foundation/Squaring/*.lean` namespace

---

## 目录

- §0 [阅读路径](#0-阅读路径)
- §1 [TL;DR](#1-tldr)
- §2 [数学骨架](#2-数学骨架)
- §3 [Mathlib 资源审计](#3-mathlib-资源审计)
- §4 [Milestone 切分](#4-milestone-切分)
- §5 [文件级 skeleton](#5-文件级-skeleton)
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
| 为什么 v0.1 → v0.2 砍了一半工作量 | §1 |
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

**v0.1 vs v0.2 对比表**：

| 项目 | v0.1 | v0.2 |
|---|---|---|
| Axiom (具名工程债) | 4 | **0** |
| Axiom (CT 元公理) | 1 (Smyth–Plotkin) | **0**（命题重述后不需要 SP） |
| 总 LOC | ~5000 | ~1700 |
| Calendar | 4-6 周 | **~2 周** |
| Mathlib 依赖 | 不引入 | 重度使用 |
| 假设 | 项目无 Mathlib CT | **Mathlib `ea11ccc` 已是依赖** |

**两个让 v0.2 变快的关键观察**：
1. **Mathlib 有的比想象多**：`Profinite.AsLimit`（自动 inverse limit）+ `Endofunctor.Algebra`（含 Lambek `str_isIso`）+ `Stream'.IsBisimulation`（含 `eq_of_bisim` coinduction）。
2. **honest 命题不需要 Smyth–Plotkin**：v0.1 的"μ(squaring) ≅ ν(R₈ × ·)"是过度戏剧化框架。真正要证的是 "profinite limit ≅ Stream R₈"，是经典拓扑事实，不是 SP。

**唯一空白**：`Endofunctor.Coalgebra` 类在 Mathlib 不存在（只有 `Endofunctor.Algebra`）。**~200 LOC 直接镜像即可**，将来甚至可 PR 回 Mathlib。

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
     ≅ Stream Cell256                                  -- 显式双射 §5.6
     ≅ {0, 1}^ℕ as topological group                   -- = Cantor 群
```

L_∞ 同时具有：
- **inverse-limit profinite group structure**（来自 `Profinite.asLimit`）
- **final coalgebra of `F X = Cell256 × X` structure**（来自 Stream 的 (head, tail) 拆分 + `Stream'.IsBisimulation` 之 universal property）

这两个结构在**同一 carrier** 上**独立可证**（都用 Mathlib 现成 API），它们的 coincidence 是 trivial 推论而非 SP 元定理。

---

## 3. Mathlib 资源审计

### 3.1 已可用清单（直接 import + instantiate）

| Mathlib 资源 | 文件 | 我们要用什么 |
|---|---|---|
| `Profinite.asLimit` | `Mathlib/Topology/Category/Profinite/AsLimit.lean` | `X ≅ lim X.diagram` 之 `IsLimit` |
| `Endofunctor.Algebra` 范畴 | `Mathlib/CategoryTheory/Endofunctor/Algebra.lean` | F-algebra 类、Hom、Category instance |
| **Lambek 定理已证** | 同上 `str_isIso` | `IsInitial A → IsIso A.str` |
| `Stream'` + cons / head / tail | `Mathlib/Data/Stream/Defs.lean` | 基础 API |
| `Stream'.IsBisimulation` | `Mathlib/Data/Stream/Init.lean §Bisim` | bisim 关系 |
| `Stream'.eq_of_bisim` | 同上 | **coinduction principle**（bisim → eq） |
| `Stream'.corec` | `Mathlib/Data/Stream/Defs.lean` | corecursion |
| `Prod.instAddCommGroup` | `Mathlib/Algebra/Group/Prod.lean` | L_n 的 group instance（递归引导） |
| `Limits.IsInitial` / `IsTerminal` | `Mathlib/CategoryTheory/Limits/IsLimit.lean` | universal property 表达 |

### 3.2 缺口清单 + 自给

| 缺口 | 填法 | 工作量 |
|---|---|---|
| `Endofunctor.Coalgebra` 类（Mathlib 只有 Algebra，没 Coalgebra） | M5.0：直接镜像 `Algebra.lean` | ~200 LOC |
| Stream 作为 `F X = Cell256 × X` 之 final coalgebra packaging | M5：~50 LOC instantiation | ~50 LOC |
| Co-Lambek (final coalgebra 的 str_isIso) | M5.0 内对偶证 | ~30 LOC（在 200 内） |

**全部填补可走纯 Lean 代码，无需 axiom**。

### 3.3 Mathlib 版本固定

```
rev: ea11ccc0c5c7c4c562742e918fe2e0b2814a58aa
toolchain: leanprover/lean4:v4.30.0-rc2
```

升级 Mathlib 时需重测本目录所有 `Squaring/*.lean`。

---

## 4. Milestone 切分

总 6 个 milestone（M1, M2, M3, M4, M5.0, M5），分布在 5 个文件 + 1 个新文件（M5.0）。

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

### M5.0 — Endofunctor.Coalgebra 类（镜像 Mathlib）

| 字段 | 值 |
|---|---|
| 文件 | `formal/SSBX/Foundation/Squaring/Coalgebra.lean` |
| LOC | ~200 |
| 估时 | 1 day |
| 风险 | 低（Mathlib 有 `Algebra.lean` 作 template） |
| 依赖 | Mathlib CategoryTheory base |
| 阻塞下游 | M5 |

**目标**：写出 Mathlib 缺失的 `Endofunctor.Coalgebra` 类（dual mirror of `Algebra.lean`）。

**Bonus**：完成后可考虑 PR 回 Mathlib。

### M5 — Profinite Limit + Stream Iso + Final Coalgebra

| 字段 | 值 |
|---|---|
| 文件 | `formal/SSBX/Foundation/Squaring/ProfiniteLimit.lean` |
| LOC | ~350 |
| 估时 | 3-4 days |
| 风险 | 中（Mathlib Profinite 类型论 dance） |
| 依赖 | M3, M4, M5.0 |
| 阻塞下游 | (terminal) |

**目标**：构造 L_∞ 与 Stream Cell256 之 `AddEquiv` + final coalgebra 性质。

### Milestone 依赖图

```
M1 ──┬─→ M2 ──→ M3 ──┐
     │                ├─→ M5
     └─→ M5 (V₄ types)│
                      │
M4 ──────────────────┤
                      │
M5.0 ────────────────┘
```

---

## 5. 文件级 skeleton

### 5.1 V4Tensor.lean

```lean
/-
# V₄ Tensor — R₈ ≅ V₄⁴ 之 explicit recasting

R₈ = Cell256 已被 BaguaAlgebra / LiftProject 隐含视为 V₄ × V₄ × V₄ × V₄。
本文件给出 explicit AddEquiv，并给第三 V₄ 轴 (y₅,y₆) 起 placeholder 名 OuterMian。

doctrine 命名权属：第三 V₄ 轴 (y₅, y₆) 之最终命名待定。
-/
import SSBX.Foundation.Bagua.Cell256
import SSBX.Foundation.Hierarchy.LiftProject

namespace SSBX.Foundation.Squaring.V4Tensor

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell256

/-! ## V₄ as a generic Klein-4 carrier -/

/-- V₄ = Yao × Yao = SiXiang. AddCommGroup via pointwise XOR. -/
abbrev V4 : Type := Yao × Yao

namespace V4
def zero : V4 := (.yang, .yang)
def add : V4 → V4 → V4
  | (a₁, a₂), (b₁, b₂) => (a₁.xor b₁, a₂.xor b₂)
def neg : V4 → V4 := id   -- self-inverse since Z/2

instance : AddCommGroup V4 := {
  zero := zero
  add := add
  neg := neg
  -- group axioms via cases on Yao
  add_assoc := by intros; cases ‹V4› <;> cases ‹V4› <;> cases ‹V4› <;> rfl
  zero_add := ...
  add_zero := ...
  add_comm := ...
  neg_add_cancel := ...
}
end V4

/-! ## OuterMian — 第三 V₄ 轴占位命名 -/

/-- Third V₄ axis from (y₅, y₆); naming is doctrine-pending. -/
abbrev OuterMian : Type := V4

/-! ## Main iso: Cell256 ≃+ V₄⁴ -/

def toV4Quad (c : Cell256) : V4 × V4 × V4 × V4 :=
  ⟨(c.hex.y1, c.hex.y2), (c.hex.y3, c.hex.y4),
   (c.hex.y5, c.hex.y6), Shi.toYinGuo c.shi⟩

def ofV4Quad : V4 × V4 × V4 × V4 → Cell256
  | ((y1, y2), (y3, y4), (y5, y6), yg) =>
      ⟨⟨y1, y2, y3, y4, y5, y6⟩, Shi.ofYinGuo yg⟩

theorem to_of (q : V4 × V4 × V4 × V4) : toV4Quad (ofV4Quad q) = q := by
  rcases q with ⟨_, _, _, ⟨y, g⟩⟩; cases y <;> cases g <;> rfl

theorem of_to (c : Cell256) : ofV4Quad (toV4Quad c) = c := by
  rcases c with ⟨h, s⟩; cases h; cases s <;> rfl

def iso : Cell256 ≃+ (V4 × V4 × V4 × V4) where
  toFun := toV4Quad
  invFun := ofV4Quad
  left_inv := of_to
  right_inv := to_of
  map_add' := by intro a b; cases a; cases b; rfl

/-! ## Acceptance examples -/

example : toV4Quad ⟨Hexagram.qian, Shi.dao⟩ =
          (V4.zero, V4.zero, V4.zero, V4.zero) := rfl
example (c : Cell256) : ofV4Quad (toV4Quad c) = c := of_to c

end SSBX.Foundation.Squaring.V4Tensor
```

### 5.2 L1.lean

```lean
/-
# L₁ = Cell256 × Cell256 — Squaring tower 之第一阶

L₁ = R₈ × R₈ as AddCommGroup; |L₁| = 65536。
本文件构造：swap involution、diag/proj、8-octant 分解（沿 R₈ 之 8 atomic flips）。

⚠️ |L₁| = 65536 已超 native_decide 舒适区；本文件起所有定理用 group-theoretic / 
parametric reasoning，不依赖 case split 65k cases。
-/
import SSBX.Foundation.Squaring.V4Tensor
import Mathlib.Algebra.Group.Prod

namespace SSBX.Foundation.Squaring.L1

open SSBX.Foundation.Bagua.Cell256

abbrev L1 : Type := Cell256 × Cell256

instance : AddCommGroup L1 := inferInstance  -- via Prod

/-! ## swap / diag / projections -/

def swap : L1 → L1 | (a, b) => (b, a)
def diag (c : Cell256) : L1 := (c, c)
def proj1 : L1 → Cell256 := Prod.fst
def proj2 : L1 → Cell256 := Prod.snd

theorem swap_swap (l : L1) : swap (swap l) = l := by cases l; rfl
theorem swap_diag (c : Cell256) : swap (diag c) = diag c := rfl
theorem proj1_diag (c : Cell256) : proj1 (diag c) = c := rfl
theorem proj2_diag (c : Cell256) : proj2 (diag c) = c := rfl

/-! ## L1.atomicFlip — 8 atomic generators of L₁ via R₈ atoms -/

inductive AtomicFlip
  | f1 | f2 | f3 | f4 | f5 | f6 | yin | tou
  deriving Repr, DecidableEq

namespace AtomicFlip
def apply : AtomicFlip → Cell256 → Cell256
  | .f1   => Cell256.flip1
  | .f2   => Cell256.flip2
  | .f3   => Cell256.flip3
  | .f4   => Cell256.flip4
  | .f5   => Cell256.flip5
  | .f6   => Cell256.flip6
  | .yin  => Cell256.yin
  | .tou  => Cell256.tou

def applyL1Left (af : AtomicFlip) : L1 → L1 := fun (a, b) => (af.apply a, b)
def applyL1Right (af : AtomicFlip) : L1 → L1 := fun (a, b) => (a, af.apply b)
end AtomicFlip

/-! ## Octant decomposition (沿 8 atomic flips) -/

/-- octantIndex via the parity of which-atomic-flip-applied-to-which-side.
    Using the 3 lowest bits of (Cell256.toFin a ⊕ Cell256.toFin b) as octant. -/
def octantIndex (l : L1) : Fin 8 := ...   -- explicit definition

def octant (i : Fin 8) : Set L1 := { l | octantIndex l = i }

theorem octant_partition : ∀ l, ∃! i, l ∈ octant i := by
  intro l; refine ⟨octantIndex l, rfl, ?_⟩; intro j hj; exact hj.symm

theorem octant_card (i : Fin 8) :
    Set.ncard (octant i) = 65536 / 8 := by
  -- 用 group-theoretic argument: octant 是 L1 / 之子群之 coset；
  -- 不走 native_decide 全枚举。
  sorry  -- placeholder; 见 §7.2 fallback

/-! ## Acceptance examples -/

example (l : L1) : swap (swap l) = l := swap_swap l
example (c : Cell256) : proj1 (diag c) = c := rfl

end SSBX.Foundation.Squaring.L1
```

### 5.3 RetractTower.lean

```lean
/-
# Retract Tower — R-梯之 lift/project pair 升塔到 L₁ 内

每个 (lift_n, proj_n) ∈ R-hierarchy 之 retract pair 升塔到 L 之
(lift_n × lift_n, proj_n × proj_n) 之乘积 retract pair。
-/
import SSBX.Foundation.Squaring.L1
import SSBX.Foundation.Hierarchy.LiftProject

namespace SSBX.Foundation.Squaring.RetractTower

open SSBX.Foundation.Squaring.L1
open SSBX.Foundation.Hierarchy.LiftProject

/-! ## 直接 R₈ ↪ L₁ -/

def liftR8toL1 : Cell256 → L1 := L1.diag
def projL1toR8 : L1 → Cell256 := L1.proj1

theorem proj_lift_id_L1 (c : Cell256) : projL1toR8 (liftR8toL1 c) = c := rfl

/-! ## Generic squaring retract -/

def squareRetract {α β : Type} (lift : α → β) (proj : β → α) :
    α × α → β × β
  | (a₁, a₂) => (lift a₁, lift a₂)

def squareProj {α β : Type} (proj : β → α) : β × β → α × α
  | (b₁, b₂) => (proj b₁, proj b₂)

theorem squareProj_squareRetract {α β}
    (lift : α → β) (proj : β → α) (h : ∀ a, proj (lift a) = a) :
    ∀ aa, squareProj proj (squareRetract lift proj aa) = aa := by
  intro ⟨a₁, a₂⟩; simp [squareRetract, squareProj, h]

/-! ## R₀..R₇ ↪ L₁ via L₁.diag ∘ existing-lift -/

def liftR0toL1 (r0 : Unit) : L1 :=
  liftR8toL1 (default : Cell256)  -- canonical anchor = 道
def liftR6toL1 (h : Hexagram) : L1 :=
  liftR8toL1 ⟨h, Shi.dao⟩

-- ... (类似 R₁..R₇)

/-! ## Summary theorem -/

theorem retract_tower_summary :
    (∀ c : Cell256, projL1toR8 (liftR8toL1 c) = c) ∧
    (∀ aa : Cell256 × Cell256,
        squareProj projL1toR8 (squareRetract liftR8toL1 projL1toR8 aa) = aa) :=
  ⟨proj_lift_id_L1, squareProj_squareRetract _ _ proj_lift_id_L1⟩

end SSBX.Foundation.Squaring.RetractTower
```

### 5.4 StreamCarrier.lean

```lean
/-
# Stream Cell256 — coalgebra view

借 Mathlib `Stream'.IsBisimulation` 直接给出 coalgebra structure +
unfold corecursion + bisimulation-based equality。
-/
import Mathlib.Data.Stream.Init
import SSBX.Foundation.Bagua.Cell256

namespace SSBX.Foundation.Squaring.StreamCarrier

open SSBX.Foundation.Bagua.Cell256

abbrev TrajCell : Type := Stream' Cell256

/-! ## Coalgebra structure -/

def step (s : TrajCell) : Cell256 × TrajCell := (s.head, s.tail)

theorem step_cons (c : Cell256) (s : TrajCell) :
    step (c :: s) = (c, s) := rfl

/-! ## Corecursion (unfold) -/

def unfold {X : Type} (f : X → Cell256 × X) : X → TrajCell :=
  Stream'.corec (fun x => (f x).1) (fun x => (f x).2)

theorem unfold_step {X : Type} (f : X → Cell256 × X) (x : X) :
    step (unfold f x) = ((f x).1, unfold f (f x).2) := by
  rfl  -- 由 Stream'.corec_eq

/-! ## Bisimulation (coinduction principle from Mathlib) -/

theorem bisim_eq (R : TrajCell → TrajCell → Prop)
    (h : Stream'.IsBisimulation R) {s t : TrajCell} (hr : R s t) : s = t :=
  Stream'.eq_of_bisim h hr

/-! ## Examples -/

def alwaysReturn (c : Cell256) : TrajCell := Stream'.const c

example : (alwaysReturn ⟨Hexagram.qian, Shi.dao⟩).head =
          ⟨Hexagram.qian, Shi.dao⟩ := rfl

example (c : Cell256) : (alwaysReturn c).tail = alwaysReturn c := by
  rw [alwaysReturn]; exact Stream'.tail_const c

/-- A periodic trajectory: cycles through 4 V₄ Shi states keeping qian fixed. -/
def shiCycle : TrajCell :=
  unfold (fun s : Shi => (⟨Hexagram.qian, s⟩, s.cuo)) Shi.dao

end SSBX.Foundation.Squaring.StreamCarrier
```

### 5.5 Coalgebra.lean (M5.0)

```lean
/-
# Endofunctor.Coalgebra — dual mirror of Mathlib `Endofunctor.Algebra`

Mathlib rev `ea11ccc` 没有 `Endofunctor.Coalgebra` 类。本文件镜像
`Mathlib.CategoryTheory.Endofunctor.Algebra` 给出 dual API。
将来可考虑 PR 回 Mathlib。
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Limits.IsLimit

namespace CategoryTheory.Endofunctor

universe v u
variable {C : Type u} [Category.{v} C]

/-- A coalgebra for an endofunctor `F : C ⥤ C` is an object `V` together with
    a "structure map" `str : V ⟶ F.obj V`, dual to `Algebra.str`. -/
structure Coalgebra (F : C ⥤ C) where
  V : C
  str : V ⟶ F.obj V

namespace Coalgebra

variable {F : C ⥤ C}

/-- A morphism between coalgebras commutes with the structure maps:
    A₀.str ≫ F.map f = f ≫ A₁.str. -/
structure Hom (A₀ A₁ : Coalgebra F) where
  f : A₀.V ⟶ A₁.V
  h : A₀.str ≫ F.map f = f ≫ A₁.str := by aesop_cat

attribute [reassoc] Hom.h

def Hom.id (A : Coalgebra F) : Hom A A where
  f := 𝟙 _
  h := by simp

def Hom.comp {A₀ A₁ A₂ : Coalgebra F} (g : Hom A₀ A₁) (h : Hom A₁ A₂) :
    Hom A₀ A₂ where
  f := g.f ≫ h.f
  h := by rw [Functor.map_comp]; rw [← Category.assoc, ← g.h, Category.assoc, h.h, ← Category.assoc]

instance : CategoryStruct (Coalgebra F) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

instance : Category (Coalgebra F) := { }

/-! ## Co-Lambek: structure map of a final coalgebra is iso -/

variable {A : Coalgebra F}

/-- Inverse of `A.str` constructed via universality of `A` as a final coalgebra. -/
noncomputable def strInv (h : Limits.IsTerminal A) : F.obj A.V ⟶ A.V :=
  let c : Coalgebra F := ⟨F.obj A.V, F.map A.str⟩
  (h.from c).f

theorem str_isIso (h : Limits.IsTerminal A) : IsIso A.str := by
  -- mirror of Mathlib.CategoryTheory.Endofunctor.Algebra.str_isIso
  sorry  -- direct dual; see Algebra.str_isIso for template

/-! ## forget functor + reflection of iso -/

def forget (F : C ⥤ C) : Coalgebra F ⥤ C where
  obj A := A.V
  map h := h.f

instance forget_faithful : (forget F).Faithful := { }

end Coalgebra
end CategoryTheory.Endofunctor
```

### 5.6 ProfiniteLimit.lean

```lean
/-
# Profinite Limit — L_∞ ≅ Stream Cell256 with final coalgebra structure

L_n := Cell256 × Cell256 × ⋯ (2^n factors)；
π_n : L_{n+1} → L_n 取 first half；
L_∞ := { f : ∀ n, L_n // ∀ n, π_n (f (n+1)) = f n }；
L_∞ ≅ Stream Cell256 as AddCommGroup；
L_∞ carries final coalgebra structure for `F X = Cell256 × X`。
-/
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.CategoryTheory.Endofunctor.Algebra
import SSBX.Foundation.Squaring.Coalgebra
import SSBX.Foundation.Squaring.StreamCarrier
import SSBX.Foundation.Squaring.RetractTower

namespace SSBX.Foundation.Squaring.ProfiniteLimit

open SSBX.Foundation.Bagua.Cell256
open SSBX.Foundation.Squaring.StreamCarrier

/-! ## L_n as recursive product -/

def L : ℕ → Type
  | 0     => Cell256
  | n + 1 => L n × L n

instance : ∀ n, AddCommGroup (L n)
  | 0     => inferInstance
  | n + 1 => @Prod.instAddCommGroup _ _ (instAddCommGroupL n) (instAddCommGroupL n)

instance : ∀ n, Fintype (L n)
  | 0     => inferInstance
  | n + 1 => @instFintypeProd _ _ (instFintypeL n) (instFintypeL n)

/-! ## Projection π_n : L_{n+1} → L_n -/

def π : ∀ n, L (n + 1) → L n := fun _ => Prod.fst

theorem π_addHom : ∀ n, IsAddHom (π n) := fun _ => ⟨rfl⟩

/-! ## L_inf as inverse limit -/

structure L_inf where
  toFun : ∀ n, L n
  coh : ∀ n, π n (toFun (n + 1)) = toFun n

namespace L_inf

instance : AddCommGroup L_inf where
  zero := ⟨fun _ => 0, fun _ => rfl⟩
  add f g := ⟨fun n => f.toFun n + g.toFun n, fun n => by simp [f.coh, g.coh]⟩
  -- ... other group operations
  ...

end L_inf

/-! ## Iso to Stream Cell256 -/

/-- Build a Stream from L_inf by reading the "leftmost" coordinate at each level. -/
def toStream (f : L_inf) : Stream' Cell256 := fun n => extractLeftmost n (f.toFun n)
  where extractLeftmost : ∀ n, L n → Cell256
    | 0    , c => c
    | _ + 1, p => extractLeftmost _ p.1

/-- Build L_inf from a Stream by recursive duplication. -/
def fromStream (s : Stream' Cell256) : L_inf :=
  ⟨fun n => buildLevel n s, fun n => buildLevel_coherent n s⟩
  where
    buildLevel : ∀ n, Stream' Cell256 → L n := ...
    buildLevel_coherent : ∀ n s, π n (buildLevel (n+1) s) = buildLevel n s := ...

theorem toStream_fromStream (s : Stream' Cell256) : toStream (fromStream s) = s := ...
theorem fromStream_toStream (f : L_inf) : fromStream (toStream f) = f := ...

def isoStream : L_inf ≃+ Stream' Cell256 where
  toFun := toStream
  invFun := fromStream
  left_inv := fromStream_toStream
  right_inv := toStream_fromStream
  map_add' := by intro f g; ext n; rfl

/-! ## Final coalgebra structure -/

def coalg (f : L_inf) : Cell256 × L_inf :=
  let s := isoStream f
  (s.head, isoStream.symm s.tail)

theorem coalg_iso_compat (f : L_inf) :
    let (c, f') := coalg f
    (c, isoStream f') = step (isoStream f) := by
  rfl

/-! ## L_inf is final coalgebra of `F X = Cell256 × X` -/

def funcF : Type → Type := fun X => Cell256 × X

/-- Coalgebra structure on L_inf w.r.t. F. -/
def L_inf_coalg : { c : Coalgebra | True } := ...
  -- packaging as Endofunctor.Coalgebra (from M5.0)

theorem L_inf_isFinalCoalgebra : ... := ...
  -- universal property: ∀ (X, ξ), ∃! morphism (X, ξ) → (L_inf, coalg)
  -- proof: use isoStream + Stream'.corec uniqueness

/-! ## Acceptance examples -/

example (s : Stream' Cell256) : isoStream (isoStream.symm s) = s :=
  isoStream.right_inv s

example (f : L_inf) : (coalg f).1 = (isoStream f).head := rfl

end SSBX.Foundation.Squaring.ProfiniteLimit
```

---

## 6. Day-by-day sprint plan

### Sprint 1 (Week 1) — 有限代数基础

#### Day 1 — M1 V4Tensor

| Hour | Task | Output |
|---|---|---|
| 1 | 设置 `Foundation/Squaring/` namespace + V4Tensor.lean stub | empty file with imports |
| 2 | V4 type + AddCommGroup instance | ~50 LOC |
| 3 | OuterMian abbrev + 第三轴 placeholder doc | ~10 LOC |
| 4-5 | toV4Quad / ofV4Quad mutual inverse | ~80 LOC |
| 6 | iso : Cell256 ≃+ V₄⁴ | ~30 LOC |
| 7 | 4 axis projection convenience | ~30 LOC |
| 8 | acceptance examples + module doc | ~50 LOC |

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

### Sprint 2 (Week 2) — Coalgebra + Profinite

#### Day 6 — M4 StreamCarrier

| Hour | Task | Output |
|---|---|---|
| 1 | TrajCell, step | ~15 LOC |
| 2-3 | unfold via Stream'.corec | ~40 LOC |
| 4 | bisim_eq wrapper | ~20 LOC |
| 5-6 | alwaysReturn, shiCycle examples | ~50 LOC |
| 7 | 与 ℕ → Cell256 之 trivial 双射 | ~30 LOC |
| 8 | doc + acceptance | ~30 LOC |

#### Day 7 — M5.0 Coalgebra

| Hour | Task | Output |
|---|---|---|
| 1 | Coalgebra structure + namespace | ~20 LOC |
| 2 | Hom structure + .id, .comp | ~50 LOC |
| 3 | Category instance | ~40 LOC |
| 4-5 | strInv + str_isIso (Co-Lambek) | ~50 LOC |
| 6 | forget functor + faithful instance | ~30 LOC |
| 7-8 | doc + acceptance + 与 Algebra.lean 对照 | ~40 LOC |

#### Day 8 — M5 ProfiniteLimit Part 1

| Hour | Task | Output |
|---|---|---|
| 1 | L : ℕ → Type 递归定义 | ~10 LOC |
| 2 | AddCommGroup, Fintype instances via induction | ~30 LOC |
| 3 | π projection + IsAddHom | ~20 LOC |
| 4-5 | L_inf structure + AddCommGroup instance | ~80 LOC |
| 6-7 | toStream / fromStream 双向定义 | ~80 LOC |
| 8 | partial commit + 验自适应 | — |

#### Day 9 — M5 ProfiniteLimit Part 2

| Hour | Task | Output |
|---|---|---|
| 1-3 | toStream_fromStream / fromStream_toStream 互逆证明 | ~80 LOC |
| 4 | isoStream : L_inf ≃+ Stream' Cell256 | ~20 LOC |
| 5-6 | coalg : L_inf → Cell256 × L_inf + commute lemma | ~50 LOC |
| 7-8 | L_inf_isFinalCoalgebra 陈述 + 部分证明 | ~50 LOC |

#### Day 10 — M5 完成 + Sprint 2 验收

| Hour | Task |
|---|---|
| 1-2 | 修补 Day 9 卡点 |
| 3-4 | optional: 与 Profinite.asLimit 桥接 |
| 5 | 全套 acceptance examples 跑通 |
| 6 | full `lake build` + 性能审查 |
| 7 | Sprint 2 review |
| 8 | 文档同步 + commit |

**Sprint 2 验收**：见 §8.2。

---

## 7. 风险登记 + fallback

### 7.1 V₄⁴ 之第三轴命名（M1）

**风险**：(y₅, y₆) 命名是 doctrine 决策；当前用 OuterMian 占位可能与未来教义冲突。

**对策**：
- 用 `abbrev OuterMian := V4` 占位
- 提供一个 `name_alias` namespace 在未来一行 rename
- 不阻塞 M2/M3

### 7.2 native_decide 在 |L₁| ≥ 65536 失效（M2）

**风险**：`octant_card` 无法 native_decide 全枚举。

**对策**：
- **首选**：group-theoretic argument — 证 octant 是 L₁ 之某子群之 coset，从而 |coset| = |L₁| / 8 = 8192
- **次选**：拆 8 octant 分别证 cardinality (each ~30 LOC)
- **fallback**：留 sorry 不影响主线推进；后续清理

### 7.3 Mathlib `Profinite.asLimit` 类型论 dance（M5）

**风险**：Profinite 范畴论 wrappers 与原生 Lean 类型之间需要 coercion；可能引入 universe / typeclass 麻烦。

**对策**：
- **首选**：不用 Profinite category 的 wrap，直接用 set-level inverse limit `{ f : ∀ n, L n // coh }`
- **次选**：先证 set-level，再桥接 Profinite category
- **fallback**：set-level 已是完整 deliverable；Profinite.asLimit 桥接是 bonus

### 7.4 Coalgebra.lean co-Lambek 证明（M5.0）

**风险**：`str_isIso` 需要镜像 Algebra.lean 之证明，dual 化中可能遇到 universe / category-theoretic 细节。

**对策**：
- 直接 copy `Algebra.str_isIso` source，逐行 dual 化
- 若卡住，留 sorry 不影响 M5 之 specific instance（M5 用 explicit isoStream，不依赖 abstract co-Lambek）

### 7.5 Lean 4 codata productivity（M4）

**风险**：自定义 corec 可能触发 termination / productivity checker。

**对策**：
- 用 Mathlib `Stream'.corec`，不自己写 corec
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

- [ ] `lake build SSBX.Foundation.Squaring.V4Tensor` 全绿
- [ ] `lake build SSBX.Foundation.Squaring.L1` 全绿
- [ ] `lake build SSBX.Foundation.Squaring.RetractTower` 全绿
- [ ] V4Tensor.lean 内 ≥ 3 个 example 通过（含 native_decide-able 之 1 个）
- [ ] L1.lean 内 ≥ 3 个 example 通过
- [ ] RetractTower.lean 内 ≥ 2 个 retract example 通过（不依赖 sorry）
- [ ] M2 之 `octant_card` 不留 sorry（或如留 sorry 必须 §7.2 对策已记录）
- [ ] 三个文件 line count 在 ±20% 估计范围内
- [ ] full `lake build` 时间增长 < 20%
- [ ] git commit "Sprint 1: M1+M2+M3 — V₄⁴ recast + L₁ + RetractTower"

### 8.2 Sprint 2 验收（M4 + M5.0 + M5）

- [ ] `lake build SSBX.Foundation.Squaring.StreamCarrier` 全绿
- [ ] `lake build SSBX.Foundation.Squaring.Coalgebra` 全绿
- [ ] `lake build SSBX.Foundation.Squaring.ProfiniteLimit` 全绿
- [ ] StreamCarrier.lean 内：alwaysReturn + shiCycle 两个 example 通过
- [ ] Coalgebra.lean 内：Category instance + str_isIso 不留 sorry（或留 sorry 必须 §7.4 对策已记录）
- [ ] ProfiniteLimit.lean 内：isoStream + coalg 两个核心 def 全证（不留 sorry）
- [ ] L_inf_isFinalCoalgebra 至少 statement compile（实际证明可留 sorry 标 followup）
- [ ] **0 axiom 在所有新文件**（grep 确认）
- [ ] full `lake build` 时间增长 < 30%
- [ ] git commit "Sprint 2: M4+M5.0+M5 — Stream + Coalgebra + Profinite Limit"

### 8.3 总体验收

- [ ] 所有 6 个文件 lake build 全绿
- [ ] 总 LOC 1500-1900（±15% 之 ~1700 估计）
- [ ] 0 axiom（无 `axiom` 关键字 in `Foundation/Squaring/`）
- [ ] sorry count ≤ 2（仅 §7 已识别且文档化的）
- [ ] L-tower-plan-v0.2.md 与实际代码一致（最终更新 Status: Implemented）
- [ ] 至少 1 篇 followup doc：`L-tower-implementation-notes.md` 记录 surprises

---

## 9. Decision log

### D1 — squaring projection π = Prod.fst（不是 Prod.snd 或 quotient）

**决策**：π_n : L_{n+1} → L_n 选 `Prod.fst`。

**理由**：
- 与 `L_inf → Stream` 之 head-tail 对齐（每次取 leftmost 等价取 head）
- π = Prod.snd 给 isomorphic 但 mirror 之 limit；选 fst 与 LiftProject 之 proj 选择一致
- 其他 quotient（如 GroupQuotient）会给 different limit，超出本次范围

### D2 — 8-octant 沿 atomic flips（不是 V₄³ 子集）

**决策**：octant 划分沿 R₈ 之 8 atomic flips（flip1..6 + 印 + 投）。

**理由**：
- 与 Yi 之卦语义对齐（单 yao 移动 + 印/投）
- 与 Cell256 之 atomic generators 对应
- V₄³ 子集划分是 group-theoretic 但与 doctrine 隔阂大

### D3 — Coalgebra.lean 自给（不是 axiom）

**决策**：Endofunctor.Coalgebra 类自己写 ~200 LOC（M5.0），不用 axiom 跳过。

**理由**：
- Mathlib 有 Algebra.lean template，~200 LOC 直接镜像
- 0 axiom 路径之最小代价
- bonus：可 PR 回 Mathlib

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

---

## 10. Future work (M6+)

完成 v0.2 全部 6 milestone 后，可启动以下：

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

### M12 — PR Coalgebra.lean 回 Mathlib

完成 M5.0 后，可作为 standalone PR 提交 mathlib4。需要 ~50 LOC 文档调整 + Mathlib style 化。

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

### 11.2 Endofunctor.Algebra

```lean
import Mathlib.CategoryTheory.Endofunctor.Algebra

open CategoryTheory.Endofunctor.Algebra

#check @Algebra              -- structure
#check @Algebra.Hom          -- structure
#check @Algebra.strInv       -- noncomputable def
#check @Algebra.str_isIso    -- 这就是 Lambek
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

完成 v0.2 全部 6 milestone 后产生：

```
formal/SSBX/Foundation/Squaring/
├── V4Tensor.lean        (M1, ~250 LOC)  -- R₈ ≅ V₄⁴
├── L1.lean              (M2, ~500 LOC)  -- L₁ + swap + 8 octant
├── RetractTower.lean    (M3, ~400 LOC)  -- R-梯 升塔到 L₁
├── StreamCarrier.lean   (M4, ~200 LOC)  -- Stream Cell256 + bisim
├── Coalgebra.lean       (M5.0, ~200 LOC) -- Endofunctor.Coalgebra 镜像
└── ProfiniteLimit.lean  (M5, ~350 LOC)  -- L_∞ ≅ Stream + final coalgebra

总: ~1900 LOC（含 doc / acceptance 在内）
```

新顶层 namespace `SSBX.Foundation.Squaring`。

---

## Appendix B — Per-milestone LOC 精算

| Milestone | 估 LOC | 估 days | hours/day | 实际？ |
|---|---|---|---|---|
| M1 V4Tensor | 250 | 1 | 8 | TBD |
| M2 L1 | 500 | 2 | 8 | TBD |
| M3 RetractTower | 400 | 2 | 8 | TBD |
| M4 StreamCarrier | 200 | 1 | 8 | TBD |
| M5.0 Coalgebra | 200 | 1 | 8 | TBD |
| M5 ProfiniteLimit | 350 | 3 | 8 | TBD |
| **小计** | **1900** | **10** | | |
| Doc / glue | (含) | +2 | | |
| **总** | **~1900** | **~12 工作日** | | **2 周 calendar** |

---

## Appendix C — 与既有项目接口

| 既有项目 | 接口点 | 完成 v0.2 后可做 |
|---|---|---|
| MetaInterp Phase A counted-loop | StreamCarrier 之 fuel-bounded 截断 | M4 完成后即可写 1 篇 [counted-loop-as-coalgebra.md](counted-loop-as-coalgebra.md) |
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
3. **是否 PR Coalgebra.lean 回 Mathlib**（M12）
4. **L₁ 内子层是否最终启用 R-index（与 R₈ 闭合冲突）**
5. **Profinite topological structure 是 v0.2 之 nice-to-have 还是 v0.3 之 core**

---

**End of v0.2 plan.**
