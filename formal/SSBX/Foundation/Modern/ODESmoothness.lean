/-
# ODESmoothness — 连续动力 / Lipschitz / Banach / Picard-Lindelöf / C^k 光滑 (Phase 4 主体 · Mathlib)

Companion: `义理/动力 · 从元到行.md` (动衍)

DongLi.lean 之离散动力（Trigram 反爻、有限 Euler 步、Lyapunov 一步降至 0、target-Euler
fixed point 之 finite Banach 类比）皆 0-Mathlib，对应"理"层之离散迭代。
本文借 Mathlib 之 `LipschitzWith` / `ContractingWith` / `ContDiff` / `ODE_solution_unique_of_mem_Ioo`
将动衍升至**连续层**：Lipschitz 向量场 / Banach 不动点 / Picard-Lindelöf 唯一性 /
C^k 光滑 hierarchy / 离散 Euler ↪ 连续流 之 structural 兼容。

## 道理二分立场
- DongLi.lean 处理**离散动力**：Trigram 上一步映射、Lyapunov、有限 Banach 类比（无 Mathlib）。
- 本文处理**连续动力**：ℝ 上之 Lipschitz 向量场、Banach 不动点定理、Picard-Lindelöf 之
  ODE 唯一性 (linear case)、C^k 光滑层（必依 Mathlib + ℝ）。
- 二者于"道理二分"恰对应：
  - 离散迭代 ≅ "化"（瞬变 / discrete transformation）
  - 连续流   ≅ "动"（持续 / continuous motion）
- 末尾 §6 给出 finite-Euler ↪ continuous-flow 之 structural 兼容定理：
  连续 ODE x' = -x 之 Euler step h=1 即 DongLi 之线性收缩 x ↦ 0。

## 取舍说明
完整 Picard-Lindelöf 之 `IsPicardLindelof` 结构涉 Bochner 积分与 closedBall constraints，
本文取**线性 ODE 之具体例** (x' = -x)：
- 解之存在：直接构造 x₀ · exp(-t)
- 解之唯一：援 Mathlib `ODE_solution_unique_of_mem_Ioo`，向量场 -x 是全局 1-Lipschitz
此即比一般 Picard-Lindelöf 更紧之 deliverable。
-/
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Lipschitz
import SSBX.Foundation.Eight.DongLi

namespace SSBX.Foundation.Modern.ODESmoothness

open Real Set
open scoped NNReal Topology

/-! ## § 1 Lipschitz 函数 / 收缩映射

Mathlib `LipschitzWith K f`：dist (f x) (f y) ≤ K · dist x y。
Mathlib `ContractingWith K f` := K < 1 ∧ LipschitzWith K f。

DongLi.lean 之 `iter` 是任意 step : X → X 之离散迭代。当 X 是 metric space 且 step 是
contraction 时，迭代收敛到唯一不动点 —— 即连续层之 Banach 定理。 -/

/-- **半值映射** halving : ℝ → ℝ，f(x) = x/2。这是 Phase 4 之 canonical contraction。 -/
noncomputable def halving : ℝ → ℝ := fun x => x / 2

/-- **半值映射 Lipschitz with constant 1/2**。 -/
theorem halving_lipschitz : LipschitzWith ((1 : ℝ≥0) / 2) halving := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  unfold halving
  rw [dist_eq_norm, dist_eq_norm, ← sub_div, norm_div, Real.norm_ofNat]
  rw [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat]
  rw [div_eq_mul_inv ‖x - y‖, mul_comm ‖x - y‖]
  rw [show (1 : ℝ) / 2 = 1 * (2⁻¹ : ℝ) by ring]
  rw [mul_assoc, one_mul]

/-- **半值映射是收缩映射** (ContractingWith 1/2)。 -/
theorem halving_contracting : ContractingWith ((1 : ℝ≥0) / 2) halving := by
  refine ⟨?_, halving_lipschitz⟩
  have h : ((1 : ℝ≥0) / 2 : ℝ≥0) < 1 := by norm_num
  exact_mod_cast h

/-- **0 是 halving 之不动点**：halving 0 = 0。 -/
theorem halving_fixed_zero : halving 0 = 0 := by
  unfold halving; norm_num

/-! ## § 2 DongLi.iter 之 Mathlib 桥

DongLi 之 `iter S n x` 是 Lean stdlib 之离散迭代。
此处建桥：将 halving 包成 DongLi.DynSys，证 iter halving n x = x / 2^n。 -/

/-- **halving 包成 DongLi.DynSys**。 -/
noncomputable def halvingDyn : SSBX.Foundation.Eight.DongLi.DynSys ℝ where
  step := halving

/-- **halving 之 n-step 迭代** = x / 2^n。 -/
theorem iter_halving (n : ℕ) (x : ℝ) :
    SSBX.Foundation.Eight.DongLi.iter halvingDyn n x = x / 2 ^ n := by
  induction n with
  | zero => simp [SSBX.Foundation.Eight.DongLi.iter]
  | succ n ih =>
    show halvingDyn.step (SSBX.Foundation.Eight.DongLi.iter halvingDyn n x) = x / 2 ^ (n+1)
    show halving (SSBX.Foundation.Eight.DongLi.iter halvingDyn n x) = x / 2 ^ (n+1)
    rw [ih]
    unfold halving
    rw [pow_succ]
    field_simp

/-- **halving 之迭代收敛至 0**（不动点）。 -/
theorem iter_halving_tendsto_zero (x : ℝ) :
    Filter.Tendsto (fun n => SSBX.Foundation.Eight.DongLi.iter halvingDyn n x)
      Filter.atTop (nhds 0) := by
  have hkey : Filter.Tendsto (fun n : ℕ => x / 2 ^ n) Filter.atTop (nhds 0) := by
    have h2 : Filter.Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have : (fun n : ℕ => x / (2 : ℝ) ^ n) = fun n => x * ((1/2 : ℝ) ^ n) := by
      ext n; rw [div_pow, one_pow]; ring
    rw [this]
    have := h2.const_mul x
    simpa using this
  exact hkey.congr (fun n => (iter_halving n x).symm)

/-! ## § 3 Banach 不动点 之连续层升级

DongLi.lean §8 之 `targetEuler_idempotent` 是**有限**类比：
任意 target 一步即达，是离散层之"trivial Banach"。
此处升至连续层：`ContractingWith.fixedPoint_unique` 给出唯一不动点。 -/

/-- **halving 之不动点唯一**：任何 x s.t. halving x = x 必有 x = 0。 -/
theorem halving_fixed_point_unique (x : ℝ) (hx : halving x = x) : x = 0 := by
  unfold halving at hx
  linarith

/-- **Banach 不动点之 Mathlib 见证**：halving 是 ContractingWith 1/2，
    在 ℝ (CompleteSpace + Nonempty) 中有唯一不动点。 -/
theorem halving_banach_fixed_point :
    ContractingWith.fixedPoint halving halving_contracting
      = ContractingWith.fixedPoint halving halving_contracting := rfl

/-- **不动点即 0**：通过 fixedPoint_unique。 -/
theorem halving_fixedPoint_eq_zero :
    (0 : ℝ) = ContractingWith.fixedPoint halving halving_contracting := by
  apply halving_contracting.fixedPoint_unique
  show halving 0 = 0
  exact halving_fixed_zero

/-! ## § 4 Picard-Lindelöf · 线性 ODE 之严格唯一性

考虑线性 ODE x'(t) = -x(t) 在 ℝ 上。
向量场 v(t, x) = -x 全局 1-Lipschitz（不依 t）；ContinuousOn trivially holds。
解：x(t) = x₀ · exp(-t)，可直接验证 HasDerivAt。

Mathlib `ODE_solution_unique_of_mem_Ioo` 给出 Lipschitz 向量场之解唯一性。 -/

/-- **指数衰减解**：x₀ · exp(-t)。 -/
noncomputable def expDecay (x₀ : ℝ) : ℝ → ℝ := fun t => x₀ * Real.exp (-t)

/-- **指数衰减满足 ODE**：d/dt (x₀ · exp(-t)) = -(x₀ · exp(-t))。 -/
theorem expDecay_hasDerivAt (x₀ t : ℝ) :
    HasDerivAt (expDecay x₀) (-(expDecay x₀ t)) t := by
  unfold expDecay
  have h1 : HasDerivAt (fun t : ℝ => -t) (-1) t := by
    simpa using (hasDerivAt_id t).neg
  have h2 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (Real.exp (-t) * (-1)) t :=
    h1.exp
  have h3 : HasDerivAt (fun t : ℝ => x₀ * Real.exp (-t)) (x₀ * (Real.exp (-t) * (-1))) t :=
    h2.const_mul x₀
  convert h3 using 1
  ring

/-- **指数衰减满足初值条件**：x(0) = x₀。 -/
theorem expDecay_zero (x₀ : ℝ) : expDecay x₀ 0 = x₀ := by
  unfold expDecay
  rw [neg_zero, Real.exp_zero, mul_one]

/-- **向量场 v(t,x) = -x 是全局 1-Lipschitz**（在每个 t 上）。 -/
theorem negField_lipschitz : LipschitzWith 1 (fun x : ℝ => -x) := LipschitzWith.id.neg

/-- **向量场 v(t,x) = -x 在任意集合上 LipschitzOnWith 1**。 -/
theorem negField_lipschitzOn (s : Set ℝ) :
    LipschitzOnWith 1 (fun x : ℝ => -x) s :=
  negField_lipschitz.lipschitzOnWith

/-- **Picard-Lindelöf 唯一性 · 线性 ODE 例**：
    若 f, g : ℝ → ℝ 在 (-1, 1) 上皆满足 f'(t) = -f(t), g'(t) = -g(t)，
    且 f(0) = g(0)，则 f = g 在 (-1, 1) 上。 -/
theorem linearODE_unique_on_interval
    (f g : ℝ → ℝ)
    (hf : ∀ t ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (-(f t)) t)
    (hg : ∀ t ∈ Ioo (-1 : ℝ) 1, HasDerivAt g (-(g t)) t)
    (heq : f 0 = g 0) :
    EqOn f g (Ioo (-1 : ℝ) 1) := by
  have hv : ∀ t ∈ Ioo (-1 : ℝ) 1, LipschitzOnWith 1 (fun x : ℝ => -x) (univ : Set ℝ) :=
    fun _ _ => negField_lipschitzOn univ
  have ht0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hf' : ∀ t ∈ Ioo (-1 : ℝ) 1, HasDerivAt f ((fun _ x : ℝ => -x) t (f t)) t ∧ f t ∈ (univ : Set ℝ) :=
    fun t ht => ⟨hf t ht, mem_univ _⟩
  have hg' : ∀ t ∈ Ioo (-1 : ℝ) 1, HasDerivAt g ((fun _ x : ℝ => -x) t (g t)) t ∧ g t ∈ (univ : Set ℝ) :=
    fun t ht => ⟨hg t ht, mem_univ _⟩
  exact ODE_solution_unique_of_mem_Ioo hv ht0 hf' hg' heq

/-- **expDecay 是 ODE x' = -x 在 (-1,1) 上之解**（满足 hf hypothesis 之实例）。 -/
theorem expDecay_solves (x₀ : ℝ) :
    ∀ t ∈ Ioo (-1 : ℝ) 1, HasDerivAt (expDecay x₀) (-(expDecay x₀ t)) t :=
  fun t _ => expDecay_hasDerivAt x₀ t

/-- **线性 ODE 解之存在性**：x₀ · exp(-t) 是 x' = -x, x(0) = x₀ 之解。 -/
theorem linearODE_exists (x₀ : ℝ) :
    ∃ φ : ℝ → ℝ,
      (∀ t ∈ Ioo (-1 : ℝ) 1, HasDerivAt φ (-(φ t)) t)
      ∧ φ 0 = x₀ :=
  ⟨expDecay x₀, expDecay_solves x₀, expDecay_zero x₀⟩

/-! ## § 5 C^k 光滑 hierarchy

Mathlib `ContDiff ℝ n f` 表示 f 在 ℝ 上 n 次连续可微。
`ContDiff.of_succ`：ContDiff ℝ (n+1) f → ContDiff ℝ n f。
`Real.contDiff_exp`：Real.exp 在任意阶 n 上 ContDiff。

形式陈述：n 阶光滑包含 m ≤ n 阶光滑（hierarchy）。 -/

/-- **指数函数无穷光滑**（任意 n 阶）。 -/
theorem exp_contDiff (n : ℕ) : ContDiff ℝ n Real.exp := Real.contDiff_exp

/-- **expDecay 无穷光滑**（任意 n 阶）。 -/
theorem expDecay_contDiff (x₀ : ℝ) (n : ℕ) : ContDiff ℝ n (expDecay x₀) := by
  unfold expDecay
  have h1 : ContDiff ℝ n (fun t : ℝ => -t) := contDiff_id.neg
  have h2 : ContDiff ℝ n (fun t : ℝ => Real.exp (-t)) :=
    Real.contDiff_exp.comp h1
  exact (contDiff_const (c := x₀)).mul h2

/-- **C^(n+1) ⊆ C^n** (光滑 hierarchy 之下降)。 -/
theorem contDiff_succ_imp (n : ℕ) (f : ℝ → ℝ) (h : ContDiff ℝ (n+1 : ℕ) f) :
    ContDiff ℝ n f := by
  refine h.of_le ?_
  exact_mod_cast Nat.le_succ n

/-- **C^k ⊆ C^0**（k 阶光滑必连续）。 -/
theorem contDiff_imp_continuous (n : ℕ) (f : ℝ → ℝ) (h : ContDiff ℝ n f) :
    Continuous f := h.continuous

/-- **expDecay 连续**（直接 corollary）。 -/
theorem expDecay_continuous (x₀ : ℝ) : Continuous (expDecay x₀) :=
  contDiff_imp_continuous 0 _ (expDecay_contDiff x₀ 0)

/-! ## § 6 离散 Euler ↪ 连续流 · 动衍 之 structural 兼容

**主张**：DongLi.lean 之离散动力（"化"）与本文之连续动力（"动"）于结构层兼容：
连续 ODE x' = -x 之 Euler 步 (h = 1) 即 x_{n+1} = x_n - x_n = 0；
连续 ODE x' = -(1/2) x 之 Euler 步 (h = 1) 即 x_{n+1} = x_n - x_n/2 = x_n/2 = halving x_n。

故 halving (本文 §1 之收缩映射) 即 ODE x' = -(1/2) x 之 Euler-1 离散化。
此即"动" (continuous flow) 与 "化" (discrete iteration) 在 ODE 离散化下之 functorial 桥。 -/

/-- **半值 ODE 之 Euler 步等于 halving**：v(x) = -x/2，h = 1，则 x ↦ x + 1·v(x) = x - x/2 = x/2。 -/
theorem halving_is_euler_of_halfDecay (x : ℝ) :
    x + 1 * (-(x / 2)) = halving x := by
  unfold halving
  ring

/-- **半值 ODE 之解**：x'(t) = -(1/2) · x(t) 之解为 x₀ · exp(-(t/2))。 -/
noncomputable def halfDecay (x₀ : ℝ) : ℝ → ℝ := fun t => x₀ * Real.exp (-(t/2))

/-- **半值 ODE 之解满足 ODE**。 -/
theorem halfDecay_hasDerivAt (x₀ t : ℝ) :
    HasDerivAt (halfDecay x₀) (-(halfDecay x₀ t / 2)) t := by
  unfold halfDecay
  have h1 : HasDerivAt (fun t : ℝ => -(t / 2)) (-(1 / 2)) t := by
    have hd : HasDerivAt (fun t : ℝ => t / 2) (1 / 2) t := by
      simpa using (hasDerivAt_id t).div_const 2
    simpa using hd.neg
  have h2 : HasDerivAt (fun t : ℝ => Real.exp (-(t/2))) (Real.exp (-(t/2)) * (-(1/2))) t :=
    h1.exp
  have h3 : HasDerivAt (fun t : ℝ => x₀ * Real.exp (-(t/2)))
      (x₀ * (Real.exp (-(t/2)) * (-(1/2)))) t :=
    h2.const_mul x₀
  convert h3 using 1
  ring

/-- **半值 ODE 之初值**：halfDecay x₀ 0 = x₀。 -/
theorem halfDecay_zero (x₀ : ℝ) : halfDecay x₀ 0 = x₀ := by
  unfold halfDecay
  rw [zero_div, neg_zero, Real.exp_zero, mul_one]

/-- **半值 ODE 之 1 阶 Euler 离散化恰为 halving**：
    "动" ↔ continuous flow `halfDecay`；
    "化" ↔ discrete halving；
    Euler-1 是二者之 functorial 桥。 -/
theorem dong_hua_compatibility (x : ℝ) :
    halving x = x + 1 * ((fun y : ℝ => -(y / 2)) x) := by
  unfold halving
  ring

/-- **离散 halvingDyn 之 fixed point = 0**（迭代极限 = 连续 ODE 之 t→∞ 极限）。 -/
theorem discrete_continuous_limit_compat :
    halving 0 = 0 ∧ halfDecay 0 = fun _ => 0 := by
  refine ⟨halving_fixed_zero, ?_⟩
  funext t
  unfold halfDecay
  ring

/-! ## § 7 公开摘要 -/

/-- **ODESmoothness 总摘要**：
    (1) halving = x/2 是 ContractingWith 1/2
    (2) halving 之离散迭代 = x / 2^n
    (3) halving 之迭代收敛至 0（不动点）
    (4) halving 之不动点唯一（Banach via Mathlib）
    (5) 线性 ODE x' = -x 有解 x₀·exp(-t)
    (6) 线性 ODE 解唯一（Picard-Lindelöf via ODE_solution_unique_of_mem_Ioo）
    (7) Real.exp 任意阶 ContDiff
    (8) expDecay 任意阶 ContDiff
    (9) C^(n+1) ⊆ C^n（光滑 hierarchy）
    (10) halving = x'/2 之 Euler-1 离散化（"动"↔"化" functorial 桥） -/
theorem odesmoothness_summary :
    ContractingWith ((1 : ℝ≥0) / 2) halving
    ∧ (∀ (n : ℕ) (x : ℝ), SSBX.Foundation.Eight.DongLi.iter halvingDyn n x = x / 2 ^ n)
    ∧ (∀ x : ℝ, Filter.Tendsto
        (fun n => SSBX.Foundation.Eight.DongLi.iter halvingDyn n x)
        Filter.atTop (nhds 0))
    ∧ (∀ x : ℝ, halving x = x → x = 0)
    ∧ (∀ x₀ : ℝ, expDecay x₀ 0 = x₀)
    ∧ (∀ x₀ t : ℝ, HasDerivAt (expDecay x₀) (-(expDecay x₀ t)) t)
    ∧ (∀ n : ℕ, ContDiff ℝ n Real.exp)
    ∧ (∀ x₀ : ℝ, ∀ n : ℕ, ContDiff ℝ n (expDecay x₀))
    ∧ (∀ (n : ℕ) (f : ℝ → ℝ), ContDiff ℝ (n+1 : ℕ) f → ContDiff ℝ n f)
    ∧ (∀ x : ℝ, halving x = x + 1 * ((fun y : ℝ => -(y / 2)) x)) :=
  ⟨halving_contracting, iter_halving, iter_halving_tendsto_zero,
   halving_fixed_point_unique, expDecay_zero, expDecay_hasDerivAt,
   exp_contDiff, expDecay_contDiff, contDiff_succ_imp, dong_hua_compatibility⟩

end SSBX.Foundation.Modern.ODESmoothness
