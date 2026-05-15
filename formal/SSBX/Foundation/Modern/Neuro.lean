/-
# Neuro — 连续神经机制 / Sigmoid / tanh / LIF / Hopfield 梯度流 (Phase 4 主体 · Mathlib)

Companion: `义理/心智 · 从元到识.md` § 神经接口（Phase 4 先行）

XinZhi.lean 之 finite Phase 3 已给离散神经元 ≅ Yao、3 神经元 pattern ≅ Trigram、
Hopfield-like attractor 之 finite 8 状态、Hebbian flip transition。
本文借 Mathlib `Real.exp` / `HasDerivAt` / 单调性判定 升至**连续神经层**：
  § 1 sigmoid σ(x) = 1/(1+exp(-x))：定义、严格单调、导数 σ' = σ(1-σ)
  § 2 tanh(x) = (e^x - e^{-x})/(e^x + e^{-x})：定义、严格单调、导数 = 1 - tanh²
  § 3 leaky integrate-and-fire (LIF)：V'(t) = -(V - V_rest)/τ + I(t) 之解 V(t) = V_rest + (V₀-V_rest)·exp(-t/τ)
  § 4 Hopfield 梯度下降之能量单调：E'(x(t)) ≤ 0 由 ∇E·dx/dt = -|∇E|² ≤ 0
  § 5 时间三相 (retention/primal/protention) 之 firing rate → Trigram 经阈值

## 道理二分立场
XinZhi.lean 之 finite 神经层（Bool³ ≅ Trigram、Hebbian flip）在 0-Mathlib 严格证；
本文之**连续动力**（ODE 解、能量梯度、sigmoid 单调）必依 Mathlib + ℝ。
二者于"道理二分"对应：finite 离散同构（理层）对 continuous flow（道层）。

## 策略：直接验证而非存在唯一性
LIF 之解 V(t) 由项目直接构造；通过 `HasDerivAt` 计算验证其满足 ODE，
避免依赖 Picard-Lindelöf 类存在性定理。Hopfield 之能量单调亦由
直接导数计算（梯度流 ⇒ E' = -|∇E|² ≤ 0）证。
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import SSBX.Foundation.Eight.XinZhi

namespace SSBX.Foundation.Modern.Neuro

open Real

/-! ## § 1 Sigmoid 激活函数 σ(x) = 1/(1+exp(-x))

神经元之"软阈值"激活：x → ∞ 时 σ → 1（fire），x → -∞ 时 σ → 0（rest），
σ(0) = 1/2 即"半激活"——心智之"悬置 (XinZ.xuan)" 在连续层之自然对应。 -/

/-- **Sigmoid 函数**：σ(x) = 1/(1 + exp(-x))。 -/
noncomputable def sigmoid (x : ℝ) : ℝ := (1 + Real.exp (-x))⁻¹

/-- **Sigmoid 在零点 = 1/2**（"悬置"对应连续层之中点）。 -/
theorem sigmoid_zero : sigmoid 0 = 1 / 2 := by
  unfold sigmoid
  rw [neg_zero, Real.exp_zero]
  norm_num

/-- **Sigmoid 之分母 1 + exp(-x) > 0**（基础事实）。 -/
theorem sigmoid_denom_pos (x : ℝ) : 0 < 1 + Real.exp (-x) := by
  have : 0 < Real.exp (-x) := Real.exp_pos _
  linarith

/-- **Sigmoid 之分母 ≠ 0**。 -/
theorem sigmoid_denom_ne_zero (x : ℝ) : (1 + Real.exp (-x)) ≠ 0 :=
  ne_of_gt (sigmoid_denom_pos x)

/-- **Sigmoid 严格正值**：σ(x) > 0。 -/
theorem sigmoid_pos (x : ℝ) : 0 < sigmoid x := by
  unfold sigmoid
  exact inv_pos.mpr (sigmoid_denom_pos x)

/-- **Sigmoid 严格小于 1**：σ(x) < 1。 -/
theorem sigmoid_lt_one (x : ℝ) : sigmoid x < 1 := by
  unfold sigmoid
  rw [inv_lt_one_iff₀]
  right
  have : 0 < Real.exp (-x) := Real.exp_pos _
  linarith

/-- **Sigmoid 之 HasDerivAt**：σ'(x) = σ(x)·(1-σ(x))。
    推导：d/dx [(1+e^{-x})⁻¹] = -(-e^{-x})/(1+e^{-x})² = e^{-x}/(1+e^{-x})²
    且 σ(x)·(1-σ(x)) = (1/(1+e^{-x})) · (e^{-x}/(1+e^{-x})) = e^{-x}/(1+e^{-x})²。 -/
theorem hasDerivAt_sigmoid (x : ℝ) :
    HasDerivAt sigmoid (sigmoid x * (1 - sigmoid x)) x := by
  -- d/dx exp(-x) = -exp(-x)
  have h_exp_neg : HasDerivAt (fun y => Real.exp (-y)) (-Real.exp (-x)) x := by
    have h1 : HasDerivAt (fun y : ℝ => -y) (-1 : ℝ) x := (hasDerivAt_id x).neg
    have h2 := h1.exp
    have : Real.exp (-x) * (-1) = -Real.exp (-x) := by ring
    rw [this] at h2
    exact h2
  -- d/dx (1 + exp(-x)) = -exp(-x)
  have h_denom_raw : HasDerivAt (fun y => (fun _ : ℝ => (1 : ℝ)) y + Real.exp (-y))
      (0 + (-Real.exp (-x))) x := (hasDerivAt_const x (1 : ℝ)).add h_exp_neg
  have h_denom : HasDerivAt (fun y => 1 + Real.exp (-y)) (-Real.exp (-x)) x := by
    have hsimp : (0 : ℝ) + (-Real.exp (-x)) = -Real.exp (-x) := by ring
    rw [hsimp] at h_denom_raw
    exact h_denom_raw
  -- d/dx (1+exp(-x))⁻¹ = exp(-x) / (1+exp(-x))²
  have h_inv : HasDerivAt (fun y => (1 + Real.exp (-y))⁻¹)
      (-(-Real.exp (-x)) / (1 + Real.exp (-x))^2) x :=
    h_denom.inv (sigmoid_denom_ne_zero x)
  -- 验证: -(-e^{-x}) / (1+e^{-x})² = sigmoid x · (1 - sigmoid x)
  convert h_inv using 1
  unfold sigmoid
  have hpos : (1 + Real.exp (-x)) ≠ 0 := sigmoid_denom_ne_zero x
  field_simp
  ring

/-- **Sigmoid 之 deriv 形式**。 -/
theorem deriv_sigmoid (x : ℝ) : deriv sigmoid x = sigmoid x * (1 - sigmoid x) :=
  (hasDerivAt_sigmoid x).deriv

/-- **Sigmoid 之导数严格正**（用于单调性）。 -/
theorem deriv_sigmoid_pos (x : ℝ) : 0 < sigmoid x * (1 - sigmoid x) := by
  have h1 : 0 < sigmoid x := sigmoid_pos x
  have h2 : sigmoid x < 1 := sigmoid_lt_one x
  have h3 : 0 < 1 - sigmoid x := by linarith
  exact mul_pos h1 h3

/-- **Sigmoid 严格单调递增**（由导数严格正）。 -/
theorem sigmoid_strictMono : StrictMono sigmoid :=
  strictMono_of_hasDerivAt_pos
    (fun y => hasDerivAt_sigmoid y) (fun y => deriv_sigmoid_pos y)

/-! ## § 2 tanh 激活函数

tanh 为 sigmoid 之 zero-centered 变体；常用于 RNN / LSTM。
项目处直接由 exp 定义，避免 Mathlib `Real.tanh` 之不同 API。 -/

/-- **tanh 函数**：tanh(x) = (e^x - e^{-x})/(e^x + e^{-x})。 -/
noncomputable def tanhN (x : ℝ) : ℝ :=
  (Real.exp x - Real.exp (-x)) / (Real.exp x + Real.exp (-x))

/-- **tanh 之分母 e^x + e^{-x} > 0**。 -/
theorem tanhN_denom_pos (x : ℝ) : 0 < Real.exp x + Real.exp (-x) := by
  have h1 : 0 < Real.exp x := Real.exp_pos _
  have h2 : 0 < Real.exp (-x) := Real.exp_pos _
  linarith

/-- **tanh 之分母 ≠ 0**。 -/
theorem tanhN_denom_ne_zero (x : ℝ) : (Real.exp x + Real.exp (-x)) ≠ 0 :=
  ne_of_gt (tanhN_denom_pos x)

/-- **tanh(0) = 0**（zero-centered）。 -/
theorem tanhN_zero : tanhN 0 = 0 := by
  unfold tanhN
  rw [neg_zero, Real.exp_zero]
  norm_num

/-- **tanh 之 HasDerivAt**：tanh'(x) = 1 - tanh²(x)。
    (e^x + e^{-x})² - (e^x - e^{-x})² = 4 (by 平方差公式) ⇒ 4 / (e^x+e^{-x})²
    与 1 - ((e^x-e^{-x})/(e^x+e^{-x}))² = 4/(e^x+e^{-x})² 一致。 -/
theorem hasDerivAt_tanhN (x : ℝ) :
    HasDerivAt tanhN (1 - (tanhN x)^2) x := by
  -- 分子 num(x) = e^x - e^{-x}, num'(x) = e^x + e^{-x}
  have h_exp_neg_y : HasDerivAt (fun y => Real.exp (-y)) (-Real.exp (-x)) x := by
    have h1 : HasDerivAt (fun y : ℝ => -y) (-1 : ℝ) x := (hasDerivAt_id x).neg
    have h2 := h1.exp
    have : Real.exp (-x) * (-1) = -Real.exp (-x) := by ring
    rw [this] at h2
    exact h2
  have h_exp_y : HasDerivAt (fun y => Real.exp y) (Real.exp x) x :=
    Real.hasDerivAt_exp x
  have h_num : HasDerivAt (fun y => Real.exp y - Real.exp (-y))
      (Real.exp x - (-Real.exp (-x))) x := h_exp_y.sub h_exp_neg_y
  have h_num' : HasDerivAt (fun y => Real.exp y - Real.exp (-y))
      (Real.exp x + Real.exp (-x)) x := by
    have heq : Real.exp x - (-Real.exp (-x)) = Real.exp x + Real.exp (-x) := by ring
    rw [heq] at h_num
    exact h_num
  -- 分母 denom(x) = e^x + e^{-x}, denom'(x) = e^x - e^{-x}
  have h_denom : HasDerivAt (fun y => Real.exp y + Real.exp (-y))
      (Real.exp x + (-Real.exp (-x))) x := h_exp_y.add h_exp_neg_y
  have h_denom' : HasDerivAt (fun y => Real.exp y + Real.exp (-y))
      (Real.exp x - Real.exp (-x)) x := by
    have heq : Real.exp x + (-Real.exp (-x)) = Real.exp x - Real.exp (-x) := by ring
    rw [heq] at h_denom
    exact h_denom
  -- 商法则
  have h_div := h_num'.div h_denom' (tanhN_denom_ne_zero x)
  -- 化简到目标形式
  convert h_div using 1
  unfold tanhN
  have hd : Real.exp x + Real.exp (-x) ≠ 0 := tanhN_denom_ne_zero x
  have hsq : (Real.exp x + Real.exp (-x))^2 ≠ 0 := pow_ne_zero _ hd
  field_simp

/-- **tanh 之 deriv 形式**。 -/
theorem deriv_tanhN (x : ℝ) : deriv tanhN x = 1 - (tanhN x)^2 :=
  (hasDerivAt_tanhN x).deriv

/-- **tanh ∈ (-1, 1)**：|tanh x| < 1。
    证明：(e^x - e^{-x})² < (e^x + e^{-x})²（由 (a-b)² < (a+b)² 当 ab > 0）。 -/
theorem tanhN_sq_lt_one (x : ℝ) : (tanhN x)^2 < 1 := by
  unfold tanhN
  have h1 : 0 < Real.exp x := Real.exp_pos _
  have h2 : 0 < Real.exp (-x) := Real.exp_pos _
  have hd : 0 < Real.exp x + Real.exp (-x) := tanhN_denom_pos x
  have hd2 : 0 < (Real.exp x + Real.exp (-x))^2 := pow_pos hd 2
  rw [div_pow, div_lt_one hd2]
  have key : (Real.exp x - Real.exp (-x))^2 + 4 * (Real.exp x * Real.exp (-x))
      = (Real.exp x + Real.exp (-x))^2 := by ring
  have hxx : 0 < 4 * (Real.exp x * Real.exp (-x)) := by positivity
  linarith

/-- **tanh 之导数严格正**：1 - tanh² > 0。 -/
theorem deriv_tanhN_pos (x : ℝ) : 0 < 1 - (tanhN x)^2 := by
  have := tanhN_sq_lt_one x
  linarith

/-- **tanh 严格单调递增**。 -/
theorem tanhN_strictMono : StrictMono tanhN :=
  strictMono_of_hasDerivAt_pos
    (fun y => hasDerivAt_tanhN y) (fun y => deriv_tanhN_pos y)

/-! ## § 3 Leaky Integrate-and-Fire (LIF) 神经元 ODE

LIF 之膜电位方程：
  τ · V'(t) = -(V(t) - V_rest) + R · I(t)
即 V'(t) = -(V(t) - V_rest)/τ + I(t)/R （此处取 R·I 合记为 I）。

齐次情形（I = 0）解：V(t) = V_rest + (V₀ - V_rest) · exp(-t/τ)。
项目直接验证此候选解满足 ODE，避免依赖 Picard-Lindelöf 之 ODE 存在唯一性。 -/

/-- **LIF 候选解**（齐次情形 I = 0）：V(t) = V_rest + (V₀ - V_rest) · exp(-t/τ)。 -/
noncomputable def lifSolution (V_rest V_0 τ : ℝ) (t : ℝ) : ℝ :=
  V_rest + (V_0 - V_rest) * Real.exp (-t / τ)

/-- **初值条件**：V(0) = V₀。 -/
theorem lifSolution_initial (V_rest V_0 τ : ℝ) :
    lifSolution V_rest V_0 τ 0 = V_0 := by
  unfold lifSolution
  rw [neg_zero, zero_div, Real.exp_zero]
  ring

/-- **LIF 解之 HasDerivAt**：V'(t) = -(V₀ - V_rest)/τ · exp(-t/τ)。 -/
theorem hasDerivAt_lifSolution (V_rest V_0 τ : ℝ) (t : ℝ) :
    HasDerivAt (lifSolution V_rest V_0 τ)
      (-(V_0 - V_rest) / τ * Real.exp (-t / τ)) t := by
  -- d/dt exp(-t/τ) = -1/τ · exp(-t/τ)
  have h_id : HasDerivAt (fun s : ℝ => s) (1 : ℝ) t := hasDerivAt_id t
  have h_neg_div : HasDerivAt (fun s : ℝ => -s / τ) (-1 / τ) t := by
    have h1 : HasDerivAt (fun s : ℝ => -s) (-1 : ℝ) t := h_id.neg
    have h2 : HasDerivAt (fun s : ℝ => -s / τ) (-1 / τ) t := h1.div_const τ
    exact h2
  have h_exp_inner : HasDerivAt (fun s : ℝ => Real.exp (-s / τ))
      (Real.exp (-t / τ) * (-1 / τ)) t := h_neg_div.exp
  -- d/dt [(V₀ - V_rest) · exp(-t/τ)] = (V₀ - V_rest) · (Real.exp (-t/τ) · (-1/τ))
  have h_mul : HasDerivAt (fun s : ℝ => (V_0 - V_rest) * Real.exp (-s / τ))
      ((V_0 - V_rest) * (Real.exp (-t / τ) * (-1 / τ))) t :=
    h_exp_inner.const_mul (V_0 - V_rest)
  -- 加上常数 V_rest
  have h_full : HasDerivAt (fun s : ℝ => V_rest + (V_0 - V_rest) * Real.exp (-s / τ))
      (0 + (V_0 - V_rest) * (Real.exp (-t / τ) * (-1 / τ))) t :=
    (hasDerivAt_const t V_rest).add h_mul
  convert h_full using 1
  ring

/-- **LIF 解满足齐次 ODE**：V'(t) = -(V(t) - V_rest)/τ。
    此即"已构造解直接满足 ODE"之验证；避免存在唯一性依赖。 -/
theorem lifSolution_satisfies_ODE (V_rest V_0 τ : ℝ) (t : ℝ) (hτ : τ ≠ 0) :
    HasDerivAt (lifSolution V_rest V_0 τ)
      (-(lifSolution V_rest V_0 τ t - V_rest) / τ) t := by
  have h := hasDerivAt_lifSolution V_rest V_0 τ t
  convert h using 1
  unfold lifSolution
  field_simp
  ring

/-- **LIF 解趋于 V_rest**（τ > 0 时 t → ∞ 时 V(t) → V_rest）。 -/
theorem lifSolution_tendsto_rest (V_rest V_0 τ : ℝ) (hτ : 0 < τ) :
    Filter.Tendsto (lifSolution V_rest V_0 τ) Filter.atTop (nhds V_rest) := by
  -- exp(-t/τ) → 0
  have h1 : Filter.Tendsto (fun t : ℝ => -t / τ) Filter.atTop Filter.atBot := by
    have hneg : Filter.Tendsto (fun t : ℝ => -t) Filter.atTop Filter.atBot :=
      Filter.tendsto_neg_atTop_atBot
    have : Filter.Tendsto (fun t : ℝ => -t / τ) Filter.atTop Filter.atBot := by
      have hinv : (0 : ℝ) < τ⁻¹ := inv_pos.mpr hτ
      have := hneg.atBot_mul_const hinv
      simpa [div_eq_mul_inv] using this
    exact this
  have h2 : Filter.Tendsto (fun t : ℝ => Real.exp (-t / τ)) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp h1
  -- (V₀ - V_rest) · exp(-t/τ) → 0
  have h3 : Filter.Tendsto (fun t => (V_0 - V_rest) * Real.exp (-t / τ))
      Filter.atTop (nhds ((V_0 - V_rest) * 0)) := h2.const_mul _
  rw [mul_zero] at h3
  -- V_rest + (V₀ - V_rest) · exp(-t/τ) → V_rest + 0 = V_rest
  have h4 : Filter.Tendsto (fun t => V_rest + (V_0 - V_rest) * Real.exp (-t / τ))
      Filter.atTop (nhds (V_rest + 0)) := h3.const_add V_rest
  rw [add_zero] at h4
  exact h4

/-! ## § 4 Hopfield-like 能量梯度下降

连续 Hopfield network 之能量函数：
  E(x) = -½ ∑ᵢⱼ Wᵢⱼ xᵢ xⱼ - ∑ᵢ bᵢ xᵢ
梯度下降动力：x'(t) = -∇E(x(t))。
关键定理：dE/dt = ∇E · x' = -|∇E|² ≤ 0，故 E 沿轨迹单调不增。

项目此节给 1-D 简化版（避免线性代数 / 内积之 setup 复杂）：
  E(x) = -½ w·x² - b·x，∇E(x) = -w·x - b
梯度下降：x'(t) = w·x(t) + b
则 dE/dt(x(t)) = E'(x(t)) · x'(t) = -(x'(t))² ≤ 0。 -/

/-- **1-D Hopfield 能量**：E(x) = -½ w x² - b x。 -/
noncomputable def hopfieldEnergy (w b : ℝ) (x : ℝ) : ℝ :=
  -(1/2) * w * x^2 - b * x

/-- **能量函数之 HasDerivAt**：E'(x) = -w·x - b。 -/
theorem hasDerivAt_hopfieldEnergy (w b : ℝ) (x : ℝ) :
    HasDerivAt (hopfieldEnergy w b) (-w * x - b) x := by
  -- d/dx (-½ w x²) = -w x；d/dx (b x) = b
  have h_id : HasDerivAt (fun y : ℝ => y) (1 : ℝ) x := hasDerivAt_id x
  have h_sq : HasDerivAt (fun y : ℝ => y^2) (2 * x) x := by
    have := h_id.mul h_id
    simpa [pow_two, two_mul] using this
  have h_term1 : HasDerivAt (fun y : ℝ => -(1/2) * w * y^2)
      (-(1/2) * w * (2 * x)) x := h_sq.const_mul (-(1/2) * w)
  have h_term2 : HasDerivAt (fun y : ℝ => b * y) (b * 1) x := h_id.const_mul b
  have h_full : HasDerivAt (fun y : ℝ => -(1/2) * w * y^2 - b * y)
      (-(1/2) * w * (2 * x) - b * 1) x := h_term1.sub h_term2
  have heq : -(1/2 : ℝ) * w * (2 * x) - b * 1 = -w * x - b := by ring
  rw [← heq]
  exact h_full

/-! **梯度流轨迹**：在 1-D Hopfield 上，x(t) 满足 x'(t) = -E'(x(t)) = w·x(t) + b。
    此为给定时刻之"沿梯度流方向"。
    项目处不构造解 x(t)，仅证：若 v 满足 v = -E'(x)，则沿此方向 dE/dx · v = -v² ≤ 0。 -/

/-- **梯度流之关键引理**：dE/dx · (-E'(x)) = -(E'(x))² ≤ 0。
    即"沿负梯度方向之能量变化率 = -(梯度幅度)² ≤ 0"。 -/
theorem hopfield_descent (w b : ℝ) (x : ℝ) :
    let dE := -w * x - b
    dE * (-dE) = -(dE)^2 ∧ -(dE)^2 ≤ 0 := by
  refine ⟨by ring, ?_⟩
  have : 0 ≤ ((-w * x - b))^2 := sq_nonneg _
  linarith

/-- **梯度流轨迹之能量单调下降**：若 x : ℝ → ℝ 满足
    x'(t) = -E'(x(t))（即梯度流），则 d/dt E(x(t)) = -(E'(x(t)))² ≤ 0。 -/
theorem energy_decreasing_along_gradient_flow (w b : ℝ)
    (x : ℝ → ℝ) (t : ℝ) (h : HasDerivAt x (-(-w * (x t) - b)) t) :
    HasDerivAt (fun s => hopfieldEnergy w b (x s))
      (-(-w * (x t) - b)^2) t := by
  -- E'(x(t)) = -w·x(t) - b
  have hE : HasDerivAt (hopfieldEnergy w b) (-w * (x t) - b) (x t) :=
    hasDerivAt_hopfieldEnergy w b (x t)
  -- 链式法则: d/dt E(x(t)) = E'(x(t)) · x'(t)
  have h_chain : HasDerivAt (fun s => hopfieldEnergy w b (x s))
      ((-w * (x t) - b) * (-(-w * (x t) - b))) t := hE.comp t h
  convert h_chain using 1
  ring

/-- **能量沿梯度流非增（值层）**：(-(E')²) ≤ 0 是显然非正。 -/
theorem hopfield_energy_nonincreasing (w b : ℝ) (x : ℝ) :
    -((-w * x - b))^2 ≤ 0 := by
  have : 0 ≤ ((-w * x - b))^2 := sq_nonneg _
  linarith

/-! ## § 5 神经 firing rate 桥接 XinZhi 时间三相 ≅ 三爻

XinZhi.lean § 9 定义 TimePhase = retention / primalImpr / protention，三相 ≅ Trigram 三爻。
本节连续层：每相之"窗口内 firing rate" r ∈ ℝ；阈值 θ 给二值化 r > θ → yang。
故 三相之 (r₁, r₂, r₃) 经阈值 → (Yao₁, Yao₂, Yao₃) → Trigram。 -/

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Eight.XinZhi

/-- **firing rate 经阈值二值化**：r > θ → yang，否则 yin。
    阈值参数 θ 通常取 sigmoid(0) 之"半激活"水平。 -/
noncomputable def rateToYao (θ r : ℝ) : Yao :=
  if r > θ then Yao.yang else Yao.yin

/-- **rate > 阈值 → yang**。 -/
theorem rateToYao_yang_of_gt (θ r : ℝ) (h : r > θ) : rateToYao θ r = Yao.yang := by
  unfold rateToYao; simp [h]

/-- **rate ≤ 阈值 → yin**。 -/
theorem rateToYao_yin_of_le (θ r : ℝ) (h : r ≤ θ) : rateToYao θ r = Yao.yin := by
  unfold rateToYao
  have : ¬ r > θ := not_lt.mpr h
  simp [this]

/-- **三相 firing rates 经阈值 → Trigram**。
    输入：θ 阈值；(r₁, r₂, r₃) 分别对应 retention / primalImpr / protention 之窗口 firing rate。 -/
noncomputable def ratesToTrigram (θ : ℝ) (r1 r2 r3 : ℝ) : Trigram :=
  Trigram.mk (rateToYao θ r1) (rateToYao θ r2) (rateToYao θ r3)

/-- **全 fire 三相 → 乾**：所有 firing rate > θ ⇒ Trigram = 乾。 -/
theorem ratesToTrigram_qian (θ r1 r2 r3 : ℝ)
    (h1 : r1 > θ) (h2 : r2 > θ) (h3 : r3 > θ) :
    ratesToTrigram θ r1 r2 r3 = Trigram.heaven := by
  apply Trigram.ext
  · simp [ratesToTrigram, Trigram.heaven, Trigram.y1_mk, rateToYao_yang_of_gt θ r1 h1]
  · simp [ratesToTrigram, Trigram.heaven, Trigram.y2_mk, rateToYao_yang_of_gt θ r2 h2]
  · simp [ratesToTrigram, Trigram.heaven, Trigram.y3_mk, rateToYao_yang_of_gt θ r3 h3]

/-- **全 rest 三相 → 坤**：所有 firing rate ≤ θ ⇒ Trigram = 坤。 -/
theorem ratesToTrigram_kun (θ r1 r2 r3 : ℝ)
    (h1 : r1 ≤ θ) (h2 : r2 ≤ θ) (h3 : r3 ≤ θ) :
    ratesToTrigram θ r1 r2 r3 = Trigram.earth := by
  apply Trigram.ext
  · simp [ratesToTrigram, Trigram.earth, Trigram.y1_mk, rateToYao_yin_of_le θ r1 h1]
  · simp [ratesToTrigram, Trigram.earth, Trigram.y2_mk, rateToYao_yin_of_le θ r2 h2]
  · simp [ratesToTrigram, Trigram.earth, Trigram.y3_mk, rateToYao_yin_of_le θ r3 h3]

/-- **桥接到 XinZhi.TimePhase.proj**：三相投影 = 阈值化之回收。
    形式：rate r 之阈值化 = 直接给定 Yao 之"恒等" projection——
    即（在 fixed Trigram 下）TimePhase.proj 与 rateToYao 经过相同 (r1,r2,r3) 一致。 -/
theorem ratesToTrigram_proj_retention (θ r1 r2 r3 : ℝ) :
    TimePhase.proj (ratesToTrigram θ r1 r2 r3) TimePhase.retention = rateToYao θ r1 := rfl

theorem ratesToTrigram_proj_primalImpr (θ r1 r2 r3 : ℝ) :
    TimePhase.proj (ratesToTrigram θ r1 r2 r3) TimePhase.primalImpr = rateToYao θ r2 := rfl

theorem ratesToTrigram_proj_protention (θ r1 r2 r3 : ℝ) :
    TimePhase.proj (ratesToTrigram θ r1 r2 r3) TimePhase.protention = rateToYao θ r3 := rfl

/-- **sigmoid 阈值化对应**：σ(x) > 1/2 ⟺ x > 0。
    心智之"悬置"（sigmoid 1/2）即 firing rate 之零点；阴阳由 σ(x) - 1/2 之符号定。 -/
theorem sigmoid_gt_half_iff (x : ℝ) : sigmoid x > 1/2 ↔ x > 0 := by
  constructor
  · intro h
    by_contra hc
    have hc' : x ≤ 0 := not_lt.mp hc
    have := sigmoid_strictMono.le_iff_le.mpr hc'
    rw [sigmoid_zero] at this
    linarith
  · intro h
    have := sigmoid_strictMono h
    rw [sigmoid_zero] at this
    exact this

/-! ## § 6 公开摘要 -/

/-- **Neuro 总摘要**：
    (1) sigmoid(0) = 1/2（悬置对应连续中点）
    (2) sigmoid 严格单调
    (3) sigmoid 之导数 = σ(1-σ)（HasDerivAt 形式）
    (4) tanh(0) = 0（zero-centered）
    (5) tanh 严格单调
    (6) tanh 之导数 = 1 - tanh²（HasDerivAt 形式）
    (7) LIF 解 V(0) = V₀（初值）
    (8) LIF 解满足齐次 ODE（τ ≠ 0 时）
    (9) LIF 解 t → ∞ 时趋于 V_rest（τ > 0 时）
    (10) Hopfield 能量梯度流之能量沿轨迹下降（dE/dt = -|∇E|² ≤ 0）
    (11) firing rates 经阈值 → Trigram（连续层接 XinZhi 三爻） -/
theorem neuro_summary :
    (sigmoid 0 = 1 / 2)
    ∧ StrictMono sigmoid
    ∧ (∀ x, HasDerivAt sigmoid (sigmoid x * (1 - sigmoid x)) x)
    ∧ (tanhN 0 = 0)
    ∧ StrictMono tanhN
    ∧ (∀ x, HasDerivAt tanhN (1 - (tanhN x)^2) x)
    ∧ (∀ V_rest V_0 τ, lifSolution V_rest V_0 τ 0 = V_0)
    ∧ (∀ V_rest V_0 τ t, τ ≠ 0 → HasDerivAt (lifSolution V_rest V_0 τ)
        (-(lifSolution V_rest V_0 τ t - V_rest) / τ) t)
    ∧ (∀ V_rest V_0 τ, 0 < τ →
        Filter.Tendsto (lifSolution V_rest V_0 τ) Filter.atTop (nhds V_rest))
    ∧ (∀ w b x : ℝ, -((-w * x - b))^2 ≤ 0)
    ∧ (∀ θ r1 r2 r3 : ℝ, r1 > θ → r2 > θ → r3 > θ →
        ratesToTrigram θ r1 r2 r3 = Trigram.heaven) :=
  ⟨sigmoid_zero, sigmoid_strictMono, hasDerivAt_sigmoid,
   tanhN_zero, tanhN_strictMono, hasDerivAt_tanhN,
   lifSolution_initial, lifSolution_satisfies_ODE,
   lifSolution_tendsto_rest, hopfield_energy_nonincreasing,
   ratesToTrigram_qian⟩

end SSBX.Foundation.Modern.Neuro
