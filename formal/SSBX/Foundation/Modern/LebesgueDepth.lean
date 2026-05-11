/-
# LebesgueDepth — 测衍深化：MCT / DCT / 完整 WLLN / Fubini (Phase 4 深化 · Mathlib)

Companion: `义理/统计 · 从元到测.md` § 7-12 (深化)

`Modern/Lebesgue.lean` 已建 lintegral 基础（线性 / 单调 / 指示 / 连续 Bayes / Markov-Chebyshev /
Chebyshev-form WLLN anchor），并嵌 finite DaYan 入 ProbabilityMeasure。
本文承之而**深化**——直转 Mathlib 之**测度收敛三定理**与**积分换序定理**：
  § 1 单调收敛定理（MCT）：∫⁻ (sup fₙ) = sup ∫⁻ fₙ
  § 2 控制收敛定理（DCT）：fₙ 受可积上界 g 控制 ∧ fₙ →ᵃᵉ f → ∫⁻ fₙ → ∫⁻ f
  § 3 弱大数律 tendsto-form：方差受控 ⟹ 偏差概率 → 0（Chebyshev squeeze）
  § 4 Fubini-Tonelli：σ-finite 积测度上 ∫⁻ z d(μ.prod ν) = ∫⁻∫⁻ f(x,y) dν dμ
  § 5 DaYan finite 分布之具体 lintegral 计算（finite ↪ continuous 之"实数算"）
  § 6 公开摘要

## 道理二分立场

Modern/Lebesgue.lean 给"积分之代数性质"（线性 / 单调 / Markov / Chebyshev-anchor）；
本文给"积分之**极限性质**"——即"测度极限可以与积分换序"之三大定理（MCT / DCT / Fubini），
并以"概率收敛"（WLLN tendsto-form）作"理之离散偏差"→"道之极限消解"之 Lean 见证。

道：连续之极限通行（MCT, DCT, Fubini）；
理：finite DaYan 之具体 expectation 计算（∫⁻ shu = 21/4，即 84/16）。
二者于 Lebesgue / lintegral 同一框架内并存。
-/
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import SSBX.Foundation.Modern.Lebesgue

namespace SSBX.Foundation.Modern.LebesgueDepth

open MeasureTheory ProbabilityTheory ENNReal Filter Topology

/-! ## § 1 单调收敛定理 (MCT)

informal: 对一列单调递增之非负 measurable 函数 fₙ，
  ∫⁻ (sup_n fₙ) dμ = sup_n ∫⁻ fₙ dμ.
此即 Beppo Levi 之单调收敛定理。

Mathlib `lintegral_iSup` 直接给此式（对 `Measurable` 版本）。
本节给 anchor wrapper，并推 tendsto 形式。 -/

variable {α : Type*} [MeasurableSpace α]

/-- **单调收敛定理 (MCT) — Mathlib `lintegral_iSup` anchor**：
    对单调递增之 measurable 序列 fₙ : α → ℝ≥0∞，
    ∫⁻ (sup_n fₙ) dμ = sup_n ∫⁻ fₙ dμ。

    informal "积分与上确界换序"之 Lean 严格化。 -/
theorem mct_iSup (μ : Measure α) {f : ℕ → α → ℝ≥0∞}
    (hf : ∀ n, Measurable (f n)) (h_mono : Monotone f) :
    ∫⁻ a, ⨆ n, f n a ∂μ = ⨆ n, ∫⁻ a, f n a ∂μ :=
  lintegral_iSup hf h_mono

/-- **MCT — AEMeasurable 版本**：放宽 measurable 假设到 a.e. measurable。 -/
theorem mct_iSup_ae (μ : Measure α) {f : ℕ → α → ℝ≥0∞}
    (hf : ∀ n, AEMeasurable (f n) μ)
    (h_mono : ∀ᵐ x ∂μ, Monotone fun n => f n x) :
    ∫⁻ a, ⨆ n, f n a ∂μ = ⨆ n, ∫⁻ a, f n a ∂μ :=
  lintegral_iSup' hf h_mono

/-- **MCT 之 tendsto 形式**：单调序列之积分 tendsto sup。
    derive 自 `mct_iSup` + `tendsto_atTop_iSup`。 -/
theorem mct_tendsto (μ : Measure α) {f : ℕ → α → ℝ≥0∞}
    (hf : ∀ n, Measurable (f n)) (h_mono : Monotone f) :
    Tendsto (fun n => ∫⁻ a, f n a ∂μ) atTop (𝓝 (∫⁻ a, ⨆ n, f n a ∂μ)) := by
  rw [mct_iSup μ hf h_mono]
  exact tendsto_atTop_iSup (fun m n hmn => lintegral_mono (h_mono hmn))

/-! ## § 2 控制收敛定理 (DCT)

informal: 若 Fₙ →ᵃᵉ f，且 ∀ n, Fₙ ≤ᵃᵉ g 与 ∫⁻ g < ∞，
  则 ∫⁻ Fₙ → ∫⁻ f.
此即 Lebesgue 控制收敛定理。

Mathlib `tendsto_lintegral_of_dominated_convergence` 直接给此式。
本节给 anchor wrapper（measurable 与 AEMeasurable 双版本）。 -/

/-- **控制收敛定理 (DCT) — Mathlib anchor**：
    Fₙ : ℕ → α → ℝ≥0∞ measurable，受可积 g 控制，且 Fₙ →ᵃᵉ f，
    则 ∫⁻ Fₙ → ∫⁻ f. -/
theorem dct_tendsto (μ : Measure α) {F : ℕ → α → ℝ≥0∞} {f : α → ℝ≥0∞}
    (bound : α → ℝ≥0∞) (hF_meas : ∀ n, Measurable (F n))
    (h_bound : ∀ n, F n ≤ᵐ[μ] bound)
    (h_fin : ∫⁻ a, bound a ∂μ ≠ ∞)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) :
    Tendsto (fun n => ∫⁻ a, F n a ∂μ) atTop (𝓝 (∫⁻ a, f a ∂μ)) :=
  tendsto_lintegral_of_dominated_convergence bound hF_meas h_bound h_fin h_lim

/-- **DCT — AEMeasurable 版本**：放宽假设到 a.e. measurable。 -/
theorem dct_tendsto_ae (μ : Measure α) {F : ℕ → α → ℝ≥0∞} {f : α → ℝ≥0∞}
    (bound : α → ℝ≥0∞) (hF_meas : ∀ n, AEMeasurable (F n) μ)
    (h_bound : ∀ n, F n ≤ᵐ[μ] bound)
    (h_fin : ∫⁻ a, bound a ∂μ ≠ ∞)
    (h_lim : ∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) :
    Tendsto (fun n => ∫⁻ a, F n a ∂μ) atTop (𝓝 (∫⁻ a, f a ∂μ)) :=
  tendsto_lintegral_of_dominated_convergence' bound hF_meas h_bound h_fin h_lim

/-- **DCT 之退化情形：常数 zero**。
    若 ∀ n, Fₙ = 0 a.e.，则 ∫⁻ Fₙ → 0。这是 DCT 在零序列之 trivial Lean 见证。 -/
theorem dct_zero_sequence (μ : Measure α) {F : ℕ → α → ℝ≥0∞}
    (hF_zero : ∀ n, F n =ᵐ[μ] (fun _ => 0)) :
    Tendsto (fun n => ∫⁻ a, F n a ∂μ) atTop (𝓝 0) := by
  have hint : ∀ n, ∫⁻ a, F n a ∂μ = 0 := fun n => by
    rw [lintegral_congr_ae (hF_zero n)]
    exact lintegral_zero
  simp only [hint]
  exact tendsto_const_nhds

/-! ## § 3 弱大数律 tendsto-form：Chebyshev squeeze

informal: 若 Xₙ : Ω → ℝ 为 a.e. measurable 序列，方差 Var Xₙ ≤ V/n（一致受控），
  则对任意 ε > 0，
    μ {ω | ε ≤ |Xₙ ω - E[Xₙ]|} ≤ V/(n·ε²) → 0.
即"偏差概率 → 0"——弱大数律之 tendsto 形式。

本节直接由 §5 Chebyshev 不等式 + ENNReal `1/n → 0` squeeze 得出。
此为 WLLN 之**具体 quantitative**版（区别于 Lebesgue.lean § 6 之 single-step anchor）。 -/

/-- **WLLN tendsto-form (scoped, Chebyshev squeeze)**：
    若 Xₙ : ℕ → Ω → ℝ a.e.-measurable，方差 evariance Xₙ μ ≤ V/n（一致），
    则对 ε ≠ 0，μ {ω | ε ≤ |Xₙ - E[Xₙ]|} → 0.

    informal: "样本均值偏差概率 → 0"之 Lean 严格化。
    此处不假设 iid 结构，仅借"方差 → 0"之假设直接 squeeze。 -/
theorem wlln_tendsto_chebyshev_scoped {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} {X : ℕ → Ω → ℝ}
    (hX : ∀ n, AEStronglyMeasurable (X n) μ)
    {ε : NNReal} (hε : ε ≠ 0)
    (V : ℝ≥0∞) (hV : V ≠ ∞)
    (hvar : ∀ n, evariance (X n) μ ≤ V / (n : ℝ≥0∞)) :
    Tendsto (fun n => μ {ω | (ε : ℝ) ≤ |X n ω - μ[X n]|}) atTop (𝓝 0) := by
  -- Chebyshev 给上界 evariance Xₙ / ε² ≤ V/(n·ε²)
  have hεpow : (ε : ℝ≥0∞) ^ 2 ≠ 0 := by
    intro h
    apply hε
    have h1 : (ε : ℝ≥0∞) = 0 :=
      (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h
    exact_mod_cast h1
  -- 上界 fun n => V / n / ε²
  have hbound : ∀ n,
      μ {ω | (ε : ℝ) ≤ |X n ω - μ[X n]|} ≤ V / (n : ℝ≥0∞) / (ε : ℝ≥0∞) ^ 2 := by
    intro n
    have hcheb := meas_ge_le_evariance_div_sq (hX n) hε
    refine hcheb.trans ?_
    gcongr
    exact hvar n
  -- 上界 → 0
  have hε2top : (ε : ℝ≥0∞) ^ 2 ≠ ∞ := by
    apply ENNReal.pow_ne_top
    exact ENNReal.coe_ne_top
  have hVε : V / (ε : ℝ≥0∞) ^ 2 ≠ ∞ := by
    rw [ne_eq, ENNReal.div_eq_top]
    rintro (⟨_, h2⟩ | ⟨h1, _⟩)
    · exact hεpow h2
    · exact hV h1
  -- Bound by larger expression with explicit form `(V/ε²) * (1/n)`
  have hbound2 : ∀ n : ℕ,
      μ {ω | (ε : ℝ) ≤ |X n ω - μ[X n]|} ≤ V / (ε : ℝ≥0∞) ^ 2 * (n : ℝ≥0∞)⁻¹ := by
    intro n
    refine (hbound n).trans ?_
    -- V / n / ε² ≤ V / ε² · (1/n)
    -- Both equal V * (n⁻¹) * (ε²)⁻¹ vs V * (ε²)⁻¹ * n⁻¹ — same
    rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
    -- Goal: (ε²)⁻¹ * (n⁻¹ * V) ≤ (ε²)⁻¹ * V * n⁻¹
    rw [mul_comm ((n : ℝ≥0∞)⁻¹) V, ← mul_assoc]
  have hupper : Tendsto (fun n : ℕ => V / (ε : ℝ≥0∞) ^ 2 * (n : ℝ≥0∞)⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ≥0∞)⁻¹) atTop (𝓝 0) :=
      ENNReal.tendsto_inv_nat_nhds_zero
    -- (V/ε²) * m, where m → 0; uses `Tendsto.const_mul` with hb = (Or.inr hVε) since b = 0
    have h2 : Tendsto (fun n : ℕ => V / (ε : ℝ≥0∞) ^ 2 * (n : ℝ≥0∞)⁻¹)
        atTop (𝓝 (V / (ε : ℝ≥0∞) ^ 2 * 0)) :=
      ENNReal.Tendsto.const_mul h1 (Or.inr hVε)
    simpa using h2
  -- squeeze: 下界 0 ≤ μ ≤ V/ε² · (1/n) → 0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun _ => bot_le) hbound2

/-- **WLLN tendsto-form 之退化**：若方差为 0，则偏差概率序列恒为 0，从而 → 0。 -/
theorem wlln_tendsto_zero_variance {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} {X : ℕ → Ω → ℝ}
    (hX : ∀ n, AEStronglyMeasurable (X n) μ)
    {ε : NNReal} (hε : ε ≠ 0)
    (hvar : ∀ n, evariance (X n) μ = 0) :
    Tendsto (fun n => μ {ω | (ε : ℝ) ≤ |X n ω - μ[X n]|}) atTop (𝓝 0) := by
  have hzero : ∀ n, μ {ω | (ε : ℝ) ≤ |X n ω - μ[X n]|} = 0 := fun n =>
    SSBX.Foundation.Modern.Lebesgue.wlln_zero_variance (hX n) hε (hvar n)
  simp only [hzero]
  exact tendsto_const_nhds

/-! ## § 4 Fubini-Tonelli 定理：积分换序

informal: 对 σ-finite 测度 μ, ν 与非负 a.e. measurable f : α × β → ℝ≥0∞，
  ∫⁻ z, f z d(μ.prod ν) = ∫⁻ x, ∫⁻ y, f(x,y) dν dμ
  = ∫⁻ y, ∫⁻ x, f(x,y) dμ dν.
即"二重积分换序"。

Mathlib `lintegral_prod` (Tonelli) 直接给此式。本节 anchor + 几个简单计算。 -/

variable {β : Type*} [MeasurableSpace β]

/-- **Fubini-Tonelli (anchor) — Mathlib `lintegral_prod`**：
    σ-finite ν 上之非负 a.e. measurable 函数，二重积分等于迭代积分。 -/
theorem fubini_tonelli (μ : Measure α) (ν : Measure β) [SFinite ν]
    (f : α × β → ℝ≥0∞) (hf : AEMeasurable f (μ.prod ν)) :
    ∫⁻ z, f z ∂(μ.prod ν) = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ :=
  lintegral_prod f hf

/-- **Fubini-Tonelli 之对称版**：先 y 后 x。 -/
theorem fubini_tonelli_symm (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (f : α × β → ℝ≥0∞) (hf : AEMeasurable f (μ.prod ν)) :
    ∫⁻ z, f z ∂(μ.prod ν) = ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν :=
  lintegral_prod_symm f hf

/-- **Fubini 之具体 anchor：积测度上之常数 1 之积分 = μ univ · ν univ**。
    informal: "1 在 (α × β) 上之 lintegral 即 μ × ν 之总测度"。
    derive 自 `lintegral_const` + `Measure.prod_apply` 之 univ 版本。 -/
theorem fubini_const_one (μ : Measure α) (ν : Measure β) [SFinite ν] :
    ∫⁻ _ : α × β, (1 : ℝ≥0∞) ∂(μ.prod ν) = μ Set.univ * ν Set.univ := by
  rw [lintegral_const, one_mul]
  rw [show (Set.univ : Set (α × β)) = (Set.univ : Set α) ×ˢ (Set.univ : Set β) by
    rw [Set.univ_prod_univ]]
  exact Measure.prod_prod _ _

/-- **Fubini 在 ProbabilityMeasure 下：常数 1 之 lintegral = 1**。
    derive 自 `fubini_const_one` + `measure_univ`. -/
theorem fubini_const_one_prob (P : ProbabilityMeasure α) (Q : ProbabilityMeasure β) :
    ∫⁻ _ : α × β, (1 : ℝ≥0∞) ∂((P : Measure α).prod (Q : Measure β)) = 1 := by
  rw [fubini_const_one]
  rw [measure_univ, measure_univ, mul_one]

/-! ## § 5 DaYan finite 分布之具体 lintegral 计算

`Modern/Lebesgue.lean` 已构 dayanMeasure（finite ↪ continuous 嵌入）。
本节给具体**实数算**——E[shu]（即"shu 函数对 dayanMeasure 之期望"）：
  ∫⁻ d, (shu d : ℝ≥0∞) ∂dayanMeasure
    = (1/16)·1 + (5/16)·5 + (7/16)·7 + (3/16)·3
    = (1 + 25 + 49 + 9)/16 = 84/16 = 21/4.

此即"finite 离散分布之期望计算"在 ENNReal lintegral 框架下之**具体 Lean 见证**——
道理二分之 finite-side 实算。 -/

open SSBX.Foundation.Modern.Lebesgue
open SSBX.Foundation.Eight.TongJi

/-- **dayanMeasure 之 lintegral 展开式**：
    任意非负 measurable g : DaYan → ℝ≥0∞，
    ∫⁻ d, g d ∂dayanMeasure
      = (1/16)·g(laoYin) + (5/16)·g(lesserYang) + (7/16)·g(lesserYin) + (3/16)·g(laoYang).

    informal: dayanMeasure 是 Dirac 测度之加权和，故 lintegral 即加权值之和。 -/
theorem dayan_lintegral_expand (g : DaYan → ℝ≥0∞) :
    ∫⁻ d, g d ∂dayanMeasure
      = dayanFreq DaYan.laoYin   * g DaYan.laoYin
      + dayanFreq DaYan.lesserYang * g DaYan.lesserYang
      + dayanFreq DaYan.lesserYin  * g DaYan.lesserYin
      + dayanFreq DaYan.laoYang  * g DaYan.laoYang := by
  unfold dayanMeasure
  rw [lintegral_add_measure, lintegral_add_measure, lintegral_add_measure]
  rw [lintegral_smul_measure, lintegral_smul_measure,
      lintegral_smul_measure, lintegral_smul_measure]
  rw [lintegral_dirac, lintegral_dirac, lintegral_dirac, lintegral_dirac]
  simp [smul_eq_mul]

/-- **shu : DaYan → ℝ≥0∞ 之期望（具体实数算）**：
    ∫⁻ d, (shu d : ℝ≥0∞) ∂dayanMeasure = 84/16.

    具体计算：(1/16)·1 + (5/16)·5 + (7/16)·7 + (3/16)·3 = (1+25+49+9)/16 = 84/16. -/
theorem dayan_lintegral_shu :
    ∫⁻ d, (DaYan.shu d : ℝ≥0∞) ∂dayanMeasure = 84 / 16 := by
  rw [dayan_lintegral_expand]
  unfold dayanFreq DaYan.shu
  -- (1/16)·1 + (5/16)·5 + (7/16)·7 + (3/16)·3
  have h1 : ((1 : ℕ) : ℝ≥0∞) = 1 := by norm_num
  have h5 : ((5 : ℕ) : ℝ≥0∞) = 5 := by norm_num
  have h7 : ((7 : ℕ) : ℝ≥0∞) = 7 := by norm_num
  have h3 : ((3 : ℕ) : ℝ≥0∞) = 3 := by norm_num
  rw [h1, h5, h7, h3]
  -- Convert each `c/16 * c` into a single fraction `(c·c)/16`
  rw [show (1 / 16 : ℝ≥0∞) = 1 * (16⁻¹ : ℝ≥0∞) by rw [ENNReal.div_eq_inv_mul, mul_comm],
      show (5 / 16 : ℝ≥0∞) = 5 * (16⁻¹ : ℝ≥0∞) by rw [ENNReal.div_eq_inv_mul, mul_comm],
      show (7 / 16 : ℝ≥0∞) = 7 * (16⁻¹ : ℝ≥0∞) by rw [ENNReal.div_eq_inv_mul, mul_comm],
      show (3 / 16 : ℝ≥0∞) = 3 * (16⁻¹ : ℝ≥0∞) by rw [ENNReal.div_eq_inv_mul, mul_comm]]
  rw [show (84 : ℝ≥0∞) / 16 = 84 * (16⁻¹ : ℝ≥0∞) by rw [ENNReal.div_eq_inv_mul, mul_comm]]
  ring

/-- **dayanMeasure 之全空间之 lintegral 1 = 1**（一致性 sanity check）。
    derive 自 `prob_lintegral_one` + `dayanMeasure 是 ProbabilityMeasure`。 -/
theorem dayan_lintegral_one :
    ∫⁻ _ : DaYan, (1 : ℝ≥0∞) ∂dayanMeasure = 1 := by
  rw [lintegral_const, one_mul, dayanMeasure_univ]

/-- **dayanMeasure 之常数 c 之 lintegral = c**。 -/
theorem dayan_lintegral_const (c : ℝ≥0∞) :
    ∫⁻ _ : DaYan, c ∂dayanMeasure = c := by
  rw [lintegral_const, dayanMeasure_univ, mul_one]

/-! ## § 6 公开摘要 -/

/-- **LebesgueDepth 总摘要**：
    (1) 单调收敛定理 (MCT)：积分与 sup 换序。
    (2) 控制收敛定理 (DCT)：受控收敛序列之积分换极限。
    (3) WLLN tendsto-form：方差受控 ⟹ 偏差概率 → 0。
    (4) Fubini-Tonelli：σ-finite 上二重积分 = 迭代积分。
    (5) DaYan ∫⁻ shu = 84/16（finite 实算）。
    (6) DaYan ∫⁻ 1 = 1（概率守恒）。 -/
theorem lebesgue_depth_summary :
    -- (1) MCT
    (∀ (μ : Measure α) {f : ℕ → α → ℝ≥0∞}, (∀ n, Measurable (f n)) → Monotone f →
        ∫⁻ a, ⨆ n, f n a ∂μ = ⨆ n, ∫⁻ a, f n a ∂μ)
    -- (2) DCT (statement skeleton: tendsto preserved)
    ∧ (∀ (μ : Measure α) {F : ℕ → α → ℝ≥0∞} {f : α → ℝ≥0∞} (bound : α → ℝ≥0∞),
        (∀ n, Measurable (F n)) →
        (∀ n, F n ≤ᵐ[μ] bound) →
        ∫⁻ a, bound a ∂μ ≠ ∞ →
        (∀ᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) →
        Tendsto (fun n => ∫⁻ a, F n a ∂μ) atTop (𝓝 (∫⁻ a, f a ∂μ)))
    -- (4) Fubini-Tonelli
    ∧ (∀ (μ : Measure α) (ν : Measure β) [SFinite ν]
        (f : α × β → ℝ≥0∞), AEMeasurable f (μ.prod ν) →
        ∫⁻ z, f z ∂(μ.prod ν) = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ)
    -- (5) DaYan E[shu] = 84/16
    ∧ (∫⁻ d, (DaYan.shu d : ℝ≥0∞) ∂dayanMeasure = 84 / 16)
    -- (6) DaYan ∫⁻ 1 = 1
    ∧ (∫⁻ _ : DaYan, (1 : ℝ≥0∞) ∂dayanMeasure = 1) := by
  refine ⟨fun μ _ hf hmono => mct_iSup μ hf hmono,
          fun μ _ _ b hF hbnd hfin hlim => dct_tendsto μ b hF hbnd hfin hlim,
          fun μ ν _ f hf => fubini_tonelli μ ν f hf,
          dayan_lintegral_shu,
          dayan_lintegral_one⟩

end SSBX.Foundation.Modern.LebesgueDepth
