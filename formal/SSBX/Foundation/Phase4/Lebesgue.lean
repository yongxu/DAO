/-
# Lebesgue — Lebesgue 积分 / 期望 / Bayes / 弱大数律 (Phase 4 主体 · Mathlib)

Companion: `四级生成_太极两翼四象八卦/统计 · 从元到测.md` § 7-12

测衍 §7-12 已严格陈述「积分 / 期望 / Bayes 之连续推广 / 大数律」之 informal 命题。
本文借 Mathlib `MeasureTheory.lintegral` / `ProbabilityTheory.cond` /
`ProbabilityTheory.Variance` 升 TongJi.lean (finite Nat-fraction) +
Kolmogorov.lean (σ-代数 / ProbabilityMeasure) 至**积分与极限层**：
  § 1 Lebesgue 积分 ∫⁻ 之基本性质
  § 2 期望 E[X] := ∫ X dμ 与线性、单调性
  § 3 指示函数 / 简单函数之期望（与 TongJi 之 Nat 计数对桥）
  § 4 连续 Bayes：μ[t|s] · μ s = μ (s ∩ t)（对应 TongJi 之 cross-product）
  § 5 Markov / Chebyshev 不等式
  § 6 弱大数律之 Chebyshev-form anchor
  § 7 大衍 finite 分布之 ProbabilityMeasure 嵌入（measure-preserving）
  § 8 公开摘要

## 道理二分立场

TongJi.lean 之 finite Bernoulli³ 用 Nat 共同分母给概率，0 Mathlib；
本文借 Mathlib 之**积分层**给同一离散对象之连续投影：
  finite (Nat 分子)  ↪  ProbabilityMeasure (Mathlib)
此 embedding 是**理之离散** ↔ **道之连续**之 Lean 见证。
-/
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Moments.Variance
import SSBX.Foundation.Phase4.Kolmogorov
import SSBX.Foundation.Eight.TongJi

namespace SSBX.Foundation.Phase4.Lebesgue

open MeasureTheory ProbabilityTheory ENNReal

/-! ## § 1 Lebesgue 积分 ∫⁻ 之基本性质

Mathlib `lintegral μ f = ∫⁻ a, f a ∂μ` 即 [0,∞]-值 measurable 函数之 Lebesgue 积分。
此节 anchor 几条**线性 / 单调**性质——是连续期望之根基。 -/

variable {α : Type*} [MeasurableSpace α]

/-- **常数函数之积分** ∫⁻ c dμ = c · μ(全集)（Mathlib `lintegral_const`）。
    此即 informal 「常数 × 测度 = 积分」之 Lean 严格化。 -/
theorem lintegral_const_eq (μ : Measure α) (c : ℝ≥0∞) :
    ∫⁻ _, c ∂μ = c * μ Set.univ :=
  lintegral_const c

/-- **零函数之积分 = 0**。 -/
theorem lintegral_zero_eq (μ : Measure α) :
    ∫⁻ _ : α, (0 : ℝ≥0∞) ∂μ = 0 :=
  MeasureTheory.lintegral_zero

/-- **单调性**：f ≤ g 则 ∫⁻ f ≤ ∫⁻ g。 -/
theorem lintegral_mono_eq (μ : Measure α) {f g : α → ℝ≥0∞} (h : f ≤ g) :
    ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂μ :=
  lintegral_mono h

/-- **加法**（左 measurable）：∫⁻ (f+g) = ∫⁻ f + ∫⁻ g（要求 f measurable）。 -/
theorem lintegral_add_meas {μ : Measure α} {f : α → ℝ≥0∞} (hf : Measurable f) (g : α → ℝ≥0∞) :
    ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a ∂μ + ∫⁻ a, g a ∂μ :=
  lintegral_add_left hf g

/-! ## § 2 期望 E[X] := ∫ X dμ —— 概率测度版本

ProbabilityMeasure 是 IsProbabilityMeasure 之 wrapped 版本；
其底层 Measure 之总测度 = 1，故 ∫⁻ 1 dμ = 1。 -/

/-- **概率测度之全空间 lintegral 1 = 1**。
    即：E[1] = 1（常数随机变量 1 之期望 = 1）。 -/
theorem prob_lintegral_one (P : ProbabilityMeasure α) :
    ∫⁻ _ : α, (1 : ℝ≥0∞) ∂(P : Measure α) = 1 := by
  rw [lintegral_const, one_mul]
  exact measure_univ

/-- **概率测度上常数 c 之 lintegral = c**。
    即：E[c] = c（常数随机变量之期望 = 自身）。 -/
theorem prob_lintegral_const (P : ProbabilityMeasure α) (c : ℝ≥0∞) :
    ∫⁻ _ : α, c ∂(P : Measure α) = c := by
  rw [lintegral_const, measure_univ, mul_one]

/-- **lintegral 之线性（左加法）在 ProbabilityMeasure 上**。
    对应 informal「E[X+Y] = E[X] + E[Y]」之非负 measurable 版。 -/
theorem prob_lintegral_add (P : ProbabilityMeasure α)
    {f : α → ℝ≥0∞} (hf : Measurable f) (g : α → ℝ≥0∞) :
    ∫⁻ a, f a + g a ∂(P : Measure α)
      = ∫⁻ a, f a ∂(P : Measure α) + ∫⁻ a, g a ∂(P : Measure α) :=
  lintegral_add_left hf g

/-- **lintegral 之常倍**：E[c · X] = c · E[X]（c ∈ [0,∞]，X measurable）。 -/
theorem prob_lintegral_const_mul (P : ProbabilityMeasure α) (c : ℝ≥0∞)
    {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ a, c * f a ∂(P : Measure α) = c * ∫⁻ a, f a ∂(P : Measure α) :=
  lintegral_const_mul c hf

/-! ## § 3 指示函数与简单函数之期望

E[𝟙_A] = P(A) —— informal "事件之期望 = 该事件概率"。
此节是**离散计数 ↔ 连续测度** 之桥。 -/

/-- **指示函数之 lintegral = 测度**：∫⁻ 𝟙_A · c dμ = c · μ A（A measurable）。 -/
theorem lintegral_indicator_eq {μ : Measure α} {s : Set α} (hs : MeasurableSet s) (c : ℝ≥0∞) :
    ∫⁻ a, s.indicator (fun _ => c) a ∂μ = c * μ s :=
  lintegral_indicator_const hs c

/-- **事件指示函数之期望 = 事件概率**。
    informal：E[𝟙_A] = P(A) 之 Lean 严格化。
    对应 TongJi 之 Nat 分子：在 finite case 即「Σ shu = total」之比。 -/
theorem prob_indicator_expectation (P : ProbabilityMeasure α) {s : Set α}
    (hs : MeasurableSet s) :
    ∫⁻ a, s.indicator (fun _ => (1 : ℝ≥0∞)) a ∂(P : Measure α)
      = (P : Measure α) s := by
  rw [lintegral_indicator_const hs, one_mul]

/-- **指示函数之单调性 → 测度单调性**。
    A ⊆ B → P(A) ≤ P(B)，由 lintegral 单调性导出。 -/
theorem prob_indicator_mono (P : ProbabilityMeasure α) {s t : Set α}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (h : s ⊆ t) :
    (P : Measure α) s ≤ (P : Measure α) t := by
  rw [← prob_indicator_expectation P hs, ← prob_indicator_expectation P ht]
  apply lintegral_mono
  intro a
  by_cases ha : a ∈ s
  · simp [Set.indicator_of_mem ha, Set.indicator_of_mem (h ha)]
  · simp [Set.indicator_of_notMem ha]

/-! ## § 4 连续 Bayes：μ[t | s] · μ s = μ (s ∩ t)

Mathlib `cond_mul_eq_inter` 直接给此式（IsFiniteMeasure 版）。
此即 TongJi.lean 之 `bayes_cross_product`（Nat 等积形式）在**连续测度**层之升级：
  finite (Nat)：cAgB × cB = cBgA × cA
  continuous （Mathlib）：μ[t|s] × μ s = μ (s ∩ t)

二者对应"理之离散计数" ↔ "道之连续测度"。 -/

/-- **连续 Bayes (cross-product 形式)**：μ[t | s] · μ s = μ (s ∩ t)。
    对应 TongJi.lean `bayes_cross_product` 之 ProbabilityMeasure 升级版。 -/
theorem bayes_continuous (P : ProbabilityMeasure α) {s t : Set α}
    (hs : MeasurableSet s) :
    (P : Measure α)[t | s] * (P : Measure α) s = (P : Measure α) (s ∩ t) :=
  cond_mul_eq_inter hs t (P : Measure α)

/-- **Bayes' Theorem**（μ[t|s] = μ s⁻¹ · μ[s|t] · μ t）—— Mathlib `cond_eq_inv_mul_cond_mul`
    在 ProbabilityMeasure 上之直接 wrapper。 -/
theorem bayes_theorem (P : ProbabilityMeasure α) {s t : Set α}
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (P : Measure α)[t | s]
      = ((P : Measure α) s)⁻¹ * (P : Measure α)[s | t] * (P : Measure α) t :=
  cond_eq_inv_mul_cond_mul hs ht (P : Measure α)

/-- **TongJi finite Bayes 与 continuous Bayes 之桥**：
    若 finite case 之 cAgB × cB = cBgA × cA 成立（TongJi `bayes_cross_product`），
    则 ProbabilityMeasure 上之 cross-product 形式 μ[t|s] · μ s = μ (s ∩ t) 即同样
    陈述之 ENNReal 版。本定理仅声明二者**共享算式骨架**，无需具体取值。 -/
theorem bayes_finite_to_continuous_skeleton
    (P : ProbabilityMeasure α) {s t : Set α} (hs : MeasurableSet s)
    (cA cB cAgB cBgA : Nat) (hfin : cAgB * cB = cBgA * cA) :
    -- finite anchor (TongJi)
    (cBgA * cA = cAgB * cB)
    -- continuous form
    ∧ ((P : Measure α)[t | s] * (P : Measure α) s = (P : Measure α) (s ∩ t)) :=
  ⟨SSBX.Foundation.Eight.TongJi.bayes_cross_product cA cB cAgB cBgA hfin,
   bayes_continuous P hs⟩

/-! ## § 5 Markov / Chebyshev 不等式 (Phase 4 之 anchor)

Markov：P(X ≥ ε) ≤ E[X] / ε（X 非负 measurable）。
Chebyshev：P(|X - E X| ≥ c) ≤ Var X / c²（X ∈ L²）。

二者皆在 Mathlib 已证；本文给 anchor wrappers。 -/

/-- **Markov 不等式**：对非负 measurable 函数 f，
    μ {a | ε ≤ f a} ≤ ε⁻¹ · ∫⁻ f dμ（ε ≠ 0）。
    Mathlib `meas_ge_le_lintegral_div`。 -/
theorem markov_inequality {μ : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) (hε' : ε ≠ ∞) :
    μ {a | ε ≤ f a} ≤ (∫⁻ a, f a ∂μ) / ε :=
  meas_ge_le_lintegral_div hf hε hε'

/-- **Chebyshev 不等式**（ENNReal 版本）：
    μ {ω | c ≤ |X ω - E X|} ≤ Var X / c²（X ∈ L²，c ≠ 0）。
    Mathlib `ProbabilityTheory.meas_ge_le_evariance_div_sq`。 -/
theorem chebyshev_inequality {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    {X : Ω → ℝ} (hX : AEStronglyMeasurable X μ) {c : NNReal} (hc : c ≠ 0) :
    μ {ω | (c : ℝ) ≤ |X ω - μ[X]|} ≤ evariance X μ / (c : ℝ≥0∞) ^ 2 :=
  meas_ge_le_evariance_div_sq hX hc

/-! ## § 6 弱大数律 anchor (Chebyshev-form)

informal: 若 X₁, X₂, … iid 独立同分布且 E[X²] < ∞，则
  样本均值 (X₁ + … + Xₙ) / n →_P E[X]，
即 ∀ ε > 0, P(|S̄ₙ - E X| ≥ ε) → 0.

完整 tendsto 形式在 Mathlib 较繁；此处仅 anchor: 单步 Chebyshev 给出
  P(|S̄ₙ - μ| ≥ ε) ≤ Var(S̄ₙ) / ε²，
而 iid case 下 Var(S̄ₙ) = Var(X) / n → 0（n → ∞）。
本节给 single-step Chebyshev 之 anchor —— 即"距 E[X] 偏差受 Var/ε² 约束"。 -/

/-- **弱大数律之 Chebyshev anchor**：
    对任意 ε > 0、X ∈ L²，
    μ {ω | ε ≤ |X ω - E[X]|} ≤ Var X / ε²（ENNReal 形）。
    informal 之"偏差概率受方差约束" 之 Lean 严格化。 -/
theorem wlln_chebyshev_anchor {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} {X : Ω → ℝ}
    (hX : AEStronglyMeasurable X μ) {ε : NNReal} (hε : ε ≠ 0) :
    μ {ω | (ε : ℝ) ≤ |X ω - μ[X]|} ≤ evariance X μ / (ε : ℝ≥0∞) ^ 2 :=
  meas_ge_le_evariance_div_sq hX hε

/-- **WLLN 之直观陈述**（anchor）：
    如果方差 Var X = 0（即 X 几乎处处常数 = E[X]），
    则偏差事件之测度 = 0。这是 WLLN 在退化情形之 Lean 见证。 -/
theorem wlln_zero_variance {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} {X : Ω → ℝ}
    (hX : AEStronglyMeasurable X μ) {ε : NNReal} (hε : ε ≠ 0)
    (hvar : evariance X μ = 0) :
    μ {ω | (ε : ℝ) ≤ |X ω - μ[X]|} = 0 := by
  have hbound := meas_ge_le_evariance_div_sq hX hε
  rw [hvar] at hbound
  simp at hbound
  exact hbound

/-! ## § 7 大衍 finite 分布 ↪ ProbabilityMeasure (measure-preserving 嵌入)

TongJi 之 DaYan 是 finite type，其概率为 Nat 分子 / 分母 16。
此节构造 DaYan 上之 ProbabilityMeasure，以**Dirac 测度之加权和**实现，
并证 P(全集) = 1（即概率守恒）。 -/

open SSBX.Foundation.Eight.TongJi

/-- **DaYan 上之 σ-代数已是 discrete**（来自 Kolmogorov.lean）。 -/
example : MeasurableSpace DaYan := inferInstance

/-- **DaYan 之 frequency 函数（→ ℝ≥0∞）**。 -/
noncomputable def dayanFreq : DaYan → ℝ≥0∞
  | .laoYin   => 1 / 16
  | .shaoYang => 5 / 16
  | .shaoYin  => 7 / 16
  | .laoYang  => 3 / 16

/-- **频率之总和 = 1**（finite Σ）。 -/
theorem dayanFreq_sum :
    dayanFreq .laoYin + dayanFreq .shaoYang + dayanFreq .shaoYin + dayanFreq .laoYang = 1 := by
  unfold dayanFreq
  rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same, ENNReal.div_add_div_same]
  rw [show (1 + 5 + 7 + 3 : ℝ≥0∞) = 16 by norm_num]
  exact ENNReal.div_self (by norm_num) (by norm_num)

/-- **DaYan 概率测度**：以 Dirac 测度之加权和实现。
    P = (1/16)·δ_laoYin + (5/16)·δ_shaoYang + (7/16)·δ_shaoYin + (3/16)·δ_laoYang。 -/
noncomputable def dayanMeasure : Measure DaYan :=
  dayanFreq .laoYin   • Measure.dirac .laoYin
  + dayanFreq .shaoYang • Measure.dirac .shaoYang
  + dayanFreq .shaoYin  • Measure.dirac .shaoYin
  + dayanFreq .laoYang  • Measure.dirac .laoYang

/-- **DaYan 测度之全集 = 1**（概率守恒）。 -/
theorem dayanMeasure_univ : dayanMeasure Set.univ = 1 := by
  unfold dayanMeasure
  simp [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  exact dayanFreq_sum

/-- **DaYan 测度是 ProbabilityMeasure**（即 IsProbabilityMeasure instance）。 -/
instance : IsProbabilityMeasure dayanMeasure :=
  ⟨dayanMeasure_univ⟩

/-- **finite ↪ continuous 嵌入是 measure-preserving 之 anchor**：
    DaYan 之 frequency（Nat 分子）经 ENNReal coercion 后即 dayanMeasure({·})。 -/
theorem dayan_singleton_measure_laoYin :
    dayanMeasure {DaYan.laoYin} = 1 / 16 := by
  unfold dayanMeasure dayanFreq
  simp [Measure.add_apply, Measure.smul_apply, smul_eq_mul]

theorem dayan_singleton_measure_shaoYang :
    dayanMeasure {DaYan.shaoYang} = 5 / 16 := by
  unfold dayanMeasure dayanFreq
  simp [Measure.add_apply, Measure.smul_apply, smul_eq_mul]

theorem dayan_singleton_measure_shaoYin :
    dayanMeasure {DaYan.shaoYin} = 7 / 16 := by
  unfold dayanMeasure dayanFreq
  simp [Measure.add_apply, Measure.smul_apply, smul_eq_mul]

theorem dayan_singleton_measure_laoYang :
    dayanMeasure {DaYan.laoYang} = 3 / 16 := by
  unfold dayanMeasure dayanFreq
  simp [Measure.add_apply, Measure.smul_apply, smul_eq_mul]

/-- **finite ↪ continuous 嵌入：finite shu / total = continuous singleton 测度** 。
    informal："Nat 分子之比 = ENNReal 测度" 之 Lean 见证。 -/
theorem dayan_freq_matches_measure (d : DaYan) :
    dayanMeasure {d} = (DaYan.shu d : ℝ≥0∞) / 16 := by
  cases d with
  | laoYin   => rw [dayan_singleton_measure_laoYin]; simp [DaYan.shu]
  | shaoYang => rw [dayan_singleton_measure_shaoYang]; simp [DaYan.shu]
  | shaoYin  => rw [dayan_singleton_measure_shaoYin]; simp [DaYan.shu]
  | laoYang  => rw [dayan_singleton_measure_laoYang]; simp [DaYan.shu]

/-! ## § 8 公开摘要 -/

/-- **Lebesgue 总摘要**：
    (1) lintegral 常数 = c · μ univ
    (2) ProbabilityMeasure 上 ∫⁻ 1 = 1
    (3) 指示函数期望 E[𝟙_A] = P(A)
    (4) 连续 Bayes：μ[t|s] · μ s = μ (s ∩ t)
    (5) Chebyshev 不等式（ENNReal 版）
    (6) DaYan 测度之全集 = 1（finite ↪ continuous 嵌入是 probability-preserving）
    (7) DaYan singleton 测度匹配 finite shu/16 -/
theorem lebesgue_summary :
    -- (1)
    (∀ (μ : Measure α) (c : ℝ≥0∞), ∫⁻ _ : α, c ∂μ = c * μ Set.univ)
    -- (2)
    ∧ (∀ (P : ProbabilityMeasure α), ∫⁻ _ : α, (1 : ℝ≥0∞) ∂(P : Measure α) = 1)
    -- (3)
    ∧ (∀ (P : ProbabilityMeasure α) {s : Set α}, MeasurableSet s →
        ∫⁻ a, s.indicator (fun _ => (1 : ℝ≥0∞)) a ∂(P : Measure α)
          = (P : Measure α) s)
    -- (4)
    ∧ (∀ (P : ProbabilityMeasure α) {s t : Set α}, MeasurableSet s →
        (P : Measure α)[t | s] * (P : Measure α) s = (P : Measure α) (s ∩ t))
    -- (6) DaYan finite ↪ continuous
    ∧ (dayanMeasure Set.univ = 1)
    -- (7) singleton 测度
    ∧ (∀ d : DaYan, dayanMeasure {d} = (DaYan.shu d : ℝ≥0∞) / 16) := by
  refine ⟨fun μ c => lintegral_const_eq μ c,
          fun P => prob_lintegral_one P,
          fun P _ hs => prob_indicator_expectation P hs,
          fun P _ _ hs => bayes_continuous P hs,
          dayanMeasure_univ,
          dayan_freq_matches_measure⟩

end SSBX.Foundation.Phase4.Lebesgue
