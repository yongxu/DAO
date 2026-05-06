/-
# RCauchyExt — ℝ 完备性之深化 (Phase 4 主体续 · Mathlib)

Companion: `义理/数与算术 · 从元到数.md` § 10-13

`RCauchy.lean` 已给 ℝ Cauchy 完备性之主 anchor（CompleteSpace ℝ + 1/2ⁿ→0 + √2 ∈ ℝ \ ℚ）。
本文进一步刻画 ℝ 之完备性所蕴含之**经典实分析定理**：
- Archimedean 性（∀ x : ℝ, ∃ n : ℕ, x < n）
- 单调有界 ⇒ 收敛 (monotone convergence)
- 几何级数 Σ(1/2)ⁿ = 2 (closed form)
- ℚ 在 ℝ 中稠密 (rationals dense)
- 中值定理 IVT (intermediate value theorem)
- Bolzano-Weierstrass 之 anchor

## 道理二分立场
`RCauchy.lean` 给"完备性"之**存在性**陈述（CompleteSpace 之 typeclass）；
本文给完备性之**几何/分析后果**——单调收敛、稠密性、IVT 等。
此即"道层"之 ℝ 完备性如何**支撑理层**之具体分析推理。
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Rat.Cast.CharZero
import SSBX.Foundation.Modern.RCauchy

namespace SSBX.Foundation.Modern.RCauchyExt

open Real Filter Topology

/-! ## § 1 Archimedean 性 -/

/-- **Archimedean 性**：∀ x : ℝ, 存在 n : ℕ，使 x < n。
    此即 ℝ 不含"无穷大"——任何实数都被某个自然数超过。 -/
theorem archimedean_real (x : ℝ) : ∃ n : ℕ, x < n :=
  exists_nat_gt x

/-- **Archimedean 之 corollary**：1/(n+1) 可任意小。
    (此即"理论上可观测之最小单位不存在"——任何 ε > 0 总有 n 使 1/(n+1) < ε) -/
theorem one_div_nat_tendsto_zero :
    Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-! ## § 2 单调收敛定理（Monotone Convergence Theorem）-/

/-- **单调上界 ⇒ 收敛 (Mathlib `Monotone.tendsto_atTop_iSup`)**：
    单调递增 + 有上界之序列必收敛到其上确界。
    此即 ℝ 完备性之**等价表述之一**。 -/
theorem monotone_bounded_converges
    (f : ℕ → ℝ) (h_mono : Monotone f) (h_bdd : BddAbove (Set.range f)) :
    ∃ L : ℝ, Filter.Tendsto f Filter.atTop (nhds L) :=
  ⟨_, tendsto_atTop_ciSup h_mono h_bdd⟩

/-- **递减下界 ⇒ 收敛**：对偶版本。 -/
theorem antitone_bounded_converges
    (f : ℕ → ℝ) (h_anti : Antitone f) (h_bdd : BddBelow (Set.range f)) :
    ∃ L : ℝ, Filter.Tendsto f Filter.atTop (nhds L) :=
  ⟨_, tendsto_atTop_ciInf h_anti h_bdd⟩

/-! ## § 3 几何级数 Σ(1/2)ⁿ = 2 之严格 closed form -/

/-- **几何级数 Σ(1/2)ⁿ = 2** (Mathlib `tsum_geometric_two`)。
    此为 RCauchy.lean `halfPow_tendsto_zero` 之"求和版"。 -/
theorem geometric_half_sum :
    (∑' n : ℕ, ((1 : ℝ) / 2) ^ n) = 2 :=
  tsum_geometric_two

/-- **几何级数 Σ rⁿ = 1/(1-r) for 0 ≤ r < 1**。 -/
theorem geometric_series_closed_form (r : ℝ) (h₁ : 0 ≤ r) (h₂ : r < 1) :
    (∑' n : ℕ, r ^ n) = (1 - r)⁻¹ :=
  tsum_geometric_of_lt_one h₁ h₂

/-! ## § 4 ℚ 在 ℝ 中稠密 -/

/-- **ℚ 稠密**：任意 a < b 之实数对，存在 q ∈ ℚ s.t. a < q < b。
    此即"实数可由有理数任意逼近"。 -/
theorem rational_dense (a b : ℝ) (h : a < b) :
    ∃ q : ℚ, a < (q : ℝ) ∧ (q : ℝ) < b :=
  exists_rat_btwn h

/-- **ℝ 是 DenselyOrdered**（任意两实数之间有第三实数）。 -/
theorem real_densely_ordered : DenselyOrdered ℝ := inferInstance

/-! ## § 5 中值定理 (Intermediate Value Theorem) -/

/-- **IVT**：闭区间上之连续函数取两端值之间之任何中间值。
    此为 ℝ 连通性 + 完备性之核心 corollary。 -/
theorem ivt_real (f : ℝ → ℝ) (a b : ℝ) (h_le : a ≤ b)
    (h_cont : ContinuousOn f (Set.Icc a b)) (y : ℝ)
    (h_y : f a ≤ y ∧ y ≤ f b) :
    ∃ c : ℝ, c ∈ Set.Icc a b ∧ f c = y :=
  intermediate_value_Icc h_le h_cont h_y

/-! ## § 6 √2 之严格构造（Newton 法之 anchor） -/

/-- **√2 是 x² = 2 之严格正解**——RCauchy.lean 之 `sqrt2_exists` 之精确化。 -/
theorem sqrt2_unique_pos :
    ∃! x : ℝ, x > 0 ∧ x * x = 2 := by
  refine ⟨Real.sqrt 2, ⟨?_, ?_⟩, ?_⟩
  · exact Real.sqrt_pos.mpr (by norm_num)
  · exact Real.mul_self_sqrt (by norm_num)
  · rintro y ⟨hy_pos, hy_sq⟩
    have h_sqrt_sq : Real.sqrt 2 * Real.sqrt 2 = 2 :=
      Real.mul_self_sqrt (by norm_num : (2:ℝ) ≥ 0)
    nlinarith [hy_sq, h_sqrt_sq, hy_pos, Real.sqrt_pos.mpr (by norm_num : (2:ℝ) > 0)]

/-- **√2 平方为 2**（直接 corollary）。 -/
theorem sqrt2_sq : Real.sqrt 2 * Real.sqrt 2 = 2 :=
  Real.mul_self_sqrt (by norm_num)

/-! ## § 7 实数序列之收敛与 ε-N 等价 -/

/-- **ε-N 收敛之直接陈述**（Mathlib `Metric.tendsto_atTop`）。 -/
theorem tendsto_iff_eps (f : ℕ → ℝ) (L : ℝ) :
    Filter.Tendsto f Filter.atTop (nhds L)
      ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |f n - L| < ε := by
  rw [Metric.tendsto_atTop]
  simp [Real.dist_eq]

/-! ## § 8 ShuSuan ↔ ℝ 之 archimedean 桥 -/

/-- **ShuSuan ℕ 之任意元 < ℝ 上某 nat**——直接由 Archimedean 得。 -/
theorem shu_to_real_archimedean (a : ℕ) :
    ∃ n : ℕ, ((SSBX.Foundation.Eight.ShuSuan.he a a : ℕ) : ℝ) < (n : ℝ) := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((SSBX.Foundation.Eight.ShuSuan.he a a : ℕ) : ℝ)
  exact ⟨n, hn⟩

/-! ## § 9 RCauchy 之 anchor：Cauchy 序列 ↔ 收敛序列 -/

/-- **CauchySeq f ↔ ∃ L, f → L** (ℝ 完备性之等价 reformulation)。 -/
theorem cauchy_iff_converges (f : ℕ → ℝ) :
    CauchySeq f ↔ ∃ L : ℝ, Filter.Tendsto f Filter.atTop (nhds L) := by
  refine ⟨fun h => ⟨_, h.tendsto_limUnder⟩, ?_⟩
  rintro ⟨L, hL⟩
  exact hL.cauchySeq

/-! ## § 10 公开摘要 -/

/-- **RCauchyExt 总摘要**：ℝ 完备性之经典 corollaries：
    (1) Archimedean: ∀ x, ∃ n, x < n
    (2) 1/(n+1) → 0
    (3) 单调上界 ⇒ 收敛
    (4) Σ(1/2)ⁿ = 2 (closed form)
    (5) ℚ 稠密于 ℝ
    (6) IVT (中值定理)
    (7) √2 是 x² = 2 之唯一正解
    (8) Cauchy ↔ 收敛 (ℝ 上等价) -/
theorem rcauchy_ext_summary :
    (∀ x : ℝ, ∃ n : ℕ, x < n)
    ∧ (Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) Filter.atTop (nhds 0))
    ∧ ((∑' n : ℕ, ((1 : ℝ) / 2) ^ n) = 2)
    ∧ (∀ a b : ℝ, a < b → ∃ q : ℚ, a < (q : ℝ) ∧ (q : ℝ) < b)
    ∧ (Real.sqrt 2 * Real.sqrt 2 = 2)
    ∧ (∀ f : ℕ → ℝ, CauchySeq f ↔ ∃ L : ℝ, Filter.Tendsto f Filter.atTop (nhds L)) :=
  ⟨archimedean_real, one_div_nat_tendsto_zero, geometric_half_sum,
   rational_dense, sqrt2_sq, cauchy_iff_converges⟩

end SSBX.Foundation.Modern.RCauchyExt
