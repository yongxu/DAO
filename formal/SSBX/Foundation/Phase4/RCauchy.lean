/-
# RCauchy — ℝ Cauchy 完备性 严格 Lean 证 (Phase 4 主体 · Mathlib)

Companion: `四级生成_太极两翼四象八卦/数与算术 · 从元到数.md` § 10

数衍 §10 之 ℝ Cauchy 完备 仅给 informal 证明骨架（§16.5）。
本文借 Mathlib 之 `Real.completeSpace`、`CauchySeq`、`UniformSpace` 给出严格 Lean 证。

## 道理二分立场
- ShuSuan.lean 处理 ℕ / ℤ / 截断减 之**对象层** finite 部分（无 Mathlib）。
- 本文处理 ℝ 之**连续层**（需 Mathlib + ℝ）—— 是 Phase 4 主体之核心 piece。
- 前者无 Mathlib，后者必依 Mathlib —— 二者于"道理二分"恰对应：
  对象之离散 vs 道层之连续。
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import SSBX.Foundation.Eight.ShuSuan

namespace SSBX.Foundation.Phase4.RCauchy

open Real

/-! ## § 1 ℝ 是 Cauchy 完备空间 -/

/-- **ℝ 完备**：ℝ 上每个 Cauchy 序列收敛。
    此即数衍 §10 「Cauchy 完备性公设」之 Lean 见证。 -/
theorem real_complete : CompleteSpace ℝ := inferInstance

/-- **ℝ 上之 Cauchy 序列必收敛**（CauchySeq.tendsto_limUnder 之直接 corollary）。 -/
theorem cauchy_converges (f : ℕ → ℝ) (h : CauchySeq f) :
    ∃ L : ℝ, Filter.Tendsto f Filter.atTop (nhds L) :=
  ⟨_, h.tendsto_limUnder⟩

/-! ## § 2 具体 Cauchy 序列例：1/2ⁿ 之极限 = 0 -/

/-- `1 / 2^n` 序列。 -/
noncomputable def halfPow (n : ℕ) : ℝ := 1 / (2 : ℝ) ^ n

/-- `1 / 2^n → 0`。 -/
theorem halfPow_tendsto_zero :
    Filter.Tendsto halfPow Filter.atTop (nhds 0) := by
  have key : Filter.Tendsto (fun n : ℕ => ((1:ℝ)/2)^n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  refine key.congr (fun n => ?_)
  unfold halfPow
  rw [div_pow, one_pow]

/-! ## § 3 √2 之 Cauchy 构造（Newton 迭代）

经典 informal 证明：x_{n+1} = (x_n + 2/x_n) / 2 → √2，from x_0 = 1。
本文不展开完整 Newton 迭代之 Cauchy 性质（涉及单调收敛）。
仅以 `Real.sqrt 2` 之存在性作 anchor —— Mathlib 已证。 -/

/-- **√2 在 ℝ 中存在**。 -/
theorem sqrt2_exists : ∃ x : ℝ, x * x = 2 ∧ x ≥ 0 :=
  ⟨Real.sqrt 2, Real.mul_self_sqrt (by norm_num), Real.sqrt_nonneg _⟩

/-- **√2 不在 ℚ 中**（需 Mathlib `irrational_sqrt_two`）。 -/
theorem sqrt2_irrational : Irrational (Real.sqrt 2) :=
  Nat.Prime.irrational_sqrt Nat.prime_two

/-! ## § 4 ShuSuan 之 ℕ 与 ℝ 之桥 -/

/-- ℕ → ℝ 之 coercion 是 monoid 同态（trivial wrapper）。 -/
theorem shu_to_real_zero : ((SSBX.Foundation.Eight.ShuSuan.kong : ℕ) : ℝ) = 0 := by
  simp [SSBX.Foundation.Eight.ShuSuan.kong]

theorem shu_to_real_one : ((SSBX.Foundation.Eight.ShuSuan.yi : ℕ) : ℝ) = 1 := by
  simp [SSBX.Foundation.Eight.ShuSuan.yi]

theorem shu_to_real_he (a b : ℕ) :
    ((SSBX.Foundation.Eight.ShuSuan.he a b : ℕ) : ℝ)
      = (a : ℝ) + (b : ℝ) := by
  simp [SSBX.Foundation.Eight.ShuSuan.he]

theorem shu_to_real_chong (a b : ℕ) :
    ((SSBX.Foundation.Eight.ShuSuan.chong a b : ℕ) : ℝ)
      = (a : ℝ) * (b : ℝ) := by
  simp [SSBX.Foundation.Eight.ShuSuan.chong]

/-! ## § 5 公开摘要 -/

/-- **RCauchy 总摘要**：
    (1) ℝ 是 CompleteSpace
    (2) Cauchy 序列必收敛
    (3) 1/2^n → 0（具体例）
    (4) √2 ∈ ℝ
    (5) √2 ∉ ℚ（无理）
    (6) ShuSuan ℕ 之四算与 ℝ 之 coercion 一致 -/
theorem rcauchy_summary :
    (CompleteSpace ℝ)
    ∧ (∀ f : ℕ → ℝ, CauchySeq f → ∃ L : ℝ, Filter.Tendsto f Filter.atTop (nhds L))
    ∧ (Filter.Tendsto halfPow Filter.atTop (nhds 0))
    ∧ (∃ x : ℝ, x * x = 2 ∧ x ≥ 0)
    ∧ (Irrational (Real.sqrt 2))
    ∧ (∀ a b : ℕ, ((SSBX.Foundation.Eight.ShuSuan.he a b : ℕ) : ℝ) = (a : ℝ) + (b : ℝ)) :=
  ⟨real_complete, cauchy_converges, halfPow_tendsto_zero,
   sqrt2_exists, sqrt2_irrational, shu_to_real_he⟩

end SSBX.Foundation.Phase4.RCauchy
