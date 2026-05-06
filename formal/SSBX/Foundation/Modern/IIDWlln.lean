/-
# IIDWlln — IID 弱大数律：Mathlib `iIndepFun` / `IdentDistrib` 桥接 (Phase 4 深化)

Companion: `义理/统计 · 从元到测.md` § WLLN-IID 深化

`Modern/LebesgueDepth.lean` 已构 WLLN tendsto-form scoped 版本——其条件是
"Var Xₙ ≤ V/n（一致受控）"。然此条件**未直接挂载** Mathlib 之
**IID infrastructure**（独立同分布之严格 σ-代数定义）。本文承之而**桥接**：
直引 `ProbabilityTheory.iIndepFun` 与 `ProbabilityTheory.IdentDistrib`，
将"IID + Var X₁ < ∞"严格归约为"Var(S̄ₙ) = Var X₁ / n → 0"，从而落于
LebesgueDepth § 3 之 squeeze。
  § 1 IsIID 谓词包装 Mathlib's `iIndepFun` + pairwise `IdentDistrib`
  § 2 IID 之方差求和：Var(S_n) = n · Var X₁
  § 3 IID 之样本均值方差：Var(S_n/n) = Var X₁ / n
  § 4 IID-aware WLLN tendsto-form：S_n/n → E X₁ in probability
  § 5 退化具体实例：常数 IID（Var = 0 之 trivial WLLN 见证）
  § 6 公开摘要

## 道理二分立场

LebesgueDepth.lean 给"方差 V/n 假设下"之 WLLN 抽象 squeeze；
本文借 Mathlib `iIndepFun`（道：σ-代数独立性）+ `IdentDistrib`（道：分布同型）
**实**化此假设——即"理之 IID 定义"⟹"道之方差 → 0"⟹"道之收敛"。
此即 informal "样本均值依概率收敛于均值"之**完整 Lean 严格化**。

道：iIndepFun + IdentDistrib（独立同分布之 Mathlib 定义）；
理：Var(S_n/n) = V/n（具体方差除 n）；
合：WLLN tendsto-form（tendsto 形之收敛）。
-/
import SSBX.Foundation.Modern.LebesgueDepth
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Variance

namespace SSBX.Foundation.Modern.IIDWlln

open MeasureTheory ProbabilityTheory ENNReal Filter Topology Finset

/-! ## § 1 IsIID 谓词包装

informal: 序列 X : ℕ → Ω → ℝ 是 IID（独立同分布），即
  - 全族 iIndepFun（任意有限子族独立）
  - 任意 i j，X i 与 X j 同分布。

Mathlib 直接给 `iIndepFun` 与 `IdentDistrib` 二者；本节包装为 `IsIID`。 -/

variable {Ω : Type*} [MeasurableSpace Ω]
variable {α : Type*} [MeasurableSpace α]

/-- **IID 谓词**：独立同分布序列 X : ℕ → Ω → α 之 Lean 严格定义。
    - 第一项：全族 `iIndepFun X μ`（任意有限子族独立）；
    - 第二项：任意 i j，X i 与 X j 同分布（`IdentDistrib`）。

    informal: 此即 "iid (independent identically distributed)" 之 Lean 严格化。 -/
def IsIID (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  iIndepFun X μ ∧ ∀ i j, IdentDistrib (X i) (X j) μ μ

variable {μ : Measure Ω}

/-- **IID 蕴含 pairwise 独立**（`iIndepFun.indepFun` 之 Lean 直推）。 -/
theorem IsIID.pairwise_indepFun {X : ℕ → Ω → α} (h : IsIID μ X) :
    Pairwise fun i j => (X i) ⟂ᵢ[μ] (X j) := by
  intro i j hij
  exact h.1.indepFun hij

/-- **IID 蕴含同分布（任意两项）**。 -/
theorem IsIID.same_distrib {X : ℕ → Ω → α} (h : IsIID μ X) (i j : ℕ) :
    IdentDistrib (X i) (X j) μ μ :=
  h.2 i j

/-- **IID 之独立性是 iIndepFun**。 -/
theorem IsIID.indep_family {X : ℕ → Ω → α} (h : IsIID μ X) : iIndepFun X μ :=
  h.1

/-! ## § 2 IID 之方差求和：Var(∑ Xᵢ) = n · Var X₁

informal: 若 X₁, …, Xₙ iid 且 Var X₁ < ∞，则
  Var(X₁ + … + Xₙ) = n · Var X₁.

证明：由独立性 ⟹ pairwise covariance = 0 ⟹ Var(∑Xᵢ) = ∑ Var Xᵢ；
再由同分布 ⟹ Var Xᵢ = Var X₁，故 ∑ Var Xᵢ = n · Var X₁。

Mathlib `ProbabilityTheory.IndepFun.variance_sum` + `IdentDistrib.variance_eq`
即此推导之**直接** anchor。 -/

/-- **IID 之方差求和（finset 形）**：
    若 X : ℕ → Ω → ℝ 是 IID 且 X 0 ∈ L²，对任意 finset s ⊆ ℕ，
    Var(∑ i ∈ s, X i) = (#s : ℝ) · Var(X 0).

    informal: "iid 序列之有限和方差等于个数倍单项方差"之 Lean 严格化。 -/
theorem variance_sum_iid [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (hiid : IsIID μ X) (hL2 : MemLp (X 0) 2 μ) (s : Finset ℕ) :
    variance (∑ i ∈ s, X i) μ = (s.card : ℝ) * variance (X 0) μ := by
  -- step 1: 由 IID ⟹ 各 Xᵢ ∈ L²（同分布之 memLp 转移）
  have hL2_all : ∀ i ∈ s, MemLp (X i) 2 μ := fun i _ =>
    (hiid.same_distrib i 0).symm.memLp_snd hL2
  -- step 2: pairwise IndepFun
  have hpair : Set.Pairwise (s : Set ℕ) fun i j => (X i) ⟂ᵢ[μ] (X j) :=
    (hiid.pairwise_indepFun).set_pairwise (s : Set ℕ)
  -- step 3: 独立性 ⟹ Var(∑) = ∑ Var
  rw [IndepFun.variance_sum hL2_all hpair]
  -- step 4: 同分布 ⟹ ∀ i, Var(Xᵢ) = Var(X₀)
  have hvar_eq : ∀ i ∈ s, variance (X i) μ = variance (X 0) μ := fun i _ =>
    (hiid.same_distrib i 0).variance_eq
  rw [Finset.sum_congr rfl hvar_eq]
  rw [Finset.sum_const, nsmul_eq_mul]

/-- **IID 之方差求和（range 形，简洁版）**：
    Var(∑ i ∈ range n, X i) = n · Var(X 0)。 -/
theorem variance_sum_iid_range [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (hiid : IsIID μ X) (hL2 : MemLp (X 0) 2 μ) (n : ℕ) :
    variance (∑ i ∈ range n, X i) μ = (n : ℝ) * variance (X 0) μ := by
  rw [variance_sum_iid hiid hL2 (range n), Finset.card_range]

/-! ## § 3 IID 之样本均值方差：Var(S_n / n) = Var X₁ / n

informal: S_n := ∑ X_i，则 S_n / n 之方差是
  Var(S_n / n) = (1/n²) · Var S_n = (1/n²) · n · Var X₁ = Var X₁ / n.

证明：由 § 2 + Mathlib `variance_const_mul`（c X 之方差 = c² · Var X）。 -/

/-- **IID 样本均值之方差**：
    Var((1/n) · S_n) = Var(X 0) / n（n ≥ 1）。

    informal: "iid 样本均值方差 = 单项方差 / n"之 Lean 严格化。 -/
theorem variance_sample_mean_iid [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (hiid : IsIID μ X) (hL2 : MemLp (X 0) 2 μ) {n : ℕ} (hn : n ≠ 0) :
    variance (fun ω => (n : ℝ)⁻¹ * (∑ i ∈ range n, X i) ω) μ
      = variance (X 0) μ / (n : ℝ) := by
  -- Var(c · X) = c² · Var X
  have h1 : variance (fun ω => (n : ℝ)⁻¹ * (∑ i ∈ range n, X i) ω) μ
      = ((n : ℝ)⁻¹) ^ 2 * variance (∑ i ∈ range n, X i) μ :=
    variance_const_mul ((n : ℝ)⁻¹) (∑ i ∈ range n, X i) μ
  -- Var(∑) = n · Var X₀
  rw [h1, variance_sum_iid_range hiid hL2]
  -- Algebra: (1/n)² · (n · v) = v / n
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  field_simp

/-! ## § 4 IID-aware WLLN tendsto-form

informal: X iid，Var X₁ = V < ∞，对任意 ε > 0，
  Tendsto (fun n => P{|S_n/n - E X₁| ≥ ε}) atTop (𝓝 0).

证明思路：由 § 3，Var(S_n/n) = V/n；
  由 Chebyshev：P{|S_n/n - E[S_n/n]| ≥ ε} ≤ Var(S_n/n) / ε² = V/(n·ε²) → 0.
注：E[S_n/n] = E X₁（线性 + 同分布），故 informal 条件正是上式。 -/

/-- **IID-aware WLLN tendsto-form**（不显式提 E X₁，仅与 S_n/n 之自身均值偏差）。
    对任意 ε > 0，
    Tendsto (fun n => μ {ω | ε ≤ |S_n/n ω - E[S_n/n]|}) atTop (𝓝 0).

    informal: "样本均值偏差概率 → 0"之 IID 完整 Lean 严格化。 -/
theorem wlln_iid_tendsto [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (hiid : IsIID μ X) (hL2 : MemLp (X 0) 2 μ)
    {ε : NNReal} (hε : ε ≠ 0) :
    Tendsto
      (fun n : ℕ =>
        μ {ω | (ε : ℝ) ≤
          |((n : ℝ)⁻¹ * (∑ i ∈ range n, X i) ω)
            - μ[fun ω' => (n : ℝ)⁻¹ * (∑ i ∈ range n, X i) ω']|})
      atTop (𝓝 0) := by
  -- 定义 S̄ₙ : Ω → ℝ
  set Sbar : ℕ → Ω → ℝ :=
    fun n ω => (n : ℝ)⁻¹ * (∑ i ∈ range n, X i) ω with hSbar
  -- a.e. measurable: 由 hiid + hL2.aestronglyMeasurable
  have hX_meas : ∀ i, AEStronglyMeasurable (X i) μ := fun i =>
    (hiid.same_distrib i 0).symm.aestronglyMeasurable_snd hL2.1
  have hSbar_meas : ∀ n, AEStronglyMeasurable (Sbar n) μ := by
    intro n
    refine AEStronglyMeasurable.const_mul ?_ _
    exact Finset.aestronglyMeasurable_sum _ (fun i _ => hX_meas i)
  -- V := evariance (X 0) μ —— 由 hL2 知 V ≠ ∞
  set V : ℝ≥0∞ := evariance (X 0) μ with hV
  have hV_ne_top : V ≠ ∞ := MemLp.evariance_ne_top hL2
  -- 任 n ≥ 1，evariance(Sbar n) = V / n
  -- 注：variance_sample_mean_iid 给 ℝ-级方差；此处需 ENNReal-级。
  -- 采用 ofReal_variance + Sbar n ∈ L² 之事实。
  have hSbar_L2 : ∀ n, n ≠ 0 → MemLp (Sbar n) 2 μ := by
    intro n hn
    refine MemLp.const_mul ?_ _
    have hsum_lp := memLp_finsetSum (range n)
      (fun i _ => (hiid.same_distrib i 0).symm.memLp_snd hL2 (p := 2))
    -- Coerce `fun a => ∑ ... a` to `∑ ...` (definitionally equal up to η)
    convert hsum_lp using 1
    funext ω
    rw [Finset.sum_apply]
  have hVbound : ∀ n : ℕ, n ≠ 0 → evariance (Sbar n) μ ≤ V / (n : ℝ≥0∞) := by
    intro n hn
    -- 借 ℝ-级 variance 之 (Var(X 0))/n
    have h_eq : variance (Sbar n) μ = variance (X 0) μ / (n : ℝ) :=
      variance_sample_mean_iid hiid hL2 hn
    -- 转 ENNReal: ofReal Var(Sbar n) = ofReal (Var(X0)/n)
    have h_evar : evariance (Sbar n) μ = ENNReal.ofReal (variance (X 0) μ / (n : ℝ)) := by
      rw [← ofReal_variance (hSbar_L2 n hn), h_eq]
    rw [h_evar]
    -- ofReal(V/n) ≤ V/n where V is the ENNReal evariance
    have hV_real : ENNReal.ofReal (variance (X 0) μ) = V :=
      MemLp.ofReal_variance_eq hL2
    -- Var(X 0) ≥ 0
    have hvarnn : 0 ≤ variance (X 0) μ := variance_nonneg _ _
    have hnnn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [ENNReal.ofReal_div_of_pos
        (by exact_mod_cast Nat.pos_of_ne_zero hn : (0 : ℝ) < (n : ℝ))]
    rw [hV_real]
    -- 余下 V / ofReal n = V / n（ENNReal 之 cast 一致性）
    rw [ENNReal.ofReal_natCast n]
  -- ============== 进入 squeeze ==============
  -- 把 evariance bound 转成 LebesgueDepth.wlln_tendsto_chebyshev_scoped 之假设
  -- 该定理之假设 hvar : ∀ n, evariance (X n) μ ≤ V / n
  -- 对 n = 0 时 V/0 = ∞（ENNReal 之 div_zero），故 trivially 满足。
  have hvar_all : ∀ n, evariance (Sbar n) μ ≤ V / (n : ℝ≥0∞) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      -- n = 0：Sbar 0 ω = 0⁻¹ * (∑ ∈ range 0, …) = 0 * 0 = 0，故 evariance = 0
      have hSbar0 : Sbar 0 = 0 := by
        funext ω
        simp [hSbar]
      rw [hSbar0]
      rw [evariance_zero]
      exact bot_le
    · exact hVbound n hn
  -- 应用 LebesgueDepth.wlln_tendsto_chebyshev_scoped
  exact SSBX.Foundation.Modern.LebesgueDepth.wlln_tendsto_chebyshev_scoped
    hSbar_meas hε V hV_ne_top hvar_all

/-! ## § 5 退化具体实例：常数 IID

informal: 任取 c : ℝ，定义 X i ω := c（常数随机变量）。
则：
  - X 之 iIndepFun 平凡（任意 finset 之交集即 universe，乘积亦同）；
  - X 同分布（每项 = δ_c）；
  - Var(X i) = 0；
  - WLLN trivially 成立（偏差概率恒 = 0）。
此为"IID 框架"在最简 case 之 Lean 见证。 -/

/-- **常数 IID 之方差 = 0**。 -/
theorem variance_const (c : ℝ) [IsProbabilityMeasure μ] :
    variance (fun _ : Ω => c) μ = 0 := by
  rw [variance, evariance]
  simp

set_option linter.unusedVariables false in
/-- **常数序列之样本均值偏差概率恒 = 0**（退化 WLLN 见证）。
    若 X i ω := c（常数），对任意 ε > 0、n ≥ 1，
    μ {ω | ε ≤ |S_n/n - E[S_n/n]|} = 0。

    informal: "常数 RV 之样本均值无偏差"之 Lean 见证。 -/
theorem wlln_const_zero (c : ℝ) [IsProbabilityMeasure μ]
    {ε : NNReal} (hε : ε ≠ 0) {n : ℕ} :
    μ {ω : Ω | (ε : ℝ) ≤
      |((n : ℝ)⁻¹ * (∑ _ ∈ range n, c))
        - μ[fun _ : Ω => (n : ℝ)⁻¹ * (∑ _ ∈ range n, c)]|} = 0 := by
  -- 由于 S_n/n 是常数表达式（不依赖 ω），其期望 = 自身，差 = 0。
  have hεpos : (0 : ℝ) < (ε : ℝ) := by
    have hε_nnpos : (0 : NNReal) < ε := lt_of_le_of_ne (by exact bot_le) (Ne.symm hε)
    exact_mod_cast hε_nnpos
  have habs_zero :
      ((n : ℝ)⁻¹ * (∑ _ ∈ range n, c))
        - μ[fun _ : Ω => (n : ℝ)⁻¹ * (∑ _ ∈ range n, c)] = 0 := by
    rw [integral_const, probReal_univ, one_smul, sub_self]
  have hkey : ∀ ω : Ω,
      ¬ ((ε : ℝ) ≤
        |((n : ℝ)⁻¹ * (∑ _ ∈ range n, c))
          - μ[fun _ : Ω => (n : ℝ)⁻¹ * (∑ _ ∈ range n, c)]|) := by
    intro _
    rw [habs_zero, abs_zero]
    exact not_le.mpr hεpos
  have hempty : {ω : Ω | (ε : ℝ) ≤
      |((n : ℝ)⁻¹ * (∑ _ ∈ range n, c))
        - μ[fun _ : Ω => (n : ℝ)⁻¹ * (∑ _ ∈ range n, c)]|} = ∅ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact hkey ω
  rw [hempty]
  exact measure_empty

/-- **常数 IID（finset 形）**：常数序列是 iIndepFun（trivial）。
    即：定义 X i ω := c，则 iIndepFun X μ。

    informal: "常数族独立"之 trivial Lean 见证（任意有限子族之乘积式恒成立）。 -/
theorem isIID_const (c : ℝ) [IsProbabilityMeasure μ] :
    IsIID μ (fun _ : ℕ => fun _ : Ω => c) := by
  refine ⟨?_, ?_⟩
  · -- iIndepFun: 任 finset s, μ (⋂ i ∈ s, fᵢ) = ∏ i ∈ s, μ fᵢ
    -- 借 iIndepFun_iff 展开，注意 comap 之 measurable set 为 {∅, univ}
    rw [iIndepFun_iff]
    intro s f' hf'
    -- (fun _ => c) 之 comap 即 ⊥（const 函数下 measurable set 等价于 univ 或 ∅）
    -- 关键观察：若 ∀ i ∈ s, f' i ∈ {∅, univ}（comap 之 measurable set），
    -- 则 ⋂ 与 ∏ 都化为 universe-style 计算。
    -- 但 const 函数 case 下：MeasurableSpace.comap (fun _ => c) = ⊥
    -- 故 hf' i hi 给出 f' i ∈ {∅, univ}。
    -- 简洁路径：对 s.induction，每步利用 const 之 trivial measurable struct。
    -- 这里采用直接计算：若任一 f' i = ∅，则 LHS 与 RHS 都 = 0；
    -- 否则 ∀ i, f' i = univ，则 LHS = μ univ = 1 = ∏ 1 = RHS。
    -- 但要直接形式化对于 induction 较复杂——用现成 lemma 更简：
    -- 注：`iIndepFun.of_subsingleton` 不适用（ℕ 不 subsingleton）。
    -- 采用更低层路径：const 函数之 comap = ⊥，
    -- ⊥ 上 measurable set 仅 ∅, univ。此即下面 cases 推导。
    by_cases h_all_univ : ∀ i ∈ s, f' i = Set.univ
    · -- 全 univ：LHS = μ univ = 1; RHS = ∏ μ univ = 1
      have hLHS : μ (⋂ i ∈ s, f' i) = 1 := by
        have : (⋂ i ∈ s, f' i) = Set.univ := by
          apply Set.eq_univ_of_forall
          intro x
          simp only [Set.mem_iInter]
          intro i hi
          rw [h_all_univ i hi]
          exact Set.mem_univ x
        rw [this]
        exact measure_univ
      have hRHS : ∏ i ∈ s, μ (f' i) = 1 := by
        rw [Finset.prod_congr rfl
          (fun i hi => by rw [h_all_univ i hi, measure_univ])]
        exact Finset.prod_const_one
      rw [hLHS, hRHS]
    · -- 存在 i₀ ∈ s 使 f' i₀ ≠ univ；
      -- 由 hf' i₀ hi₀（comap (fun _ => c) struct）⟹ f' i₀ ∈ {∅, univ}
      -- 故 f' i₀ = ∅，LHS = μ (∩ ⊆ ∅) = 0，RHS 中含 μ ∅ = 0 故 = 0
      have h_exists : ∃ i ∈ s, f' i ≠ Set.univ := by
        by_contra h_all
        apply h_all_univ
        intro i hi
        by_contra h_ne
        exact h_all ⟨i, hi, h_ne⟩
      obtain ⟨i₀, hi₀, hne_univ⟩ := h_exists
      -- 下证 f' i₀ = ∅
      have h_struct := hf' i₀ hi₀
      -- comap (fun _ => c) m 之 measurable set s ⟺ ∃ t ∈ m, s = (fun _ => c)⁻¹ t
      -- preimage of t under const := if c ∈ t then univ else ∅
      have : f' i₀ = ∅ ∨ f' i₀ = Set.univ := by
        rcases h_struct with ⟨t, _, ht_eq⟩
        rcases Classical.em (c ∈ t) with hc | hc
        · right
          rw [← ht_eq]
          exact Set.eq_univ_of_forall fun _ => hc
        · left
          rw [← ht_eq]
          ext x
          simp [hc]
      rcases this with hempty | huniv
      · -- f' i₀ = ∅
        have hLHS : μ (⋂ i ∈ s, f' i) = 0 := by
          have hsub : (⋂ i ∈ s, f' i) ⊆ f' i₀ := Set.biInter_subset_of_mem hi₀
          rw [hempty] at hsub
          have := measure_mono (μ := μ) hsub
          rw [measure_empty] at this
          exact le_antisymm this (by exact bot_le)
        have hRHS : ∏ i ∈ s, μ (f' i) = 0 := by
          rw [Finset.prod_eq_zero hi₀]
          rw [hempty]
          exact measure_empty
        rw [hLHS, hRHS]
      · exact absurd huniv hne_univ
  · -- IdentDistrib: const 函数全部相等故 trivially 同分布
    intro i j
    refine IdentDistrib.refl ?_
    exact aemeasurable_const

/-! ## § 6 公开摘要 -/

/-- **IIDWlln 总摘要**：
    (1) IsIID 谓词包装 iIndepFun + IdentDistrib；
    (2) IID 之方差求和 Var(∑ Xᵢ) = n · Var(X 0)；
    (3) IID 样本均值方差 Var(S_n/n) = Var(X 0) / n；
    (4) IID-aware WLLN tendsto-form：S_n/n 偏差概率 → 0；
    (5) 退化具体实例：常数 IID（Var = 0 ⟹ 偏差概率恒 = 0）。 -/
theorem iid_wlln_summary [IsProbabilityMeasure μ] :
    -- (2) Var(∑) = n · Var X₀
    (∀ {X : ℕ → Ω → ℝ}, IsIID μ X → MemLp (X 0) 2 μ →
      ∀ n : ℕ, variance (∑ i ∈ range n, X i) μ = (n : ℝ) * variance (X 0) μ)
    -- (3) Var(S_n/n) = Var(X 0)/n（n ≠ 0）
    ∧ (∀ {X : ℕ → Ω → ℝ}, IsIID μ X → MemLp (X 0) 2 μ →
      ∀ {n : ℕ}, n ≠ 0 →
        variance (fun ω => (n : ℝ)⁻¹ * (∑ i ∈ range n, X i) ω) μ
          = variance (X 0) μ / (n : ℝ))
    -- (5) 常数 IID 之方差 = 0
    ∧ (∀ c : ℝ, variance (fun _ : Ω => c) μ = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro X hiid hL2 n
    exact variance_sum_iid_range hiid hL2 n
  · intro X hiid hL2 n hn
    exact variance_sample_mean_iid hiid hL2 hn
  · intro c
    exact variance_const c

end SSBX.Foundation.Modern.IIDWlln
