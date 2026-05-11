/-
  EconGame.lean — 现代经济学 / 博弈论之 Kernel sieve
  ====================================================

  本文 NOT a Kernel layer (不增 axiom, 不增 KernelDanZi). 它是 Kernel 之
  下游 application: 把 Kernel 之 primitives (中 / 同根 / 礼 / ZhongField /
  attractor) 当 sieve, 套 modern economics & game theory 之 主流命题, 分类:

    实证 (validated)   — 在 Kernel 中可证为定理
    有条件 (conditional) — 仅在某些条件下成立, 条件 explicit
    证错 (refuted)     — 与 Kernel invariants 冲突, 形式上不可能

  注: 这 NOT 否定 这些 results 之 历史 / 计算 / 经验 价值. 仅 标 它们 之
  specific 形式陈述 与 minimum-axiom 之 ZhongField/ZhongOrbit 之 关系.

  全部 theorem 复用 Kernel 既立 primitives. 0 sorry, 0 axiom, 0 新 def.
-/

import SSBX.Foundation.Wen.Kernel

namespace SSBX.Foundation.Wen.EconGame

open SSBX.Foundation.Wen.Kernel

/-! ## 一 · 实证 (Validated) — 6 条

  这 些 经济学 / 博弈论 之 命题 在 Kernel 中 形式 可证. -/

/-- **Pareto efficiency at center (帕累托效率之 ZhongField 实证)**:
    Pareto-optimality 之 minimal 形式: 不存在 一个 reallocation 让 一者 worse-off.
    在 ZhongField 之 中 中: 没有 orbit 在 极 — 故 无 orbit 是 「worse-off than 中」 之 状态.
    形式: 任 i, orbit_i 之 状态 在 中, 即 没人 在 极 (= 「无人 worse-off」).
    此 是 Pareto efficiency 之 structural minimum: 全 中 ⟹ 无 strict 改进 之 必要. -/
theorem pareto_at_middle (f : ZhongField) (n : Nat) :
    (∀ i : Fin f.k, center ((f.orbits i).states n))                        -- 全 中 (no one in 极)
    ∧ (∀ i : Fin f.k, ¬ terminus ((f.orbits i).states n)) :=                 -- 无 worse-off
  ⟨fun i => (f.orbits i).inMiddle n,
   fun i => (f.orbits i).inMiddle n⟩

/-- **Coase 定理 之 zero-transaction-cost 形式 (科斯定理 之 同根 重写)**:
    Coase 定理: 若 transaction cost 为 0 且 property rights 清晰, 则 externality
    可被 internalized. 形式 sieve: internalize externality = 重建 同根 (sameRoot).
    在 同根 之 下, A 之 action 对 A 与 B 之 极-effect 等价 — 没有 「A 受益 / B 受损」
    之 asymmetric externality (此 即 `moloch_via_externality_refuted` 之 corollary).
    形式: sameRoot ∧ center (a (h1 state)) ⟹ ¬ terminus (a (h2 state)). -/
theorem coase_internalizes_externality
    (a : Field → Field) (h_tongGen : sameRoot a)
    (h1 h2 : ZhongOrbit) (n : Nat)
    (h_local : center (a (h1.states n))) :
    ¬ terminus (a (h2.states n)) := by
  intro h_ext
  exact moloch_via_externality_refuted a h_tongGen h1 h2 n h_local h_ext

/-- **Mechanism design 之 incentive compatibility (机制设计 之 激励相容)**:
    Direct mechanism 之 IC: agent 之 truth-telling 是 dominant. 形式 sieve:
    truth-telling 是 dominant ⟺ action 之 中-effect 是 universal (sameRootCentered).
    若 action a 是 中-preserving 在 i, 则 它 也 中-preserving 在 j —
    故 agent 没有 incentive 偏离 truth (因 truth 之 reward 是 universal).  -/
theorem mechanism_incentive_compatibility
    (a : Field → Field) (h_universal : sameRootCentered a)
    (s t : Field) (hs : center s) (ht : center t) :
    center (a s) ↔ center (a t) :=
  h_universal s t hs ht

/-- **Nash bargaining (合作博弈) 之 cooperation-as-道**:
    Nash bargaining solution 假设 cooperative 解 maximizes joint surplus.
    在 Kernel 中, cooperation 之 形式 = `propriety` (礼-window 内 benevolence). 本定理
    重述 `cooperation_cong_dao`: 礼-window 内 双方 中 + 仁. 此 是 positive-sum
    之 形式: 没有 「分蛋糕 而 必有 winner / loser」 — 而是 二者 同 在 中.  -/
theorem nash_bargaining_cong_dao
    (h1 h2 : ZhongOrbit) (n m : Nat) (h_li : propriety h1 h2 n m)
    (k : Nat) (hk : k ≤ m) :
    center (h1.states (n + k))
    ∧ center (h2.states (n + k))
    ∧ benevolence h1 h2 (n + k) :=
  ⟨h1.inMiddle (n + k), h2.inMiddle (n + k), h_li k hk⟩

/-- **Public goods provision via 礼-coordination (公共品 之 礼-维持)**:
    Public goods 之 contribution 在 「coordinated repeat」 之 下 stable.
    形式 sieve: 在 礼-window 内, 双方 之 仁 (= contribution-pattern 之 sustained
    center) 持续. 此 是 Olson 之 "logic of collective action" 之 positive 解.  -/
theorem public_goods_via_liRitual
    (h1 h2 : ZhongOrbit) (n m : Nat) (h_li : propriety h1 h2 n m) :
    ∀ k : Nat, k ≤ m → benevolence h1 h2 (n + k) := h_li

/-- **Smith 看不见的手 之 proper reading (亚当·斯密 自发秩序)**:
    Smith 之 invisible-hand 之 valid 读法 是 spontaneous order — 各 agent 自主
    advance, 无 central designer, 整体仍 显 多样 + 流通. 此 直接 = `hayek_spontaneous_order`.  -/
theorem smith_invisible_hand_proper (f : ZhongField) (n : Nat) :
    (∀ i : Fin f.k, motion ((f.orbits i).states n) = (f.orbits i).states (n + 1))
    ∧ (∀ i : Fin f.k, (f.orbits i).states n ≠ (f.orbits i).states (n + 1))
    ∧ (∃ i j : Fin f.k, i ≠ j ∧ (f.orbits i).states n ≠ (f.orbits j).states n) :=
  hayek_spontaneous_order f n


/-! ## 二 · 有条件 (Conditional) — 4 条

  这 些 命题 在 specific 条件 下 valid; 在 absence of those conditions, fail.
  Conditional theorems 显 explicit 它们 之 premise. -/

/-- **Nash equilibrium existence is conditional on it not being 极**:
    Nash eq. 之 经典 dilemma: PD 之 (defect, defect) 是 Nash eq. 但 是 极-attractor.
    形式 sieve: equilibrium 之 「fixed-point」 form (state stays at s, i.e. motion s = s)
    IS 极 之 定义. 故 「Nash eq. as fixed-point」 IS 极, NOT 中.
    本定理: 若 state s 是 fixed-point of motion (即 Nash eq. in static reading),
    则 s 必 是 极, 不 是 中. 「Nash eq. exists」 ≠ 「Nash eq. is 中」. -/
theorem nash_equilibrium_static_is_extreme
    (s : Field) (h_fixed : motion s = s) :
    terminus s ∧ ¬ center s := by
  refine ⟨h_fixed, ?_⟩
  intro h_mid
  exact h_mid h_fixed

/-- **Rational choice 仅 在 决策者 之 状态 已 classifiable 时 有效**:
    Rational choice theory 假设 actor 之 preference 已 totally determined.
    形式 sieve: 此 假设 = `wisdom_universal` (state 已 classifiable as 中 ∨ 极).
    在 Kernel 中, wisdom 是 universal — 故 二值 form 之 rational choice 总 valid.
    Conditional 形式 (即 strict 「全 决定」 reading 之 限制): rational choice
    总 produces 中 ∨ 极, NEVER 显 「悬置」 之 第三 option. 此 即 二值 之 局限. -/
theorem rational_choice_only_binary (s : Field) :
    center s ∨ terminus s := wisdom_universal s

/-- **Static equilibrium IS 极, dynamic equilibrium IS 中**:
    Equilibrium 之 经济学 standard reading 是 fixed-point. 但 ZhongOrbit 拒
    fixed-point (`momentumDirection_no_telos`). 故 经济学 之 「static equilibrium」 (state
    settles) 是 极, NOT 中. 但 「dynamic equilibrium」 (orbit-state, 永 advance)
    是 中. 二 reading 形式上 distinct. -/
theorem equilibrium_static_vs_dynamic
    (o : ZhongOrbit) (target : Field) (N : Nat) :
    ¬ (∀ n, n ≥ N → o.states n = target)                     -- static eq. impossible
    ∧ (∀ n, center (o.states n)) :=                          -- dynamic eq. (orbit-form) holds
  ⟨ZhongOrbit.momentumDirection_no_telos o target N, o.inMiddle⟩

/-- **VCG auction 之 efficiency conditional on sameRoot (truth-telling)**:
    VCG (Vickrey-Clarke-Groves) auction efficiency 依赖 truth-telling 之 dominance.
    形式 sieve: truth-telling-dominance ⟺ sameRoot — action 之 极-pattern universal,
    故 没有 incentive 撒谎 (撒谎 之 极-effect 与 truth 之 极-effect 同).
    Conditional: 在 sameRoot 之 下, action 之 极-pattern 在 任何 中-states 上 等价.  -/
theorem vcg_auction_efficient_under_tongGen
    (a : Field → Field) (h_tongGen : sameRoot a)
    (s t : Field) (hs : center s) (ht : center t) :
    terminus (a s) ↔ terminus (a t) := h_tongGen s t hs ht


/-! ## 三 · 证错 (Refuted) — 8 条

  这 些 命题 之 specific 形式陈述 与 Kernel invariants 冲突, 形式上 站不住.  -/

/-- **Prisoner's dilemma 之 「defect-defect 是 universal」 形式 之 否定**:
    PD 之 经典 narrative: 双方 defect 是 dominant, defect-defect 是 「rational」 outcome.
    形式 sieve: 此 narrative 假设 defect 之 universal collapse (= selfNotDesire + applyToOther).
    但 在 同根 之 下, defect 之 collapse-effect 必 symmetric — 故 「我 defect 是 rational
    even though 它 害 你」 是 不可能. 此 即 `zhen_dou_self_refuting`: 害 你 = 害 己.  -/
theorem prisoners_dilemma_refuted_under_tongGen
    (x : Xin) (a : Field → Field) (other : ZhongOrbit) (n : Nat)
    (h_tongGen : sameRoot a)
    (h_defect_other : applyToOther a other n) :
    selfNotDesire x a n :=
  zhen_dou_self_refuting x a other n h_tongGen h_defect_other

/-- **Tragedy of the commons 之 否定 (公地悲剧 之 形式 refute)**:
    Tragedy of the commons: 个人 局部 rational ⟹ 集体 极 (= Moloch via externality).
    直接 = `moloch_via_externality_refuted`: 在 同根 之 下, 「个人 中 / 集体 极」
    之 asymmetric externality 是 不可能.  -/
theorem tragedy_of_commons_refuted
    (a : Field → Field) (h_tongGen : sameRoot a)
    (h1 h2 : ZhongOrbit) (n : Nat)
    (h_local_rational : center (a (h1.states n)))
    (h_collapse_other : terminus (a (h2.states n))) :
    False := moloch_via_externality_refuted a h_tongGen h1 h2 n h_local_rational h_collapse_other

/-- **Free-rider 之 universality 之 否定 (搭便车 之 universal form 之 refute)**:
    「universal free-riding」 = 所有 agents 都 collapse 至 contribution-terminus.
    在 ZhongField 之 中, 不可能 同时 全 极 (= `moloch_endpoint_refuted`).  -/
theorem universal_free_rider_refuted (f : ZhongField) :
    ¬ (∃ n, ∀ i : Fin f.k, terminus ((f.orbits i).states n)) :=
  moloch_endpoint_refuted f

/-- **Race-to-bottom in regulatory competition 之 否定 (竞次)**:
    Regulatory race-to-bottom 假设 orbit 永 滑向 极. 直接 = `race_to_bottom_refuted`. -/
theorem regulatory_race_to_bottom_refuted (o : ZhongOrbit) :
    ¬ (∃ N, ∀ n, n ≥ N → terminus (o.states n)) :=
  race_to_bottom_refuted o

/-- **Arrow's impossibility 之 strict-dictator reading 之 否定**:
    Arrow's theorem strict reading: 任 aggregation rule (满足 several conditions) 必 有
    dictator. 形式 sieve: 此 reading 假设 「全 同 一 状态」 (uniformity = dictator's
    preference imposed on all). ZhongField 之 `he_not_same` 直接 否定 此 uniformity —
    structural plurality forbids dictatorial collapse. 故 strict-dictator reading 不
    necessary. (Arrow's theorem 自身 是 mathematical fact 在 boolean 偏好域; 但 它 之
    political-dictator interpretation 在 ZhongField 中 fail.) -/
theorem arrow_dictator_refuted (f : ZhongField) (n : Nat) :
    ¬ (∀ i j : Fin f.k, (f.orbits i).states n = (f.orbits j).states n) :=
  f.he_not_same n

/-- **Homo economicus as descriptive model 之 否定**:
    Homo economicus: 决策者 是 isolated 极-pursuer, 无 仁 / 礼 / 同根.
    形式 sieve: 任 Xin 之 process 必 在 中 (`heart_middle`) — 故 「人 = 极-pursuer」
    描述 与 Xin 之 structural inMiddle 冲突. Xin 不 是 homo economicus. -/
theorem homo_economicus_refuted (x : Xin) (n : Nat) :
    center (x.process.states n) ∧ ¬ terminus (x.process.states n) :=
  ⟨x.process.inMiddle n, x.process.inMiddle n⟩

/-- **「Greed-as-virtue」 (Mandeville/naive Smith) 之 否定**:
    naive Mandeville 之 reading: universal 私利 ⟹ 集体 福. 但 universal greed
    要求 universal terminus (全 在 极 = Moloch endpoint), 直接 violate ZhongField
    之 全 中. 形式 = `moloch_endpoint_refuted`. -/
theorem universal_greed_refuted (f : ZhongField) :
    ¬ (∃ n, ∀ i : Fin f.k, terminus ((f.orbits i).states n)) :=
  moloch_endpoint_refuted f

/-- **Zero-sum framing 之 否定**:
    Zero-sum: 二焦点 之 间 必 有 winner (中) / loser (极). 在 仁 之 下, 二者
    同 中 — 没有 loser. 直接 = `zero_sum_refuted_by_ren`.  -/
theorem zero_sum_refuted
    (h1 h2 : ZhongOrbit) (n : Nat) (h_distinct : h1.states n ≠ h2.states n) :
    center (h1.states n) ∧ center (h2.states n) ∧ benevolence h1 h2 n :=
  zero_sum_refuted_by_ren h1 h2 n h_distinct


/-! ## 四 · 总览 / 结构 之 meta-theorem -/

/-- **Market 之 二 face**: market 在 ZhongField 中 advance IS 道; 但 specific
    极-attractor configurations (PD, commons, race-to-bottom) IS 非道.
    本 meta-theorem 同时 给 二 形式: 全 中 (道 face) ∧ uniformity-attractor 不可能 (非道 之 否). -/
theorem market_two_faces (f : ZhongField) (n : Nat) (target : Field) :
    (∀ i : Fin f.k, center ((f.orbits i).states n))   -- market 之 道 face: 全 中
    ∧ ¬ attractor target f                            -- 非道 之 否: uniformity attractor 不可能
    ∧ ¬ (∀ i j : Fin f.k, (f.orbits i).states n = (f.orbits j).states n) := by  -- ¬ uniformity
  refine ⟨fun i => (f.orbits i).inMiddle n, ?_, f.he_not_same n⟩
  exact winner_takes_all_refuted f target

end SSBX.Foundation.Wen.EconGame
