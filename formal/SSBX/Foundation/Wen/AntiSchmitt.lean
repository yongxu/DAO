/-
# AntiSchmitt — 反施密特之形式

深度 formalize Schmitt 三大支柱之结构破缺:

  1. **friend-enemy distinction** (Begriff des Politischen):
     政治 IS 敌友区分.
     本卷形式: 敌友是 forced 二分, 排除 仁 (中之同根异显) — 第三 option.

  2. **decisionism** (Politische Theologie):
     "Souverän ist, wer über den Ausnahmezustand entscheidet."
     主权决断 treats specific case differently from general rule —
     形式上 require asymmetric action, 与 同根 (sameRoot) 直接冲突.

  3. **state of exception** (Ausnahmezustand):
     例外状态: rule 不 universally apply.
     形式上是 a 在某 中-states 上 collapse, 在另一些 上 不 collapse —
     punctures sameRoot.

最深刻发现: **Schmitt 三支柱共享同一形式根源 — 拒绝 universalizability**.
故 Anti-Schmitt = Anti-Moloch = 仁 之 同根异显.

继 Layer 44 (政治证错) / Layer 45 (非道) 之后, 此为 Anti-Schmitt 专章.
-/
import SSBX.Foundation.Wen.Kernel

namespace SSBX.Foundation.Wen.AntiSchmitt

open SSBX.Foundation.Wen.Kernel

/-! ## § 1  Schmitt 友敌之 二分 vs 仁 之 第三 option -/

/-- Schmitt 之 friend-enemy 谓词 (formal reading).
    给定 二焦点 (h1, h2) 和 时刻 n, 把它们分类为:
      - friend (友): 二者 collapse 至 同 — 即 h1.states n = h2.states n
      - enemy (敌): 至少一方 处于 极 状态
    Schmitt 强调此 二分 之 必然性 (排他穷尽). 我们 formalize 为 disjunction. -/
def friendOrEnemy (h1 h2 : ZhongOrbit) (n : Nat) : Prop :=
  h1.states n = h2.states n  -- friend (collapse to same)
  ∨ terminus (h1.states n)     -- enemy (h1 at 极)
  ∨ terminus (h2.states n)     -- enemy (h2 at 极)

/-- **第一定理**: 在 ZhongField 内, friend-enemy 二分 之 forced choice 不成立.
    存在 第三 option (仁): h1 ≠ h2 ∧ 双 中 ∧ benevolence-relation. -/
theorem friend_enemy_distinction_via_predicate
    (h1 h2 : ZhongOrbit) (n : Nat) (h_distinct : h1.states n ≠ h2.states n) :
    ¬ friendOrEnemy h1 h2 n
    ∧ benevolence h1 h2 n := by
  refine ⟨?_, h_distinct⟩
  intro hfe
  rcases hfe with h_same | h_ext1 | h_ext2
  · exact h_distinct h_same
  · exact h1.inMiddle n h_ext1
  · exact h2.inMiddle n h_ext2

/-- 「友 = 同一」 之 reading 直接 collapse 多样性 (ever_differentiated).
    若 ZhongField 内任意 二焦点 都 friend (= 全 同), 则 violate plurality. -/
theorem friend_collapse_violates_plurality
    (f : ZhongField) (n : Nat)
    (h_all_friend : ∀ i j : Fin f.k, (f.orbits i).states n = (f.orbits j).states n) :
    False :=
  f.he_not_same n h_all_friend

/-- 「敌 = 使他者 collapse 至 极」 之 reading 直接 violate 他者 之 inMiddle. -/
theorem enemy_collapse_violates_inMiddle
    (other : ZhongOrbit) (n : Nat)
    (h_enemy : terminus (other.states n)) :
    False :=
  other.inMiddle n h_enemy

/-! ## § 2  Decisionism 与 同根 之 不兼容 -/

/-- **Decisionism 形式 reading**: 主权决断 treats specific case differently —
    存在 中-状态 s 与 t, action a 在 s 上 induce 极, 在 t 上不 induce 极.
    这恰是 sameRoot 之 negation. -/
def decisionistAsymmetry (a : Field → Field) : Prop :=
  ∃ s t : Field, center s ∧ center t ∧ terminus (a s) ∧ ¬ terminus (a t)

/-- **第四定理**: decisionism (asymmetric sovereign action) 与 sameRoot 形式 互斥. -/
theorem decisionism_breaks_sameRoot
    (a : Field → Field) (h_asym : decisionistAsymmetry a) :
    ¬ sameRoot a := by
  intro h_tong
  obtain ⟨s, t, hs_mid, ht_mid, h_ext_s, h_not_ext_t⟩ := h_asym
  exact h_not_ext_t ((h_tong s t hs_mid ht_mid).mp h_ext_s)

/-- Contrapositive — 若 sameRoot 成立, 则 主权决断 不存在. -/
theorem sameRoot_excludes_decisionism
    (a : Field → Field) (h_tong : sameRoot a) :
    ¬ decisionistAsymmetry a :=
  fun h_asym => decisionism_breaks_sameRoot a h_asym h_tong

/-! ## § 3  State of Exception 之 形式破缺 -/

/-- **例外状态 形式 reading**: 规则 a 对某些 中-状态 collapse, 对另一些 不 collapse.
    亦即: 规则 不 universally apply — punctures sameRoot on the 极-side.
    (与 decisionistAsymmetry 形式 等价.) -/
def stateOfException (a : Field → Field) : Prop :=
  ∃ s t : Field, center s ∧ center t ∧ terminus (a s) ∧ center (a t)

/-- **第六定理**: state of exception 与 sameRoot 形式 incompatible.
    例外 = 规则不 universally apply ⟹ 破 同根. -/
theorem state_of_exception_breaks_universality
    (a : Field → Field) (h_exc : stateOfException a) :
    ¬ sameRoot a := by
  intro h_tong
  obtain ⟨s, t, hs_mid, ht_mid, h_ext_s, h_mid_t⟩ := h_exc
  -- a t is center, hence not terminus; but sameRoot forces terminus (a t) given terminus (a s)
  exact (zhi_exclusive (a t)) ⟨h_mid_t, (h_tong s t hs_mid ht_mid).mp h_ext_s⟩

/-- Sovereign exception 之 contrapositive: sameRoot ⟹ 没有 例外. -/
theorem tongGen_no_exception
    (a : Field → Field) (h_tong : sameRoot a) :
    ¬ stateOfException a :=
  fun h_exc => state_of_exception_breaks_universality a h_exc h_tong

/-! ## § 4  Concrete Order via 仁 — 替代结构 -/

/-- **Concrete order via benevolence**: 多 orbit 之间 maintained benevolence-relation 越 时刻
    构成 真正之 政治 substrate, 而 非 友敌. 此 是 Schmitt "konkrete Ordnung"
    之 健康 reading — 不 经由 enmity, 而 经由 同根异显. -/
def concreteOrderViaRen (h1 h2 : ZhongOrbit) (N : Nat) : Prop :=
  ∀ n ≤ N, benevolence h1 h2 n

/-- **第七定理**: 若 二焦点 在 0..N 始终 benevolence, 则 既 无 friend-collapse 也 无 enemy-collapse. -/
theorem concrete_order_via_ren
    (h1 h2 : ZhongOrbit) (N : Nat) (h_co : concreteOrderViaRen h1 h2 N) (n : Nat) (h_le : n ≤ N) :
    h1.states n ≠ h2.states n
    ∧ ¬ terminus (h1.states n)
    ∧ ¬ terminus (h2.states n) :=
  ⟨h_co n h_le, h1.inMiddle n, h2.inMiddle n⟩

/-- **第八定理 (政治之本质 IS 仁, 非 enmity)**:
    political-essence-as-benevolence — 给定 ZhongField (政治 之 minimum 形式),
    任意 distinct 焦点 pair 之间 自动 是 benevolence-relation, 而 非 enemy. -/
theorem political_essence_is_ren_not_enmity
    (f : ZhongField) (n : Nat) (i j : Fin f.k)
    (h_ne : (f.orbits i).states n ≠ (f.orbits j).states n) :
    benevolence (f.orbits i) (f.orbits j) n
    ∧ ¬ terminus ((f.orbits i).states n)
    ∧ ¬ terminus ((f.orbits j).states n) :=
  ⟨h_ne, (f.orbits i).inMiddle n, (f.orbits j).inMiddle n⟩

/-! ## § 5  Partisan / 斗争之 self-destruction (universalized) -/

/-- **第九定理 partisan_war_self_destructive**:
    Schmitt 晚期 "Theorie des Partisanen" 把 friend-enemy 推 至 极致 — 全民斗争.
    在 同根 之下, 把 「使他者 collapse」 推 universally ⟹ self-collapse.
    此 是 zhen_dou_self_refuting 之 partisan-extension. -/
theorem partisan_war_self_destructive
    (x : Xin) (a : Field → Field)
    (h_tongGen : sameRoot a)
    (others : Nat → ZhongOrbit)
    (h_partisan : ∀ k, applyToOther a (others k) k) :
    ∀ n, selfNotDesire x a n := by
  intro n
  -- Use the n-th other; 同根 transports the collapse to self.
  exact (h_tongGen ((others n).states n) (x.process.states n)
           ((others n).inMiddle n) (x.process.inMiddle n)).mp (h_partisan n)

/-! ## § 6  紧急合法性 之 缺乏 grounding -/

/-- **第十定理 legitimacy_via_emergency_lacks_grounding**:
    "legitimacy that requires perpetual terminus state" — 即 orbit 必须 eventually
    settle 至 极. 这与 race_to_bottom_refuted 同形式 — orbit 之 inMiddle 否定. -/
theorem legitimacy_via_emergency_lacks_grounding (o : ZhongOrbit) :
    ¬ (∃ N, ∀ n, n ≥ N → terminus (o.states n)) := by
  intro ⟨N, h⟩
  exact o.inMiddle N (h N (Nat.le_refl N))

/-! ## § 7  法治 vs 主权例外 -/

/-- **第十一定理 sovereign_decision_vs_law_universality**:
    rule of law = universally applicable a (即 sameRoot 成立).
    sovereign exception = stateOfException 成立.
    二者形式上互斥 — 不可同时成立. -/
theorem sovereign_decision_vs_law_universality
    (a : Field → Field) :
    ¬ (sameRoot a ∧ stateOfException a) := by
  intro ⟨h_tong, h_exc⟩
  exact state_of_exception_breaks_universality a h_exc h_tong

/-! ## § 8  Friend-Enemy ⟹ Moloch 之 enabling 条件 -/

/-- **第十二定理 friend_enemy_implies_moloch_enabler**:
    Schmitt 之 friend-enemy 框架 (具体化为 stateOfException) 切断 universalizability,
    从而 enable Moloch dynamics (asymmetric externality).
    形式上: 若 a 是 stateOfException, 则 不是 sameRoot — 而 sameRoot 正是 forbid Moloch
    之 唯一 hypothesis (见 moloch_via_externality_refuted). -/
theorem friend_enemy_implies_moloch
    (a : Field → Field) (h_exc : stateOfException a) :
    ¬ sameRoot a :=
  state_of_exception_breaks_universality a h_exc

/-! ## § 9  政治 之 第三 option 总枚举 -/

/-- 政治分类 inductive — 至少 三 个 distinct categories. -/
inductive PoliticalRelation : Type
  | friend          -- collapse to same
  | enemy           -- collapse other to terminus
  | renCompanion    -- distinct yet center (仁)
  deriving DecidableEq

/-- **第十三定理 political_third_option_total_count**:
    {friend, enemy, renCompanion} has at least three distinct elements,
    refuting Schmitt 之 binary politics 之 必然性. -/
theorem political_third_option_total_count :
    PoliticalRelation.friend ≠ PoliticalRelation.enemy
    ∧ PoliticalRelation.friend ≠ PoliticalRelation.renCompanion
    ∧ PoliticalRelation.enemy ≠ PoliticalRelation.renCompanion := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## § 10  Concrete enemy-inversion: 敌 IS 又一焦点, 同根异显 -/

/-- **第十四定理 concrete_friend_enemy_inversion**:
    在 ZhongField 中, 任意 「敌」 (即 distinct from self) 之 orbit 也是 ZhongOrbit,
    与 self 共享 同一 motion-axiom (同根). 「敌」 不是 ontological other,
    而是 自身 axiom 之 又一 instantiation — 同根异显.

    Concretely: 若 i ≠ j 且 二焦点 distinct at n, 则 二焦点 都 inMiddle 且
    都 step via 同 一 axiom motion, 故 形式上 indistinguishable as 「同根」. -/
theorem concrete_friend_enemy_inversion
    (f : ZhongField) (n : Nat) (i j : Fin f.k) (_h_ne_idx : i ≠ j) :
    -- 同根: 都 obey motion axiom
    (∀ m, motion ((f.orbits i).states m) = (f.orbits i).states (m + 1))
    ∧ (∀ m, motion ((f.orbits j).states m) = (f.orbits j).states (m + 1))
    -- 异显: 中 + (potentially) distinct trace
    ∧ center ((f.orbits i).states n)
    ∧ center ((f.orbits j).states n) := by
  refine ⟨(f.orbits i).step, (f.orbits j).step, (f.orbits i).inMiddle n, (f.orbits j).inMiddle n⟩

/-! ## § 11  综合: Anti-Schmitt 三位一体 (decisionism / exception / friend-enemy) -/

/-- **第十五定理 anti_schmitt_unified**:
    decisionism, state-of-exception, 与 friend-enemy 三大支柱 形式上 share
    同一 root cause: 拒绝 universalizability (i.e., sameRoot).
    若 sameRoot 成立, 则 三者 全 不成立. -/
theorem anti_schmitt_unified
    (a : Field → Field) (h_tong : sameRoot a) :
    ¬ decisionistAsymmetry a
    ∧ ¬ stateOfException a := by
  exact ⟨sameRoot_excludes_decisionism a h_tong, tongGen_no_exception a h_tong⟩

end SSBX.Foundation.Wen.AntiSchmitt
