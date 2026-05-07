/-
古文虚字 (wenyan operators) — framework-level operator layer.

实现 Kernel header 之 「presupposed 古文虚字」 — 不再 仅 是 Lean built-ins
之 documentation, 而 是 framework-internal named operators with ASCII aliases.

这 不 是 严格 categorical refactor of Lean's primitives — Lean 之 type theory
仍 在 ambient. 但 framework 之 definitions 现在 可 用 framework-internal names,
后续 layers 可 layer 上 these names instead of Lean primitives directly.

Layer 23 (this file) presents:
  之 / 者 / 而 / 也 / 不 / 凡 / X之又X / 自 / 相 / 似 / 要
  + ASCII aliases for each.
  + Basic identity theorems (Wenyan name ≡ Lean primitive).
-/

namespace SSBX.Foundation.Wen.Operators

/-! ### S-1: 之 (zhi) — function application / possessive

  「X 之 Y」 = "Y of X" / application of f to x.
  In Lean: f x. -/

/-- 之 (zhi): function application. -/
abbrev «之» {α β : Sort _} (f : α → β) (x : α) : β := f x

/-- ASCII alias: zhi. -/
abbrev zhiOp {α β : Sort _} (f : α → β) (x : α) : β := f x

/-- 之 ≡ Lean's function application. -/
theorem zhi_eq_app {α β : Sort _} (f : α → β) (x : α) : «之» f x = f x := rfl

/-! ### 的 (de) — modern genitive / projection binding

  「X 的 Y」 is the modern surface counterpart of 「X 之 Y」.  It is registered
  as a single-glyph operator so modern explanatory prose can reduce to the same
  projection/application primitive. -/

/-- 的 (de): modern genitive/projection binding, semantically equal to 之. -/
abbrev «的» {α β : Sort _} (f : α → β) (x : α) : β := f x

abbrev deOp {α β : Sort _} (f : α → β) (x : α) : β := f x

theorem de_eq_zhi {α β : Sort _} (f : α → β) (x : α) : «的» f x = «之» f x := rfl

theorem de_eq_app {α β : Sort _} (f : α → β) (x : α) : «的» f x = f x := rfl

/-! ### S-13: 者 (zhe) — λ-binder marker

  「X 者 ... 也」 = "X is defined as ..." 「者」 marks the binder.
  In Lean: lambda is native; 者 is just a documentation alias. -/

/-- 者 (zhe): lambda-binder marker (identity on functions). -/
abbrev «者» {α β : Sort _} (f : α → β) : α → β := f

abbrev zheOp {α β : Sort _} (f : α → β) : α → β := f

theorem zhe_eq_id {α β : Sort _} (f : α → β) : «者» f = f := rfl

/-! ### S-2: 而 (er) — sequential composition with time-grain

  「f 而 g」 = "f then g" — non-commutative time-ordered composition.
  In Lean: g ∘ f. -/

/-- 而 (er): sequential composition (f then g). -/
def «而» {α : Sort _} (f g : α → α) : α → α := g ∘ f

abbrev erOp {α : Sort _} (f g : α → α) : α → α := «而» f g

theorem er_eq_comp {α : Sort _} (f g : α → α) (x : α) :
    «而» f g x = g (f x) := rfl

/-- 而 之 non-commutativity: in general f而g ≠ g而f. (We don't prove the negation
    here since it requires concrete f, g; this theorem just asserts the structural
    asymmetry of the definition.) -/
theorem er_associative {α : Sort _} (f g h : α → α) (x : α) :
    «而» («而» f g) h x = «而» f («而» g h) x := rfl

/-! ### S-14: 也 (ye) — state closure / assertion marker

  「P 也」 = "P, indeed" / state-closure marker on Prop.
  In Lean: P (identity on Prop). -/

/-- 也 (ye): state-closure / assertion on Prop. -/
abbrev «也» (P : Prop) : Prop := P

abbrev yeOp (P : Prop) : Prop := P

theorem ye_eq_id (P : Prop) : «也» P ↔ P := Iff.rfl

/-! ### S-15: 于 / 於 (yu) — context binding

  「P 于 Γ」 = P holds in context Γ. -/

/-- 于 (yu): context binding / holds-in. -/
abbrev «于» {Γ : Sort _} (P : Γ → Prop) (ctx : Γ) : Prop := P ctx

abbrev yuCtxOp {Γ : Sort _} (P : Γ → Prop) (ctx : Γ) : Prop := P ctx

theorem yu_ctx_eq_app {Γ : Sort _} (P : Γ → Prop) (ctx : Γ) : «于» P ctx ↔ P ctx :=
  Iff.rfl

/-- 於 (yu): traditional-form context binding. -/
abbrev «於» {Γ : Sort _} (P : Γ → Prop) (ctx : Γ) : Prop := P ctx

abbrev yuTradCtxOp {Γ : Sort _} (P : Γ → Prop) (ctx : Γ) : Prop := P ctx

theorem yu_trad_ctx_eq_app {Γ : Sort _} (P : Γ → Prop) (ctx : Γ) :
    «於» P ctx ↔ P ctx := Iff.rfl

/-! ### 地 (di) — situated ground / context-place

  「地」 is the single-glyph ground/place reading of situatedness: a proposition
  is not just abstractly true, but holds on a given ground or in a given place. -/

/-- 地 (di): situated ground; a place/context-specific holds-in operator. -/
abbrev «地» {Γ : Sort _} (P : Γ → Prop) (ctx : Γ) : Prop := P ctx

abbrev diGroundOp {Γ : Sort _} (P : Γ → Prop) (ctx : Γ) : Prop := P ctx

theorem di_eq_yu {Γ : Sort _} (P : Γ → Prop) (ctx : Γ) : «地» P ctx ↔ «于» P ctx :=
  Iff.rfl

theorem di_eq_app {Γ : Sort _} (P : Γ → Prop) (ctx : Γ) : «地» P ctx ↔ P ctx :=
  Iff.rfl

/-! ### 不 (bu) — negation

  「不 X」 = "not X". -/

/-- 不 (bu): negation. -/
abbrev «不» (P : Prop) : Prop := ¬ P

abbrev buOp (P : Prop) : Prop := ¬ P

theorem bu_eq_not (P : Prop) : «不» P ↔ ¬ P := Iff.rfl

/-! ### Q-1: 凡 (fan) — universal quantifier

  「凡 X, P X」 = "for all X, P X". -/

/-- 凡 (fan): universal quantifier. -/
abbrev «凡» {α : Sort _} (P : α → Prop) : Prop := ∀ x : α, P x

abbrev fanOp {α : Sort _} (P : α → Prop) : Prop := ∀ x : α, P x

theorem fan_eq_forall {α : Sort _} (P : α → Prop) :
    «凡» P ↔ ∀ x : α, P x := Iff.rfl

/-! ### X之又X — structural recursion (iteration)

  「X 之 又 X」 = X-of-itself, n times. Pattern for recursion / repetition. -/

/-- X之又X: n-fold iteration of f from x. -/
def XzhiyouX {α : Sort _} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => f (XzhiyouX f n x)

/-- 0-fold iteration is identity. -/
theorem XzhiyouX_zero {α : Sort _} (f : α → α) (x : α) : XzhiyouX f 0 x = x := rfl

/-- (n+1)-fold iteration unfolds. -/
theorem XzhiyouX_succ {α : Sort _} (f : α → α) (n : Nat) (x : α) :
    XzhiyouX f (n + 1) x = f (XzhiyouX f n x) := rfl

/-! ### K-3 / Z-32: 自 (zi) — reflexive / self / from-self

  「自 X」 = "by X itself" / reflexive marker.
  In Lean: id (x = x). -/

/-- 自 (zi): reflexive identity (returns input unchanged). -/
abbrev «自» {α : Sort _} (x : α) : α := x

abbrev ziOp {α : Sort _} (x : α) : α := x

theorem zi_eq_id {α : Sort _} (x : α) : «自» x = x := rfl

/-! ### 相 (xiang) — mutual / pair-marker

  「X 相 Y」 = "X mutually with Y" — symmetric pair-marker.
  Used in 「X 相 似 Y」 = "X is similar to Y (mutually)". -/

/-- 相 (xiang): symmetric (mutual) closure of a relation. -/
def «相» {α : Sort _} (R : α → α → Prop) (x y : α) : Prop :=
  R x y ∧ R y x

abbrev xiangOp {α : Sort _} (R : α → α → Prop) (x y : α) : Prop :=
  R x y ∧ R y x

/-- 相 之 commutativity: 相 R x y ↔ 相 R y x. -/
theorem xiang_comm {α : Sort _} (R : α → α → Prop) (x y : α) :
    «相» R x y ↔ «相» R y x :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-! ### 似 (si) — similarity / structural equivalence

  「X 似 Y」 = "X is similar to Y" — structural / formal equivalence.
  In Lean: equality. -/

/-- 似 (si): equivalence (here, equality). -/
abbrev «似» {α : Sort _} (x y : α) : Prop := x = y

abbrev siOp {α : Sort _} (x y : α) : Prop := x = y

theorem si_eq_eq {α : Sort _} (x y : α) : «似» x y ↔ x = y := Iff.rfl

theorem si_refl {α : Sort _} (x : α) : «似» x x := rfl

theorem si_symm {α : Sort _} {x y : α} (h : «似» x y) : «似» y x := h.symm

theorem si_trans {α : Sort _} {x y z : α} (h1 : «似» x y) (h2 : «似» y z) :
    «似» x z := h1.trans h2

/-! ### 要 (yao) — modal necessity

  「X 要 Y」 = "X requires Y" / modal necessity.
  In simple Prop logic, kept as identity wrapper.
  Future layer can refine to Necessity in modal logic. -/

/-- 要 (yao): modal necessity wrapper. -/
abbrev «要» (P : Prop) : Prop := P

abbrev yaoOp (P : Prop) : Prop := P

theorem yao_eq_id (P : Prop) : «要» P ↔ P := Iff.rfl

/-! ### 与 (yu) — conjunction (∧)

  「X 与 Y」 = "X and Y". -/

/-- 与 (yu): conjunction. -/
abbrev «与» (P Q : Prop) : Prop := P ∧ Q

abbrev yuOp (P Q : Prop) : Prop := P ∧ Q

theorem yu_eq_and (P Q : Prop) : «与» P Q ↔ P ∧ Q := Iff.rfl

theorem yu_comm (P Q : Prop) : «与» P Q ↔ «与» Q P := And.comm

/-! ### 或 (huo) — disjunction (∨)

  「或 X 或 Y」 = "either X or Y". -/

/-- 或 (huo): disjunction. -/
abbrev «或» (P Q : Prop) : Prop := P ∨ Q

abbrev huoOp (P Q : Prop) : Prop := P ∨ Q

theorem huo_eq_or (P Q : Prop) : «或» P Q ↔ P ∨ Q := Iff.rfl

theorem huo_comm (P Q : Prop) : «或» P Q ↔ «或» Q P := Or.comm

/-! ### 若 (ruo) — antecedent / "if"

  「若 X, 则 Y」 = "if X then Y". 若 marks the antecedent. -/

/-- 若 (ruo): identity wrapper marking antecedent. -/
abbrev «若» (P : Prop) : Prop := P

abbrev ruoOp (P : Prop) : Prop := P

theorem ruo_eq_id (P : Prop) : «若» P ↔ P := Iff.rfl

/-! ### 则 (ze) — consequent / "then"

  「若 X 则 Y」 = "if X then Y". 则 marks the consequent + implies. -/

/-- 则 (ze): implication. -/
abbrev «则» (P Q : Prop) : Prop := P → Q

abbrev zeOp (P Q : Prop) : Prop := P → Q

theorem ze_eq_imp (P Q : Prop) : «则» P Q ↔ (P → Q) := Iff.rfl

/-- 「若 X 则 Y」 之 落地: 若 X, then Y. -/
theorem ruo_ze_eq_imp (P Q : Prop) : «则» («若» P) Q ↔ (P → Q) := Iff.rfl

/-! ### 故 (gu) — therefore / causation marker

  「X, 故 Y」 = "X, therefore Y". 与 则 类似, 但 emphasizes causation. -/

/-- 故 (gu): therefore (implication, with causation emphasis). -/
abbrev «故» (P Q : Prop) : Prop := P → Q

abbrev guOp (P Q : Prop) : Prop := P → Q

theorem gu_eq_imp (P Q : Prop) : «故» P Q ↔ (P → Q) := Iff.rfl

/-- 故 与 则 同 logical content. -/
theorem gu_eq_ze (P Q : Prop) : «故» P Q ↔ «则» P Q := Iff.rfl

/-! ### 是 (shi) — copula / identity

  「X 是 Y」 = "X is Y" — identity / copula.
  与 似 类似 但 emphasis on identity rather than similarity. -/

/-- 是 (shi): copula / identity. -/
abbrev «是» {α : Sort _} (x y : α) : Prop := x = y

abbrev shiOp {α : Sort _} (x y : α) : Prop := x = y

theorem shi_eq_eq {α : Sort _} (x y : α) : «是» x y ↔ x = y := Iff.rfl

theorem shi_iff_si {α : Sort _} (x y : α) : «是» x y ↔ «似» x y := Iff.rfl

/-! ### 系 (xi) — relational connection

  「X 系 Y」 does not collapse X and Y by identity; it asserts an explicit
  relation between them.  This is the relational isness complement to 是. -/

/-- 系 (xi): relational connection under a supplied relation. -/
abbrev «系» {α : Sort _} (R : α → α → Prop) (x y : α) : Prop := R x y

abbrev xiRelOp {α : Sort _} (R : α → α → Prop) (x y : α) : Prop := R x y

theorem xi_rel_eq {α : Sort _} (R : α → α → Prop) (x y : α) :
    «系» R x y ↔ R x y := Iff.rfl

/-! ### 即 (ji) — immediately is / equivalence

  「X 即 Y」 = "X is just Y" — strong equivalence. -/

/-- 即 (ji): immediate equivalence. For Prop: iff. For values: equality. -/
abbrev «即» (P Q : Prop) : Prop := P ↔ Q

abbrev jiOp (P Q : Prop) : Prop := P ↔ Q

theorem ji_eq_iff (P Q : Prop) : «即» P Q ↔ (P ↔ Q) := Iff.rfl

/-! ### 必 (bi) — necessity / "must"

  「必 X」 = "must X" / necessarily X.
  In Prop logic, kept as identity wrapper (no modal subdivision yet). -/

/-- 必 (bi): modal necessity wrapper. -/
abbrev «必» (P : Prop) : Prop := P

abbrev biOp (P : Prop) : Prop := P

theorem bi_eq_id (P : Prop) : «必» P ↔ P := Iff.rfl

/-- 「凡 X 必 P X」 ≡ 「∀ X, P X」 — universal-necessity composition. -/
theorem fan_bi_eq_forall {α : Sort _} (P : α → Prop) :
    «凡» (fun x => «必» (P x)) ↔ ∀ x : α, P x := Iff.rfl

/-! ### 可 (ke) — possibility / "can"

  「可 X」 = "can X" / possibly X. -/

/-- 可 (ke): possibility / decidability. -/
abbrev «可» (P : Prop) : Prop := P

abbrev keOp (P : Prop) : Prop := P

theorem ke_eq_id (P : Prop) : «可» P ↔ P := Iff.rfl

/-! ### 能 (neng) — ability / capacity

  「能 X」 = "able to X" — agent-relative possibility. -/

/-- 能 (neng): agent-capacity. -/
abbrev «能» (P : Prop) : Prop := P

abbrev nengOp (P : Prop) : Prop := P

theorem neng_eq_id (P : Prop) : «能» P ↔ P := Iff.rfl

/-! ### 有 (you-exists) — existence

  「有 X」 = "there is X" / ∃X. -/

/-- 有 (you, exists): existential quantifier. -/
abbrev «有» {α : Sort _} (P : α → Prop) : Prop := ∃ x : α, P x

abbrev youExistsOp {α : Sort _} (P : α → Prop) : Prop := ∃ x : α, P x

theorem you_eq_exists {α : Sort _} (P : α → Prop) :
    «有» P ↔ ∃ x : α, P x := Iff.rfl

/-! ### 无 (wu) — non-existence

  「无 X」 = "no X" / ¬∃X. -/

/-- 无 (wu): negated existence. -/
abbrev «无» {α : Sort _} (P : α → Prop) : Prop := ¬ ∃ x : α, P x

abbrev wuOp {α : Sort _} (P : α → Prop) : Prop := ¬ ∃ x : α, P x

theorem wu_eq_not_exists {α : Sort _} (P : α → Prop) :
    «无» P ↔ ¬ ∃ x, P x := Iff.rfl

/-- 无 ≡ 不 有 — non-existence is negated existence. -/
theorem wu_eq_bu_you {α : Sort _} (P : α → Prop) :
    «无» P ↔ «不» («有» P) := Iff.rfl

/-! ### 已 (yi-perfective) — perfective aspect

  「已 X」 = "already X" / X has occurred. Aspect monad marker. -/

/-- 已 (yi, perfective): aspect marker for completed state. -/
abbrev «已» (P : Prop) : Prop := P

abbrev yiPerfOp (P : Prop) : Prop := P

theorem yi_perf_eq_id (P : Prop) : «已» P ↔ P := Iff.rfl

/-! ### 未 (wei) — imperfective / "not yet"

  「未 X」 = "not yet X" — imperfective aspect. -/

/-- 未 (wei): imperfective negation. -/
abbrev «未» (P : Prop) : Prop := ¬ P

abbrev weiOp (P : Prop) : Prop := ¬ P

theorem wei_eq_not (P : Prop) : «未» P ↔ ¬ P := Iff.rfl

/-- 未 ≡ 不: at the propositional level, imperfective IS negation
    (the temporal "not yet" reduces to current "not"). -/
theorem wei_eq_bu (P : Prop) : «未» P ↔ «不» P := Iff.rfl

/-! ### 将 (jiang) — future / "will"

  「将 X」 = "will X" / future tense.
  At the Prop level, kept as identity (no temporal types yet). -/

/-- 将 (jiang): future-tense marker. -/
abbrev «将» (P : Prop) : Prop := P

abbrev jiangOp (P : Prop) : Prop := P

theorem jiang_eq_id (P : Prop) : «将» P ↔ P := Iff.rfl

/-! ### 由 (you-cause) — cause / from

  「由 X」 = "from X" / "caused by X". -/

/-- 由 (you, cause): causal marker (identity wrapper). -/
abbrev «由» (P : Prop) : Prop := P

abbrev youCauseOp (P : Prop) : Prop := P

theorem you_cause_eq_id (P : Prop) : «由» P ↔ P := Iff.rfl

/-! ### Composite identities -/

/-- 「f 而 g」 之 X = g (f X) — 而 之 时序性 落地. -/
theorem zhi_er_compose {α : Sort _} (f g : α → α) (x : α) :
    «之» («而» f g) x = g (f x) := rfl

/-- 「凡 X, P X 也」 ↔ ∀ X, P X. -/
theorem fan_ye_eq_forall {α : Sort _} (P : α → Prop) :
    («凡» (fun x => «也» (P x))) ↔ ∀ x : α, P x := Iff.rfl

/-- 「不 凡 X, P X」 ↔ ∃ X, ¬ P X. -/
theorem bu_fan_eq_exists_not {α : Sort _} (P : α → Prop) :
    «不» («凡» P) ↔ ∃ x : α, ¬ P x := by
  unfold «不» «凡»
  exact ⟨fun h => Classical.byContradiction (fun hne =>
    h (fun x => Classical.byContradiction (fun hp => hne ⟨x, hp⟩))),
    fun ⟨x, hp⟩ hf => hp (hf x)⟩

/-- 「若 P 则 Q」, 即 P → Q. -/
theorem ruo_ze_compose (P Q : Prop) : («则» («若» P) Q) ↔ (P → Q) := Iff.rfl

/-- 「P 与 Q 与 R」 之 associativity. -/
theorem yu_assoc (P Q R : Prop) :
    «与» («与» P Q) R ↔ «与» P («与» Q R) :=
  ⟨fun ⟨⟨hP, hQ⟩, hR⟩ => ⟨hP, hQ, hR⟩,
   fun ⟨hP, hQ, hR⟩ => ⟨⟨hP, hQ⟩, hR⟩⟩

/-- De Morgan: 不 (P 与 Q) ↔ 不 P 或 不 Q. -/
theorem de_morgan_yu (P Q : Prop) :
    «不» («与» P Q) ↔ «或» («不» P) («不» Q) := by
  unfold «不» «与» «或»
  exact ⟨fun h => Classical.byContradiction (fun hne =>
    h ⟨Classical.byContradiction (fun hp => hne (Or.inl hp)),
       Classical.byContradiction (fun hq => hne (Or.inr hq))⟩),
    fun h hPQ => h.elim (· hPQ.1) (· hPQ.2)⟩

/-- De Morgan: 不 (P 或 Q) ↔ 不 P 与 不 Q. -/
theorem de_morgan_huo (P Q : Prop) :
    «不» («或» P Q) ↔ «与» («不» P) («不» Q) := by
  unfold «不» «或» «与»
  exact ⟨fun h => ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩,
    fun ⟨hP, hQ⟩ h => h.elim hP hQ⟩

/-- 「不 有 X, P X」 ↔ 「凡 X, 不 P X」 (existential negation). -/
theorem bu_you_eq_fan_bu {α : Sort _} (P : α → Prop) :
    «不» («有» P) ↔ «凡» (fun x => «不» (P x)) :=
  ⟨fun h x hp => h ⟨x, hp⟩, fun h ⟨x, hp⟩ => h x hp⟩

/-- 「不 凡 X, P X」 ↔ 「有 X, 不 P X」 (universal negation). -/
theorem bu_fan_eq_you_bu {α : Sort _} (P : α → Prop) :
    «不» («凡» P) ↔ «有» (fun x => «不» (P x)) := bu_fan_eq_exists_not P

/-! ## Batch 3: instrumentals, copulas, demonstratives, iteration -/

/-! ### 以 (yi) — instrumental: 「以 f 之 x」 = f applied via instrument. -/

/-- 以 (yi): instrumental. 等同 application; semantic role = "by means of f, on x". -/
abbrev «以» {α β : Sort _} (f : α → β) (x : α) : β := f x
abbrev yiBy {α β : Sort _} (f : α → β) (x : α) : β := f x
theorem yi_eq_app {α β : Sort _} (f : α → β) (x : α) : «以» f x = f x := rfl

/-! ### 为 (wei) — copula: 「A 为 B」 = A is B. -/

/-- 为 (wei): copula. 「A 为 B」 ≡ A = B. -/
abbrev «为» {α : Sort _} (a b : α) : Prop := a = b
abbrev weiCop {α : Sort _} (a b : α) : Prop := a = b
theorem wei_eq_eq {α : Sort _} (a b : α) : («为» a b) = (a = b) := rfl

/-! ### 所 (suo) — relative pronoun: 「所 P」 = "that which P". -/

/-- 所 (suo): relative pronoun / nominalizer. Acts as identity on predicates. -/
abbrev «所» {α : Sort _} (P : α → Prop) : α → Prop := P
abbrev suoOp {α : Sort _} (P : α → Prop) : α → Prop := P
theorem suo_eq {α : Sort _} (P : α → Prop) : «所» P = P := rfl

/-! ### 其 (qi) — anaphoric/possessive: 「其 f x」 = f applied to anaphoric subject. -/

/-- 其 (qi): anaphoric reference. 等同 application; semantic role = "its f-of-x". -/
abbrev «其» {α β : Sort _} (f : α → β) (x : α) : β := f x
abbrev qiOp {α β : Sort _} (f : α → β) (x : α) : β := f x
theorem qi_eq_app {α β : Sort _} (f : α → β) (x : α) : «其» f x = f x := rfl

/-! ### 此 / 彼 (ci, bi) — demonstratives. -/

/-- 此 (ci): "this" — identity on the current focus. -/
abbrev «此» {α : Sort _} (a : α) : α := a
abbrev ciOp {α : Sort _} (a : α) : α := a
theorem ci_eq {α : Sort _} (a : α) : «此» a = a := rfl

/-- 彼 (bi): "that" — identity on a distinguished other focus. -/
abbrev «彼» {α : Sort _} (a : α) : α := a
abbrev biThat {α : Sort _} (a : α) : α := a
theorem bi_eq {α : Sort _} (a : α) : «彼» a = a := rfl

/-! ### 乃 (nai) — sequential "thereupon": 「A 乃 B」 = A then B. -/

/-- 乃 (nai): sequential connective. 「A 乃 B」 ≡ A → B. -/
abbrev «乃» (P Q : Prop) : Prop := P → Q
abbrev naiOp (P Q : Prop) : Prop := P → Q
theorem nai_eq_imp (P Q : Prop) : («乃» P Q) = (P → Q) := rfl

/-! ### 复 (fu) — n-fold iteration. -/

/-- 复 (fu): n-fold iteration. 「复 0 f x = x」, 「复 (n+1) f x = f (复 n f x)」. -/
def «复» {α : Sort _} : Nat → (α → α) → α → α
  | 0, _, x => x
  | n+1, f, x => f («复» n f x)
def fuOp {α : Sort _} : Nat → (α → α) → α → α := @«复» α
theorem fu_zero {α : Sort _} (f : α → α) (x : α) : «复» 0 f x = x := rfl
theorem fu_succ {α : Sort _} (n : Nat) (f : α → α) (x : α) :
    «复» (n+1) f x = f («复» n f x) := rfl
theorem fu_one {α : Sort _} (f : α → α) (x : α) : «复» 1 f x = f x := rfl

/-! ### 至 (zhi-reach) — bounded iteration: 「至 P f x」 = ∃ n, P (复 n f x). -/

/-- 至 (zhi-reach): existence of an iteration step satisfying P. -/
abbrev «至» {α : Sort _} (P : α → Prop) (f : α → α) (x : α) : Prop :=
  ∃ n : Nat, P («复» n f x)
abbrev zhiReach {α : Sort _} (P : α → Prop) (f : α → α) (x : α) : Prop :=
  ∃ n : Nat, P («复» n f x)
theorem zhi_reach_eq {α : Sort _} (P : α → Prop) (f : α → α) (x : α) :
    «至» P f x = (∃ n : Nat, P («复» n f x)) := rfl

/-! ### 同 / 异 (tong, yi-diff) — equality / inequality. -/

/-- 同 (tong): equality. 「a 同 b」 ≡ a = b. -/
abbrev «同» {α : Sort _} (a b : α) : Prop := a = b
abbrev tongOp {α : Sort _} (a b : α) : Prop := a = b
theorem tong_eq_eq {α : Sort _} (a b : α) : («同» a b) = (a = b) := rfl
theorem tong_refl {α : Sort _} (a : α) : «同» a a := rfl
theorem tong_symm {α : Sort _} {a b : α} : «同» a b → «同» b a := Eq.symm
theorem tong_trans {α : Sort _} {a b c : α} : «同» a b → «同» b c → «同» a c := Eq.trans

/-- 异 (yi-diff): inequality. 「a 异 b」 ≡ a ≠ b. -/
abbrev «异» {α : Sort _} (a b : α) : Prop := a ≠ b
abbrev yiDiff {α : Sort _} (a b : α) : Prop := a ≠ b
theorem yi_diff_eq_ne {α : Sort _} (a b : α) : («异» a b) = (a ≠ b) := rfl
theorem yi_diff_eq_bu_tong {α : Sort _} (a b : α) :
    «异» a b ↔ «不» («同» a b) := Iff.rfl

/-! ### 反 (fan-inv) — reversal/involution on propositions. -/

/-- 反 (fan-inv): propositional reversal. 「反 P」 ≡ ¬ P (classical involution). -/
abbrev «反» (P : Prop) : Prop := ¬ P
abbrev fanInv (P : Prop) : Prop := ¬ P
theorem fan_eq_not (P : Prop) : («反» P) = (¬ P) := rfl
theorem fan_fan (P : Prop) : «反» («反» P) ↔ P := by
  unfold «反»; exact ⟨fun h => Classical.byContradiction h, fun hp hnp => hnp hp⟩

/-! ### 非 (fei) — strong negation. Classically equal to 不. -/

/-- 非 (fei): strong negation. 「非 P」 ≡ ¬ P. -/
abbrev «非» (P : Prop) : Prop := ¬ P
abbrev feiOp (P : Prop) : Prop := ¬ P
theorem fei_eq_not (P : Prop) : («非» P) = (¬ P) := rfl
theorem fei_eq_bu (P : Prop) : «非» P ↔ «不» P := Iff.rfl

/-! ### Composite theorems for batch 3. -/

/-- 「以 f 为 (f x) 之 x」 = trivial copula match. -/
theorem yi_wei_app {α β : Sort _} (f : α → β) (x : α) :
    «为» («以» f x) (f x) := rfl

/-- 复 之 加法分配: 复 (n+m) f x = 复 n f (复 m f x). -/
theorem fu_add {α : Sort _} (n m : Nat) (f : α → α) (x : α) :
    «复» (n + m) f x = «复» n f («复» m f x) := by
  induction n with
  | zero => simp [«复»]
  | succ k ih =>
    show «复» (k + 1 + m) f x = f («复» k f («复» m f x))
    rw [show k + 1 + m = (k + m) + 1 from by omega, fu_succ, ih]

/-- 复 之 1 加 n: 复 (n+1) f x = 复 n f (f x) — iteration commutes with one step. -/
theorem fu_succ_inside {α : Sort _} (n : Nat) (f : α → α) (x : α) :
    «复» (n + 1) f x = «复» n f (f x) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show f («复» (k + 1) f x) = f («复» k f (f x))
    rw [ih]

/-- 「至 P f x」 trivially holds 若 P x already (n=0). -/
theorem zhi_reach_zero {α : Sort _} {P : α → Prop} {f : α → α} {x : α}
    (h : P x) : «至» P f x := ⟨0, h⟩

/-- 「至 P f x」 holds 若 P (f x) (n=1 witness). -/
theorem zhi_reach_one {α : Sort _} {P : α → Prop} {f : α → α} {x : α}
    (h : P (f x)) : «至» P f x := ⟨1, h⟩

/-! ## Batch 4: quantifier variants, affirmation/denial particles -/

/-! ### 皆 (jie) — "all"; universal alias for 凡. -/

/-- 皆 (jie): universal quantifier (alternate of 凡). -/
abbrev «皆» {α : Sort _} (P : α → Prop) : Prop := ∀ x, P x
abbrev jieOp {α : Sort _} (P : α → Prop) : Prop := ∀ x, P x
theorem jie_eq_fan {α : Sort _} (P : α → Prop) : «皆» P ↔ «凡» P := Iff.rfl

/-! ### 莫 (mo) — "none"; alias for 无. -/

/-- 莫 (mo): emptiness quantifier (alternate of 无). -/
abbrev «莫» {α : Sort _} (P : α → Prop) : Prop := ¬ ∃ x, P x
abbrev moOp {α : Sort _} (P : α → Prop) : Prop := ¬ ∃ x, P x
theorem mo_eq_wu {α : Sort _} (P : α → Prop) : «莫» P ↔ «无» P := Iff.rfl

/-! ### 唯 (wei-only) — uniqueness. -/

/-- 唯 (wei-only): unique-existence quantifier. -/
abbrev «唯» {α : Sort _} (P : α → Prop) : Prop := ∃ x, P x ∧ ∀ y, P y → y = x
abbrev weiOnly {α : Sort _} (P : α → Prop) : Prop := ∃ x, P x ∧ ∀ y, P y → y = x
theorem wei_only_eq {α : Sort _} (P : α → Prop) :
    («唯» P) = (∃ x, P x ∧ ∀ y, P y → y = x) := rfl

/-! ### 然 (ran) — affirmation: 「P 然」 = P holds. -/

/-- 然 (ran): affirmation marker (identity on Prop). -/
abbrev «然» (P : Prop) : Prop := P
abbrev ranOp (P : Prop) : Prop := P
theorem ran_eq (P : Prop) : «然» P = P := rfl

/-- The isness micro-family and its companion operators are all single-glyph
    operators reducing to existing Lean primitives, with no new axioms. -/
theorem isness_with_companion_operators
    {α β Γ : Sort _} (x y : α) (R : α → α → Prop) (f : α → β)
    (PΓ : Γ → Prop) (ctx : Γ) (P Q : Prop) :
    («是» x y ↔ x = y) ∧
      («系» R x y ↔ R x y) ∧
      («之» f x = f x) ∧
      («的» f x = f x) ∧
      («地» PΓ ctx ↔ PΓ ctx) ∧
      («于» PΓ ctx ↔ PΓ ctx) ∧
      («所» PΓ = PΓ) ∧
      («有» PΓ ↔ ∃ z : Γ, PΓ z) ∧
      («无» PΓ ↔ ¬ ∃ z : Γ, PΓ z) ∧
      («为» x y = (x = y)) ∧
      («者» f = f) ∧
      («也» P ↔ P) ∧
      («然» Q = Q) := by
  simp [«是», «系», «之», «的», «地», «于», «所», «有», «无», «为», «者», «也», «然»]

/-! ### 否 (fou) — interrogative denial: 「P 否」 ≡ ¬ P. -/

/-- 否 (fou): denial / interrogative-negation marker. -/
abbrev «否» (P : Prop) : Prop := ¬ P
abbrev fouOp (P : Prop) : Prop := ¬ P
theorem fou_eq_not (P : Prop) : «否» P = (¬ P) := rfl
theorem fou_eq_bu (P : Prop) : «否» P ↔ «不» P := Iff.rfl

/-! ### 各 (ge) — distributive: 「各 P」 = each satisfies P (= 凡). -/

/-- 各 (ge): distributive universal (each individually satisfies P). -/
abbrev «各» {α : Sort _} (P : α → Prop) : Prop := ∀ x, P x
abbrev geOp {α : Sort _} (P : α → Prop) : Prop := ∀ x, P x
theorem ge_eq_fan {α : Sort _} (P : α → Prop) : «各» P ↔ «凡» P := Iff.rfl

/-! ## § 之 as axiomatic combinator — dimensional generation

之 IS the architectural primitive: function application. Every other compounding
operator decomposes through 之. This section demonstrates the decomposition,
making 之-primacy structurally explicit (not merely notational).

Reading guide:
  - 「f 之 x」 consumes one structural dimension (descends one level in the tower).
  - Iterating 之 (via 复 / 而 / X之又X) navigates n-level structures.
  - 之 alone descends; 者 marks an abstraction point (where new dimension is bound).

Each equivalence theorem here is `rfl` — the existing operator definitions ARE
之-compositions, just written in surface form. No new axioms; only decomposition.
-/

namespace ZhiPrimacy

/-! ### Direct identities: aliases that are just 之 in different roles. -/

/-- 以 = 之 (instrumental ≡ application). -/
theorem yi_is_zhi {α β : Sort _} (f : α → β) (x : α) :
    «以» f x = «之» f x := rfl

/-- 其 = 之 (anaphoric ≡ application). -/
theorem qi_is_zhi {α β : Sort _} (f : α → β) (x : α) :
    «其» f x = «之» f x := rfl

/-- 者 之 application is 之: applying a 者-marked function = 之-application. -/
theorem zhe_app_is_zhi {α β : Sort _} (f : α → β) (x : α) :
    «之» («者» f) x = «之» f x := rfl

/-! ### Composite identities: operators built by iterating 之. -/

/-- 而 = 之 ∘ 之 (sequencing ≡ two 之-applications, inner-then-outer). -/
theorem er_is_double_zhi {α : Sort _} (f g : α → α) (x : α) :
    «而» f g x = «之» g («之» f x) := rfl

/-- 复 (n+1) = 之-prepend (one more 之-application onto n-fold iteration). -/
theorem fu_succ_is_zhi {α : Sort _} (n : Nat) (f : α → α) (x : α) :
    «复» (n + 1) f x = «之» f («复» n f x) := rfl

/-- X之又X = 之-iterated; literally "X 之 X 之 ... 之 X" (n-fold 之 chain). -/
theorem XzhiyouX_succ_is_zhi {α : Sort _} (f : α → α) (n : Nat) (x : α) :
    XzhiyouX f (n + 1) x = «之» f (XzhiyouX f n x) := rfl

/-- 至 之 witness reduces to 之-iteration: 「至 P f x at step n」 ≡ P (复 n f x). -/
theorem zhi_reach_witness_is_fu {α : Sort _} (P : α → Prop) (f : α → α) (x : α) (n : Nat) :
    P («复» n f x) ↔ P («复» n f x) := Iff.rfl

/-! ### Dimensional tower: 之 as level-traversal operator. -/

/-- 之-tower over base α: at level n, structures of arity n+1 (n 之-applications away from atom).
    Level 0 = atomic α. Level n+1 = α → (level n). -/
def ZhiTower (α : Type) : Nat → Type
  | 0 => α
  | n + 1 => α → ZhiTower α n

/-- Tower at level 0 reduces to the base atom. -/
theorem tower_zero (α : Type) : ZhiTower α 0 = α := rfl

/-- Tower at level n+1 reads as α → (tower at level n). -/
theorem tower_succ (α : Type) (n : Nat) :
    ZhiTower α (n + 1) = (α → ZhiTower α n) := rfl

/-- 之 descends the tower: applying f at level n+1 to x : α yields a level-n structure. -/
def zhi_descend {α : Type} (n : Nat) (f : ZhiTower α (n + 1)) (x : α) : ZhiTower α n :=
  «之» f x

/-- 之 at level 1 yields an atom: f : α → α applied to x : α gives x' : α. -/
theorem zhi_at_level_one {α : Type} (f : ZhiTower α 1) (x : α) :
    zhi_descend 0 f x = «之» f x := rfl

/-- n successive 之-applications navigate from level n to level 0 (atom).
    Take f : level-n tower, supply n atomic arguments, end at an atom. -/
def zhi_descend_all {α : Type} : (n : Nat) → ZhiTower α n → (Nat → α) → α
  | 0, x, _ => x
  | n + 1, f, args => zhi_descend_all n («之» f (args 0)) (fun k => args (k + 1))

/-- Atomic level: zero descents leaves the value unchanged. -/
theorem zhi_descend_all_zero {α : Type} (x : α) (args : Nat → α) :
    zhi_descend_all 0 x args = x := rfl

/-! ### 者 — abstraction binder, dual to 之.

之 (apply) DESCENDS dimensions: f at level n+1, x at atom → result at level n.
者 (abstract) ASCENDS dimensions: a-dependent expression at level n → packaged at level n+1.

Together: 之 + 者 = bidirectional dimensional navigator.
The pair forms a Galois connection (round-trip identities below).

Reading guide:
  - "X 者 ... 也" in wenyan introduces a binding: "X is that-which (...)".
  - In type theory: 者 is the λ-abstraction marker.
  - At the term level, 者 = id (Lean's λ is native), but its ROLE is structural.
-/

/-- 者 ascends the tower: a function-of-α valued at level n is a level-(n+1) structure. -/
def zhe_ascend {α : Type} (n : Nat) (g : α → ZhiTower α n) : ZhiTower α (n + 1) :=
  «者» g

/-- 者-applied = original function (者 is identity at the term level). -/
theorem zhe_ascend_eq {α : Type} (n : Nat) (g : α → ZhiTower α n) (x : α) :
    zhe_ascend n g x = g x := rfl

/-- Round-trip 1: ascend-then-descend recovers the original argument.
    者 之 之 = id (descending what was just abstracted yields the original). -/
theorem zhe_then_zhi {α : Type} (n : Nat) (g : α → ZhiTower α n) (x : α) :
    zhi_descend n (zhe_ascend n g) x = g x := rfl

/-- Round-trip 2: descend-then-ascend recovers the original function.
    之 之 者 = id (abstracting an applied function via η yields the original). -/
theorem zhi_then_zhe {α : Type} (n : Nat) (f : ZhiTower α (n + 1)) :
    zhe_ascend n (fun x => zhi_descend n f x) = f := rfl

/-! ### Operators expressed via 之 + 者 (bidirectional navigation). -/

/-- 而 f g = 者 (λ x. 之 g (之 f x)) — sequencing as abstract-of-double-application.
    A 之 sequence wrapped by 者 to package as a new function. -/
theorem er_via_zhe_zhi {α : Sort _} (f g : α → α) :
    «而» f g = «者» (fun x => «之» g («之» f x)) := rfl

/-- 复 (succ) = 者 (λ x. 之 f (复 n f x)) — iteration packaged via 者.
    Each iteration step abstracts (者) the prior 之-chain. -/
theorem fu_via_zhe_zhi {α : Sort _} (n : Nat) (f : α → α) :
    («复» (n + 1) f) = «者» (fun x => «之» f («复» n f x)) := rfl

/-- 自 = 者 of identity: «自» abstracts the identity-on-α as a level-1 structure. -/
theorem zi_via_zhe {α : Sort _} :
    (fun x : α => «自» x) = «者» (fun x : α => x) := rfl

/-- Tower iso: level (n+1) ≃ (α → level n) via 之/者 round-trip.
    Statement: every level-(n+1) structure decomposes as (者 ∘ application). -/
theorem tower_iso {α : Type} (n : Nat) (f : ZhiTower α (n + 1)) :
    f = zhe_ascend n (fun x => zhi_descend n f x) := rfl

end ZhiPrimacy

end SSBX.Foundation.Wen.Operators
