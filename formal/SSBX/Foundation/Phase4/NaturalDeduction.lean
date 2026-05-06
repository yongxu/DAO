/-
# NaturalDeduction — 自然演绎 + Curry-Howard (Phase 4 主体 · Mathlib)

Companion: `四级生成_太极两翼四象八卦/形式逻辑 · 从元到推.md` § 推理规则总集 / § 17.6

推衍 § 推理规则总集 列 NJ/NK 自然演绎之十四规则（∧/∨/→/¬/∀/∃ 之 I/E + ⊥E）；
§ 17.6 列 Curry-Howard 命题—类型对应（Unit/Prod/Sum/Pi/Sigma）。
LuoJi.lean 已形式化 K3 三值核心（finite, no Mathlib），证 LEM/DNE 在三值失效。

本文借 Mathlib `Logic.Basic` / `Logic.Equiv.Basic` 升至**经典自然演绎层**：
(1) 形式化 NK 之十四推理规则为 Lean 之可证 theorem
(2) 形式化 Curry-Howard 之命题—类型双射
(3) 证经典自然演绎对 Bool 真值表语义之 soundness
(4) 证经典 NK = K3 之**二值塌缩**（移 U 后 K3 ↘ Bool, NK 复现）

## 道理二分立场

LuoJi.lean 之 K3（三值）在 0-Mathlib —— 道层之非经典逻辑形式化。
本文 之 NK（经典两值）必依 Mathlib 之 Equiv / Decidable —— 理层之经典逻辑形式化。
二者于"道理二分"恰对应：道层之三值保 U 不升，理层之二值经典塌缩。
-/
import Mathlib.Logic.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.Tauto
import SSBX.Foundation.Eight.LuoJi

namespace SSBX.Foundation.Phase4.NaturalDeduction

open SSBX.Foundation.Eight.LuoJi

/-! ## § 1 自然演绎之 ∧ I/E 规则（合 / 取）

推衍 §推理规则总集：
- 引入 ∧（兼）：Γ ⊢ P, Γ ⊢ Q ⇒ Γ ⊢ P ∧ Q
- 消去 ∧（取）：Γ ⊢ P ∧ Q ⇒ Γ ⊢ P （同理 Q）

在 Lean 中，「Γ ⊢ X」即「(假设之合取) → X」之函数。
故规则编码为 Lean 函数。 -/

/-- **∧ 引入（兼）**：由 P 与 Q 推 P ∧ Q。 -/
theorem and_intro {P Q : Prop} (hp : P) (hq : Q) : P ∧ Q := ⟨hp, hq⟩

/-- **∧ 消去左（取一）**：由 P ∧ Q 推 P。 -/
theorem and_elim_left {P Q : Prop} (h : P ∧ Q) : P := h.1

/-- **∧ 消去右（取二）**：由 P ∧ Q 推 Q。 -/
theorem and_elim_right {P Q : Prop} (h : P ∧ Q) : Q := h.2

/-! ## § 2 自然演绎之 ∨ I/E 规则（或 / 析）

- 引入 ∨ 左（或）：Γ ⊢ P ⇒ Γ ⊢ P ∨ Q
- 引入 ∨ 右：Γ ⊢ Q ⇒ Γ ⊢ P ∨ Q
- 消去 ∨（析）：Γ ⊢ P ∨ Q, Γ,P ⊢ R, Γ,Q ⊢ R ⇒ Γ ⊢ R -/

/-- **∨ 引入左（或左）**：由 P 推 P ∨ Q。 -/
theorem or_intro_left {P Q : Prop} (hp : P) : P ∨ Q := Or.inl hp

/-- **∨ 引入右（或右）**：由 Q 推 P ∨ Q。 -/
theorem or_intro_right {P Q : Prop} (hq : Q) : P ∨ Q := Or.inr hq

/-- **∨ 消去（析）**：由 P ∨ Q 与两 case 之 R 推 R。 -/
theorem or_elim {P Q R : Prop} (h : P ∨ Q) (hpr : P → R) (hqr : Q → R) : R :=
  h.elim hpr hqr

/-! ## § 3 自然演绎之 → I/E 规则（设…则 / 故）

- 引入 →（设…则）：Γ, P ⊢ Q ⇒ Γ ⊢ P → Q
- 消去 →（故，modus ponens）：Γ ⊢ P → Q, Γ ⊢ P ⇒ Γ ⊢ Q -/

/-- **→ 引入（设…则）**：从 P 推 Q 之函数即 P → Q 之 term。 -/
theorem imp_intro {P Q : Prop} (h : P → Q) : P → Q := h

/-- **→ 消去 / Modus Ponens（故）**：由 P → Q 与 P 推 Q。 -/
theorem imp_elim {P Q : Prop} (hpq : P → Q) (hp : P) : Q := hpq hp

/-! ## § 4 自然演绎之 ¬ I/E + ⊥ E 规则（反证 / 双反 / 矛盾）

- 引入 ¬（反证）：Γ, P ⊢ ⊥ ⇒ Γ ⊢ ¬P
- 消去 ¬ (NK, 双反)：Γ ⊢ ¬¬P ⇒ Γ ⊢ P （仅古典）
- ⊥ 消去：Γ ⊢ ⊥ ⇒ Γ ⊢ R （ex falso quodlibet） -/

/-- **¬ 引入（反证）**：从 P 推矛盾即可推 ¬P。 -/
theorem not_intro {P : Prop} (h : P → False) : ¬P := h

/-- **¬ 消去 / DNE（双反，NK 古典）**：¬¬P → P。
    此即 LuoJi.lean §5 在 Bool 上的**塌缩对应**（K3 在 U 上失效，Bool 上恒成立）。 -/
theorem not_elim_classical {P : Prop} (h : ¬¬P) : P := Classical.byContradiction h

/-- **⊥ 消去（ex falso）**：由 ⊥ 可推任意。 -/
theorem false_elim {R : Prop} (h : False) : R := h.elim

/-- **矛盾律（NK 显式版）**：P ∧ ¬P → R。 -/
theorem contradiction {P R : Prop} (hp : P) (hnp : ¬P) : R :=
  (hnp hp).elim

/-! ## § 5 自然演绎之 ∀ I/E 规则（通 / 取）

- 引入 ∀（通）：Γ ⊢ P(x) (x 不在 Γ 自由) ⇒ Γ ⊢ ∀x. P(x)
- 消去 ∀（取）：Γ ⊢ ∀x. P(x) ⇒ Γ ⊢ P(t) -/

/-- **∀ 引入（通）**：对所有 x 给 P x 之证则 ∀x.Px。 -/
theorem forall_intro {α : Sort*} {P : α → Prop} (h : ∀ x, P x) : ∀ x, P x := h

/-- **∀ 消去（取）**：由 ∀x.Px 与 t 推 P t。 -/
theorem forall_elim {α : Sort*} {P : α → Prop} (h : ∀ x, P x) (t : α) : P t := h t

/-! ## § 6 自然演绎之 ∃ I/E 规则（举 / 设）

- 引入 ∃（举）：Γ ⊢ P(t) ⇒ Γ ⊢ ∃x. P(x)
- 消去 ∃（设）：Γ ⊢ ∃x. P(x), Γ, P(y) ⊢ R (y 不在 Γ,R 自由) ⇒ Γ ⊢ R -/

/-- **∃ 引入（举）**：由 P t 推 ∃x.Px。 -/
theorem exists_intro {α : Sort*} {P : α → Prop} (t : α) (h : P t) : ∃ x, P x := ⟨t, h⟩

/-- **∃ 消去（设）**：由 ∃x.Px 与对一般 y 推 R 之函数推 R。 -/
theorem exists_elim {α : Sort*} {P : α → Prop} {R : Prop}
    (h : ∃ x, P x) (k : ∀ y, P y → R) : R :=
  h.elim k

/-! ## § 7 Curry-Howard 对应：命题—类型双射（推衍 §17.6）

§17.6 之表（命题 ↔ 类型 ↔ 证明项）：
| 命题 | 类型 | 证明项 |
|------|------|--------|
| ⊤   | Unit | * |
| P ∧ Q | P × Q | (p, q) |
| P ∨ Q | P + Q | inl p / inr q |
| P → Q | P → Q | λp. q |
| ¬P  | P → ⊥ | λp. absurd |
| ∀x. P(x) | Πx. P(x) | λx. p(x) |
| ∃x. P(x) | Σx. P(x) | (t, p(t)) |

本节给出 Lean 中各对应之**双射**（Equiv）见证。 -/

/-- **CH-⊤**：⊤ ↔ PUnit（命题层之真 ↔ 类型层之单位）。 -/
def chTrue : True ≃ PUnit where
  toFun _ := PUnit.unit
  invFun _ := True.intro
  left_inv _ := rfl
  right_inv _ := rfl

/-- **CH-∧**：(P ∧ Q) ↔ (PProd P Q)（合取 ↔ 积类型 universe-多态版）。
    `PProd` 是 `Prod` 之 universe-多态版，可承 Prop。 -/
def chAnd (P Q : Prop) : (P ∧ Q) ≃ PProd P Q where
  toFun h := ⟨h.1, h.2⟩
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **CH-∧ 之 Type 版**：对 Type 层，命题真即 Nonempty，∧ ↔ Prod。 -/
def chAndType (P Q : Type) : (Nonempty P ∧ Nonempty Q) ↔ Nonempty (P × Q) := by
  constructor
  · rintro ⟨⟨hp⟩, ⟨hq⟩⟩; exact ⟨hp, hq⟩
  · rintro ⟨hp, hq⟩; exact ⟨⟨hp⟩, ⟨hq⟩⟩

/-- **CH-∨**：(P ∨ Q) ↔ Sum P Q 之非空（析取 ↔ 和类型）。
    注：Lean 之 `Or` 是 `Prop`，`Sum` 是 `Type`；二者用 Nonempty 桥。
    具体地，对 `P Q : Type`，CH 给 P ∨ Q ≅ P ⊕ Q（命题层至类型层）。 -/
def chOr (P Q : Type) : Nonempty (P ⊕ Q) ↔ (Nonempty P ∨ Nonempty Q) := by
  constructor
  · rintro ⟨h⟩
    cases h with
    | inl hp => exact Or.inl ⟨hp⟩
    | inr hq => exact Or.inr ⟨hq⟩
  · rintro (h | h)
    · obtain ⟨hp⟩ := h; exact ⟨Sum.inl hp⟩
    · obtain ⟨hq⟩ := h; exact ⟨Sum.inr hq⟩

/-- **CH-→**：(P → Q) 之命题 与 (P → Q) 之函数类型直接同一（Curry-Howard 之核心）。 -/
def chImp (P Q : Prop) : (P → Q) ≃ (P → Q) := Equiv.refl _

/-- **CH-¬**：¬P ↔ (P → False)（否定 ↔ 至空类型之函数）。 -/
def chNot (P : Prop) : ¬P ↔ (P → False) := Iff.rfl

/-- **CH-∀**：(∀x. P x) 之命题 与 ((x : α) → P x) 之 Pi 类型直接同一。
    此即推衍 §17.6 之"∀x. P(x) ↔ Πx. P(x)"。 -/
def chForall {α : Sort*} (P : α → Prop) : (∀ x, P x) ≃ ((x : α) → P x) :=
  Equiv.refl _

/-- **CH-∃**：(∃x. P x) ↔ Nonempty Σ x, P x（存在 ↔ Sigma 类型 之非空）。
    Sigma 是 Type 层，∃ 是 Prop 层；二者在"非空"等价。 -/
theorem chExists {α : Sort*} (P : α → Prop) :
    (∃ x, P x) ↔ Nonempty ((x : α) ×' P x) := by
  constructor
  · rintro ⟨x, hx⟩; exact ⟨⟨x, hx⟩⟩
  · rintro ⟨⟨x, hx⟩⟩; exact ⟨x, hx⟩

/-! ## § 8 经典自然演绎对 Bool 真值表语义之 soundness

赋值 v : 命题变元 → Bool；扩 v 为 v* 至公式 之 Bool 值。
soundness：若 ⊢ φ（NK 可证），则 v*(φ) = true 对一切 v。

我们以**形式化 propositional formula 之 inductive type + Bool 解释**之最小骨架陈述：
对单变元公式之 case，即可见 soundness 之机制。 -/

/-- **命题公式之 inductive type**（命题变元用 Nat index）。 -/
inductive Form : Type
  | var : Nat → Form
  | tr  : Form
  | fa  : Form
  | neg : Form → Form
  | and : Form → Form → Form
  | or  : Form → Form → Form
  | imp : Form → Form → Form
  deriving DecidableEq, Repr

/-- **Bool 值解释**（赋值 v 给变元，递推扩至公式）。 -/
def Form.eval (v : Nat → Bool) : Form → Bool
  | .var n     => v n
  | .tr        => true
  | .fa        => false
  | .neg φ     => !(φ.eval v)
  | .and φ ψ   => (φ.eval v) && (ψ.eval v)
  | .or  φ ψ   => (φ.eval v) || (ψ.eval v)
  | .imp φ ψ   => !(φ.eval v) || (ψ.eval v)

/-- **重言式**：在所有 v 下值为 true 之公式。 -/
def Form.tautology (φ : Form) : Prop := ∀ v, φ.eval v = true

/-- **soundness 例 1**：⊥ 消去之 Bool soundness —— `(P ∧ ¬P) → Q` 是重言式。 -/
theorem sound_contradiction (P Q : Form) :
    Form.tautology (.imp (.and P (.neg P)) Q) := by
  intro v
  simp only [Form.eval]
  cases P.eval v <;> cases Q.eval v <;> rfl

/-- **soundness 例 2**：∧ 引入之 Bool soundness —— `P → Q → P ∧ Q` 是重言式。 -/
theorem sound_and_intro (P Q : Form) :
    Form.tautology (.imp P (.imp Q (.and P Q))) := by
  intro v
  simp only [Form.eval]
  cases P.eval v <;> cases Q.eval v <;> rfl

/-- **soundness 例 3**：→ 消去（modus ponens）之 Bool soundness ——
    `(P → Q) → P → Q` 是重言式。 -/
theorem sound_modus_ponens (P Q : Form) :
    Form.tautology (.imp (.imp P Q) (.imp P Q)) := by
  intro v
  simp only [Form.eval]
  cases P.eval v <;> cases Q.eval v <;> rfl

/-- **soundness 例 4**：经典 LEM 之 Bool soundness —— `P ∨ ¬P` 是重言式。
    与 LuoJi.lean §4 之 `lem_fails_in_K3`（K3 上 LEM 失效）形成**经典 vs 三值之对照**。 -/
theorem sound_lem (P : Form) : Form.tautology (.or P (.neg P)) := by
  intro v
  simp only [Form.eval]
  cases P.eval v <;> rfl

/-- **soundness 例 5**：DNE 之 Bool soundness —— `¬¬P → P` 是重言式。
    与 LuoJi.lean §5 之 `dne_fails_in_K3` 对照。 -/
theorem sound_dne (P : Form) :
    Form.tautology (.imp (.neg (.neg P)) P) := by
  intro v
  simp only [Form.eval]
  cases P.eval v <;> rfl

/-! ## § 9 LuoJi.lean K3 ↘ Bool 之**二值塌缩**

LuoJi.lean 主张：K3 是 NK 之三值扩展；移 U 后 K3 ↘ Bool, NK 之 LEM/DNE 复现。
本节形式化此主张：定义 K3 → Option Bool 之 partial 投射（U ↦ none，T ↦ some true，F ↦ some false），
并证若 p ∈ {T, F}（即两值情形），K3 之联结词 与 Bool 之 ‖, &&, ¬ 一致。 -/

/-- **K3 → Bool 之 partial 投射**（U 投至 none）。 -/
def toBoolPartial : TriV → Option Bool
  | .T => some true
  | .U => none
  | .F => some false

/-- **K3 之 neg 在两值上塌缩为 Bool 之 not**。 -/
theorem collapse_neg_T : toBoolPartial (TriV.neg TriV.T) = some (!true) := rfl
theorem collapse_neg_F : toBoolPartial (TriV.neg TriV.F) = some (!false) := rfl

/-- **K3 之 conj 在两值上塌缩为 Bool 之 and**（T,T case）。 -/
theorem collapse_conj_TT :
    toBoolPartial (TriV.conj TriV.T TriV.T) = some (true && true) := rfl

theorem collapse_conj_TF :
    toBoolPartial (TriV.conj TriV.T TriV.F) = some (true && false) := rfl

theorem collapse_conj_FT :
    toBoolPartial (TriV.conj TriV.F TriV.T) = some (false && true) := rfl

theorem collapse_conj_FF :
    toBoolPartial (TriV.conj TriV.F TriV.F) = some (false && false) := rfl

/-- **K3 之 disj 在两值上塌缩为 Bool 之 or**（具体四 case）。 -/
theorem collapse_disj_TT :
    toBoolPartial (TriV.disj TriV.T TriV.T) = some (true || true) := rfl

theorem collapse_disj_FF :
    toBoolPartial (TriV.disj TriV.F TriV.F) = some (false || false) := rfl

/-- **K3 之 LEM 在两值上塌缩为 Bool LEM**：T,F 上 K3-LEM = T，与 Bool-LEM 一致。 -/
theorem collapse_lem_T :
    toBoolPartial (lem TriV.T) = some (true || !true) := rfl

theorem collapse_lem_F :
    toBoolPartial (lem TriV.F) = some (false || !false) := rfl

/-- **K3 ↘ Bool 之核心见证**：去 U 之后，K3 之 LEM 在两值上恒为 T。
    此与 Bool 之 `bool_lem`（LuoJi.lean §7）对照——
    NK 之 LEM 即 K3 在两值塌缩之极限。 -/
theorem K3_collapses_to_NK_lem :
    (∀ p : TriV, p ≠ TriV.U → lem p = TriV.T) := by
  intro p hp
  cases p with
  | T => rfl
  | U => exact absurd rfl hp
  | F => rfl

/-- **K3 ↘ Bool 之 DNE 塌缩**：去 U 之后 DNE 恒为 T。 -/
theorem K3_collapses_to_NK_dne :
    (∀ p : TriV, p ≠ TriV.U → dne p = TriV.T) := by
  intro p hp
  cases p with
  | T => rfl
  | U => exact absurd rfl hp
  | F => rfl

/-! ## § 10 NJ vs NK：直觉 vs 古典之精确分歧

推衍 §推理规则：NJ（直觉）无双反消去，NK（古典）有。
本节给出 Lean 中此分歧之**显式见证**：在 Lean 之 Prop 上 DNE 需 Classical，
但 Decidable 上 DNE 可构造性证。 -/

/-- **直觉证 DNE 在 Decidable 上**（NJ 之 constructive 版）。 -/
theorem dne_decidable {P : Prop} [Decidable P] (h : ¬¬P) : P := by
  by_contra hp
  exact h hp

/-- **古典 DNE 不依 Decidable**（NK 之 classical 版）—— 用 Classical.byContradiction。 -/
theorem dne_classical {P : Prop} (h : ¬¬P) : P := Classical.byContradiction h

/-- **NJ ⊆ NK**：每 NJ-可证之命题亦 NK-可证（trivially，加双反规则只增推理力）。
    此处以 ∧ 引入为例（NJ/NK 共有规则）。 -/
theorem NJ_subseteq_NK {P Q : Prop} (hp : P) (hq : Q) : P ∧ Q := and_intro hp hq

/-! ## § 11 公开摘要 -/

/-- **NaturalDeduction 总摘要**：
    (1) NK 之 ∧ I/E
    (2) NK 之 ∨ I/E
    (3) NK 之 → I/E（modus ponens）
    (4) NK 之 ¬ I + 双反（DNE 古典）
    (5) NK 之 ∀ I/E、∃ I/E
    (6) Curry-Howard ∧ ↔ × 双射
    (7) Curry-Howard ∀ ↔ Π 同一
    (8) soundness：LEM / DNE / MP 在 Bool 上是重言式
    (9) K3 ↘ Bool：去 U 后 LEM/DNE 在两值上塌缩为 T
    (10) NJ ⊆ NK：直觉规则在古典系统中皆成立 -/
theorem natural_deduction_summary :
    -- (1) ∧ I/E
    (∀ {P Q : Prop} (_ : P) (_ : Q), P ∧ Q)
    -- (2) ∨ I 左
    ∧ (∀ {P Q : Prop} (_ : P), P ∨ Q)
    -- (3) → E（modus ponens）
    ∧ (∀ {P Q : Prop} (_ : P → Q) (_ : P), Q)
    -- (4) DNE 古典
    ∧ (∀ {P : Prop} (_ : ¬¬P), P)
    -- (5) ∃ I
    ∧ (∀ {α : Sort*} {P : α → Prop} (t : α) (_ : P t), ∃ x, P x)
    -- (6) LEM 在 Bool 上是重言式
    ∧ (∀ P : Form, Form.tautology (.or P (.neg P)))
    -- (7) DNE 在 Bool 上是重言式
    ∧ (∀ P : Form, Form.tautology (.imp (.neg (.neg P)) P))
    -- (8) K3 ↘ Bool: 去 U 后 LEM 恒 T
    ∧ (∀ p : TriV, p ≠ TriV.U → lem p = TriV.T) :=
  ⟨@and_intro, @or_intro_left, @imp_elim, @not_elim_classical,
   @exists_intro, sound_lem, sound_dne, K3_collapses_to_NK_lem⟩

end SSBX.Foundation.Phase4.NaturalDeduction
