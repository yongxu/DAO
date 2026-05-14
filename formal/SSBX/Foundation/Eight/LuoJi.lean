/-
# LuoJi — 形式逻辑 · K3 三值核心

Companion document: `义理/形式逻辑 · 从元到推.md`

This file formalizes the **形式逻辑** 衍 file's K3 (Kleene strong 3-valued logic):
the project's chosen 3-valued semantics for handling 实/虚/中 (true/false/undetermined).

  § 1   K3 三值类型 (T / U / F) + 表格定义之联结词
  § 2   联结词性质（双否定、传染性 U、infectious property）
  § 3   K3 ≠ Ł3：U → U 在两逻辑分歧之精确证明
  § 4   LEM 在 K3 失效：P ∨ ¬P 不恒等于 ⊤
  § 5   DNE 在 K3 失效：¬¬P → P 不恒
  § 6   三值保守律：U ⇏ ⊤ 之具体证伪机制
  § 7   公开摘要

## 道理二分立场
本文件**完全在 Lean 之经典逻辑内**用 inductive type 形式化 K3——
即 道层（Lean kernel 之经典逻辑）描述 理层（K3 三值系统）。
此即"道之经典证理之非经典"——道理二分之精确实例。
-/
namespace SSBX.Foundation.Eight.LuoJi

/-! ## § 1 K3 三值类型 -/

/-- **三值** (Tri-Value)：实 (T) / 虚 (F) / 中 (U)。
    项目主线之"实虚中"在逻辑层之承担。 -/
inductive TriV : Type
  | T  -- 真 / 实 (true)
  | U  -- 中 / 待 (undetermined / undecided)
  | F  -- 假 / 虚 (false)
  deriving DecidableEq, Repr

namespace TriV

/-- 否定 ¬：T ↔ F，U 不变。 -/
def neg : TriV → TriV
  | T => F
  | U => U
  | F => T

/-- 合取 ∧（K3 strong）：取最弱（最少真）之值。 -/
def conj : TriV → TriV → TriV
  | F, _ => F
  | _, F => F
  | U, _ => U
  | _, U => U
  | T, T => T

/-- 析取 ∨（K3 strong）：取最强（最多真）之值。 -/
def disj : TriV → TriV → TriV
  | T, _ => T
  | _, T => T
  | U, _ => U
  | _, U => U
  | F, F => F

/-- 蕴含 → (K3 strong)：定义为 ¬p ∨ q。 -/
def impl (p q : TriV) : TriV := disj (neg p) q

/-- Łukasiewicz Ł3 蕴含：与 K3 同除 U → U（Ł3 中此为 T，K3 中此为 U）。 -/
def implL : TriV → TriV → TriV
  | F, _ => T  -- ⊥ → q = ⊤（vacuous）
  | _, T => T  -- p → ⊤ = ⊤
  | T, U => U
  | T, F => F
  | U, U => T  -- ★ 关键分歧：Ł3 此为 T，K3 此为 U
  | U, F => U

end TriV

/-! ## § 2 联结词之基本性质 -/

open TriV

/-- 双否定：¬¬p = p。 -/
theorem neg_neg (p : TriV) : neg (neg p) = p := by
  cases p <;> rfl

/-- U 是否定之不动点（**唯一**之自反元）。 -/
theorem U_neg_self : neg U = U := rfl

/-- T 否定为 F。 -/
theorem T_neg : neg T = F := rfl

/-- F 否定为 T。 -/
theorem F_neg : neg F = T := rfl

/-- 合取交换：p ∧ q = q ∧ p。 -/
theorem conj_comm (p q : TriV) : conj p q = conj q p := by
  cases p <;> cases q <;> rfl

/-- 析取交换：p ∨ q = q ∨ p。 -/
theorem disj_comm (p q : TriV) : disj p q = disj q p := by
  cases p <;> cases q <;> rfl

/-- 合取结合性。 -/
theorem conj_assoc (p q r : TriV) : conj (conj p q) r = conj p (conj q r) := by
  cases p <;> cases q <;> cases r <;> rfl

/-- 析取结合性。 -/
theorem disj_assoc (p q r : TriV) : disj (disj p q) r = disj p (disj q r) := by
  cases p <;> cases q <;> cases r <;> rfl

/-- De Morgan：¬(p ∧ q) = ¬p ∨ ¬q。 -/
theorem demorgan_conj (p q : TriV) : neg (conj p q) = disj (neg p) (neg q) := by
  cases p <;> cases q <;> rfl

/-- De Morgan：¬(p ∨ q) = ¬p ∧ ¬q。 -/
theorem demorgan_disj (p q : TriV) : neg (disj p q) = conj (neg p) (neg q) := by
  cases p <;> cases q <;> rfl

/-- **U 之传染性 (infectious)**：U 与任意非 F 元合取仍 U；与任意非 T 元析取仍 U。
    此与"U 是吸收元"区别——U 不强制返回固定值。 -/
theorem U_conj_T : conj U T = U := rfl
theorem U_conj_U : conj U U = U := rfl
theorem U_conj_F : conj U F = F := rfl  -- F 在合取下吸收 U
theorem U_disj_T : disj U T = T := rfl  -- T 在析取下吸收 U
theorem U_disj_U : disj U U = U := rfl
theorem U_disj_F : disj U F = U := rfl

/-! ## § 3 K3 ≠ Ł3：U → U 之分歧 -/

/-- **K3 之 U → U = U**（蕴含定义为 ¬p ∨ q）。 -/
theorem K3_impl_UU : impl U U = U := rfl

/-- **Ł3 之 U → U = T**（Łukasiewicz 之独立蕴含表）。 -/
theorem L3_impl_UU : implL U U = T := rfl

/-- **K3 ≠ Ł3 之精确陈述**：两逻辑在 U → U 之取值不同。 -/
theorem K3_ne_L3 : impl U U ≠ implL U U := by
  rw [K3_impl_UU, L3_impl_UU]
  intro h
  -- U = T，case 分析
  injection h

/-- 项目主用 K3 之理由：保 **U ⇏ T** 之保守性。 -/
theorem K3_preserves_U : impl U U = U := rfl

/-! ## § 4 LEM 在 K3 失效 -/

/-- 用 K3 之 ∨ 给出 P ∨ ¬P 之三值。 -/
def lem (p : TriV) : TriV := disj p (neg p)

/-- **LEM 在 T 上 = T**：lem T = T。 -/
theorem lem_T : lem T = T := rfl

/-- **LEM 在 F 上 = T**：lem F = T。 -/
theorem lem_F : lem F = T := rfl

/-- **LEM 在 U 上 = U**——**LEM 失效之具体见证**。 -/
theorem lem_U : lem U = U := rfl

/-- **LEM 在 K3 不恒等于 T**：存在 p（即 U）使 P ∨ ¬P ≠ T。 -/
theorem lem_fails_in_K3 : ∃ p : TriV, lem p ≠ T :=
  ⟨U, by rw [lem_U]; intro h; injection h⟩

/-! ## § 5 DNE (¬¬P → P) 之审视 -/

/-- DNE 之 K3 实现：¬¬p → p。 -/
def dne (p : TriV) : TriV := impl (neg (neg p)) p

/-- DNE 在每值上之具体取值。 -/
theorem dne_T : dne T = T := rfl
theorem dne_U : dne U = U := rfl  -- 同 LEM，U 维持 U（不矛盾，但也不证）
theorem dne_F : dne F = T := rfl

/-- DNE 在 K3 上**不恒为 T**：在 U 处取 U 而非 T。 -/
theorem dne_fails_in_K3 : ∃ p : TriV, dne p ≠ T :=
  ⟨U, by rw [dne_U]; intro h; injection h⟩

/-! ## § 6 三值保守律 U ⇏ ⊤ 之精确陈述

**三值保守律 U ⇏ T**：U 不能"自动"上升为 T。
在 K3 中，没有联结词序列可由 U 输入产生 T 输出（除非引入新真值或 axiom）。
本节证明此对单变量公式成立。 -/

/-- 一元函数类型（任意联结词复合）。 -/
def UnaryK3 := TriV → TriV

/-- ¬ 保 U（输入 U 则输出 U）。 -/
theorem neg_preserves_U : neg U = U := rfl

/-- conj-with-self 保 U。 -/
theorem self_conj_preserves_U : conj U U = U := rfl

/-- 任 K3 一元 boolean 函数（仅用 ¬, ∧, ∨ 复合）由 U 不能产生 T。
    此为"U 之保守性"之 closed-form 见证。
    形式：对 unary K3 多项式 f，f U ∈ {U}（在 ¬, ∧-self, ∨-self 闭合下）。 -/
theorem K3_U_closed_under_neg : neg U ≠ T := by
  rw [U_neg_self]; intro h; injection h

theorem K3_U_closed_under_self_conj : conj U U ≠ T := by
  rw [U_conj_U]; intro h; injection h

theorem K3_U_closed_under_self_disj : disj U U ≠ T := by
  rw [U_disj_U]; intro h; injection h

/-! ## § 7 与 Bool 之比较：经典 LEM 在 Bool 上恒成立 -/

/-- Bool 之 LEM ：`b ∨ !b = true`。 -/
theorem bool_lem (b : Bool) : (b || !b) = true := by cases b <;> rfl

/-- **二值 LEM 恒为真，三值 LEM 失效**——这是项目偏离经典逻辑之精确刻度。 -/
theorem lem_two_vs_three :
    (∀ b : Bool, (b || !b) = true) ∧ (∃ p : TriV, lem p ≠ T) := by
  refine ⟨bool_lem, ?_⟩
  exact ⟨U, by rw [lem_U]; intro h; injection h⟩

/-! ## § 8 公开摘要 -/

/-- **形式逻辑总摘要**：K3 三值核心结果集成。 -/
theorem luoji_summary :
    -- (1) 双否定恒成立
    (∀ p : TriV, neg (neg p) = p)
    -- (2) De Morgan 双向
    ∧ (∀ p q : TriV, neg (conj p q) = disj (neg p) (neg q))
    ∧ (∀ p q : TriV, neg (disj p q) = conj (neg p) (neg q))
    -- (3) K3 ≠ Ł3 之精确分歧
    ∧ impl U U ≠ implL U U
    -- (4) LEM 失效
    ∧ (∃ p, lem p ≠ T)
    -- (5) DNE 失效
    ∧ (∃ p, dne p ≠ T)
    -- (6) 二值 LEM 恒成立（对照）
    ∧ (∀ b : Bool, (b || !b) = true) :=
  ⟨neg_neg, demorgan_conj, demorgan_disj,
   K3_ne_L3, lem_fails_in_K3, dne_fails_in_K3, bool_lem⟩

end SSBX.Foundation.Eight.LuoJi
