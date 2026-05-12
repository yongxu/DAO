/-
# Wen.V4Kernel.Combinator -- V4 endomaps and term-level application

Combinators here are V4-native functions on V4 values.  They can be applied back
to object-language terms while preserving direct evaluation.
-/

import SSBX.Foundation.Wen.V4Kernel.Semantics

namespace SSBX.Foundation.Wen.V4Kernel

open SSBX.Foundation.Hierarchy.Operators

/-- A small combinator fragment over V4 values. -/
inductive Comb where
  | id
  | const (g : V4)
  | translate (mask : V4)
  | seq (first second : Comb)
  deriving DecidableEq, Repr

namespace Comb

/-- Evaluate a combinator as a V4 endomap. -/
def eval : Comb → V4 → V4
  | .id, x => x
  | .const g, _ => g
  | .translate mask, x => V4.compose mask x
  | .seq first second, x => second.eval (first.eval x)

/-- Apply a combinator to a term, staying inside the existing term fragment. -/
def applyTerm : Comb → Term → Term
  | .id, t => t
  | .const g, _ => .atom g
  | .translate mask, t => .compose (.atom mask) t
  | .seq first second, t => second.applyTerm (first.applyTerm t)

@[simp] theorem eval_id (x : V4) :
    eval .id x = x := rfl

@[simp] theorem eval_const (g x : V4) :
    eval (.const g) x = g := rfl

@[simp] theorem eval_translate (mask x : V4) :
    eval (.translate mask) x = V4.compose mask x := rfl

@[simp] theorem eval_seq (first second : Comb) (x : V4) :
    eval (.seq first second) x = second.eval (first.eval x) := rfl

@[simp] theorem applyTerm_correct (c : Comb) (t : Term) :
    (c.applyTerm t).eval = c.eval t.eval := by
  induction c generalizing t with
  | id =>
      rfl
  | const g =>
      rfl
  | translate mask =>
      rfl
  | seq first second ihFirst ihSecond =>
      simp [applyTerm, eval, ihFirst, ihSecond]

theorem translate_dao_eq_id (x : V4) :
    eval (.translate .dao) x = eval .id x := by
  simp [V4.compose_dao_left]

theorem translate_self_cancel (mask x : V4) :
    eval (.seq (.translate mask) (.translate mask)) x = x := by
  cases mask <;> cases x <;> rfl

end Comb

def sampleTranslateCuoZong : Comb :=
  .seq (.translate .cuo) (.translate .zong)

example : sampleTranslateCuoZong.eval .dao = .cuoZong := rfl

theorem combinator_summary :
    (∀ c : Comb, ∀ t : Term, (c.applyTerm t).eval = c.eval t.eval)
    ∧ (∀ mask x : V4, Comb.eval (.seq (.translate mask) (.translate mask)) x = x)
    ∧ sampleTranslateCuoZong.eval .dao = .cuoZong :=
  ⟨Comb.applyTerm_correct, Comb.translate_self_cancel, rfl⟩

end SSBX.Foundation.Wen.V4Kernel
