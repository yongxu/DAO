/-
# Wen.RKernel.Semantics -- V4 expression evaluation
-/

import SSBX.Foundation.Wen.RKernel.Syntax

namespace SSBX.Foundation.Wen.RKernel

open SSBX.Foundation.Hierarchy.Operators

namespace Term

/-- Evaluate a V4 term by folding canonical V4 composition. -/
def eval : Term → V4
  | .atom g => g
  | .compose left right => V4.compose left.eval right.eval

@[simp] theorem eval_atom (g : V4) :
    eval (.atom g) = g := rfl

@[simp] theorem eval_compose (left right : Term) :
    eval (.compose left right) = V4.compose left.eval right.eval := rfl

theorem eval_compose_assoc (a b c : Term) :
    eval (.compose (.compose a b) c) =
      eval (.compose a (.compose b c)) := by
  simp [V4.compose_assoc]

theorem eval_compose_comm (a b : Term) :
    eval (.compose a b) = eval (.compose b a) := by
  simp [V4.compose_comm]

theorem eval_self_cancel (t : Term) :
    V4.compose t.eval t.eval = .dao :=
  V4.compose_self t.eval

end Term

def sampleCuoZong : Term :=
  .compose (.atom .cuo) (.atom .zong)

example : sampleCuoZong.eval = .cuoZong := rfl

theorem semantics_summary :
    sampleCuoZong.eval = .cuoZong
    ∧ (∀ t : Term, V4.compose t.eval t.eval = .dao)
    ∧ (∀ a b : Term, (Term.compose a b).eval = (Term.compose b a).eval) :=
  ⟨rfl, Term.eval_self_cancel, Term.eval_compose_comm⟩

end SSBX.Foundation.Wen.RKernel
