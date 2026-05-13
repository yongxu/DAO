/-
# Wen.Native.Universal -- reference universal evaluator
-/

import SSBX.Foundation.Wen.Native.Quote

namespace SSBX.Foundation.Wen.Native

/-- Universal evaluator for one encoded native expression. -/
def universalEvalExpr {n : Nat} (fuel : Nat) (code : CodeTree n) :
    Option (Value n) := do
  let expr ← CodeTree.decodeExpr code
  evalFuel fuel [] expr

/-- Universal evaluator for one encoded native top-level form. -/
def universalEvalTop {n : Nat} (fuel : Nat) (code : CodeTree n) :
    Option (Value n) := do
  let form ← CodeTree.decodeTopForm code
  let (_, value) ← evalTopFuel fuel [] form
  some value

@[simp] theorem universalEvalExpr_encodeExpr {n : Nat}
    (fuel : Nat) (expr : Expr n) :
    universalEvalExpr fuel (CodeTree.encodeExpr expr) = evalFuel fuel [] expr := by
  simp [universalEvalExpr]

@[simp] theorem universalEvalTop_encodeTopForm {n : Nat}
    (fuel : Nat) (form : TopForm n) :
    universalEvalTop fuel (CodeTree.encodeTopForm form) =
      match evalTopFuel fuel [] form with
      | some (_, value) => some value
      | none => none := by
  simp [universalEvalTop]
  cases evalTopFuel fuel [] form <;> rfl

theorem universalEvalExpr_lambdaAddExpr {n : Nat} :
    universalEvalExpr (n := n) 12 (CodeTree.encodeExpr lambdaAddExpr) =
      some (.num 5) := by
  rw [universalEvalExpr_encodeExpr]
  exact evalFuel_lambdaAddExpr

theorem universalEvalTop_defineOrigin {n : Nat} :
    universalEvalTop (n := n) 2
      (CodeTree.encodeTopForm (.define originCell (.num 7))) =
        some (.num 7) := by
  rw [universalEvalTop_encodeTopForm]
  rfl

theorem universal_eval_laws {n : Nat} :
    (∀ fuel : Nat, ∀ expr : Expr n,
      universalEvalExpr fuel (CodeTree.encodeExpr expr) = evalFuel fuel [] expr)
    ∧ universalEvalExpr (n := n) 12 (CodeTree.encodeExpr lambdaAddExpr) =
      some (.num 5)
    ∧ universalEvalTop (n := n) 2
      (CodeTree.encodeTopForm (.define originCell (.num 7))) = some (.num 7) :=
  ⟨universalEvalExpr_encodeExpr, universalEvalExpr_lambdaAddExpr,
    universalEvalTop_defineOrigin⟩

end SSBX.Foundation.Wen.Native
