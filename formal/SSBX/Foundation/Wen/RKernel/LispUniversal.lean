/-
# Wen.RKernel.LispUniversal -- universal evaluator for Lisp expressions
-/

import SSBX.Foundation.Wen.RKernel.LispQuote

namespace SSBX.Foundation.Wen.RKernel

open SSBX.Foundation.Hierarchy.Operators

/-- Universal evaluator for quoted Lisp expressions. -/
def universalEvalExpr (fuel : Nat) (code : V4Tree) : Option Value := do
  let expr ← decodeExpr code
  evalFuel fuel [] expr

/-- Universal evaluator for one encoded top-level form. -/
def universalEvalTop (fuel : Nat) (code : V4Tree) : Option Value := do
  let form ← decodeTopForm code
  let (_, value) ← evalTopFuel fuel [] form
  some value

@[simp] theorem universalEvalExpr_encodeExpr (fuel : Nat) (expr : Expr) :
    universalEvalExpr fuel (encodeExpr expr) = evalFuel fuel [] expr := by
  simp [universalEvalExpr]

theorem universalEvalExpr_sampleCompose :
    universalEvalExpr 8 (encodeExpr sampleLispCompose) = some (.atom .cuoZong) := by
  rw [universalEvalExpr_encodeExpr]
  exact evalFuel_sampleLispCompose

theorem universalEvalExpr_sampleLambdaCompose :
    universalEvalExpr 12 (encodeExpr sampleLispLambdaCompose) = some (.atom .cuoZong) := by
  rw [universalEvalExpr_encodeExpr]
  exact evalFuel_sampleLispLambdaCompose

theorem universalEvalTop_sampleDefine :
    universalEvalTop 2 (encodeTopForm (.define .qian (.num 7))) = some (.num 7) := by
  simp [universalEvalTop, evalTopFuel, evalFuelG]

theorem lisp_universal_summary :
    (∀ fuel : Nat, ∀ expr : Expr,
      universalEvalExpr fuel (encodeExpr expr) = evalFuel fuel [] expr)
    ∧ universalEvalExpr 8 (encodeExpr sampleLispCompose) = some (.atom .cuoZong)
    ∧ universalEvalExpr 12 (encodeExpr sampleLispLambdaCompose) = some (.atom .cuoZong)
    ∧ universalEvalTop 2 (encodeTopForm (.define .qian (.num 7))) = some (.num 7) :=
  ⟨universalEvalExpr_encodeExpr, universalEvalExpr_sampleCompose,
    universalEvalExpr_sampleLambdaCompose, universalEvalTop_sampleDefine⟩

end SSBX.Foundation.Wen.RKernel
