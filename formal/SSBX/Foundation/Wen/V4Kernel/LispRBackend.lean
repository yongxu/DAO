/-
# Wen.V4Kernel.LispRBackend -- abstract backend contract for Lisp expressions

This is the R-space boundary for the Lisp kernel.  Concrete R0..R8 encodings
instantiate this contract later; the Lisp evaluator itself stays V4-native.
-/

import SSBX.Foundation.Wen.V4Kernel.LispUniversal

namespace SSBX.Foundation.Wen.V4Kernel

/-- Representation backend for Lisp expressions. -/
structure LispBackend where
  Code : Type
  encodeExprCode : Expr → Code
  decodeExprCode : Code → Option Expr
  decode_encodeExprCode : ∀ expr, decodeExprCode (encodeExprCode expr) = some expr
  encodeTopFormCode : TopForm → Code
  decodeTopFormCode : Code → Option TopForm
  decode_encodeTopFormCode : ∀ form, decodeTopFormCode (encodeTopFormCode form) = some form

namespace LispBackend

def evalCodeFuel (backend : LispBackend) (fuel : Nat) (code : backend.Code) :
    Option Value := do
  let expr ← backend.decodeExprCode code
  evalFuel fuel [] expr

def evalTopCodeFuel (backend : LispBackend) (fuel : Nat) (code : backend.Code) :
    Option Value := do
  let form ← backend.decodeTopFormCode code
  let (_, value) ← evalTopFuel fuel [] form
  some value

@[simp] theorem evalCodeFuel_encodeExprCode
    (backend : LispBackend) (fuel : Nat) (expr : Expr) :
    backend.evalCodeFuel fuel (backend.encodeExprCode expr) = evalFuel fuel [] expr := by
  simp [evalCodeFuel, backend.decode_encodeExprCode expr]

@[simp] theorem evalTopCodeFuel_encodeTopFormCode
    (backend : LispBackend) (fuel : Nat) (form : TopForm) :
    backend.evalTopCodeFuel fuel (backend.encodeTopFormCode form) =
      match evalTopFuel fuel [] form with
      | some (_, value) => some value
      | none => none := by
  simp [evalTopCodeFuel, backend.decode_encodeTopFormCode form]
  cases evalTopFuel fuel [] form <;> rfl

end LispBackend

/-- Reference backend through the canonical V4Tree encoding. -/
def lispTreeBackend : LispBackend where
  Code := V4Tree
  encodeExprCode := encodeExpr
  decodeExprCode := decodeExpr
  decode_encodeExprCode := decodeExpr_encodeExpr
  encodeTopFormCode := encodeTopForm
  decodeTopFormCode := decodeTopForm
  decode_encodeTopFormCode := decodeTopForm_encodeTopForm

theorem lispTreeBackend_sampleCompose :
    lispTreeBackend.evalCodeFuel 8 (lispTreeBackend.encodeExprCode sampleLispCompose) =
      some (.atom .cuoZong) := by
  rw [LispBackend.evalCodeFuel_encodeExprCode]
  exact evalFuel_sampleLispCompose

theorem lispTreeBackend_sampleTopDefine :
    lispTreeBackend.evalTopCodeFuel 2
      (lispTreeBackend.encodeTopFormCode (.define .qian (.num 7))) =
        some (.num 7) := by
  rw [LispBackend.evalTopCodeFuel_encodeTopFormCode]
  simp [evalTopFuel, evalFuelG]

theorem lisp_rbackend_summary :
    (∀ backend : LispBackend, ∀ fuel : Nat, ∀ expr : Expr,
      backend.evalCodeFuel fuel (backend.encodeExprCode expr) = evalFuel fuel [] expr)
    ∧ lispTreeBackend.evalCodeFuel 8 (lispTreeBackend.encodeExprCode sampleLispCompose) =
      some (.atom .cuoZong)
    ∧ lispTreeBackend.evalTopCodeFuel 2
      (lispTreeBackend.encodeTopFormCode (.define .qian (.num 7))) = some (.num 7) :=
  ⟨LispBackend.evalCodeFuel_encodeExprCode, lispTreeBackend_sampleCompose,
    lispTreeBackend_sampleTopDefine⟩

end SSBX.Foundation.Wen.V4Kernel
