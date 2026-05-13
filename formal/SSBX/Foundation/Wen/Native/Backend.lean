/-
# Wen.Native.Backend -- abstract native code backend contract

Concrete R0..R8 carriers instantiate this contract over `Expr n`; they are
bridges over the native kernel, not interpreter roots.
-/

import SSBX.Foundation.Wen.Native.Universal

namespace SSBX.Foundation.Wen.Native

/-- Representation backend for native Wen expressions. -/
structure Backend (n : Nat) where
  Code : Type
  encodeExprCode : Expr n → Code
  decodeExprCode : Code → Option (Expr n)
  decode_encodeExprCode : ∀ expr, decodeExprCode (encodeExprCode expr) = some expr
  encodeTopFormCode : TopForm n → Code
  decodeTopFormCode : Code → Option (TopForm n)
  decode_encodeTopFormCode : ∀ form, decodeTopFormCode (encodeTopFormCode form) = some form

namespace Backend

def evalCodeFuel {n : Nat} (backend : Backend n) (fuel : Nat) (code : backend.Code) :
    Option (Value n) := do
  let expr ← backend.decodeExprCode code
  evalFuel fuel [] expr

def evalTopCodeFuel {n : Nat} (backend : Backend n) (fuel : Nat) (code : backend.Code) :
    Option (Value n) := do
  let form ← backend.decodeTopFormCode code
  let (_, value) ← evalTopFuel fuel [] form
  some value

@[simp] theorem evalCodeFuel_encodeExprCode {n : Nat}
    (backend : Backend n) (fuel : Nat) (expr : Expr n) :
    backend.evalCodeFuel fuel (backend.encodeExprCode expr) = evalFuel fuel [] expr := by
  simp [evalCodeFuel, backend.decode_encodeExprCode expr]

@[simp] theorem evalTopCodeFuel_encodeTopFormCode {n : Nat}
    (backend : Backend n) (fuel : Nat) (form : TopForm n) :
    backend.evalTopCodeFuel fuel (backend.encodeTopFormCode form) =
      match evalTopFuel fuel [] form with
      | some (_, value) => some value
      | none => none := by
  simp [evalTopCodeFuel, backend.decode_encodeTopFormCode form]
  cases evalTopFuel fuel [] form <;> rfl

end Backend

/-- Reference backend through `CodeTree`. -/
def treeBackend (n : Nat) : Backend n where
  Code := CodeTree n
  encodeExprCode := CodeTree.encodeExpr
  decodeExprCode := CodeTree.decodeExpr
  decode_encodeExprCode := CodeTree.decodeExpr_encodeExpr
  encodeTopFormCode := CodeTree.encodeTopForm
  decodeTopFormCode := CodeTree.decodeTopForm
  decode_encodeTopFormCode := CodeTree.decodeTopForm_encodeTopForm

theorem treeBackend_sampleNativeAdd {n : Nat} :
    (treeBackend n).evalCodeFuel 12 ((treeBackend n).encodeExprCode sampleNativeLambdaAdd) =
      some (.num 5) := by
  rw [Backend.evalCodeFuel_encodeExprCode]
  exact evalFuel_sampleNativeLambdaAdd

theorem treeBackend_sampleTopDefine {n : Nat} :
    (treeBackend n).evalTopCodeFuel 2
      ((treeBackend n).encodeTopFormCode (.define sampleCell (.num 7))) =
        some (.num 7) := by
  rw [Backend.evalTopCodeFuel_encodeTopFormCode]
  rfl

theorem native_backend_summary {n : Nat} :
    (∀ backend : Backend n, ∀ fuel : Nat, ∀ expr : Expr n,
      backend.evalCodeFuel fuel (backend.encodeExprCode expr) = evalFuel fuel [] expr)
    ∧ (treeBackend n).evalCodeFuel 12 ((treeBackend n).encodeExprCode sampleNativeLambdaAdd) =
      some (.num 5)
    ∧ (treeBackend n).evalTopCodeFuel 2
      ((treeBackend n).encodeTopFormCode (.define sampleCell (.num 7))) = some (.num 7) :=
  ⟨Backend.evalCodeFuel_encodeExprCode, treeBackend_sampleNativeAdd,
    treeBackend_sampleTopDefine⟩

end SSBX.Foundation.Wen.Native
