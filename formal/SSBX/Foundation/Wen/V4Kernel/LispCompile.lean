/-
# Wen.V4Kernel.LispCompile -- boundary compiler to YiInstr

This is only the compiler boundary.  It does not claim that the VM already has a
full Lisp value carrier; it records supported fragments, emits YiInstr programs,
and proves the corresponding Lisp-side evaluation value.
-/

import SSBX.Foundation.Hierarchy.Operators.V4.Temporal
import SSBX.Foundation.Bagua.BaguaTuring
import SSBX.Foundation.Wen.V4Kernel.LispRSpacePlan

namespace SSBX.Foundation.Wen.V4Kernel

open SSBX.Foundation.Hierarchy.Operators
open SSBX.Foundation.Bagua.BaguaTuring

def v4ComposeExpr (a b : V4) : Expr :=
  .app (.prim .v4Compose) (Expr.list [.atom a, .atom b])

def quoteDatumExpr? : Expr → Option Unit
  | .atom _ => some ()
  | .nil => some ()
  | .cons head tail => do
      let _ ← quoteDatumExpr? head
      quoteDatumExpr? tail
  | _ => none

/-- A supported compiler result carries its Lisp-side semantic witness. -/
structure CompileResult (expr : Expr) where
  prog : List YiInstr
  value : Value
  fuel : Nat
  eval_ok : evalFuel fuel [] expr = some value

def setTemporalProg (g : V4) : List YiInstr :=
  [YiInstr.setShi (V4.toTemporal g)]

/-- Compile only the currently supported closed fragment. -/
def compileExprResult : (expr : Expr) → Option (CompileResult expr)
  | .atom g =>
      some
        { prog := setTemporalProg g
          value := .atom g
          fuel := 1
          eval_ok := rfl }
  | .app (.prim .v4Compose) (.cons (.atom a) (.cons (.atom b) .nil)) =>
      some
        { prog := setTemporalProg (V4.compose a b)
          value := .atom (V4.compose a b)
          fuel := 8
          eval_ok := rfl }
  | .quote quoted =>
      match quoteDatumExpr? quoted with
      | some _ =>
          some
            { prog := [YiInstr.push]
              value := quoteValue quoted
              fuel := 1
              eval_ok := rfl }
      | none => none
  | _ => none

def compileExpr (expr : Expr) : Option (List YiInstr) :=
  match compileExprResult expr with
  | some result => some result.prog
  | none => none

theorem compileResult_preserves_eval (expr : Expr) (result : CompileResult expr) :
    evalFuel result.fuel [] expr = some result.value :=
  result.eval_ok

@[simp] theorem compileExpr_atom (g : V4) :
    compileExpr (.atom g) = some (setTemporalProg g) := rfl

@[simp] theorem compileExpr_v4Compose_atoms (a b : V4) :
    compileExpr (v4ComposeExpr a b) = some (setTemporalProg (V4.compose a b)) := rfl

@[simp] theorem compileExpr_quote_atom (g : V4) :
    compileExpr (.quote (.atom g)) = some [YiInstr.push] := rfl

@[simp] theorem compileExpr_unsupported_lam :
    compileExpr (.lam (.var 0)) = none := rfl

theorem lisp_compile_summary :
    compileExpr (v4ComposeExpr .cuo .zong) = some (setTemporalProg .cuoZong)
    ∧ compileExpr (.quote (.cons (.atom .cuo) .nil)) = some [YiInstr.push]
    ∧ compileExpr (.lam (.var 0)) = none
    ∧ (∀ expr : Expr, ∀ result : CompileResult expr,
        evalFuel result.fuel [] expr = some result.value) :=
  ⟨rfl, rfl, rfl, compileResult_preserves_eval⟩

end SSBX.Foundation.Wen.V4Kernel
