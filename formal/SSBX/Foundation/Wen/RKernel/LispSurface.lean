/-
# Wen.RKernel.LispSurface -- 64-word surface and de Bruijn elaboration

Surface variables are Word64 names.  Elaboration keeps proof-level local
binding de Bruijn-stable: bound names become `Expr.var`, unbound names become
global `Expr.ref`.
-/

import SSBX.Foundation.Wen.RKernel.LispEval

namespace SSBX.Foundation.Wen.RKernel

open SSBX.Foundation.Hierarchy.Operators

inductive SurfaceExpr where
  | ref (name : Word64)
  | symbol (name : Word64)
  | atom (g : V4)
  | num (n : Nat)
  | nil
  | list (items : List SurfaceExpr)
  | quote (body : SurfaceExpr)
  | lambda (param : Word64) (body : SurfaceExpr)
  | app (fn : SurfaceExpr) (args : List SurfaceExpr)
  | if0 (test thenBranch elseBranch : SurfaceExpr)
  | prim (p : Prim)
  deriving Repr

inductive SurfaceTopForm where
  | expr (body : SurfaceExpr)
  | define (name : Word64) (body : SurfaceExpr)
  deriving Repr

namespace SurfaceExpr

def lookupLocal : List Word64 → Word64 → Option Nat
  | [], _ => none
  | head :: tail, name =>
      if head = name then some 0
      else (lookupLocal tail name).map Nat.succ

def coreAppMany : Expr → List Expr → Expr
  | fn, [] => fn
  | fn, arg :: rest => coreAppMany (.app fn arg) rest

mutual

def elabList (ctx : List Word64) : List SurfaceExpr → Option (List Expr)
  | [] => some []
  | head :: tail => do
      let h ← elabExpr ctx head
      let t ← elabList ctx tail
      some (h :: t)

def elabQuoteList : List SurfaceExpr → Option (List Expr)
  | [] => some []
  | head :: tail => do
      let h ← elabQuote head
      let t ← elabQuoteList tail
      some (h :: t)

def elabQuote : SurfaceExpr → Option Expr
  | .ref name => some (.symbol name)
  | .symbol name => some (.symbol name)
  | .atom g => some (.atom g)
  | .num n => some (.num n)
  | .nil => some .nil
  | .list items => do
      let xs ← elabQuoteList items
      some (Expr.list xs)
  | .quote body => do
      let b ← elabQuote body
      some (.quote b)
  | .lambda param body => do
      let b ← elabQuote body
      some (.cons (.symbol param) b)
  | .app fn args => do
      let f ← elabQuote fn
      let as ← elabQuoteList args
      some (Expr.list (f :: as))
  | .if0 test thenBranch elseBranch => do
      let c ← elabQuote test
      let t ← elabQuote thenBranch
      let e ← elabQuote elseBranch
      some (Expr.list [.symbol .qian, c, t, e])
  | .prim p => some (.prim p)

def elabExpr (ctx : List Word64) : SurfaceExpr → Option Expr
  | .ref name =>
      match lookupLocal ctx name with
      | some index => some (.var index)
      | none => some (.ref name)
  | .symbol name => some (.symbol name)
  | .atom g => some (.atom g)
  | .num n => some (.num n)
  | .nil => some .nil
  | .list items => do
      let xs ← elabList ctx items
      some (Expr.list xs)
  | .quote body => do
      let b ← elabQuote body
      some (.quote b)
  | .lambda param body => do
      let b ← elabExpr (param :: ctx) body
      some (.lam b)
  | .app (.prim .eval) [arg] => do
      let a ← elabExpr ctx arg
      some (.app (.prim .eval) a)
  | .app (.prim p) args => do
      let as ← elabList ctx args
      some (.app (.prim p) (Expr.list as))
  | .app fn args => do
      let f ← elabExpr ctx fn
      let as ← elabList ctx args
      some (coreAppMany f as)
  | .if0 test thenBranch elseBranch => do
      let c ← elabExpr ctx test
      let t ← elabExpr ctx thenBranch
      let e ← elabExpr ctx elseBranch
      some (.if0 c t e)
  | .prim p => some (.prim p)

end

end SurfaceExpr

namespace SurfaceTopForm

def elaborate : SurfaceTopForm → Option TopForm
  | .expr body => do
      let expr ← SurfaceExpr.elabExpr [] body
      some (.expr expr)
  | .define name body => do
      let expr ← SurfaceExpr.elabExpr [] body
      some (.define name expr)

def evalFuel (fuel : Nat) (global : GlobalEnv) (form : SurfaceTopForm) :
    Option (GlobalEnv × Value) := do
  let core ← form.elaborate
  evalTopFuel fuel global core

end SurfaceTopForm

def sampleSurfaceLambdaShadow : SurfaceExpr :=
  .app (.lambda .qian (.ref .qian)) [.num 2]

def sampleSurfaceQuoteName : SurfaceExpr :=
  .quote (.ref .qian)

theorem elab_local_shadow :
    SurfaceExpr.elabExpr [] sampleSurfaceLambdaShadow =
      some (.app (.lam (.var 0)) (.num 2)) := rfl

theorem eval_surface_local_shadows_global :
    (match SurfaceExpr.elabExpr [] sampleSurfaceLambdaShadow with
    | some expr => evalFuelG 8 [(.qian, .num 7)] [] expr
    | none => none) =
    some (Value.num 2) := rfl

theorem elab_quote_name_is_symbol :
    SurfaceExpr.elabExpr [] sampleSurfaceQuoteName =
      some (.quote (.symbol .qian))
    ∧ evalFuelG 1 [(.qian, .num 7)] [] (.quote (.symbol .qian)) =
      some (.symbol .qian) :=
  ⟨rfl, rfl⟩

theorem surface_define_ref :
    SurfaceTopForm.evalFuel 2 [] (.define .qian (.num 7)) =
      some ([(.qian, .num 7)], .num 7)
    ∧ SurfaceTopForm.evalFuel 1 [(.qian, .num 7)] (.expr (.ref .qian)) =
      some ([(.qian, .num 7)], .num 7) :=
  ⟨rfl, by simp [SurfaceTopForm.evalFuel, SurfaceTopForm.elaborate,
    SurfaceExpr.elabExpr, SurfaceExpr.lookupLocal, evalTopFuel, evalFuelG,
    GlobalEnv.lookup]⟩

theorem lisp_surface_summary :
    SurfaceExpr.elabExpr [] sampleSurfaceLambdaShadow =
      some (.app (.lam (.var 0)) (.num 2))
    ∧ SurfaceExpr.elabExpr [] sampleSurfaceQuoteName =
      some (.quote (.symbol .qian))
    ∧ SurfaceTopForm.evalFuel 2 [] (.define .qian (.num 7)) =
      some ([(.qian, .num 7)], .num 7) :=
  ⟨elab_local_shadow, elab_quote_name_is_symbol.1, surface_define_ref.1⟩

end SSBX.Foundation.Wen.RKernel
