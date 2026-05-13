/-
# Wen.Native.Surface -- native surface forms and de Bruijn elaboration

Surface names are `Rn n` cells.  Bound names elaborate to de Bruijn variables;
unbound names elaborate to immutable globals.
-/

import SSBX.Foundation.Wen.Native.Backend

namespace SSBX.Foundation.Wen.Native

inductive SurfaceExpr (n : Nat) where
  | ref (name : Cell n)
  | cell (value : Cell n)
  | bool (value : Bool)
  | num (value : Nat)
  | nil
  | list (items : List (SurfaceExpr n))
  | quote (body : SurfaceExpr n)
  | lambda (param : Cell n) (body : SurfaceExpr n)
  | app (fn : SurfaceExpr n) (args : List (SurfaceExpr n))
  | if0 (test thenBranch elseBranch : SurfaceExpr n)
  | prim (prim : Prim n)

inductive SurfaceTopForm (n : Nat) where
  | expr (body : SurfaceExpr n)
  | define (name : Cell n) (body : SurfaceExpr n)

namespace SurfaceExpr

def lookupLocal {n : Nat} : List (Cell n) → Cell n → Option Nat
  | [], _ => none
  | head :: tail, name =>
      if head = name then some 0
      else (lookupLocal tail name).map Nat.succ

def coreAppMany {n : Nat} : Expr n → List (Expr n) → Expr n
  | fn, [] => fn
  | fn, arg :: rest => coreAppMany (.app fn arg) rest

mutual

def elabList {n : Nat} (ctx : List (Cell n)) :
    List (SurfaceExpr n) → Option (List (Expr n))
  | [] => some []
  | head :: tail => do
      let h ← elabExpr ctx head
      let t ← elabList ctx tail
      some (h :: t)

def elabQuoteList {n : Nat} : List (SurfaceExpr n) → Option (List (Expr n))
  | [] => some []
  | head :: tail => do
      let h ← elabQuote head
      let t ← elabQuoteList tail
      some (h :: t)

def elabQuote {n : Nat} : SurfaceExpr n → Option (Expr n)
  | .ref name => some (.cell name)
  | .cell value => some (.cell value)
  | .bool value => some (.bool value)
  | .num value => some (.num value)
  | .nil => some .nil
  | .list items => do
      let xs ← elabQuoteList items
      some (Expr.list xs)
  | .quote body => do
      let b ← elabQuote body
      some (.quote b)
  | .lambda param body => do
      let b ← elabQuote body
      some (.cons (.cell param) b)
  | .app fn args => do
      let f ← elabQuote fn
      let as ← elabQuoteList args
      some (Expr.list (f :: as))
  | .if0 test thenBranch elseBranch => do
      let c ← elabQuote test
      let t ← elabQuote thenBranch
      let e ← elabQuote elseBranch
      some (Expr.list [c, t, e])
  | SurfaceExpr.prim op => some (Expr.prim op)

def elabExpr {n : Nat} (ctx : List (Cell n)) : SurfaceExpr n → Option (Expr n)
  | .ref name =>
      match lookupLocal ctx name with
      | some index => some (.var index)
      | none => some (.ref name)
  | .cell value => some (.cell value)
  | .bool value => some (.bool value)
  | .num value => some (.num value)
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
  | SurfaceExpr.app (SurfaceExpr.prim .eval) [arg] => do
      let a ← elabExpr ctx arg
      some (.app (.prim .eval) a)
  | SurfaceExpr.app (SurfaceExpr.prim op) args => do
      let as ← elabList ctx args
      some (.app (.prim op) (Expr.list as))
  | .app fn args => do
      let f ← elabExpr ctx fn
      let as ← elabList ctx args
      some (coreAppMany f as)
  | .if0 test thenBranch elseBranch => do
      let c ← elabExpr ctx test
      let t ← elabExpr ctx thenBranch
      let e ← elabExpr ctx elseBranch
      some (.if0 c t e)
  | SurfaceExpr.prim op => some (Expr.prim op)

end

end SurfaceExpr

namespace SurfaceTopForm

def elaborate {n : Nat} : SurfaceTopForm n → Option (TopForm n)
  | .expr body => do
      let expr ← SurfaceExpr.elabExpr [] body
      some (.expr expr)
  | .define name body => do
      let expr ← SurfaceExpr.elabExpr [] body
      some (.define name expr)

def evalFuel {n : Nat} (fuel : Nat) (global : GlobalEnv n) (form : SurfaceTopForm n) :
    Option (GlobalEnv n × Value n) := do
  let core ← form.elaborate
  evalTopFuel fuel global core

end SurfaceTopForm

def localShadowExpr {n : Nat} : SurfaceExpr n :=
  .app (.lambda originCell (.ref originCell)) [.num 2]

def quotedNameExpr {n : Nat} : SurfaceExpr n :=
  .quote (.ref originCell)

def originSevenGlobal {n : Nat} : GlobalEnv n :=
  [(originCell, .num 7)]

def defineOriginAsSeven {n : Nat} : SurfaceTopForm n :=
  .define originCell (.num 7)

def refOriginForm {n : Nat} : SurfaceTopForm n :=
  .expr (.ref originCell)

theorem elab_local_shadow {n : Nat} :
    SurfaceExpr.elabExpr [] (localShadowExpr : SurfaceExpr n) =
      some (.app (.lam (.var 0)) (.num 2)) := by
  simp [localShadowExpr, SurfaceExpr.elabExpr, SurfaceExpr.lookupLocal,
    SurfaceExpr.elabList, SurfaceExpr.coreAppMany]

theorem eval_surface_local_shadows_global {n : Nat} :
    (match SurfaceExpr.elabExpr [] (localShadowExpr : SurfaceExpr n) with
    | some expr => evalFuelG 8 (originSevenGlobal : GlobalEnv n) [] expr
    | none => none) =
    some (Value.num 2) := by
  rw [elab_local_shadow]
  rfl

theorem elab_quote_name_is_cell {n : Nat} :
    SurfaceExpr.elabExpr [] (quotedNameExpr : SurfaceExpr n) =
      some (.quote (.cell originCell)) := by
  rfl

theorem surface_define_ref {n : Nat} :
    SurfaceTopForm.evalFuel 2 [] (defineOriginAsSeven : SurfaceTopForm n) =
      some ((originSevenGlobal : GlobalEnv n), .num 7)
    ∧ SurfaceTopForm.evalFuel 1 (originSevenGlobal : GlobalEnv n)
        (refOriginForm : SurfaceTopForm n) =
      some ((originSevenGlobal : GlobalEnv n), .num 7) := by
  constructor
  · rfl
  · simp [refOriginForm, originSevenGlobal, SurfaceTopForm.evalFuel,
      SurfaceTopForm.elaborate, SurfaceExpr.elabExpr, SurfaceExpr.lookupLocal,
      evalTopFuel, evalFuelG, GlobalEnv.lookup]

theorem surface_elaboration_laws {n : Nat} :
    SurfaceExpr.elabExpr [] (localShadowExpr : SurfaceExpr n) =
      some (.app (.lam (.var 0)) (.num 2))
    ∧ SurfaceExpr.elabExpr [] (quotedNameExpr : SurfaceExpr n) =
      some (.quote (.cell originCell))
    ∧ SurfaceTopForm.evalFuel 2 [] (defineOriginAsSeven : SurfaceTopForm n) =
      some ((originSevenGlobal : GlobalEnv n), .num 7) :=
  ⟨elab_local_shadow, elab_quote_name_is_cell, surface_define_ref.1⟩

end SSBX.Foundation.Wen.Native
