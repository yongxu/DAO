/-
# Wen.Native.Quote -- native expression code trees

`CodeTree n` is the reference program-as-data backend for the native kernel.
It is intentionally rank-polymorphic and carries `Rn n` atoms directly.
-/

import SSBX.Foundation.Wen.Native.Eval

namespace SSBX.Foundation.Wen.Native

/-- Reference native code carrier for expressions and top-level forms. -/
inductive CodeTree (n : Nat) where
  | cell (value : Cell n)
  | bool (value : Bool)
  | num (value : Nat)
  | nil
  | cons (head tail : CodeTree n)
  | quote (body : CodeTree n)
  | var (index : Nat)
  | ref (name : Cell n)
  | lam (body : CodeTree n)
  | app (fn arg : CodeTree n)
  | if0 (test thenBranch elseBranch : CodeTree n)
  | prim (prim : Prim n)
  | topExpr (body : CodeTree n)
  | topDefine (name : Cell n) (body : CodeTree n)

namespace CodeTree

/-- Encode an expression as the reference native code tree. -/
def encodeExpr {n : Nat} : Expr n → CodeTree n
  | .cell value => .cell value
  | .bool value => .bool value
  | .num value => .num value
  | .nil => .nil
  | .cons head tail => .cons (encodeExpr head) (encodeExpr tail)
  | .quote body => .quote (encodeExpr body)
  | .var index => .var index
  | .ref name => .ref name
  | .lam body => .lam (encodeExpr body)
  | .app fn arg => .app (encodeExpr fn) (encodeExpr arg)
  | .if0 test thenBranch elseBranch =>
      .if0 (encodeExpr test) (encodeExpr thenBranch) (encodeExpr elseBranch)
  | Expr.prim op => CodeTree.prim op

/-- Decode an expression from the reference native code tree. -/
def decodeExpr {n : Nat} : CodeTree n → Option (Expr n)
  | .cell value => some (.cell value)
  | .bool value => some (.bool value)
  | .num value => some (.num value)
  | .nil => some .nil
  | .cons head tail => do
      let h ← decodeExpr head
      let t ← decodeExpr tail
      some (.cons h t)
  | .quote body => do
      let b ← decodeExpr body
      some (.quote b)
  | .var index => some (.var index)
  | .ref name => some (.ref name)
  | .lam body => do
      let b ← decodeExpr body
      some (.lam b)
  | .app fn arg => do
      let f ← decodeExpr fn
      let a ← decodeExpr arg
      some (.app f a)
  | .if0 test thenBranch elseBranch => do
      let c ← decodeExpr test
      let t ← decodeExpr thenBranch
      let e ← decodeExpr elseBranch
      some (.if0 c t e)
  | CodeTree.prim op => some (Expr.prim op)
  | .topExpr _ => none
  | .topDefine _ _ => none

@[simp] theorem decodeExpr_encodeExpr {n : Nat} (expr : Expr n) :
    decodeExpr (encodeExpr expr) = some expr := by
  exact
    Expr.rec
      (motive_1 := fun e => decodeExpr (encodeExpr e) = some e)
      (motive_2 := fun _ => True)
      (motive_3 := fun _ => True)
      (motive_4 := fun _ => True)
      (motive_5 := fun _ => True)
      (fun _ => rfl)
      (fun _ => rfl)
      (fun _ => rfl)
      rfl
      (fun head tail ihHead ihTail => by
        change
          ((decodeExpr (encodeExpr head)).bind fun h =>
            (decodeExpr (encodeExpr tail)).bind fun t => some (Expr.cons h t)) =
            some (Expr.cons head tail)
        rw [ihHead, ihTail]
        rfl)
      (fun body ih => by
        change
          ((decodeExpr (encodeExpr body)).bind fun b => some (Expr.quote b)) =
            some (Expr.quote body)
        rw [ih]
        rfl)
      (fun _ => rfl)
      (fun _ => rfl)
      (fun body ih => by
        change
          ((decodeExpr (encodeExpr body)).bind fun b => some (Expr.lam b)) =
            some (Expr.lam body)
        rw [ih]
        rfl)
      (fun fn arg ihFn ihArg => by
        change
          ((decodeExpr (encodeExpr fn)).bind fun f =>
            (decodeExpr (encodeExpr arg)).bind fun a => some (Expr.app f a)) =
            some (Expr.app fn arg)
        rw [ihFn, ihArg]
        rfl)
      (fun test thenBranch elseBranch ihTest ihThen ihElse => by
        change
          ((decodeExpr (encodeExpr test)).bind fun c =>
            (decodeExpr (encodeExpr thenBranch)).bind fun t =>
              (decodeExpr (encodeExpr elseBranch)).bind fun e => some (Expr.if0 c t e)) =
            some (Expr.if0 test thenBranch elseBranch)
        rw [ihTest, ihThen, ihElse]
        rfl)
      (fun _ => rfl)
      (fun _ => True.intro)
      (fun _ => True.intro)
      (fun _ => True.intro)
      True.intro
      (fun _ _ _ _ => True.intro)
      (fun _ _ _ _ _ _ => True.intro)
      (fun _ => True.intro)
      True.intro
      (fun _ _ _ _ => True.intro)
      True.intro
      (fun _ _ _ _ => True.intro)
      (fun _ _ _ => True.intro)
      expr

def encodeTopForm {n : Nat} : TopForm n → CodeTree n
  | .expr body => .topExpr (encodeExpr body)
  | .define name body => .topDefine name (encodeExpr body)

def decodeTopForm {n : Nat} : CodeTree n → Option (TopForm n)
  | .topExpr body => do
      let expr ← decodeExpr body
      some (.expr expr)
  | .topDefine name body => do
      let expr ← decodeExpr body
      some (.define name expr)
  | _ => none

@[simp] theorem decodeTopForm_encodeTopForm {n : Nat} (form : TopForm n) :
    decodeTopForm (encodeTopForm form) = some form := by
  cases form with
  | expr body =>
      simp [encodeTopForm, decodeTopForm]
  | define name body =>
      simp [encodeTopForm, decodeTopForm]

end CodeTree

@[simp] theorem valueAsExpr_quoteValue {n : Nat} (expr : Expr n) :
    valueAsExpr (quoteValue expr) = some expr := by
  simpa [exprAsValue] using valueAsExpr_exprAsValue (n := n) expr

theorem evalFuel_quote_exprAsValue {n : Nat}
    (fuel : Nat) (env : Env n) (expr : Expr n) :
    evalFuel (fuel + 1) env (.quote expr) = some (exprAsValue expr) := rfl

theorem quote_roundtrip_laws {n : Nat} :
    (∀ expr : Expr n, CodeTree.decodeExpr (CodeTree.encodeExpr expr) = some expr)
    ∧ (∀ form : TopForm n,
        CodeTree.decodeTopForm (CodeTree.encodeTopForm form) = some form)
    ∧ (∀ expr : Expr n, valueAsExpr (exprAsValue expr) = some expr)
    ∧ (∀ fuel : Nat, ∀ env : Env n, ∀ expr : Expr n,
        evalFuel (fuel + 1) env (.quote expr) = some (exprAsValue expr)) :=
  ⟨CodeTree.decodeExpr_encodeExpr, CodeTree.decodeTopForm_encodeTopForm,
    valueAsExpr_exprAsValue, evalFuel_quote_exprAsValue⟩

end SSBX.Foundation.Wen.Native
