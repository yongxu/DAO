/-
# Wen.Native.Eval -- fuelled evaluator for the native Wen kernel

The evaluator is rank-polymorphic over `Layered.Rn n`.  Structural runtime
values remain separate from the external code backend, but `.quote` and the
primitive `.eval` share one value-level expression encoding.
-/

import SSBX.Foundation.Wen.Native.Syntax

namespace SSBX.Foundation.Wen.Native

open SSBX.Foundation.Wen.Layered

namespace Prim

def arity {n : Nat} : Prim n → Nat
  | .zero => 0
  | .xor => 2
  | .act => 2
  | .eq => 2
  | .flip _ => 1
  | .cons => 2
  | .car => 1
  | .cdr => 1
  | .null => 1
  | .atom => 1
  | .isBool => 1
  | .isNumber => 1
  | .numEq => 2
  | .succ => 1
  | .pred => 1
  | .add => 2
  | .eval => 1

end Prim

def truthValue {n : Nat} (b : Bool) : Value n :=
  .bool b

def valueAtom? {n : Nat} : Value n → Bool
  | .cell _ => true
  | .bool _ => true
  | .num _ => true
  | .nil => true
  | .prim _ => true
  | _ => false

/-! ## Quoted syntax as values -/

def taggedQuote {n : Nat} (tag : Nat) (payload : Value n) : Value n :=
  .cons (.num tag) payload

/-- Encode an expression as a runtime value. -/
def quoteValue {n : Nat} : Expr n → Value n
  | .cell value => taggedQuote 0 (.cell value)
  | .bool value => taggedQuote 1 (.bool value)
  | .num value => taggedQuote 2 (.num value)
  | .nil => taggedQuote 3 .nil
  | .cons head tail =>
      taggedQuote 4 (.cons (quoteValue head) (quoteValue tail))
  | .quote body => taggedQuote 5 (quoteValue body)
  | .var index => taggedQuote 6 (.num index)
  | .ref name => taggedQuote 7 (.cell name)
  | .lam body => taggedQuote 8 (quoteValue body)
  | .app fn arg =>
      taggedQuote 9 (.cons (quoteValue fn) (quoteValue arg))
  | .if0 test thenBranch elseBranch =>
      taggedQuote 10
        (.cons (quoteValue test) (.cons (quoteValue thenBranch) (quoteValue elseBranch)))
  | .prim prim => taggedQuote 11 (.prim prim)

/-- Decode quote-compatible values back to expressions. -/
def valueAsExpr {n : Nat} : Value n → Option (Expr n)
  | .cons (.num 0) (.cell value) => some (.cell value)
  | .cons (.num 1) (.bool value) => some (.bool value)
  | .cons (.num 2) (.num value) => some (.num value)
  | .cons (.num 3) .nil => some .nil
  | .cons (.num 4) (.cons head tail) => do
      let h ← valueAsExpr head
      let t ← valueAsExpr tail
      some (.cons h t)
  | .cons (.num 5) body => do
      let b ← valueAsExpr body
      some (.quote b)
  | .cons (.num 6) (.num index) => some (.var index)
  | .cons (.num 7) (.cell name) => some (.ref name)
  | .cons (.num 8) body => do
      let b ← valueAsExpr body
      some (.lam b)
  | .cons (.num 9) (.cons fn arg) => do
      let f ← valueAsExpr fn
      let a ← valueAsExpr arg
      some (.app f a)
  | .cons (.num 10) (.cons test (.cons thenBranch elseBranch)) => do
      let c ← valueAsExpr test
      let t ← valueAsExpr thenBranch
      let e ← valueAsExpr elseBranch
      some (.if0 c t e)
  | .cons (.num 11) (.prim prim) => some (.prim prim)
  | _ => none

def exprAsValue {n : Nat} (expr : Expr n) : Value n :=
  quoteValue expr

theorem valueAsExpr_exprAsValue {n : Nat} (expr : Expr n) :
    valueAsExpr (exprAsValue expr) = some expr := by
  exact
    Expr.rec
      (motive_1 := fun e => valueAsExpr (exprAsValue e) = some e)
      (motive_2 := fun _ => True)
      (motive_3 := fun _ => True)
      (motive_4 := fun _ => True)
      (motive_5 := fun _ => True)
      (fun _ => rfl)
      (fun _ => rfl)
      (fun _ => rfl)
      rfl
      (fun head tail ihHead ihTail => by
        change valueAsExpr (quoteValue head) = some head at ihHead
        change valueAsExpr (quoteValue tail) = some tail at ihTail
        simp [exprAsValue, quoteValue, taggedQuote, valueAsExpr, ihHead, ihTail])
      (fun body ih => by
        change valueAsExpr (quoteValue body) = some body at ih
        simp [exprAsValue, quoteValue, taggedQuote, valueAsExpr, ih])
      (fun _ => rfl)
      (fun _ => rfl)
      (fun body ih => by
        change valueAsExpr (quoteValue body) = some body at ih
        simp [exprAsValue, quoteValue, taggedQuote, valueAsExpr, ih])
      (fun fn arg ihFn ihArg => by
        change valueAsExpr (quoteValue fn) = some fn at ihFn
        change valueAsExpr (quoteValue arg) = some arg at ihArg
        simp [exprAsValue, quoteValue, taggedQuote, valueAsExpr, ihFn, ihArg])
      (fun test thenBranch elseBranch ihTest ihThen ihElse => by
        change valueAsExpr (quoteValue test) = some test at ihTest
        change valueAsExpr (quoteValue thenBranch) = some thenBranch at ihThen
        change valueAsExpr (quoteValue elseBranch) = some elseBranch at ihElse
        simp [exprAsValue, quoteValue, taggedQuote, valueAsExpr, ihTest, ihThen, ihElse])
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

def valueList? {n : Nat} : Value n → Option (List (Value n))
  | .nil => some []
  | .cons head tail => do
      let rest ← valueList? tail
      some (head :: rest)
  | _ => none

/-! ## Primitive application -/

def applyPrim {n : Nat} : Prim n → List (Value n) → Option (Value n)
  | .zero, [] => some (.cell Vn.zero)
  | .zero, _ => none
  | .xor, [.cell a, .cell b] => some (.cell (Vn.xor a b))
  | .xor, _ => none
  | .act, [.cell g, .cell x] => some (.cell (Vn.act g x))
  | .act, _ => none
  | .eq, [.cell a, .cell b] => some (truthValue (decide (a = b)))
  | .eq, _ => none
  | .flip slot, [.cell x] => some (.cell (Vn.act (BitSpace.single slot) x))
  | .flip _, _ => none
  | .cons, [head, tail] => some (.cons head tail)
  | .cons, _ => none
  | .car, [.cons head _] => some head
  | .car, _ => none
  | .cdr, [.cons _ tail] => some tail
  | .cdr, _ => none
  | .null, [v] => some (truthValue (v.isNil = true))
  | .null, _ => none
  | .atom, [v] => some (truthValue (valueAtom? v = true))
  | .atom, _ => none
  | .isBool, [.bool _] => some (truthValue true)
  | .isBool, [_] => some (truthValue false)
  | .isBool, _ => none
  | .isNumber, [.num _] => some (truthValue true)
  | .isNumber, [_] => some (truthValue false)
  | .isNumber, _ => none
  | .numEq, [.num a, .num b] => some (truthValue (a = b))
  | .numEq, _ => none
  | .succ, [.num value] => some (.num (value + 1))
  | .succ, _ => none
  | .pred, [.num 0] => some (.num 0)
  | .pred, [.num (value + 1)] => some (.num value)
  | .pred, _ => none
  | .add, [.num a, .num b] => some (.num (a + b))
  | .add, _ => none
  | .eval, _ => none

mutual

/-- Evaluate a native Wen expression with explicit fuel and globals. -/
def evalFuelG {n : Nat} : Nat → GlobalEnv n → Env n → Expr n → Option (Value n)
  | 0, _, _, _ => none
  | fuel + 1, global, env, expr =>
      match expr with
      | .cell value => some (.cell value)
      | .bool value => some (.bool value)
      | .num value => some (.num value)
      | .nil => some .nil
      | .cons head tail => do
          let h ← evalFuelG fuel global env head
          let t ← evalFuelG fuel global env tail
          some (.cons h t)
      | .quote body => some (quoteValue body)
      | .var index => Env.lookup env index
      | .ref name => GlobalEnv.lookup global name
      | .lam body => some (.closure global env body)
      | .app fn arg => do
          let f ← evalFuelG fuel global env fn
          match f with
          | .prim .eval => do
              let quoted ← evalFuelG fuel global env arg
              let decoded ← valueAsExpr quoted
              evalFuelG fuel global env decoded
          | .prim prim => do
              let args ← evalListFuelG fuel global env arg
              applyPrim prim args
          | _ => do
              let a ← evalFuelG fuel global env arg
              applyFuelG fuel global env f a
      | .if0 test thenBranch elseBranch => do
          let v ← evalFuelG fuel global env test
          if v.truthy then
            evalFuelG fuel global env thenBranch
          else
            evalFuelG fuel global env elseBranch
      | .prim prim => some (.prim prim)

/-- Apply an already evaluated function value to one already evaluated value. -/
def applyFuelG {n : Nat} : Nat → GlobalEnv n → Env n → Value n → Value n → Option (Value n)
  | 0, _, _, _, _ => none
  | fuel + 1, global, env, fn, arg =>
      match fn with
      | .closure closureGlobal closureEnv body =>
          evalFuelG fuel closureGlobal (arg :: closureEnv) body
      | .prim .eval => do
          let decoded ← valueAsExpr arg
          evalFuelG fuel global env decoded
      | .prim prim => applyPrim prim [arg]
      | _ => none

/-- Evaluate an expression expected to produce a proper native argument list. -/
def evalListFuelG {n : Nat} : Nat → GlobalEnv n → Env n → Expr n → Option (List (Value n))
  | 0, _, _, _ => none
  | fuel + 1, global, env, expr => do
      let v ← evalFuelG fuel global env expr
      valueList? v

end

def evalFuel {n : Nat} (fuel : Nat) (env : Env n) (expr : Expr n) : Option (Value n) :=
  evalFuelG fuel [] env expr

def applyFuel {n : Nat} (fuel : Nat) (fn arg : Value n) : Option (Value n) :=
  applyFuelG fuel [] [] fn arg

def evalListFuel {n : Nat} (fuel : Nat) (env : Env n) (expr : Expr n) :
    Option (List (Value n)) :=
  evalListFuelG fuel [] env expr

/-- Evaluate a core top-level form, returning the extended immutable globals. -/
def evalTopFuel {n : Nat} (fuel : Nat) (global : GlobalEnv n) :
    TopForm n → Option (GlobalEnv n × Value n)
  | .expr body => do
      let value ← evalFuelG fuel global [] body
      some (global, value)
  | .define name body => do
      let value ← evalFuelG fuel global [] body
      some ((name, value) :: global, value)

@[simp] theorem evalFuel_zero {n : Nat} (env : Env n) (expr : Expr n) :
    evalFuel 0 env expr = none := rfl

@[simp] theorem evalFuel_cell_succ {n : Nat}
    (fuel : Nat) (env : Env n) (value : Cell n) :
    evalFuel (fuel + 1) env (.cell value) = some (.cell value) := rfl

@[simp] theorem evalFuel_nil_succ {n : Nat} (fuel : Nat) (env : Env n) :
    evalFuel (fuel + 1) env .nil = some .nil := rfl

@[simp] theorem evalFuel_quote_succ {n : Nat}
    (fuel : Nat) (env : Env n) (expr : Expr n) :
    evalFuel (fuel + 1) env (.quote expr) = some (quoteValue expr) := rfl

@[simp] theorem evalFuel_var_zero_succ {n : Nat}
    (fuel : Nat) (env : Env n) (v : Value n) :
    evalFuel (fuel + 1) (v :: env) (.var 0) = some v := rfl

@[simp] theorem valueList_nil {n : Nat} :
    valueList? (.nil : Value n) = some [] := rfl

@[simp] theorem valueList_cons {n : Nat}
    (head tail : Value n) (rest : List (Value n))
    (h : valueList? tail = some rest) :
    valueList? (.cons head tail) = some (head :: rest) := by
  simp [valueList?, h]

@[simp] theorem applyPrim_add_nums {n : Nat} (a b : Nat) :
    applyPrim (.add : Prim n) [.num a, .num b] = some (.num (a + b)) := rfl

@[simp] theorem applyPrim_xor_cells {n : Nat} (a b : Cell n) :
    applyPrim (.xor : Prim n) [.cell a, .cell b] =
      some (.cell (Vn.xor a b)) := rfl

@[simp] theorem applyPrim_zero {n : Nat} :
    applyPrim (.zero : Prim n) [] = some (.cell Vn.zero) := rfl

@[simp] theorem applyPrim_car_cons {n : Nat} (head tail : Value n) :
    applyPrim (.car : Prim n) [.cons head tail] = some head := rfl

@[simp] theorem applyPrim_cdr_cons {n : Nat} (head tail : Value n) :
    applyPrim (.cdr : Prim n) [.cons head tail] = some tail := rfl

def lambdaAddExpr {n : Nat} : Expr n :=
  .app
    (.lam (.app (.prim .add) (Expr.list [.var 0, .num 3])))
    (.num 2)

theorem evalFuel_lambdaAddExpr {n : Nat} :
    evalFuel (n := n) 12 [] lambdaAddExpr = some (.num 5) := rfl

theorem evalFuel_slotXorExpr {n : Nat} (slot : Slot n) :
    evalFuel 8 [] (slotXorExpr slot) =
      some (.cell (Vn.xor (BitSpace.single slot) originCell)) := rfl

theorem evalFuel_eval_quote_num {n : Nat} :
    evalFuel (n := n) 3 [] (.app (.prim .eval) (.quote (.num 5))) = some (.num 5) := rfl

theorem eval_core_laws {n : Nat} :
    evalFuel (n := n) 12 [] lambdaAddExpr = some (.num 5)
    ∧ evalFuel (n := n) 3 [] (.app (.prim .eval) (.quote (.num 5))) = some (.num 5)
    ∧ (∀ env : Env n, ∀ expr : Expr n, evalFuel 0 env expr = none)
    ∧ (∀ fuel : Nat, ∀ env : Env n, ∀ expr : Expr n,
        evalFuel (fuel + 1) env (.quote expr) = some (quoteValue expr)) :=
  ⟨evalFuel_lambdaAddExpr, evalFuel_eval_quote_num, evalFuel_zero, evalFuel_quote_succ⟩

end SSBX.Foundation.Wen.Native
