/-
# Wen.V4Kernel.LispEval -- fuelled evaluator for the V4-native Lisp kernel

The evaluator is deliberately small and total: all failure modes are represented
by `Option.none`, and fuel zero always fails.
-/

import SSBX.Foundation.Wen.V4Kernel.LispPrim

namespace SSBX.Foundation.Wen.V4Kernel

open SSBX.Foundation.Hierarchy.Operators

/-! ## Quoted syntax as values -/

def natValue : Nat → Value
  | 0 => .nil
  | n + 1 => .cons (.atom .dao) (natValue n)

def quoteTag (major minor : V4) : Value :=
  .cons (.atom major) (.atom minor)

def taggedQuote (major minor : V4) (payload : Value) : Value :=
  .cons (quoteTag major minor) payload

/-- Encode an expression as a Lisp value. -/
def quoteValue : Expr → Value
  | .atom g => taggedQuote .dao .dao (.atom g)
  | .symbol name => .symbol name
  | .num n => .num n
  | .nil => taggedQuote .dao .cuo .nil
  | .cons head tail =>
      taggedQuote .dao .zong (.cons (quoteValue head) (quoteValue tail))
  | .quote body => taggedQuote .dao .cuoZong (quoteValue body)
  | .var index => taggedQuote .cuo .dao (natValue index)
  | .ref name => taggedQuote .zong .cuoZong (.symbol name)
  | .lam body => taggedQuote .cuo .cuo (quoteValue body)
  | .app fn arg =>
      taggedQuote .cuo .zong (.cons (quoteValue fn) (quoteValue arg))
  | .if0 test thenBranch elseBranch =>
      taggedQuote .cuo .cuoZong
        (.cons (quoteValue test) (.cons (quoteValue thenBranch) (quoteValue elseBranch)))
  | .prim p => taggedQuote .zong .dao (.prim p)

def valueNat? : Value → Option Nat
  | .nil => some 0
  | .cons (.atom .dao) rest => do
      let n ← valueNat? rest
      some (n + 1)
  | _ => none

@[simp] theorem valueNat_natValue (n : Nat) :
    valueNat? (natValue n) = some n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [natValue, valueNat?, ih]

/-- Decode quote-compatible values back to expressions. -/
def valueAsExpr : Value → Option Expr
  | .cons (.cons (.atom .dao) (.atom .dao)) (.atom g) => some (.atom g)
  | .symbol name => some (.symbol name)
  | .num n => some (.num n)
  | .cons (.cons (.atom .dao) (.atom .cuo)) .nil => some .nil
  | .cons (.cons (.atom .dao) (.atom .zong)) (.cons head tail) => do
      let h ← valueAsExpr head
      let t ← valueAsExpr tail
      some (.cons h t)
  | .cons (.cons (.atom .dao) (.atom .cuoZong)) body => do
      let b ← valueAsExpr body
      some (.quote b)
  | .cons (.cons (.atom .cuo) (.atom .dao)) indexValue => do
      let n ← valueNat? indexValue
      some (.var n)
  | .cons (.cons (.atom .zong) (.atom .cuoZong)) (.symbol name) => some (.ref name)
  | .cons (.cons (.atom .cuo) (.atom .cuo)) body => do
      let b ← valueAsExpr body
      some (.lam b)
  | .cons (.cons (.atom .cuo) (.atom .zong)) (.cons fn arg) => do
      let f ← valueAsExpr fn
      let a ← valueAsExpr arg
      some (.app f a)
  | .cons (.cons (.atom .cuo) (.atom .cuoZong))
      (.cons test (.cons thenBranch elseBranch)) => do
      let c ← valueAsExpr test
      let t ← valueAsExpr thenBranch
      let e ← valueAsExpr elseBranch
      some (.if0 c t e)
  | .cons (.cons (.atom .zong) (.atom .dao)) (.prim p) => some (.prim p)
  | _ => none

def valueList? : Value → Option (List Value)
  | .nil => some []
  | .cons head tail => do
      let rest ← valueList? tail
      some (head :: rest)
  | _ => none

mutual

/-- Evaluate a Lisp expression with explicit fuel and a global word environment. -/
def evalFuelG : Nat → GlobalEnv → Env → Expr → Option Value
  | 0, _, _, _ => none
  | fuel + 1, global, env, expr =>
      match expr with
      | .atom g => some (.atom g)
      | .symbol name => some (.symbol name)
      | .num n => some (.num n)
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
          | .prim p => do
              let args ← evalListFuelG fuel global env arg
              applyPrim p args
          | _ => do
              let a ← evalFuelG fuel global env arg
              applyFuelG fuel global env f a
      | .if0 test thenBranch elseBranch => do
          let v ← evalFuelG fuel global env test
          match v with
          | .nil => evalFuelG fuel global env elseBranch
          | _ => evalFuelG fuel global env thenBranch
      | .prim p => some (.prim p)

/-- Apply an already evaluated function value to one already evaluated value. -/
def applyFuelG : Nat → GlobalEnv → Env → Value → Value → Option Value
  | 0, _, _, _, _ => none
  | fuel + 1, global, env, fn, arg =>
      match fn with
      | .closure closureGlobal closureEnv body =>
          evalFuelG fuel closureGlobal (arg :: closureEnv) body
      | .prim .eval => do
          let decoded ← valueAsExpr arg
          evalFuelG fuel global env decoded
      | .prim p => applyPrim p [arg]
      | _ => none

/-- Evaluate an expression expected to produce a proper Lisp argument list. -/
def evalListFuelG : Nat → GlobalEnv → Env → Expr → Option (List Value)
  | 0, _, _, _ => none
  | fuel + 1, global, env, expr => do
      let v ← evalFuelG fuel global env expr
      valueList? v

end

/-- Closed-global wrapper retained for the first Lisp fragment. -/
def evalFuel (fuel : Nat) (env : Env) (expr : Expr) : Option Value :=
  evalFuelG fuel [] env expr

def applyFuel (fuel : Nat) (fn arg : Value) : Option Value :=
  applyFuelG fuel [] [] fn arg

def evalListFuel (fuel : Nat) (env : Env) (expr : Expr) : Option (List Value) :=
  evalListFuelG fuel [] env expr

/-- Evaluate a core top-level form, returning the extended immutable globals. -/
def evalTopFuel (fuel : Nat) (global : GlobalEnv) : TopForm → Option (GlobalEnv × Value)
  | .expr body => do
      let value ← evalFuelG fuel global [] body
      some (global, value)
  | .define name body => do
      let value ← evalFuelG fuel global [] body
      some ((name, value) :: global, value)

@[simp] theorem evalFuel_zero (env : Env) (expr : Expr) :
    evalFuel 0 env expr = none := rfl

@[simp] theorem evalFuel_atom_succ (fuel : Nat) (env : Env) (g : V4) :
    evalFuel (fuel + 1) env (.atom g) = some (.atom g) := rfl

@[simp] theorem evalFuel_nil_succ (fuel : Nat) (env : Env) :
    evalFuel (fuel + 1) env .nil = some .nil := rfl

@[simp] theorem evalFuel_quote_succ (fuel : Nat) (env : Env) (expr : Expr) :
    evalFuel (fuel + 1) env (.quote expr) = some (quoteValue expr) := rfl

@[simp] theorem evalFuel_var_zero_succ (fuel : Nat) (env : Env) (v : Value) :
    evalFuel (fuel + 1) (v :: env) (.var 0) = some v := rfl

@[simp] theorem valueList_nil :
    valueList? .nil = some [] := rfl

@[simp] theorem valueList_cons (head tail : Value) (rest : List Value)
    (h : valueList? tail = some rest) :
    valueList? (.cons head tail) = some (head :: rest) := by
  simp [valueList?, h]

def sampleLispLambdaCompose : Expr :=
  .app
    (.lam (.app (.prim .v4Compose) (Expr.list [.var 0, .atom .cuo])))
    (.atom .zong)

theorem evalFuel_sampleLispCompose :
    evalFuel 8 [] sampleLispCompose = some (.atom .cuoZong) := by
  change some (Value.atom (V4.compose .cuo .zong)) = some (Value.atom .cuoZong)
  rw [V4.cuo_zong_eq_cuoZong]

theorem evalFuel_sampleLispLambdaCompose :
    evalFuel 12 [] sampleLispLambdaCompose = some (.atom .cuoZong) := by
  change some (Value.atom (V4.compose .zong .cuo)) = some (Value.atom .cuoZong)
  rw [V4.zong_cuo_eq_cuoZong]

theorem evalFuel_sampleWordCompose :
    evalFuel 8 [] sampleWordCompose = some (.symbol .kun) := by
  change some (Value.symbol (Word64.compose Word64.qian Word64.kun)) =
    some (Value.symbol .kun)
  simp [Word64.compose, Word64.qian, Word64.kun, Word64.origin, V4.compose_dao_left]

theorem evalFuel_sampleNatAdd :
    evalFuel 8 [] sampleNatAdd = some (.num 5) := by
  change some (Value.num (2 + 3)) = some (Value.num 5)
  rfl

theorem evalTop_define_then_ref :
    evalTopFuel 2 [] (.define .qian (.num 7)) =
      some ([(.qian, .num 7)], .num 7)
    ∧ evalTopFuel 1 [(.qian, .num 7)] (.expr (.ref .qian)) =
      some ([(.qian, .num 7)], .num 7) :=
  ⟨rfl, rfl⟩

theorem evalFuel_quote_symbol :
    evalFuel 1 [] (.quote (.symbol .qian)) = some (.symbol .qian) := rfl

theorem evalFuel_eval_quote_num :
    evalFuel 3 [] (.app (.prim .eval) (.quote (.num 5))) = some (.num 5) := rfl

theorem lisp_eval_summary :
    evalFuel 8 [] sampleLispCompose = some (.atom .cuoZong)
    ∧ evalFuel 12 [] sampleLispLambdaCompose = some (.atom .cuoZong)
    ∧ evalFuel 8 [] sampleWordCompose = some (.symbol .kun)
    ∧ evalFuel 8 [] sampleNatAdd = some (.num 5)
    ∧ evalFuel 1 [] (.quote (.symbol .qian)) = some (.symbol .qian)
    ∧ (∀ env : Env, ∀ expr : Expr, evalFuel 0 env expr = none)
    ∧ (∀ fuel : Nat, ∀ env : Env, ∀ expr : Expr,
        evalFuel (fuel + 1) env (.quote expr) = some (quoteValue expr)) :=
  ⟨evalFuel_sampleLispCompose, evalFuel_sampleLispLambdaCompose,
    evalFuel_sampleWordCompose, evalFuel_sampleNatAdd, evalFuel_quote_symbol,
    evalFuel_zero, evalFuel_quote_succ⟩

end SSBX.Foundation.Wen.V4Kernel
