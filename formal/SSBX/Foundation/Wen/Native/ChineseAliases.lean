/-
# Wen.Native.ChineseAliases -- Chinese surface names for native Wen layers

This module fixes the Chinese vocabulary for the native Wen expression stack.
It is deliberately thin: every term below is an `abbrev` or a constructor
wrapper over the existing native core.  It does not add evaluator cases,
primitive constructors, or a new carrier layer.
-/

import SSBX.Foundation.Wen.Native.Program
import SSBX.Foundation.Wen.RootRuleKernel

namespace SSBX.Foundation.Wen.Native

namespace ChineseAliases

open SSBX.Foundation.Wen.Layered

universe u

/-! ## Layer names -/

abbrev «式» (n : Nat) : Type := Expr n
abbrev «核式» : Type := SSBX.Foundation.Wen.RootRuleKernel.CoreForm
abbrev «行» (n : Nat) : Type := TopForm n
abbrev «列» (α : Type u) : Type u := List α
abbrev «行列» (n : Nat) : Type := «列» (TopForm n)
abbrev «文» (n : Nat) : Type := List (TopForm n)
abbrev «值» (n : Nat) : Type := Value n
abbrev «值列» (n : Nat) : Type := List (Value n)
abbrev «元型» (n : Nat) : Type := Cell n

/-- A finite set is represented by a list plus an explicit no-duplicate proof. -/
structure «集» (α : Type u) where
  items : List α
  nodup : items.Nodup

abbrev «元集» (n : Nat) : Type := «集» (Cell n)
abbrev «值集» (n : Nat) : Type := «集» (Value n)

def «空集» {α : Type u} : «集» α :=
  { items := [], nodup := by simp }

def «属» {α : Type u} (x : α) (s : «集» α) : Prop :=
  x ∈ s.items

def «去重判准» {α : Type u} (xs : List α) : Prop :=
  xs.Nodup

/-! ## Primitive-name aliases -/

namespace «原语»

abbrev «结» {n : Nat} : Prim n := .cons
abbrev «首» {n : Nat} : Prim n := .car
abbrev «余» {n : Nat} : Prim n := .cdr
abbrev «空乎» {n : Nat} : Prim n := .null
abbrev «判空» {n : Nat} : Prim n := .null
abbrev «不大于» {n : Nat} : Prim n := .numLe
abbrev «大于» {n : Nat} : Prim n := .numLt
abbrev «解» {n : Nat} : Prim n := .eval

end «原语»

/-! ## Core expression aliases -/

def «元» {n : Nat} (value : Cell n) : Expr n :=
  .cell value

def «名» {n : Nat} (name : Cell n) : Expr n :=
  .ref name

def «算子» {n : Nat} (prim : Prim n) : Expr n :=
  .prim prim

def «空» {n : Nat} : Expr n :=
  .nil

def «空值» {n : Nat} : Value n :=
  .nil

def «结» {n : Nat} (head tail : Expr n) : Expr n :=
  .cons head tail

def «函» {n : Nat} (body : Expr n) : Expr n :=
  .lam body

def «施» {n : Nat} (fn arg : Expr n) : Expr n :=
  .app fn arg

def «若» {n : Nat} (test thenBranch elseBranch : Expr n) : Expr n :=
  .if0 test thenBranch elseBranch

def «引» {n : Nat} (body : Expr n) : Expr n :=
  .quote body

def «列式» {n : Nat} (items : List (Expr n)) : Expr n :=
  Expr.list items

def «列值» {n : Nat} (items : List (Value n)) : Value n :=
  Value.list items

def «原语施» {n : Nat} (prim : Prim n) (args : List (Expr n)) : Expr n :=
  .app (.prim prim) (Expr.list args)

def «首» {n : Nat} (expr : Expr n) : Expr n :=
  «原语施» .car [expr]

def «余» {n : Nat} (expr : Expr n) : Expr n :=
  «原语施» .cdr [expr]

def «空乎» {n : Nat} (expr : Expr n) : Expr n :=
  «原语施» .null [expr]

def «判空» {n : Nat} (expr : Expr n) : Expr n :=
  «空乎» expr

def «不大于» {n : Nat} (left right : Expr n) : Expr n :=
  «原语施» .numLe [left, right]

def «大于» {n : Nat} (left right : Expr n) : Expr n :=
  «原语施» .numLt [right, left]

def «解» {n : Nat} (expr : Expr n) : Expr n :=
  .app (.prim .eval) expr

/-! ## Alias laws -/

theorem chinese_type_alias_laws (n : Nat) :
    «式» n = Expr n
    ∧ «行» n = TopForm n
    ∧ «文» n = List (TopForm n)
    ∧ «值» n = Value n
    ∧ «值列» n = List (Value n) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem chinese_primitive_alias_laws {n : Nat} :
    («原语».«结» : Prim n) = .cons
    ∧ («原语».«首» : Prim n) = .car
    ∧ («原语».«余» : Prim n) = .cdr
    ∧ («原语».«空乎» : Prim n) = .null
    ∧ («原语».«判空» : Prim n) = .null
    ∧ («原语».«不大于» : Prim n) = .numLe
    ∧ («原语».«大于» : Prim n) = .numLt
    ∧ («原语».«解» : Prim n) = .eval :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem chinese_expr_alias_laws {n : Nat}
    (cell name : Cell n) (prim : Prim n) (x y test thenBranch elseBranch : Expr n) :
    «元» cell = .cell cell
    ∧ «名» name = .ref name
    ∧ «算子» prim = .prim prim
    ∧ («空» : Expr n) = .nil
    ∧ «结» x y = .cons x y
    ∧ «函» x = .lam x
    ∧ «施» x y = .app x y
    ∧ «若» test thenBranch elseBranch = .if0 test thenBranch elseBranch
    ∧ «引» x = .quote x
    ∧ «首» x = .app (.prim .car) (Expr.list [x])
    ∧ «余» x = .app (.prim .cdr) (Expr.list [x])
    ∧ «空乎» x = .app (.prim .null) (Expr.list [x])
    ∧ «判空» x = .app (.prim .null) (Expr.list [x])
    ∧ «不大于» x y = .app (.prim .numLe) (Expr.list [x, y])
    ∧ «大于» x y = .app (.prim .numLt) (Expr.list [y, x])
    ∧ «解» x = .app (.prim .eval) x :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem empty_set_laws {α : Type u} :
    («空集» : «集» α).items = []
    ∧ («空集» : «集» α).items.Nodup :=
  ⟨rfl, by simp [«空集»]⟩

theorem eval_chinese_cons_origin_nil {n : Nat} :
    evalFuel (n := n) 3 [] («结» (.cell originCell) «空») =
      some (.cons (.cell originCell) .nil) :=
  rfl

theorem eval_chinese_car_cons_origin_nil {n : Nat} :
    evalFuel (n := n) 8 [] («首» («结» (.cell originCell) «空»)) =
      some (.cell originCell) :=
  rfl

theorem eval_chinese_if_null_nil {n : Nat} :
    evalFuel (n := n) 8 [] («若» («空乎» «空») (.num 1) (.num 2)) =
      some (.num 1) :=
  rfl

theorem chinese_alias_summary {n : Nat} :
    («式» n = Expr n)
    ∧ («核式» = SSBX.Foundation.Wen.RootRuleKernel.CoreForm)
    ∧ («文» n = List (TopForm n))
    ∧ (evalFuel (n := n) 3 [] («结» (.cell originCell) «空») =
        some (.cons (.cell originCell) .nil))
    ∧ (evalFuel (n := n) 8 [] («首» («结» (.cell originCell) «空»)) =
        some (.cell originCell))
    ∧ (evalFuel (n := n) 8 [] («若» («空乎» «空») (.num 1) (.num 2)) =
        some (.num 1)) :=
  ⟨rfl, rfl, rfl, eval_chinese_cons_origin_nil,
    eval_chinese_car_cons_origin_nil, eval_chinese_if_null_nil⟩

end ChineseAliases

end SSBX.Foundation.Wen.Native
