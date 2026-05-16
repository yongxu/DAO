/-
# Wen.RKernel.LispSyntax -- unified Lisp-shaped core

This is the canonical V4-native Lisp syntax layer.  It does not import an R
backend; R-space remains a later representation theorem.
-/

import SSBX.Foundation.Wen.RKernel.Binding
import SSBX.Foundation.Wen.RKernel.Data
import SSBX.Foundation.Wen.RKernel.Word64

namespace SSBX.Foundation.Wen.RKernel

open SSBX.Foundation.Hierarchy.Operators

/-- Structural primitive names for the minimal Lisp kernel. -/
inductive Prim where
  | v4Compose
  | v4Eq
  | wordCompose
  | wordEq
  | numEq
  | succ
  | pred
  | add
  | cons
  | car
  | cdr
  | null
  | atom
  | isSymbol
  | isNumber
  | eval
  | r5Is
  | r5ToR4
  | r5Compose
  | r5Coords
  deriving DecidableEq, Repr

namespace Prim

def all : List Prim :=
  [.v4Compose, .v4Eq, .wordCompose, .wordEq, .numEq, .succ, .pred, .add,
    .cons, .car, .cdr, .null, .atom, .isSymbol, .isNumber, .eval,
    .r5Is, .r5ToR4, .r5Compose, .r5Coords]

theorem all_length : all.length = 20 := rfl

end Prim

mutual

/-- Unified Lisp expression syntax over V4 atoms and structural primitives. -/
inductive Expr where
  | atom (g : V4)
  | symbol (name : Word64)
  | num (n : Nat)
  | nil
  | cons (head tail : Expr)
  | quote (body : Expr)
  | var (index : Nat)
  | ref (name : Word64)
  | lam (body : Expr)
  | app (fn arg : Expr)
  | if0 (test thenBranch elseBranch : Expr)
  | prim (p : Prim)
  deriving Repr

/-- Runtime values for the V4-native Lisp kernel. -/
inductive Value where
  | atom (g : V4)
  | symbol (name : Word64)
  | num (n : Nat)
  | nil
  | cons (head tail : Value)
  | closure (global : List (Word64 × Value)) (env : List Value) (body : Expr)
  | prim (p : Prim)
  deriving Repr

end

abbrev Env : Type := List Value
abbrev GlobalEnv : Type := List (Word64 × Value)

/-- Core top-level Lisp form after surface names have been elaborated. -/
inductive TopForm where
  | expr (body : Expr)
  | define (name : Word64) (body : Expr)
  deriving Repr

namespace Env

def lookup : Env → Nat → Option Value
  | [], _ => none
  | v :: _, 0 => some v
  | _ :: rest, n + 1 => lookup rest n

@[simp] theorem lookup_zero (env : Env) (v : Value) :
    lookup (v :: env) 0 = some v := rfl

end Env

namespace GlobalEnv

def lookup : GlobalEnv → Word64 → Option Value
  | [], _ => none
  | (name, value) :: rest, target =>
      if name = target then some value else lookup rest target

@[simp] theorem lookup_cons_self (env : GlobalEnv) (name : Word64) (value : Value) :
    lookup ((name, value) :: env) name = some value := by
  simp [lookup]

end GlobalEnv

namespace Expr

def list : List Expr → Expr
  | [] => .nil
  | head :: tail => .cons head (list tail)

@[simp] theorem list_nil :
    list [] = nil := rfl

@[simp] theorem list_cons (head : Expr) (tail : List Expr) :
    list (head :: tail) = cons head (list tail) := rfl

end Expr

namespace Value

def list : List Value → Value
  | [] => .nil
  | head :: tail => .cons head (list tail)

def isNil : Value → Bool
  | .nil => true
  | _ => false

def truthy (v : Value) : Bool :=
  !isNil v

@[simp] theorem list_nil :
    list [] = nil := rfl

@[simp] theorem list_cons (head : Value) (tail : List Value) :
    list (head :: tail) = cons head (list tail) := rfl

end Value

namespace Term

/-- Embed the old V4 term fragment into the unified Lisp syntax. -/
def toExpr : Term → Expr
  | .atom g => .atom g
  | .compose left right =>
      .app (.prim .v4Compose) (Expr.list [left.toExpr, right.toExpr])

end Term

namespace Datum

/-- Embed the old data fragment into Lisp syntax. -/
def toExpr : Datum → Expr
  | .atom g => .atom g
  | .nil => .nil
  | .cons head tail => .cons head.toExpr tail.toExpr

end Datum

namespace BTerm

/-- Embed the old de Bruijn value-only fragment into Lisp syntax. -/
def toExpr : BTerm → Expr
  | .atom g => .atom g
  | .var index => .var index
  | .compose left right =>
      .app (.prim .v4Compose) (Expr.list [left.toExpr, right.toExpr])
  | .let1 value body => .app (.lam body.toExpr) value.toExpr

end BTerm

def sampleLispCompose : Expr :=
  .app (.prim .v4Compose) (Expr.list [.atom .cuo, .atom .zong])

def sampleWordCompose : Expr :=
  .app (.prim .wordCompose) (Expr.list [.symbol .qian, .symbol .kun])

def sampleNatAdd : Expr :=
  .app (.prim .add) (Expr.list [.num 2, .num 3])

def sampleLispLetCompose : Expr :=
  sampleLetCompose.toExpr

theorem lisp_syntax_summary :
    Prim.all.length = 20
    ∧ sampleCuoZong.toExpr = sampleLispCompose
    ∧ sampleWordCompose =
      .app (.prim .wordCompose) (Expr.list [.symbol .qian, .symbol .kun])
    ∧ sampleNatAdd = .app (.prim .add) (Expr.list [.num 2, .num 3])
    ∧ sampleLetCompose.toExpr = sampleLispLetCompose :=
  ⟨Prim.all_length, rfl, rfl, rfl, rfl⟩

end SSBX.Foundation.Wen.RKernel
