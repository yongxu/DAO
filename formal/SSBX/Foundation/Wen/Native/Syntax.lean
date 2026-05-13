/-
# Wen.Native.Syntax -- rank-polymorphic Wen expression core

The native Wen kernel is parameterized by the Layered rank `n`.  Its atomic
program values are `Rn n`; V4, Word64/R6, and R8/Cell256 enter only through
bridges over this generic carrier.
-/

import SSBX.Foundation.Wen.Layered.VnRn

namespace SSBX.Foundation.Wen.Native

open SSBX.Foundation.Wen.Layered

abbrev Cell (n : Nat) : Type := Rn n
abbrev Op (n : Nat) : Type := Vn n

/-- Structural and layer-native primitive names for the native Wen kernel. -/
inductive Prim (n : Nat) where
  | zero
  | xor
  | act
  | eq
  | flip (slot : Slot n)
  | cons
  | car
  | cdr
  | null
  | atom
  | isBool
  | isNumber
  | numEq
  | numLe
  | numLt
  | succ
  | pred
  | add
  | eval

mutual

/-- Rank-polymorphic native Wen expressions. -/
inductive Expr (n : Nat) where
  | cell (value : Cell n)
  | bool (value : Bool)
  | num (value : Nat)
  | nil
  | cons (head tail : Expr n)
  | quote (body : Expr n)
  | var (index : Nat)
  | ref (name : Cell n)
  | lam (body : Expr n)
  | app (fn arg : Expr n)
  | if0 (test thenBranch elseBranch : Expr n)
  | prim (prim : Prim n)

/-- Runtime values for native Wen evaluation. -/
inductive Value (n : Nat) where
  | cell (value : Cell n)
  | bool (value : Bool)
  | num (value : Nat)
  | nil
  | cons (head tail : Value n)
  | closure (global : List (Cell n × Value n)) (env : List (Value n)) (body : Expr n)
  | recClosure (name : Cell n) (global : List (Cell n × Value n))
      (env : List (Value n)) (body : Expr n)
  | prim (prim : Prim n)

end

abbrev Env (n : Nat) : Type := List (Value n)
abbrev GlobalEnv (n : Nat) : Type := List (Cell n × Value n)

/-- Top-level forms after surface elaboration. -/
inductive TopForm (n : Nat) where
  | expr (body : Expr n)
  | define (name : Cell n) (body : Expr n)

namespace Env

def lookup {n : Nat} : Env n → Nat → Option (Value n)
  | [], _ => none
  | v :: _, 0 => some v
  | _ :: rest, k + 1 => lookup rest k

@[simp] theorem lookup_zero {n : Nat} (env : Env n) (value : Value n) :
    lookup (value :: env) 0 = some value := rfl

end Env

namespace GlobalEnv

def lookup {n : Nat} : GlobalEnv n → Cell n → Option (Value n)
  | [], _ => none
  | (name, value) :: rest, target =>
      if name = target then some value else lookup rest target

@[simp] theorem lookup_cons_self {n : Nat}
    (env : GlobalEnv n) (name : Cell n) (value : Value n) :
    lookup ((name, value) :: env) name = some value := by
  simp [lookup]

end GlobalEnv

namespace Expr

def list {n : Nat} : List (Expr n) → Expr n
  | [] => .nil
  | head :: tail => .cons head (list tail)

@[simp] theorem list_nil {n : Nat} :
    list ([] : List (Expr n)) = nil := rfl

@[simp] theorem list_cons {n : Nat} (head : Expr n) (tail : List (Expr n)) :
    list (head :: tail) = cons head (list tail) := rfl

end Expr

namespace Value

def list {n : Nat} : List (Value n) → Value n
  | [] => .nil
  | head :: tail => .cons head (list tail)

def isNil {n : Nat} : Value n → Bool
  | .nil => true
  | _ => false

def truthy {n : Nat} : Value n → Bool
  | .nil => false
  | .bool false => false
  | _ => true

@[simp] theorem list_nil {n : Nat} :
    list ([] : List (Value n)) = nil := rfl

@[simp] theorem list_cons {n : Nat} (head : Value n) (tail : List (Value n)) :
    list (head :: tail) = cons head (list tail) := rfl

end Value

/-- The neutral native cell at any rank.  At rank 8 this is the same
all-`o` origin used by the Cell256/R8 bridge. -/
def originCell {n : Nat} : Cell n := Vn.zero

/-- Core expression that xors one basis coordinate with the origin cell. -/
def slotXorExpr {n : Nat} (slot : Slot n) : Expr n :=
  .app (.prim .xor) (Expr.list [.cell (BitSpace.single slot), .cell originCell])

theorem syntax_core_laws (n : Nat) :
    (originCell : Cell n) = Vn.zero
    ∧ Expr.list ([] : List (Expr n)) = .nil
    ∧ Value.list ([] : List (Value n)) = .nil :=
  ⟨rfl, rfl, rfl⟩

end SSBX.Foundation.Wen.Native
