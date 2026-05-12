/-
# Wen.V4Kernel.Binding -- de Bruijn environment fragment

This is the first binding layer above the V4 term kernel.  It uses de Bruijn
indices so the core does not depend on surface names.
-/

import SSBX.Foundation.Wen.V4Kernel.Combinator

namespace SSBX.Foundation.Wen.V4Kernel

open SSBX.Foundation.Hierarchy.Operators

abbrev BEnv : Type := List V4

namespace BEnv

def lookup : BEnv → Nat → Option V4
  | [], _ => none
  | g :: _, 0 => some g
  | _ :: rest, n + 1 => lookup rest n

@[simp] theorem lookup_zero (env : BEnv) (g : V4) :
    lookup (g :: env) 0 = some g := rfl

end BEnv

/-- V4 expression fragment with de Bruijn variables and one-binding `let`. -/
inductive BTerm where
  | atom (g : V4)
  | var (index : Nat)
  | compose (left right : BTerm)
  | let1 (value body : BTerm)
  deriving DecidableEq, Repr

namespace BTerm

def eval (env : BEnv) : BTerm → Option V4
  | .atom g => some g
  | .var index => BEnv.lookup env index
  | .compose left right => do
      let l ← eval env left
      let r ← eval env right
      some (V4.compose l r)
  | .let1 value body => do
      let v ← eval env value
      eval (v :: env) body

@[simp] theorem eval_atom (env : BEnv) (g : V4) :
    eval env (.atom g) = some g := rfl

@[simp] theorem eval_var_zero (env : BEnv) (g : V4) :
    eval (g :: env) (.var 0) = some g := rfl

@[simp] theorem eval_compose_atom (env : BEnv) (a b : V4) :
    eval env (.compose (.atom a) (.atom b)) = some (V4.compose a b) := rfl

@[simp] theorem eval_let1_atom_var_zero (env : BEnv) (g : V4) :
    eval env (.let1 (.atom g) (.var 0)) = some g := by
  rfl

/-- Lower a closed binding term to the old value-only `Term` fragment. -/
def lowerClosed (t : BTerm) : Option Term := do
  let v ← eval [] t
  some (.atom v)

theorem lowerClosed_correct (t : BTerm) (v : V4)
    (h : lowerClosed t = some (.atom v)) :
    eval [] t = some v := by
  unfold lowerClosed at h
  cases hEval : eval [] t with
  | none =>
      simp [hEval] at h
  | some w =>
      simp [hEval] at h
      exact congrArg some h

end BTerm

def sampleLetCompose : BTerm :=
  .let1 (.atom .cuo) (.compose (.var 0) (.atom .zong))

example : sampleLetCompose.eval [] = some .cuoZong := rfl

theorem binding_summary :
    sampleLetCompose.eval [] = some .cuoZong
    ∧ (∀ env : BEnv, ∀ g : V4, BTerm.eval (g :: env) (.var 0) = some g)
    ∧ (∀ t : BTerm, ∀ v : V4,
        BTerm.lowerClosed t = some (.atom v) → BTerm.eval [] t = some v) :=
  ⟨rfl, BTerm.eval_var_zero, BTerm.lowerClosed_correct⟩

end SSBX.Foundation.Wen.V4Kernel
