/-
# Wen.V4Kernel.Mode16 -- the sixteen V4² action modes

`Mode16` is the action/control layer above state carriers.  It is not a new
cell carrier: it is `V4 x V4`, interpreted later as word-action plus temporal
control.
-/

import SSBX.Foundation.Hierarchy.Operators.V4

namespace SSBX.Foundation.Wen.V4Kernel

open SSBX.Foundation.Hierarchy.Operators

/-- The sixteen basic action/control structures: one V4 for the word action,
one V4 for the temporal/control action. -/
structure Mode16 where
  word : V4
  temporal : V4
  deriving DecidableEq, BEq, Repr

namespace Mode16

def identity : Mode16 := ⟨.dao, .dao⟩

def pureWord (g : V4) : Mode16 := ⟨g, .dao⟩

def pureTemporal (g : V4) : Mode16 := ⟨.dao, g⟩

def all : List Mode16 :=
  V4.all.flatMap fun word => V4.all.map fun temporal => ⟨word, temporal⟩

theorem all_length : all.length = 16 := by
  native_decide

def compose (a b : Mode16) : Mode16 :=
  ⟨V4.compose a.word b.word, V4.compose a.temporal b.temporal⟩

@[simp] theorem compose_identity_left (m : Mode16) :
    compose identity m = m := by
  cases m
  simp [compose, identity, V4.compose_dao_left]

@[simp] theorem compose_identity_right (m : Mode16) :
    compose m identity = m := by
  cases m
  simp [compose, identity, V4.compose_dao_right]

@[simp] theorem compose_self (m : Mode16) :
    compose m m = identity := by
  cases m
  simp [compose, identity, V4.compose_self]

theorem compose_comm (a b : Mode16) :
    compose a b = compose b a := by
  cases a
  cases b
  simp [compose, V4.compose_comm]

theorem compose_assoc (a b c : Mode16) :
    compose (compose a b) c = compose a (compose b c) := by
  cases a
  cases b
  cases c
  simp [compose, V4.compose_assoc]

def compound : Mode16 := ⟨.cuoZong, .cuoZong⟩

theorem mode16_summary :
    all.length = 16
    ∧ (∀ m : Mode16, compose identity m = m)
    ∧ (∀ m : Mode16, compose m identity = m)
    ∧ (∀ m : Mode16, compose m m = identity)
    ∧ (∀ a b : Mode16, compose a b = compose b a)
    ∧ (∀ a b c : Mode16, compose (compose a b) c = compose a (compose b c)) :=
  ⟨all_length, compose_identity_left, compose_identity_right, compose_self,
    compose_comm, compose_assoc⟩

end Mode16

end SSBX.Foundation.Wen.V4Kernel
