/-
# Wen.V4Kernel.Word64 -- V4-native 64-word carrier

The real Wen Lisp surface uses 64 words.  The core carrier is not `Fin 64`:
it is three independent V4 coordinates, i.e. `V4^3`.
-/

import SSBX.Foundation.Hierarchy.Operators.V4
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod

namespace SSBX.Foundation.Wen.V4Kernel

open SSBX.Foundation.Hierarchy.Operators

/-- A 64-word coordinate is three V4 axes. -/
structure Word64 where
  first : V4
  second : V4
  third : V4
  deriving DecidableEq, BEq, Repr

namespace Word64

def ofV4 (first second third : V4) : Word64 :=
  ⟨first, second, third⟩

def origin : Word64 :=
  ⟨.dao, .dao, .dao⟩

def withThird (first second : V4) : List Word64 :=
  V4.all.map fun third => ⟨first, second, third⟩

def withSecond (first : V4) : List Word64 :=
  withThird first .dao ++ withThird first .cuo ++
    withThird first .zong ++ withThird first .cuoZong

def all : List Word64 :=
  withSecond .dao ++ withSecond .cuo ++ withSecond .zong ++ withSecond .cuoZong

theorem all_length : all.length = 64 := by native_decide

theorem all_length_eq_v4_card_cubed :
    all.length = Fintype.card V4 ^ 3 := by native_decide

theorem all_length_eq_four_cubed :
    all.length = 4 ^ 3 := by native_decide

/-- `Word64` is exactly three independent V4 coordinates. -/
def v4TripleEquiv : Word64 ≃ V4 × V4 × V4 where
  toFun := fun w => (w.first, w.second, w.third)
  invFun := fun p => ⟨p.1, p.2.1, p.2.2⟩
  left_inv := by
    intro w
    cases w
    rfl
  right_inv := by
    intro p
    rcases p with ⟨a, b, c⟩
    rfl

instance instFintype : Fintype Word64 where
  elems := all.toFinset
  complete := by
    intro word
    cases word with
    | mk first second third =>
        cases first <;> cases second <;> cases third <;> native_decide

theorem card_eq_v4_card_cubed :
    Fintype.card Word64 = Fintype.card V4 ^ 3 := by native_decide

theorem card_eq_four_cubed :
    Fintype.card Word64 = 4 ^ 3 := by native_decide

theorem card_eq_64 :
    Fintype.card Word64 = 64 := by native_decide

def compose (a b : Word64) : Word64 :=
  ⟨V4.compose a.first b.first,
    V4.compose a.second b.second,
    V4.compose a.third b.third⟩

@[simp] theorem compose_origin_left (w : Word64) :
    compose origin w = w := by
  cases w
  simp [compose, origin, V4.compose_dao_left]

@[simp] theorem compose_origin_right (w : Word64) :
    compose w origin = w := by
  cases w
  simp [compose, origin, V4.compose_dao_right]

@[simp] theorem compose_self (w : Word64) :
    compose w w = origin := by
  cases w
  simp [compose, origin, V4.compose_self]

theorem compose_comm (a b : Word64) :
    compose a b = compose b a := by
  cases a
  cases b
  simp [compose, V4.compose_comm]

theorem compose_assoc (a b c : Word64) :
    compose (compose a b) c = compose a (compose b c) := by
  cases a
  cases b
  cases c
  simp [compose, V4.compose_assoc]

def qian : Word64 := origin

def kun : Word64 := ⟨.cuoZong, .cuoZong, .cuoZong⟩

def complete : Word64 := ⟨.zong, .zong, .zong⟩

def incomplete : Word64 := ⟨.cuo, .cuo, .cuo⟩

theorem word64_summary :
    all.length = 64
    ∧ all.length = Fintype.card V4 ^ 3
    ∧ Fintype.card Word64 = 64
    ∧ (∀ w : Word64, compose origin w = w)
    ∧ (∀ w : Word64, compose w origin = w)
    ∧ (∀ w : Word64, compose w w = origin)
    ∧ (∀ a b : Word64, compose a b = compose b a)
    ∧ (∀ a b c : Word64, compose (compose a b) c = compose a (compose b c)) :=
  ⟨all_length, all_length_eq_v4_card_cubed, card_eq_64,
    compose_origin_left, compose_origin_right, compose_self,
    compose_comm, compose_assoc⟩

end Word64

end SSBX.Foundation.Wen.V4Kernel
