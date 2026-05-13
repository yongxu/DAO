/-
# Wen.Layered.Slot -- finite position layer

Layer 0 names finite slots and the canonical even split of slot indices.  It
does not carry state, truth, or Wen interpretation.
-/

import Mathlib.Tactic

namespace SSBX.Foundation.Wen.Layered

/-- A finite position set with `n` slots. -/
abbrev Slot (n : Nat) : Type := Fin n

namespace Slot

/-- Left slot injection into the first half of `2 * n` slots. -/
def inl {n : Nat} (i : Slot n) : Slot (2 * n) :=
  ⟨i.val, by
    have hi := i.isLt
    omega⟩

/-- Right slot injection into the second half of `2 * n` slots. -/
def inr {n : Nat} (i : Slot n) : Slot (2 * n) :=
  ⟨n + i.val, by
    have hi := i.isLt
    omega⟩

@[simp] theorem inl_val {n : Nat} (i : Slot n) :
    (inl i).val = i.val := rfl

@[simp] theorem inr_val {n : Nat} (i : Slot n) :
    (inr i).val = n + i.val := rfl

theorem inl_lt_mid {n : Nat} (i : Slot n) :
    (inl i).val < n := i.isLt

theorem not_inr_lt_mid {n : Nat} (i : Slot n) :
    ¬ (inr i).val < n := by
  simp [inr]

end Slot

end SSBX.Foundation.Wen.Layered
