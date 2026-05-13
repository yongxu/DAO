/-
# Wen.Layered.Split -- outer/inner decomposition for bit spaces
-/

import SSBX.Foundation.Wen.Layered.BitSpace

namespace SSBX.Foundation.Wen.Layered

namespace BitSpace

/-- First half of a doubled bit-space. -/
def outer {n : Nat} (v : BitSpace (2 * n)) : BitSpace n :=
  fun i => v (Slot.inl i)

/-- Second half of a doubled bit-space. -/
def inner {n : Nat} (v : BitSpace (2 * n)) : BitSpace n :=
  fun i => v (Slot.inr i)

/-- Combine outer and inner halves into a doubled bit-space. -/
def combine {n : Nat} (o i : BitSpace n) : BitSpace (2 * n) :=
  fun j =>
    if h : j.val < n then
      o ⟨j.val, h⟩
    else
      i ⟨j.val - n, by
        have hj := j.isLt
        omega⟩

@[simp] theorem outer_combine {n : Nat} (o i : BitSpace n) :
    outer (combine o i) = o := by
  funext j
  simp [outer, combine]

@[simp] theorem inner_combine {n : Nat} (o i : BitSpace n) :
    inner (combine o i) = i := by
  funext j
  unfold inner combine
  simp

@[simp] theorem combine_outer_inner {n : Nat} (v : BitSpace (2 * n)) :
    combine (outer v) (inner v) = v := by
  funext j
  by_cases h : j.val < n
  · unfold combine outer
    simp [h]
    have hidx :
        Slot.inl (⟨j.val, h⟩ : Slot n) = j := by
      ext
      rfl
    rw [hidx]
  · unfold combine inner
    simp [h]
    have hidx :
        Slot.inr
          (⟨j.val - n, by
            have hj := j.isLt
            omega⟩ : Slot n) = j := by
      ext
      simp [Slot.inr]
      have hj := j.isLt
      omega
    rw [hidx]

theorem split_summary (n : Nat) :
    (∀ o i : BitSpace n, outer (combine o i) = o)
    ∧ (∀ o i : BitSpace n, inner (combine o i) = i)
    ∧ (∀ v : BitSpace (2 * n), combine (outer v) (inner v) = v) :=
  ⟨outer_combine, inner_combine, combine_outer_inner⟩

end BitSpace

end SSBX.Foundation.Wen.Layered
