/-
# Wen.Layered.Flip -- bit flips and doubled-space flips
-/

import SSBX.Foundation.Wen.Layered.Split

namespace SSBX.Foundation.Wen.Layered

namespace BitSpace

/-- Toggle one coordinate. -/
def flip {n : Nat} (j : Slot n) (v : BitSpace n) : BitSpace n :=
  fun i => if i = j then !v i else v i

def flipOuter {n : Nat} (j : Slot n) (v : BitSpace (2 * n)) : BitSpace (2 * n) :=
  combine (flip j (outer v)) (inner v)

def flipInner {n : Nat} (j : Slot n) (v : BitSpace (2 * n)) : BitSpace (2 * n) :=
  combine (outer v) (flip j (inner v))

@[simp] theorem flip_apply_self {n : Nat} (j : Slot n) (v : BitSpace n) :
    flip j v j = !v j := by
  simp [flip]

theorem flip_apply_ne {n : Nat} {i j : Slot n} (h : i ≠ j) (v : BitSpace n) :
    flip j v i = v i := by
  simp [flip, h]

@[simp] theorem flip_self {n : Nat} (j : Slot n) (v : BitSpace n) :
    flip j (flip j v) = v := by
  funext i
  by_cases h : i = j
  · subst i
    simp [flip]
  · simp [flip, h]

@[simp] theorem outer_flipOuter {n : Nat} (j : Slot n) (v : BitSpace (2 * n)) :
    outer (flipOuter j v) = flip j (outer v) := by
  simp [flipOuter]

@[simp] theorem inner_flipOuter {n : Nat} (j : Slot n) (v : BitSpace (2 * n)) :
    inner (flipOuter j v) = inner v := by
  simp [flipOuter]

@[simp] theorem outer_flipInner {n : Nat} (j : Slot n) (v : BitSpace (2 * n)) :
    outer (flipInner j v) = outer v := by
  simp [flipInner]

@[simp] theorem inner_flipInner {n : Nat} (j : Slot n) (v : BitSpace (2 * n)) :
    inner (flipInner j v) = flip j (inner v) := by
  simp [flipInner]

@[simp] theorem flipOuter_self {n : Nat} (j : Slot n) (v : BitSpace (2 * n)) :
    flipOuter j (flipOuter j v) = v := by
  rw [← combine_outer_inner v]
  simp [flipOuter]

@[simp] theorem flipInner_self {n : Nat} (j : Slot n) (v : BitSpace (2 * n)) :
    flipInner j (flipInner j v) = v := by
  rw [← combine_outer_inner v]
  simp [flipInner]

theorem flip_summary (n : Nat) :
    (∀ j : Slot n, ∀ v : BitSpace n, flip j (flip j v) = v)
    ∧ (∀ j : Slot n, ∀ v : BitSpace (2 * n), outer (flipInner j v) = outer v)
    ∧ (∀ j : Slot n, ∀ v : BitSpace (2 * n), inner (flipOuter j v) = inner v)
    ∧ (∀ j : Slot n, ∀ v : BitSpace (2 * n), flipOuter j (flipOuter j v) = v)
    ∧ (∀ j : Slot n, ∀ v : BitSpace (2 * n), flipInner j (flipInner j v) = v) :=
  ⟨flip_self, outer_flipInner, inner_flipOuter, flipOuter_self, flipInner_self⟩

end BitSpace

end SSBX.Foundation.Wen.Layered
