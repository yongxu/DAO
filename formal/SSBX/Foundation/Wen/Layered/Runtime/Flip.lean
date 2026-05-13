/-
# Wen.Layered.Runtime.Flip -- runtime bit flips
-/

import SSBX.Foundation.Wen.Layered.Runtime.Split
import SSBX.Foundation.Wen.Layered.Flip

namespace SSBX.Foundation.Wen.Layered.Runtime

def flip {n : Nat} (j : Slot n) (v : Cell n) : Cell n :=
  ofSpec (BitSpace.flip j (toSpec v))

def flipOuter {n : Nat} (j : Slot n) (v : Cell (2 * n)) : Cell (2 * n) :=
  ofSpec (BitSpace.flipOuter j (toSpec v))

def flipInner {n : Nat} (j : Slot n) (v : Cell (2 * n)) : Cell (2 * n) :=
  ofSpec (BitSpace.flipInner j (toSpec v))

@[simp] theorem toSpec_flip {n : Nat} (j : Slot n) (v : Cell n) :
    toSpec (flip j v) = BitSpace.flip j (toSpec v) := by
  simp [flip]

@[simp] theorem toSpec_flipOuter {n : Nat} (j : Slot n) (v : Cell (2 * n)) :
    toSpec (flipOuter j v) = BitSpace.flipOuter j (toSpec v) := by
  simp [flipOuter]

@[simp] theorem toSpec_flipInner {n : Nat} (j : Slot n) (v : Cell (2 * n)) :
    toSpec (flipInner j v) = BitSpace.flipInner j (toSpec v) := by
  simp [flipInner]

@[simp] theorem flip_self {n : Nat} (j : Slot n) (v : Cell n) :
    flip j (flip j v) = v := by
  apply eq_of_toSpec_eq
  simp

@[simp] theorem outer_flipOuter {n : Nat} (j : Slot n) (v : Cell (2 * n)) :
    outer (flipOuter j v) = flip j (outer v) := by
  apply eq_of_toSpec_eq
  simp

@[simp] theorem inner_flipOuter {n : Nat} (j : Slot n) (v : Cell (2 * n)) :
    inner (flipOuter j v) = inner v := by
  apply eq_of_toSpec_eq
  simp

@[simp] theorem outer_flipInner {n : Nat} (j : Slot n) (v : Cell (2 * n)) :
    outer (flipInner j v) = outer v := by
  apply eq_of_toSpec_eq
  simp

@[simp] theorem inner_flipInner {n : Nat} (j : Slot n) (v : Cell (2 * n)) :
    inner (flipInner j v) = flip j (inner v) := by
  apply eq_of_toSpec_eq
  simp

@[simp] theorem flipOuter_self {n : Nat} (j : Slot n) (v : Cell (2 * n)) :
    flipOuter j (flipOuter j v) = v := by
  apply eq_of_toSpec_eq
  simp

@[simp] theorem flipInner_self {n : Nat} (j : Slot n) (v : Cell (2 * n)) :
    flipInner j (flipInner j v) = v := by
  apply eq_of_toSpec_eq
  simp

end SSBX.Foundation.Wen.Layered.Runtime
