/-
# Wen.Layered.Runtime.Core -- runtime Hamming core and boundary
-/

import SSBX.Foundation.Wen.Layered.Runtime.Modal
import SSBX.Foundation.Wen.Layered.Core

namespace SSBX.Foundation.Wen.Layered.Runtime

/-- Runtime Hamming distance, defined by the specification view of cells. -/
def hamming {n : Nat} (a b : Cell n) : Nat :=
  BitSpace.hamming (Runtime.toSpec a) (Runtime.toSpec b)

def core {n : Nat} (k : Nat) (D : Set (Cell n)) : Set (Cell n) :=
  fun x => D x ∧ ∀ y : Cell n, hamming x y ≤ k → D y

def boundary {n : Nat} (D : Set (Cell n)) : Set (Cell n) :=
  fun x => D x ∧ ∃ j : Slot n, ¬ D (flip j x)

def flipSequence {n : Nat} (js : List (Slot n)) (v : Cell n) :
    Cell n :=
  js.foldl (fun acc j => flip j acc) v

theorem hamming_toSpec {n : Nat} (a b : Cell n) :
    hamming a b = BitSpace.hamming (Runtime.toSpec a) (Runtime.toSpec b) :=
  rfl

@[simp] theorem toSpec_flipSequence {n : Nat}
    (js : List (Slot n)) (v : Cell n) :
    Runtime.toSpec (flipSequence js v) =
      BitSpace.flipSequence js (Runtime.toSpec v) := by
  induction js generalizing v with
  | nil =>
      rfl
  | cons j rest ih =>
      change Runtime.toSpec (flipSequence rest (flip j v)) =
        BitSpace.flipSequence rest (BitSpace.flip j (Runtime.toSpec v))
      rw [ih (flip j v), Runtime.toSpec_flip]

theorem hamming_self {n : Nat} (v : Cell n) :
    hamming v v = 0 := by
  simpa [hamming] using BitSpace.hamming_self (Runtime.toSpec v)

theorem hamming_triangle {n : Nat} (a b c : Cell n) :
    hamming a c ≤ hamming a b + hamming b c := by
  exact BitSpace.hamming_triangle (Runtime.toSpec a) (Runtime.toSpec b)
    (Runtime.toSpec c)

theorem hamming_flip_le_one {n : Nat} (j : Slot n) (v : Cell n) :
    hamming v (flip j v) ≤ 1 := by
  simpa [hamming, Runtime.toSpec_flip] using
    BitSpace.hamming_flip_le_one j (Runtime.toSpec v)

theorem hamming_flipSequence_le_length {n : Nat}
    (js : List (Slot n)) (v : Cell n) :
    hamming v (flipSequence js v) ≤ js.length := by
  simpa [hamming, toSpec_flipSequence] using
    BitSpace.hamming_flipSequence_le_length js (Runtime.toSpec v)

theorem core_mono {n k l : Nat} {D : Set (Cell n)}
    (hkl : k ≤ l) :
    core l D ⊆ core k D := by
  intro x hx
  exact ⟨hx.1, fun y hy => hx.2 y (Nat.le_trans hy hkl)⟩

theorem core_contains_hamming {n k : Nat} {D : Set (Cell n)}
    {x y : Cell n} (hx : core k D x) (hy : hamming x y ≤ k) :
    D y :=
  hx.2 y hy

theorem core_contains_flipSequence {n k : Nat} {D : Set (Cell n)}
    {x : Cell n} (hx : core k D x) {js : List (Slot n)}
    (hlen : js.length ≤ k) :
    D (flipSequence js x) :=
  hx.2 (flipSequence js x)
    (Nat.le_trans (hamming_flipSequence_le_length js x) hlen)

theorem boundary_iff_flip_escape {n : Nat} (D : Set (Cell n))
    (x : Cell n) :
    boundary D x ↔ D x ∧ ∃ j : Slot n, ¬ D (flip j x) :=
  Iff.rfl

theorem boundary_subset {n : Nat} (D : Set (Cell n)) :
    boundary D ⊆ D := by
  intro x hx
  exact hx.1

theorem core_summary (n k : Nat) (D : Set (Cell n)) :
    (∀ l, k ≤ l → core l D ⊆ core k D)
    ∧ (∀ x y, core k D x → hamming x y ≤ k → D y)
    ∧ (∀ x js, core k D x → js.length ≤ k → D (flipSequence js x))
    ∧ boundary D ⊆ D :=
  ⟨fun _ h => core_mono h, fun _ _ => core_contains_hamming,
   fun _ _ hx hlen => core_contains_flipSequence hx hlen, boundary_subset D⟩

end SSBX.Foundation.Wen.Layered.Runtime
