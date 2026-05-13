/-
# Wen.Layered.Runtime.Rescue -- runtime collapse and rescue facts
-/

import SSBX.Foundation.Wen.Layered.Runtime.Core
import SSBX.Foundation.Wen.Layered.Rescue

namespace SSBX.Foundation.Wen.Layered.Runtime

def innerOnly {n : Nat} (js : List (Slot n)) (v : Cell (2 * n)) :
    Cell (2 * n) :=
  js.foldl (fun acc j => flipInner j acc) v

@[simp] theorem toSpec_innerOnly {n : Nat}
    (js : List (Slot n)) (v : Cell (2 * n)) :
    Runtime.toSpec (innerOnly js v) =
      BitSpace.innerOnly js (Runtime.toSpec v) := by
  induction js generalizing v with
  | nil =>
      rfl
  | cons j rest ih =>
      change Runtime.toSpec (innerOnly rest (flipInner j v)) =
        BitSpace.innerOnly rest (BitSpace.flipInner j (Runtime.toSpec v))
      rw [ih (flipInner j v), Runtime.toSpec_flipInner]

theorem outer_innerOnly {n : Nat} (js : List (Slot n)) (v : Cell (2 * n)) :
    outer (innerOnly js v) = outer v := by
  induction js generalizing v with
  | nil =>
      rfl
  | cons j rest ih =>
      change outer (innerOnly rest (flipInner j v)) = outer v
      rw [ih (flipInner j v), outer_flipInner]

theorem boxtimes_innerOnly {n : Nat} (D : DaoFamily n)
    (js : List (Slot n)) {v : Cell (2 * n)}
    (hv : DaoFamily.boxtimes D v) :
    DaoFamily.boxtimes D (innerOnly js v) := by
  simpa [DaoFamily.boxtimes, toSpec_innerOnly] using
    BitSpace.boxtimes_innerOnly (DaoFamily.toSpec D) js
      (v := Runtime.toSpec v) hv

theorem no_inner_only_rescue_to_observable {n : Nat} (D : DaoFamily n)
    (js : List (Slot n)) {v u : Cell (2 * n)}
    (hv : DaoFamily.boxtimes D v)
    (hu : DaoFamily.observable D u) :
    innerOnly js v ≠ u := by
  intro h
  subst u
  exact boxtimes_innerOnly D js hv hu

def rescueCandidateWithin {n : Nat} (D : DaoFamily n)
    (v : Cell (2 * n)) (L : Nat) : Prop :=
  ∃ u : Cell (2 * n),
    DaoFamily.region D u
      ∧ hamming (outer v) (outer u) + hamming (inner v) (inner u) ≤ L

def rescueDistanceWitness {n : Nat} (D : DaoFamily n)
    (v : Cell (2 * n)) (L : Nat) : Prop :=
  ∃ u : Cell (2 * n),
    DaoFamily.region D u
      ∧ hamming (outer v) (outer u) + hamming (inner v) (inner u) ≤ L

theorem rescue_distance_characterization {n : Nat} (D : DaoFamily n)
    (v : Cell (2 * n)) (L : Nat) :
    rescueCandidateWithin D v L ↔ rescueDistanceWitness D v L :=
  Iff.rfl

theorem rescue_summary (n : Nat) (D : DaoFamily n) :
    (∀ js (v : Cell (2 * n)), outer (innerOnly js v) = outer v)
    ∧ (∀ js (v : Cell (2 * n)),
        DaoFamily.boxtimes D v → DaoFamily.boxtimes D (innerOnly js v))
    ∧ (∀ js (v u : Cell (2 * n)),
        DaoFamily.boxtimes D v → DaoFamily.observable D u →
          innerOnly js v ≠ u) :=
  ⟨outer_innerOnly, fun js _ hv => boxtimes_innerOnly D js hv,
   fun js _ _ hv hu => no_inner_only_rescue_to_observable D js hv hu⟩

end SSBX.Foundation.Wen.Layered.Runtime
