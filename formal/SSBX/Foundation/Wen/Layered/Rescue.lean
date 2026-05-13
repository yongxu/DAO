/-
# Wen.Layered.Rescue -- collapse and rescue facts
-/

import SSBX.Foundation.Wen.Layered.Core

namespace SSBX.Foundation.Wen.Layered

namespace BitSpace

def innerOnly {n : Nat} (js : List (Slot n)) (v : BitSpace (2 * n)) :
    BitSpace (2 * n) :=
  js.foldl (fun acc j => flipInner j acc) v

theorem outer_innerOnly {n : Nat} (js : List (Slot n)) (v : BitSpace (2 * n)) :
    outer (innerOnly js v) = outer v := by
  induction js generalizing v with
  | nil =>
      rfl
  | cons j rest ih =>
      unfold innerOnly
      simp [List.foldl_cons]
      change outer (innerOnly rest (flipInner j v)) = outer v
      rw [ih (flipInner j v), outer_flipInner]

theorem boxtimes_innerOnly {n : Nat} (D : DaoFamily n)
    (js : List (Slot n)) {v : BitSpace (2 * n)}
    (hv : DaoFamily.boxtimes D v) :
    DaoFamily.boxtimes D (innerOnly js v) := by
  intro hobs
  exact hv (by
    unfold DaoFamily.observable at hobs ⊢
    rwa [outer_innerOnly js v] at hobs)

theorem no_inner_only_rescue_to_observable {n : Nat} (D : DaoFamily n)
    (js : List (Slot n)) {v u : BitSpace (2 * n)}
    (hv : DaoFamily.boxtimes D v)
    (hu : DaoFamily.observable D u) :
    innerOnly js v ≠ u := by
  intro h
  subst u
  exact boxtimes_innerOnly D js hv hu

def rescueCandidateWithin {n : Nat} (D : DaoFamily n)
    (v : BitSpace (2 * n)) (L : Nat) : Prop :=
  ∃ u : BitSpace (2 * n),
    DaoFamily.region D u
      ∧ hamming (outer v) (outer u) + hamming (inner v) (inner u) ≤ L

def rescueDistanceWitness {n : Nat} (D : DaoFamily n)
    (v : BitSpace (2 * n)) (L : Nat) : Prop :=
  ∃ u : BitSpace (2 * n),
    DaoFamily.region D u
      ∧ hamming (outer v) (outer u) + hamming (inner v) (inner u) ≤ L

theorem rescue_distance_characterization {n : Nat} (D : DaoFamily n)
    (v : BitSpace (2 * n)) (L : Nat) :
    rescueCandidateWithin D v L ↔ rescueDistanceWitness D v L :=
  Iff.rfl

theorem rescue_summary (n : Nat) (D : DaoFamily n) :
    (∀ js (v : BitSpace (2 * n)), outer (innerOnly js v) = outer v)
    ∧ (∀ js (v : BitSpace (2 * n)),
        DaoFamily.boxtimes D v → DaoFamily.boxtimes D (innerOnly js v))
    ∧ (∀ js (v u : BitSpace (2 * n)),
        DaoFamily.boxtimes D v → DaoFamily.observable D u →
          innerOnly js v ≠ u) :=
  ⟨outer_innerOnly, fun js _ hv => boxtimes_innerOnly D js hv,
   fun js _ _ hv hu => no_inner_only_rescue_to_observable D js hv hu⟩

end BitSpace

end SSBX.Foundation.Wen.Layered
