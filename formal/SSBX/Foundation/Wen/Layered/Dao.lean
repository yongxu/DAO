/-
# Wen.Layered.Dao -- Dao regions and observability
-/

import SSBX.Foundation.Wen.Layered.Flip

namespace SSBX.Foundation.Wen.Layered

namespace BitSpace

/-- A dependent Dao-region specification for `BitSpace (2*n)`: the outer gate
selects visible outer states; each visible outer state owns an inner region. -/
structure DaoFamily (n : Nat) where
  outer : Set (BitSpace n)
  inner : (o : BitSpace n) → outer o → Set (BitSpace n)

namespace DaoFamily

def region {n : Nat} (D : DaoFamily n) : Set (BitSpace (2 * n)) :=
  fun v =>
    ∃ h : D.outer (BitSpace.outer v),
      D.inner (BitSpace.outer v) h (BitSpace.inner v)

def observable {n : Nat} (D : DaoFamily n) : Set (BitSpace (2 * n)) :=
  fun v => D.outer (BitSpace.outer v)

def boxtimes {n : Nat} (D : DaoFamily n) : Set (BitSpace (2 * n)) :=
  fun v => ¬ observable D v

theorem region_subset_observable {n : Nat} (D : DaoFamily n) :
    ∀ v : BitSpace (2 * n), region D v → observable D v := by
  intro v hv
  rcases hv with ⟨h, _⟩
  exact h

theorem boxtimes_iff_not_observable {n : Nat} (D : DaoFamily n)
    (v : BitSpace (2 * n)) :
    boxtimes D v ↔ ¬ observable D v :=
  Iff.rfl

theorem not_boxtimes_of_region {n : Nat} (D : DaoFamily n)
    {v : BitSpace (2 * n)} (hv : region D v) :
    ¬ boxtimes D v := by
  intro hb
  exact hb (region_subset_observable D v hv)

end DaoFamily

end BitSpace

end SSBX.Foundation.Wen.Layered
