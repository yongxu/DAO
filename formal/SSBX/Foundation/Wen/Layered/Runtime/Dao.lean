/-
# Wen.Layered.Runtime.Dao -- runtime Dao regions and observability
-/

import SSBX.Foundation.Wen.Layered.Runtime.Flip
import SSBX.Foundation.Wen.Layered.Dao

namespace SSBX.Foundation.Wen.Layered.Runtime

/-- Runtime Dao-region specification over `Cell`.  The outer gate selects
visible outer cells; each visible outer cell owns an inner region. -/
structure DaoFamily (n : Nat) where
  outer : Set (Cell n)
  inner : (o : Cell n) → outer o → Set (Cell n)

namespace DaoFamily

/-- Push a runtime Dao-family to the specification carrier by decoding spec
points through `ofSpec`. -/
def toSpec {n : Nat} (D : DaoFamily n) : BitSpace.DaoFamily n where
  outer o := D.outer (Runtime.ofSpec o)
  inner o ho i := D.inner (Runtime.ofSpec o) ho (Runtime.ofSpec i)

/-- Pull a specification Dao-family back along `toSpec`. -/
def ofSpec {n : Nat} (D : BitSpace.DaoFamily n) : DaoFamily n where
  outer o := D.outer (Runtime.toSpec o)
  inner o ho i := D.inner (Runtime.toSpec o) ho (Runtime.toSpec i)

def region {n : Nat} (D : DaoFamily n) : Set (Cell (2 * n)) :=
  fun v => BitSpace.DaoFamily.region (toSpec D) (Runtime.toSpec v)

def observable {n : Nat} (D : DaoFamily n) : Set (Cell (2 * n)) :=
  fun v => BitSpace.DaoFamily.observable (toSpec D) (Runtime.toSpec v)

def boxtimes {n : Nat} (D : DaoFamily n) : Set (Cell (2 * n)) :=
  fun v => BitSpace.DaoFamily.boxtimes (toSpec D) (Runtime.toSpec v)

theorem region_iff_toSpec {n : Nat} (D : DaoFamily n)
    (v : Cell (2 * n)) :
    region D v ↔ BitSpace.DaoFamily.region (toSpec D) (Runtime.toSpec v) :=
  Iff.rfl

theorem observable_iff_toSpec {n : Nat} (D : DaoFamily n)
    (v : Cell (2 * n)) :
    observable D v ↔
      BitSpace.DaoFamily.observable (toSpec D) (Runtime.toSpec v) :=
  Iff.rfl

theorem boxtimes_iff_toSpec {n : Nat} (D : DaoFamily n)
    (v : Cell (2 * n)) :
    boxtimes D v ↔ BitSpace.DaoFamily.boxtimes (toSpec D) (Runtime.toSpec v) :=
  Iff.rfl

theorem region_subset_observable {n : Nat} (D : DaoFamily n) :
    ∀ v : Cell (2 * n), region D v → observable D v := by
  intro v hv
  exact BitSpace.DaoFamily.region_subset_observable (toSpec D) (Runtime.toSpec v) hv

theorem boxtimes_iff_not_observable {n : Nat} (D : DaoFamily n)
    (v : Cell (2 * n)) :
    boxtimes D v ↔ ¬ observable D v :=
  Iff.rfl

theorem not_boxtimes_of_region {n : Nat} (D : DaoFamily n)
    {v : Cell (2 * n)} (hv : region D v) :
    ¬ boxtimes D v := by
  exact BitSpace.DaoFamily.not_boxtimes_of_region (toSpec D) hv

end DaoFamily

end SSBX.Foundation.Wen.Layered.Runtime
