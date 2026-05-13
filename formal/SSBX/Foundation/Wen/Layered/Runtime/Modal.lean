/-
# Wen.Layered.Runtime.Modal -- runtime modal judgment mirrors
-/

import SSBX.Foundation.Wen.Layered.Runtime.Dao
import SSBX.Foundation.Wen.Layered.Modal

namespace SSBX.Foundation.Wen.Layered.Runtime

/-- Push a runtime relation to the specification carrier by decoding both
arguments through `ofSpec`. -/
def relToSpec {n : Nat} (R : Cell n → Cell n → Prop) :
    BitSpace n → BitSpace n → Prop :=
  fun v u => R (Runtime.ofSpec v) (Runtime.ofSpec u)

namespace DaoFamily

def necessaryTrue {n : Nat} (D : DaoFamily n)
    (R : Cell (2 * n) → Cell (2 * n) → Prop)
    (v : Cell (2 * n)) : Prop :=
  BitSpace.DaoFamily.necessaryTrue (toSpec D) (relToSpec R) (Runtime.toSpec v)

def necessaryFalse {n : Nat} (D : DaoFamily n)
    (R : Cell (2 * n) → Cell (2 * n) → Prop)
    (v : Cell (2 * n)) : Prop :=
  BitSpace.DaoFamily.necessaryFalse (toSpec D) (relToSpec R) (Runtime.toSpec v)

def contingent {n : Nat} (D : DaoFamily n)
    (R : Cell (2 * n) → Cell (2 * n) → Prop)
    (v : Cell (2 * n)) : Prop :=
  BitSpace.DaoFamily.contingent (toSpec D) (relToSpec R) (Runtime.toSpec v)

theorem necessaryTrue_iff_toSpec {n : Nat} (D : DaoFamily n)
    (R : Cell (2 * n) → Cell (2 * n) → Prop)
    (v : Cell (2 * n)) :
    necessaryTrue D R v ↔
      BitSpace.DaoFamily.necessaryTrue (toSpec D) (relToSpec R)
        (Runtime.toSpec v) :=
  Iff.rfl

theorem necessaryFalse_iff_toSpec {n : Nat} (D : DaoFamily n)
    (R : Cell (2 * n) → Cell (2 * n) → Prop)
    (v : Cell (2 * n)) :
    necessaryFalse D R v ↔
      BitSpace.DaoFamily.necessaryFalse (toSpec D) (relToSpec R)
        (Runtime.toSpec v) :=
  Iff.rfl

theorem contingent_iff_toSpec {n : Nat} (D : DaoFamily n)
    (R : Cell (2 * n) → Cell (2 * n) → Prop)
    (v : Cell (2 * n)) :
    contingent D R v ↔
      BitSpace.DaoFamily.contingent (toSpec D) (relToSpec R)
        (Runtime.toSpec v) :=
  Iff.rfl

theorem modal_exhaustive {n : Nat} (D : DaoFamily n)
    (R : Cell (2 * n) → Cell (2 * n) → Prop)
    (v : Cell (2 * n)) :
    necessaryTrue D R v ∨ necessaryFalse D R v ∨ contingent D R v ∨ boxtimes D v := by
  exact BitSpace.DaoFamily.modal_exhaustive (toSpec D) (relToSpec R)
    (Runtime.toSpec v)

theorem necessaryTrue_not_necessaryFalse {n : Nat} (D : DaoFamily n)
    (R : Cell (2 * n) → Cell (2 * n) → Prop)
    (hrefl : ∀ v, R v v) (v : Cell (2 * n)) :
    necessaryTrue D R v → ¬ necessaryFalse D R v := by
  have hsrefl : ∀ v, relToSpec R v v := fun v => hrefl (Runtime.ofSpec v)
  exact BitSpace.DaoFamily.necessaryTrue_not_necessaryFalse
    (toSpec D) (relToSpec R) hsrefl (Runtime.toSpec v)

theorem contingent_not_necessaryTrue {n : Nat} (D : DaoFamily n)
    (R : Cell (2 * n) → Cell (2 * n) → Prop)
    (v : Cell (2 * n)) :
    contingent D R v → ¬ necessaryTrue D R v :=
  BitSpace.DaoFamily.contingent_not_necessaryTrue
    (toSpec D) (relToSpec R) (Runtime.toSpec v)

theorem contingent_not_necessaryFalse {n : Nat} (D : DaoFamily n)
    (R : Cell (2 * n) → Cell (2 * n) → Prop)
    (v : Cell (2 * n)) :
    contingent D R v → ¬ necessaryFalse D R v :=
  BitSpace.DaoFamily.contingent_not_necessaryFalse
    (toSpec D) (relToSpec R) (Runtime.toSpec v)

theorem necessaryTrue_not_contingent {n : Nat} (D : DaoFamily n)
    (R : Cell (2 * n) → Cell (2 * n) → Prop)
    (v : Cell (2 * n)) :
    necessaryTrue D R v → ¬ contingent D R v :=
  BitSpace.DaoFamily.necessaryTrue_not_contingent
    (toSpec D) (relToSpec R) (Runtime.toSpec v)

theorem necessaryFalse_not_contingent {n : Nat} (D : DaoFamily n)
    (R : Cell (2 * n) → Cell (2 * n) → Prop)
    (v : Cell (2 * n)) :
    necessaryFalse D R v → ¬ contingent D R v :=
  BitSpace.DaoFamily.necessaryFalse_not_contingent
    (toSpec D) (relToSpec R) (Runtime.toSpec v)

theorem boxtimes_not_observable {n : Nat} (D : DaoFamily n)
    {v : Cell (2 * n)} :
    boxtimes D v → ¬ observable D v :=
  id

theorem necessaryTrue_not_boxtimes {n : Nat} (D : DaoFamily n)
    (R : Cell (2 * n) → Cell (2 * n) → Prop)
    (v : Cell (2 * n)) :
    necessaryTrue D R v → ¬ boxtimes D v :=
  BitSpace.DaoFamily.necessaryTrue_not_boxtimes
    (toSpec D) (relToSpec R) (Runtime.toSpec v)

theorem necessaryFalse_not_boxtimes {n : Nat} (D : DaoFamily n)
    (R : Cell (2 * n) → Cell (2 * n) → Prop)
    (v : Cell (2 * n)) :
    necessaryFalse D R v → ¬ boxtimes D v :=
  BitSpace.DaoFamily.necessaryFalse_not_boxtimes
    (toSpec D) (relToSpec R) (Runtime.toSpec v)

theorem contingent_not_boxtimes {n : Nat} (D : DaoFamily n)
    (R : Cell (2 * n) → Cell (2 * n) → Prop)
    (v : Cell (2 * n)) :
    contingent D R v → ¬ boxtimes D v :=
  BitSpace.DaoFamily.contingent_not_boxtimes
    (toSpec D) (relToSpec R) (Runtime.toSpec v)

theorem modal_mutual_exclusion_summary {n : Nat} (D : DaoFamily n)
    (R : Cell (2 * n) → Cell (2 * n) → Prop)
    (hrefl : ∀ v, R v v) (v : Cell (2 * n)) :
    (necessaryTrue D R v → ¬ necessaryFalse D R v)
    ∧ (necessaryTrue D R v → ¬ contingent D R v)
    ∧ (necessaryFalse D R v → ¬ contingent D R v)
    ∧ (necessaryTrue D R v → ¬ boxtimes D v)
    ∧ (necessaryFalse D R v → ¬ boxtimes D v)
    ∧ (contingent D R v → ¬ boxtimes D v) :=
  ⟨necessaryTrue_not_necessaryFalse D R hrefl v,
   necessaryTrue_not_contingent D R v,
   necessaryFalse_not_contingent D R v,
   necessaryTrue_not_boxtimes D R v,
   necessaryFalse_not_boxtimes D R v,
   contingent_not_boxtimes D R v⟩

end DaoFamily

end SSBX.Foundation.Wen.Layered.Runtime
