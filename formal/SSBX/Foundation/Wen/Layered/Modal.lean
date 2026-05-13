/-
# Wen.Layered.Modal -- classical four-way modal judgment
-/

import SSBX.Foundation.Wen.Layered.Dao

namespace SSBX.Foundation.Wen.Layered

namespace BitSpace

namespace DaoFamily

def necessaryTrue {n : Nat} (D : DaoFamily n)
    (R : BitSpace (2 * n) → BitSpace (2 * n) → Prop)
    (v : BitSpace (2 * n)) : Prop :=
  observable D v ∧ ∀ u, R v u → region D u

def necessaryFalse {n : Nat} (D : DaoFamily n)
    (R : BitSpace (2 * n) → BitSpace (2 * n) → Prop)
    (v : BitSpace (2 * n)) : Prop :=
  observable D v ∧ ∀ u, R v u → ¬ region D u

def contingent {n : Nat} (D : DaoFamily n)
    (R : BitSpace (2 * n) → BitSpace (2 * n) → Prop)
    (v : BitSpace (2 * n)) : Prop :=
  observable D v ∧ ¬ necessaryTrue D R v ∧ ¬ necessaryFalse D R v

theorem modal_exhaustive {n : Nat} (D : DaoFamily n)
    (R : BitSpace (2 * n) → BitSpace (2 * n) → Prop)
    (v : BitSpace (2 * n)) :
    necessaryTrue D R v ∨ necessaryFalse D R v ∨ contingent D R v ∨ boxtimes D v := by
  by_cases hobs : observable D v
  · by_cases ht : necessaryTrue D R v
    · exact Or.inl ht
    · by_cases hf : necessaryFalse D R v
      · exact Or.inr (Or.inl hf)
      · exact Or.inr (Or.inr (Or.inl ⟨hobs, ht, hf⟩))
  · exact Or.inr (Or.inr (Or.inr hobs))

theorem necessaryTrue_not_necessaryFalse {n : Nat} (D : DaoFamily n)
    (R : BitSpace (2 * n) → BitSpace (2 * n) → Prop)
    (hrefl : ∀ v, R v v) (v : BitSpace (2 * n)) :
    necessaryTrue D R v → ¬ necessaryFalse D R v := by
  intro ht hf
  exact hf.2 v (hrefl v) (ht.2 v (hrefl v))

theorem contingent_not_necessaryTrue {n : Nat} (D : DaoFamily n)
    (R : BitSpace (2 * n) → BitSpace (2 * n) → Prop)
    (v : BitSpace (2 * n)) :
    contingent D R v → ¬ necessaryTrue D R v :=
  fun hc => hc.2.1

theorem contingent_not_necessaryFalse {n : Nat} (D : DaoFamily n)
    (R : BitSpace (2 * n) → BitSpace (2 * n) → Prop)
    (v : BitSpace (2 * n)) :
    contingent D R v → ¬ necessaryFalse D R v :=
  fun hc => hc.2.2

theorem necessaryTrue_not_contingent {n : Nat} (D : DaoFamily n)
    (R : BitSpace (2 * n) → BitSpace (2 * n) → Prop)
    (v : BitSpace (2 * n)) :
    necessaryTrue D R v → ¬ contingent D R v :=
  fun ht hc => hc.2.1 ht

theorem necessaryFalse_not_contingent {n : Nat} (D : DaoFamily n)
    (R : BitSpace (2 * n) → BitSpace (2 * n) → Prop)
    (v : BitSpace (2 * n)) :
    necessaryFalse D R v → ¬ contingent D R v :=
  fun hf hc => hc.2.2 hf

theorem boxtimes_not_observable {n : Nat} (D : DaoFamily n)
    {v : BitSpace (2 * n)} :
    boxtimes D v → ¬ observable D v :=
  id

theorem necessaryTrue_not_boxtimes {n : Nat} (D : DaoFamily n)
    (R : BitSpace (2 * n) → BitSpace (2 * n) → Prop)
    (v : BitSpace (2 * n)) :
    necessaryTrue D R v → ¬ boxtimes D v :=
  fun ht hb => hb ht.1

theorem necessaryFalse_not_boxtimes {n : Nat} (D : DaoFamily n)
    (R : BitSpace (2 * n) → BitSpace (2 * n) → Prop)
    (v : BitSpace (2 * n)) :
    necessaryFalse D R v → ¬ boxtimes D v :=
  fun hf hb => hb hf.1

theorem contingent_not_boxtimes {n : Nat} (D : DaoFamily n)
    (R : BitSpace (2 * n) → BitSpace (2 * n) → Prop)
    (v : BitSpace (2 * n)) :
    contingent D R v → ¬ boxtimes D v :=
  fun hc hb => hb hc.1

theorem modal_mutual_exclusion_summary {n : Nat} (D : DaoFamily n)
    (R : BitSpace (2 * n) → BitSpace (2 * n) → Prop)
    (hrefl : ∀ v, R v v) (v : BitSpace (2 * n)) :
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

end BitSpace

end SSBX.Foundation.Wen.Layered
