/-
# Wen.Layered.Core -- Hamming core and boundary
-/

import SSBX.Foundation.Wen.Layered.Modal
import Mathlib.Data.Finset.Card

namespace SSBX.Foundation.Wen.Layered

namespace BitSpace

/-- Hamming distance on finite bit spaces. -/
def hamming {n : Nat} (a b : BitSpace n) : Nat :=
  (Finset.univ.filter fun i => a i != b i).card

def core {n : Nat} (k : Nat) (D : Set (BitSpace n)) : Set (BitSpace n) :=
  fun x => D x ∧ ∀ y : BitSpace n, hamming x y ≤ k → D y

def boundary {n : Nat} (D : Set (BitSpace n)) : Set (BitSpace n) :=
  fun x => D x ∧ ∃ j : Slot n, ¬ D (flip j x)

def flipSequence {n : Nat} (js : List (Slot n)) (v : BitSpace n) :
    BitSpace n :=
  js.foldl (fun acc j => flip j acc) v

theorem hamming_self {n : Nat} (v : BitSpace n) :
    hamming v v = 0 := by
  simp [hamming]

theorem hamming_triangle {n : Nat} (a b c : BitSpace n) :
    hamming a c ≤ hamming a b + hamming b c := by
  unfold hamming
  let ac : Finset (Slot n) := Finset.univ.filter fun i => a i != c i
  let ab : Finset (Slot n) := Finset.univ.filter fun i => a i != b i
  let bc : Finset (Slot n) := Finset.univ.filter fun i => b i != c i
  have hsubset : ac ⊆ ab ∪ bc := by
    intro i hi
    simp [ac, ab, bc] at hi ⊢
    cases ha : a i <;> cases hb : b i <;> cases hc : c i <;>
      simp [ha, hc] at hi ⊢
  have hcard : ac.card ≤ (ab ∪ bc).card := Finset.card_le_card hsubset
  have hunion : (ab ∪ bc).card ≤ ab.card + bc.card := Finset.card_union_le ab bc
  exact Nat.le_trans hcard hunion

theorem hamming_flip_le_one {n : Nat} (j : Slot n) (v : BitSpace n) :
    hamming v (flip j v) ≤ 1 := by
  unfold hamming flip
  let changed : Finset (Slot n) := Finset.univ.filter fun i =>
    v i != if i = j then !v i else v i
  have hsubset : changed ⊆ ({j} : Finset (Slot n)) := by
    intro i hi
    simp [changed] at hi ⊢
    by_cases hij : i = j
    · exact hij
    · simp [hij] at hi
  have hcard : changed.card ≤ ({j} : Finset (Slot n)).card :=
    Finset.card_le_card hsubset
  simpa [changed] using hcard

theorem hamming_flipSequence_le_length {n : Nat}
    (js : List (Slot n)) (v : BitSpace n) :
    hamming v (flipSequence js v) ≤ js.length := by
  induction js generalizing v with
  | nil =>
      simp [flipSequence, hamming_self]
  | cons j rest ih =>
      change hamming v (flipSequence rest (flip j v)) ≤ (j :: rest).length
      have htri := hamming_triangle v (flip j v) (flipSequence rest (flip j v))
      have hstep := hamming_flip_le_one j v
      have hrest := ih (flip j v)
      have hsum :
          hamming v (flip j v) +
              hamming (flip j v) (flipSequence rest (flip j v)) ≤
            1 + rest.length :=
        Nat.add_le_add hstep hrest
      exact Nat.le_trans htri (by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsum)

theorem core_mono {n k l : Nat} {D : Set (BitSpace n)}
    (hkl : k ≤ l) :
    core l D ⊆ core k D := by
  intro x hx
  exact ⟨hx.1, fun y hy => hx.2 y (Nat.le_trans hy hkl)⟩

theorem core_contains_hamming {n k : Nat} {D : Set (BitSpace n)}
    {x y : BitSpace n} (hx : core k D x) (hy : hamming x y ≤ k) :
    D y :=
  hx.2 y hy

theorem core_contains_flipSequence {n k : Nat} {D : Set (BitSpace n)}
    {x : BitSpace n} (hx : core k D x) {js : List (Slot n)}
    (hlen : js.length ≤ k) :
    D (flipSequence js x) :=
  hx.2 (flipSequence js x)
    (Nat.le_trans (hamming_flipSequence_le_length js x) hlen)

theorem boundary_iff_flip_escape {n : Nat} (D : Set (BitSpace n))
    (x : BitSpace n) :
    boundary D x ↔ D x ∧ ∃ j : Slot n, ¬ D (flip j x) :=
  Iff.rfl

theorem boundary_subset {n : Nat} (D : Set (BitSpace n)) :
    boundary D ⊆ D := by
  intro x hx
  exact hx.1

theorem core_summary (n k : Nat) (D : Set (BitSpace n)) :
    (∀ l, k ≤ l → core l D ⊆ core k D)
    ∧ (∀ x y, core k D x → hamming x y ≤ k → D y)
    ∧ (∀ x js, core k D x → js.length ≤ k → D (flipSequence js x))
    ∧ boundary D ⊆ D :=
  ⟨fun _ h => core_mono h, fun _ _ => core_contains_hamming,
   fun _ _ hx hlen => core_contains_flipSequence hx hlen, boundary_subset D⟩

end BitSpace

end SSBX.Foundation.Wen.Layered
