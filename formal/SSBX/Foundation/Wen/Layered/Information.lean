/-
# Wen.Layered.Information -- invariant queries and derivability
-/

import SSBX.Foundation.Wen.Layered.BitSpace
import Mathlib.Data.Finset.Card

namespace SSBX.Foundation.Wen.Layered

namespace BitSpace

def andBit {n : Nat} (q x : BitSpace n) (i : Slot n) : Bool :=
  q i && x i

/-- Generic F2 dot product, implemented as xor-fold over all finite slots. -/
noncomputable def linearEval {n : Nat} (q x : BitSpace n) : Bool :=
  (Finset.univ.toList.map (fun i : Slot n => andBit q x i)).foldl Bool.xor false

/-- A finite bit-space subgroup, represented by its carrier predicate. -/
structure Subgroup (n : Nat) where
  carrier : BitSpace n → Prop
  zero_mem : carrier zero
  xor_mem : ∀ {a b : BitSpace n}, carrier a → carrier b → carrier (xor a b)

def isInvariant {n : Nat} (H : Subgroup n)
    (eval : BitSpace n → Bool) : Prop :=
  ∀ x g : BitSpace n, H.carrier g → eval (xor x g) = eval x

def orbit {n : Nat} (H : Subgroup n) (x y : BitSpace n) : Prop :=
  ∃ g : BitSpace n, H.carrier g ∧ y = xor x g

theorem eval_constant_on_orbit {n : Nat} {H : Subgroup n}
    {eval : BitSpace n → Bool} {x y : BitSpace n}
    (hinv : isInvariant H eval) (hy : orbit H x y) :
    eval y = eval x := by
  rcases hy with ⟨g, hg, rfl⟩
  exact hinv x g hg

theorem info_preservation {n : Nat}
    (eval : BitSpace n → Bool) (H : Subgroup n)
    (root y : BitSpace n)
    (hinv : isInvariant H eval) (hy : orbit H root y) :
    eval y = eval root :=
  eval_constant_on_orbit hinv hy

def annihilates {n : Nat} (H : Subgroup n) (eval : BitSpace n → Bool) : Prop :=
  isInvariant H eval

def inAnnihilator {n : Nat} (H : Subgroup n) (eval : BitSpace n → Bool) : Prop :=
  annihilates H eval

def orbitDerives {n : Nat} (H : Subgroup n)
    (eval : BitSpace n → Bool) (root : BitSpace n) : Prop :=
  ∀ y : BitSpace n, orbit H root y → eval y = eval root

theorem isInvariant_iff_annihilates {n : Nat}
    (H : Subgroup n) (eval : BitSpace n → Bool) :
    isInvariant H eval ↔ annihilates H eval :=
  Iff.rfl

theorem invariant_iff_all_orbits_derive {n : Nat}
    (H : Subgroup n) (eval : BitSpace n → Bool) :
    isInvariant H eval ↔ ∀ root : BitSpace n, orbitDerives H eval root := by
  constructor
  · intro h root y hy
    exact eval_constant_on_orbit h hy
  · intro h x g hg
    exact h x (xor x g) ⟨g, hg, rfl⟩

theorem derivable_iff_invariant {n : Nat}
    (H : Subgroup n) (eval : BitSpace n → Bool) :
    (∀ root : BitSpace n, orbitDerives H eval root) ↔ isInvariant H eval :=
  (invariant_iff_all_orbits_derive H eval).symm

def spanOneCarrier {n : Nat} (m g : BitSpace n) : Prop :=
  g = zero ∨ g = m

def spanOne {n : Nat} (m : BitSpace n) : Subgroup n where
  carrier := spanOneCarrier m
  zero_mem := Or.inl rfl
  xor_mem := by
    intro a b ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rw [xor_zero_left]
      exact Or.inl rfl
    · rw [xor_zero_left]
      exact Or.inr rfl
    · rw [xor_zero_right]
      exact Or.inr rfl
    · rw [xor_self]
      exact Or.inl rfl

theorem information_summary (n : Nat) :
    (∀ H eval, isInvariant (n := n) H eval ↔ annihilates H eval)
    ∧ (∀ H eval,
        (∀ root : BitSpace n, orbitDerives H eval root) ↔ isInvariant H eval) :=
  ⟨isInvariant_iff_annihilates, derivable_iff_invariant⟩

end BitSpace

end SSBX.Foundation.Wen.Layered
