/-
# Wen.Layered.Runtime.Information -- BitVec runtime information mirrors
-/

import SSBX.Foundation.Wen.Layered.Information
import SSBX.Foundation.Wen.Layered.Runtime.Cell

namespace SSBX.Foundation.Wen.Layered.Runtime

/-- Runtime subgroup, carried by a spec-level bit-space subgroup and read on
`Cell n` through `toSpec`. -/
structure Subgroup (n : Nat) where
  spec : BitSpace.Subgroup n

namespace Subgroup

def carrier {n : Nat} (H : Subgroup n) (g : Cell n) : Prop :=
  H.spec.carrier (toSpec g)

theorem zero_mem {n : Nat} (H : Subgroup n) :
    H.carrier (ofSpec (BitSpace.zero : BitSpace n)) := by
  simpa [carrier] using H.spec.zero_mem

theorem xor_mem {n : Nat} (H : Subgroup n) {a b : Cell n}
    (ha : H.carrier a) (hb : H.carrier b) :
    H.carrier (ofSpec (BitSpace.xor (toSpec a) (toSpec b))) := by
  simpa [carrier] using H.spec.xor_mem ha hb

def fromSpec {n : Nat} (H : BitSpace.Subgroup n) : Subgroup n where
  spec := H

end Subgroup

def orbit {n : Nat} (H : Subgroup n) (x y : Cell n) : Prop :=
  ∃ g : Cell n, H.carrier g ∧ toSpec y = BitSpace.xor (toSpec x) (toSpec g)

def isInvariant {n : Nat} (H : Subgroup n) (eval : Cell n → Bool) : Prop :=
  ∀ x g : Cell n, H.carrier g →
    ∀ y : Cell n, toSpec y = BitSpace.xor (toSpec x) (toSpec g) →
      eval y = eval x

theorem eval_constant_on_orbit {n : Nat} {H : Subgroup n}
    {eval : Cell n → Bool} {x y : Cell n}
    (hinv : isInvariant H eval) (hy : orbit H x y) :
    eval y = eval x := by
  rcases hy with ⟨g, hg, hspec⟩
  exact hinv x g hg y hspec

theorem info_preservation {n : Nat}
    (eval : Cell n → Bool) (H : Subgroup n)
    (root y : Cell n)
    (hinv : isInvariant H eval) (hy : orbit H root y) :
    eval y = eval root :=
  eval_constant_on_orbit hinv hy

def annihilates {n : Nat} (H : Subgroup n) (eval : Cell n → Bool) : Prop :=
  isInvariant H eval

def inAnnihilator {n : Nat} (H : Subgroup n) (eval : Cell n → Bool) : Prop :=
  annihilates H eval

def orbitDerives {n : Nat} (H : Subgroup n)
    (eval : Cell n → Bool) (root : Cell n) : Prop :=
  ∀ y : Cell n, orbit H root y → eval y = eval root

theorem isInvariant_iff_annihilates {n : Nat}
    (H : Subgroup n) (eval : Cell n → Bool) :
    isInvariant H eval ↔ annihilates H eval :=
  Iff.rfl

theorem invariant_iff_all_orbits_derive {n : Nat}
    (H : Subgroup n) (eval : Cell n → Bool) :
    isInvariant H eval ↔ ∀ root : Cell n, orbitDerives H eval root := by
  constructor
  · intro h root y hy
    exact eval_constant_on_orbit h hy
  · intro h x g hg y hspec
    exact h x y ⟨g, hg, hspec⟩

theorem derivable_iff_invariant {n : Nat}
    (H : Subgroup n) (eval : Cell n → Bool) :
    (∀ root : Cell n, orbitDerives H eval root) ↔ isInvariant H eval :=
  (invariant_iff_all_orbits_derive H eval).symm

def liftEval {n : Nat} (eval : BitSpace n → Bool) : Cell n → Bool :=
  fun x => eval (toSpec x)

theorem isInvariant_of_spec {n : Nat} {H : Subgroup n}
    {eval : BitSpace n → Bool}
    (hinv : BitSpace.isInvariant H.spec eval) :
    isInvariant H (liftEval eval) := by
  intro x g hg y hspec
  unfold liftEval
  rw [hspec]
  exact hinv (toSpec x) (toSpec g) hg

theorem information_summary (n : Nat) :
    (∀ H eval, isInvariant (n := n) H eval ↔ annihilates H eval)
    ∧ (∀ H eval,
        (∀ root : Cell n, orbitDerives H eval root) ↔ isInvariant H eval) :=
  ⟨isInvariant_iff_annihilates, derivable_iff_invariant⟩

end SSBX.Foundation.Wen.Layered.Runtime
