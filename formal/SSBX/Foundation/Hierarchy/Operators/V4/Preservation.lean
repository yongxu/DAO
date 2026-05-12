/-
# Operators · V4.Preservation -- registry-level preservation hierarchy

These are typed markers for the V4 atlas.  They are not global semantic
proofs for every mathematical domain.
-/

import SSBX.Foundation.Hierarchy.Operators.V4.Core

namespace SSBX.Foundation.Hierarchy.Operators

namespace V4

inductive PreservationLevel where
  | setBijection
  | algebraHom
  | categoricalFunctor
  | implicationTruth
  deriving DecidableEq, Repr

/-- Registry-level preservation marker.

`implicationTruth` means the classical-logic implication slice where
contraposition preserves truth.  It is intentionally not a global truth claim
for arbitrary logical systems. -/
def preservesAt : V4 → PreservationLevel → Bool
  | _, .setBijection => true
  | .dao, .algebraHom => true
  | .cuo, .algebraHom => false
  | .zong, .algebraHom => false
  | .cuoZong, .algebraHom => true
  | _, .categoricalFunctor => true
  | .dao, .implicationTruth => true
  | .cuo, .implicationTruth => false
  | .zong, .implicationTruth => false
  | .cuoZong, .implicationTruth => true

def contentAxis (g : V4) : Prop :=
  g = .dao ∨ g = .cuo

def frameAxis (g : V4) : Prop :=
  g = .dao ∨ g = .zong

/-- The privileged nontrivial structure-preserving subgroup `{dao, cuoZong}`. -/
def structurePreservingAxis (g : V4) : Prop :=
  g = .dao ∨ g = .cuoZong

theorem contentAxis_closed
    {a b : V4} (ha : contentAxis a) (hb : contentAxis b) :
    contentAxis (compose a b) := by
  cases a <;> cases b <;>
    simp [contentAxis, compose, ofBits, contentBit, frameBit] at ha hb ⊢

theorem frameAxis_closed
    {a b : V4} (ha : frameAxis a) (hb : frameAxis b) :
    frameAxis (compose a b) := by
  cases a <;> cases b <;>
    simp [frameAxis, compose, ofBits, contentBit, frameBit] at ha hb ⊢

theorem structurePreservingAxis_closed
    {a b : V4} (ha : structurePreservingAxis a)
    (hb : structurePreservingAxis b) :
    structurePreservingAxis (compose a b) := by
  cases a <;> cases b <;>
    simp [structurePreservingAxis, compose, ofBits, contentBit, frameBit] at ha hb ⊢

theorem preserves_algebraHom_iff (g : V4) :
    preservesAt g .algebraHom = true ↔ structurePreservingAxis g := by
  cases g <;> simp [preservesAt, structurePreservingAxis]

theorem preserves_implicationTruth_iff (g : V4) :
    preservesAt g .implicationTruth = true ↔ structurePreservingAxis g := by
  cases g <;> simp [preservesAt, structurePreservingAxis]

theorem preservation_summary :
    (∀ g, preservesAt g .setBijection = true)
    ∧ (∀ g, preservesAt g .categoricalFunctor = true)
    ∧ (∀ g, preservesAt g .algebraHom = true ↔ structurePreservingAxis g)
    ∧ (∀ g, preservesAt g .implicationTruth = true ↔ structurePreservingAxis g)
    ∧ (∀ {a b}, structurePreservingAxis a → structurePreservingAxis b →
      structurePreservingAxis (compose a b)) :=
  ⟨fun g => by cases g <;> rfl,
   fun g => by cases g <;> rfl,
   preserves_algebraHom_iff,
   preserves_implicationTruth_iff,
   fun ha hb => structurePreservingAxis_closed ha hb⟩

end V4

end SSBX.Foundation.Hierarchy.Operators
