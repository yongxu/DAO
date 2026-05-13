/-
# Operators · V4.PreservationLogic -- finite proof layer

This sidecar turns the V4 preservation registry into small auditable finite
facts.  It does not add domain claims beyond the classical implication slice
modeled below.
-/

import SSBX.Foundation.Hierarchy.Operators.V4.Instances
import SSBX.Foundation.Hierarchy.Operators.V4.Preservation
import Mathlib.Algebra.Group.Subgroup.Basic

namespace SSBX.Foundation.Hierarchy.Operators

namespace V4

/-! ## Three two-element axes -/

theorem contentAxis_iff (g : V4) :
    contentAxis g ↔ g = .dao ∨ g = .cuo := Iff.rfl

theorem frameAxis_iff (g : V4) :
    frameAxis g ↔ g = .dao ∨ g = .zong := Iff.rfl

theorem structurePreservingAxis_iff (g : V4) :
    structurePreservingAxis g ↔ g = .dao ∨ g = .cuoZong := Iff.rfl

theorem contentAxis_iff_noFrame (g : V4) :
    contentAxis g ↔ frameBit g = false := by
  cases g <;> simp [contentAxis, frameBit]

theorem frameAxis_iff_noContent (g : V4) :
    frameAxis g ↔ contentBit g = false := by
  cases g <;> simp [frameAxis, contentBit]

theorem structurePreservingAxis_iff_equalBits (g : V4) :
    structurePreservingAxis g ↔ contentBit g = frameBit g := by
  cases g <;> simp [structurePreservingAxis, contentBit, frameBit]

theorem structurePreservingAxis_exact (g : V4) :
    structurePreservingAxis g ↔ g = .dao ∨ g = .cuoZong :=
  structurePreservingAxis_iff g

theorem contentAxis_exact (g : V4) :
    contentAxis g ↔ g = .dao ∨ g = .cuo :=
  contentAxis_iff g

theorem frameAxis_exact (g : V4) :
    frameAxis g ↔ g = .dao ∨ g = .zong :=
  frameAxis_iff g

theorem three_axis_classification :
    (∀ g : V4, contentAxis g ↔ g = .dao ∨ g = .cuo)
    ∧ (∀ g : V4, frameAxis g ↔ g = .dao ∨ g = .zong)
    ∧ (∀ g : V4, structurePreservingAxis g ↔ g = .dao ∨ g = .cuoZong)
    ∧ (∀ {a b : V4}, contentAxis a → contentAxis b →
      contentAxis (compose a b))
    ∧ (∀ {a b : V4}, frameAxis a → frameAxis b →
      frameAxis (compose a b))
    ∧ (∀ {a b : V4}, structurePreservingAxis a →
      structurePreservingAxis b → structurePreservingAxis (compose a b)) :=
  ⟨contentAxis_exact,
   frameAxis_exact,
   structurePreservingAxis_exact,
   fun ha hb => contentAxis_closed ha hb,
   fun ha hb => frameAxis_closed ha hb,
   fun ha hb => structurePreservingAxis_closed ha hb⟩

/-! ## Structure-preserving subgroup -/

/-- The privileged subgroup `{dao, cuoZong}` selected by the
variance-corrected structure-preservation marker. -/
def structurePreservingSubgroup : Subgroup V4 where
  carrier := {g | structurePreservingAxis g}
  one_mem' := by
    simp [structurePreservingAxis]
  mul_mem' := by
    intro a b ha hb
    change structurePreservingAxis (a * b)
    simpa [mul_eq_compose] using structurePreservingAxis_closed ha hb
  inv_mem' := by
    intro g hg
    simpa [inv_eq_self] using hg

theorem mem_structurePreservingSubgroup (g : V4) :
    g ∈ structurePreservingSubgroup ↔ g = .dao ∨ g = .cuoZong :=
  structurePreservingAxis_exact g

theorem mem_structurePreservingSubgroup_iff_axis (g : V4) :
    g ∈ structurePreservingSubgroup ↔ structurePreservingAxis g :=
  Iff.rfl

/-! ## Classical implication slice -/

/-- A finite classical implication `antecedent -> consequent`. -/
structure ImplicationSlice where
  antecedent : Bool
  consequent : Bool
  deriving DecidableEq, Repr

namespace ImplicationSlice

def truth (s : ImplicationSlice) : Bool :=
  (!s.antecedent) || s.consequent

def act : V4 → ImplicationSlice → ImplicationSlice
  | .dao, s => s
  | .cuo, s =>
      { antecedent := !s.antecedent, consequent := !s.consequent }
  | .zong, s =>
      { antecedent := s.consequent, consequent := s.antecedent }
  | .cuoZong, s =>
      { antecedent := !s.consequent, consequent := !s.antecedent }

theorem truth_mk (p q : Bool) :
    truth { antecedent := p, consequent := q } = ((!p) || q) := rfl

theorem act_cuoZong (p q : Bool) :
    act .cuoZong { antecedent := p, consequent := q }
      = { antecedent := !q, consequent := !p } := rfl

theorem contrapositive_truth (p q : Bool) :
    truth (act .cuoZong { antecedent := p, consequent := q })
      = truth { antecedent := p, consequent := q } := by
  cases p <;> cases q <;> rfl

theorem dao_preserves_truth (s : ImplicationSlice) :
    truth (act .dao s) = truth s := rfl

theorem cuoZong_preserves_truth (s : ImplicationSlice) :
    truth (act .cuoZong s) = truth s := by
  cases s with
  | mk p q => exact contrapositive_truth p q

theorem cuo_not_truth_preserving :
    ¬ (∀ s : ImplicationSlice, truth (act .cuo s) = truth s) := by
  intro h
  have bad := h { antecedent := false, consequent := true }
  simp [truth, act] at bad

theorem zong_not_truth_preserving :
    ¬ (∀ s : ImplicationSlice, truth (act .zong s) = truth s) := by
  intro h
  have bad := h { antecedent := false, consequent := true }
  simp [truth, act] at bad

theorem preserves_truth_iff_structureAxis (g : V4) :
    (∀ s : ImplicationSlice, truth (act g s) = truth s)
      ↔ structurePreservingAxis g := by
  cases g
  · simp [structurePreservingAxis, dao_preserves_truth]
  · constructor
    · intro h
      exact False.elim (cuo_not_truth_preserving h)
    · intro h
      cases h with
      | inl hdao => contradiction
      | inr hcz => contradiction
  · constructor
    · intro h
      exact False.elim (zong_not_truth_preserving h)
    · intro h
      cases h with
      | inl hdao => contradiction
      | inr hcz => contradiction
  · simp [structurePreservingAxis, cuoZong_preserves_truth]

end ImplicationSlice

theorem cuoZong_classical_implication_truth :
    ∀ s : ImplicationSlice,
      ImplicationSlice.truth (ImplicationSlice.act .cuoZong s)
        = ImplicationSlice.truth s :=
  ImplicationSlice.cuoZong_preserves_truth

theorem preserves_algebraHom_exact (g : V4) :
    preservesAt g .algebraHom = true ↔ g = .dao ∨ g = .cuoZong := by
  simpa [structurePreservingAxis] using preserves_algebraHom_iff g

theorem preserves_implicationTruth_exact (g : V4) :
    preservesAt g .implicationTruth = true ↔ g = .dao ∨ g = .cuoZong := by
  simpa [structurePreservingAxis] using preserves_implicationTruth_iff g

theorem mem_structurePreservingSubgroup_iff_preserves_algebraHom (g : V4) :
    g ∈ structurePreservingSubgroup ↔ preservesAt g .algebraHom = true := by
  rw [mem_structurePreservingSubgroup, preserves_algebraHom_exact]

theorem preserves_algebraHom_iff_mem_structurePreservingSubgroup (g : V4) :
    preservesAt g .algebraHom = true ↔ g ∈ structurePreservingSubgroup :=
  (mem_structurePreservingSubgroup_iff_preserves_algebraHom g).symm

/-- Category-level preservation remains registry data in Phase 2. -/
theorem categoricalFunctor_registry_only (g : V4) :
    preservesAt g .categoricalFunctor = true := by
  cases g <;> rfl

theorem cuoZong_contrapositive_consistency :
    preservesAt .cuoZong .implicationTruth = true
      ∧ (∀ s : ImplicationSlice,
        ImplicationSlice.truth (ImplicationSlice.act .cuoZong s)
          = ImplicationSlice.truth s) :=
  ⟨rfl, cuoZong_classical_implication_truth⟩

theorem preservation_logic_summary :
    (∀ g : V4, preservesAt g .algebraHom = true ↔ g = .dao ∨ g = .cuoZong)
    ∧ (∀ g : V4, preservesAt g .implicationTruth = true ↔
      g = .dao ∨ g = .cuoZong)
    ∧ (∀ g : V4, g ∈ structurePreservingSubgroup ↔
      preservesAt g .algebraHom = true)
    ∧ (∀ g : V4,
      (∀ s : ImplicationSlice,
        ImplicationSlice.truth (ImplicationSlice.act g s)
          = ImplicationSlice.truth s) ↔ structurePreservingAxis g)
    ∧ (∀ g : V4, preservesAt g .categoricalFunctor = true) :=
  ⟨preserves_algebraHom_exact,
   preserves_implicationTruth_exact,
   mem_structurePreservingSubgroup_iff_preserves_algebraHom,
   ImplicationSlice.preserves_truth_iff_structureAxis,
   categoricalFunctor_registry_only⟩

end V4

end SSBX.Foundation.Hierarchy.Operators
