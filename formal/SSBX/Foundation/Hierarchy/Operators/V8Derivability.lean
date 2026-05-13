/-
# Operators · V8Derivability -- derivability iff and time-subgroup checker

This module closes the practical information-preservation loop for the V4 time
plane inside V8.  It does not enumerate the full V8 subgroup lattice; it gives
the complete five-element subgroup lattice of the canonical y7/y8 time plane
and a small derivability checker for linear queries on that lattice.
-/

import SSBX.Foundation.Hierarchy.Operators.V8Audit

namespace SSBX.Foundation.Hierarchy.Operators

namespace V8Info

/-! ## XOR algebra facts used by derivability -/

theorem xor_zero_left (x : V8) :
    xor zero x = x := by
  funext i
  unfold xor zero
  cases x i <;> rfl

theorem xor_zero_right (x : V8) :
    xor x zero = x := by
  funext i
  unfold xor zero
  cases x i <;> rfl

theorem xor_self (x : V8) :
    xor x x = zero := by
  funext i
  unfold xor zero
  cases x i <;> rfl

theorem evalQuery_zero (q : V8) :
    evalQuery q zero = false := by
  simp [evalQuery, bxor8, andBit, zero]

/-! ## Annihilator and derivability iff -/

/-- Operational annihilator predicate.  It is definitionally the invariant
condition used by the checker; a later Mathlib linear-algebra layer can refine
this into a subspace orthogonal complement theorem. -/
def annihilates (H : Subgroup) (q : V8) : Prop :=
  isInvariant H q

def inAnnihilator (H : Subgroup) (q : V8) : Prop :=
  annihilates H q

theorem isInvariant_iff_annihilates (H : Subgroup) (q : V8) :
    isInvariant H q ↔ annihilates H q :=
  Iff.rfl

/-- A query is derivable from a root's H-orbit when it has the same value on
all states in that orbit. -/
def orbitDerives (H : Subgroup) (q root : V8) : Prop :=
  ∀ y : V8, orbit H root y → evalQuery q y = evalQuery q root

theorem invariant_iff_all_orbits_derive (H : Subgroup) (q : V8) :
    isInvariant H q ↔ ∀ root : V8, orbitDerives H q root := by
  constructor
  · intro h root y hy
    exact evalQuery_constant_on_orbit h hy
  · intro h x g hg
    exact h x (xor x g) ⟨g, hg, rfl⟩

theorem derivable_iff_invariant (H : Subgroup) (q : V8) :
    (∀ root : V8, orbitDerives H q root) ↔ isInvariant H q :=
  (invariant_iff_all_orbits_derive H q).symm

/-! ## Complete five-element lattice of the V4 time plane -/

def spanOneCarrier (m g : V8) : Prop :=
  g = zero ∨ g = m

def spanOne (m : V8) : Subgroup where
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

def trivial : Subgroup := spanOne zero
def daoJi : Subgroup := spanOne timeY7Mask
def daoWei : Subgroup := spanOne timeY8Mask

inductive TimeSubgroupTag where
  | dao
  | daoJi
  | daoWei
  | daoJin
  | full
  deriving DecidableEq, Repr

namespace TimeSubgroupTag

def all : List TimeSubgroupTag :=
  [.dao, .daoJi, .daoWei, .daoJin, .full]

theorem all_length : all.length = 5 := rfl

def subgroup : TimeSubgroupTag → Subgroup
  | .dao => trivial
  | .daoJi => V8Info.daoJi
  | .daoWei => V8Info.daoWei
  | .daoJin => V8Info.daoJin
  | .full => V8Info.v4Time

/-- Tag-level order for the five subgroups of the y7/y8 time plane. -/
def le : TimeSubgroupTag → TimeSubgroupTag → Bool
  | .dao, _ => true
  | .daoJi, .daoJi | .daoJi, .full => true
  | .daoWei, .daoWei | .daoWei, .full => true
  | .daoJin, .daoJin | .daoJin, .full => true
  | .full, .full => true
  | _, _ => false

theorem le_refl (tag : TimeSubgroupTag) :
    le tag tag = true := by
  cases tag <;> rfl

theorem atoms_le_full :
    le .daoJi .full = true
    ∧ le .daoWei .full = true
    ∧ le .daoJin .full = true := by
  exact ⟨rfl, rfl, rfl⟩

theorem atoms_incomparable :
    le .daoJi .daoWei = false
    ∧ le .daoJi .daoJin = false
    ∧ le .daoWei .daoJin = false
    ∧ le .daoJin .daoJi = false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

def generators : TimeSubgroupTag → List V8
  | .dao => []
  | .daoJi => [timeY7Mask]
  | .daoWei => [timeY8Mask]
  | .daoJin => [parityMask]
  | .full => [timeY7Mask, timeY8Mask]

end TimeSubgroupTag

/-! ## Lean-native derivability checker for the time-plane lattice -/

def allFalseOn (q : V8) : List V8 → Bool
  | [] => true
  | g :: rest => (evalQuery q g == false) && allFalseOn q rest

def derivableTime? (tag : TimeSubgroupTag) (q root : V8) : Option Bool :=
  if allFalseOn q (TimeSubgroupTag.generators tag) then
    some (evalQuery q root)
  else
    none

theorem allFalseOn_nil (q : V8) :
    allFalseOn q [] = true := rfl

theorem derivableTime_dao (q root : V8) :
    derivableTime? .dao q root = some (evalQuery q root) := by
  simp [derivableTime?, TimeSubgroupTag.generators, allFalseOn]

theorem derivableTime_daoJin_parity (root : V8) :
    derivableTime? .daoJin parityMask root = some (evalQuery parityMask root) := by
  simp [derivableTime?, TimeSubgroupTag.generators, allFalseOn,
    evalQuery_parityMask_parityMask]

theorem evalQuery_parityMask_timeY7 :
    evalQuery parityMask timeY7Mask = true := by
  rw [evalQuery_parityMask]
  rfl

theorem derivableTime_full_rejects_parity (root : V8) :
    derivableTime? .full parityMask root = none := by
  simp [derivableTime?, TimeSubgroupTag.generators, allFalseOn,
    evalQuery_parityMask_timeY7]

theorem time_lattice_summary :
    TimeSubgroupTag.all.length = 5
    ∧ TimeSubgroupTag.le .dao .full = true
    ∧ TimeSubgroupTag.le .daoJi .full = true
    ∧ TimeSubgroupTag.le .daoWei .full = true
    ∧ TimeSubgroupTag.le .daoJin .full = true
    ∧ TimeSubgroupTag.le .daoJi .daoJin = false :=
  ⟨TimeSubgroupTag.all_length, rfl, rfl, rfl, rfl, rfl⟩

theorem derivability_summary :
    (∀ H q, (∀ root : V8, orbitDerives H q root) ↔ isInvariant H q)
    ∧ (∀ H q, isInvariant H q ↔ annihilates H q)
    ∧ (∀ q root, derivableTime? .dao q root = some (evalQuery q root))
    ∧ (∀ root, derivableTime? .daoJin parityMask root =
      some (evalQuery parityMask root))
    ∧ (∀ root, derivableTime? .full parityMask root = none)
    ∧ TimeSubgroupTag.all.length = 5 :=
  ⟨derivable_iff_invariant, isInvariant_iff_annihilates,
   derivableTime_dao, derivableTime_daoJin_parity,
   derivableTime_full_rejects_parity, TimeSubgroupTag.all_length⟩

end V8Info

end SSBX.Foundation.Hierarchy.Operators
