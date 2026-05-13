/-
# Wen.Layered.Bridges.V4Time -- y7/y8 V4 time-plane bridge

This module specializes the generic layered information kernel to the canonical
R8 y7/y8 time plane.  It imports V4 sidecars directly, avoiding the
`Operators.V4` umbrella to keep import cycles out of Phase 8.
-/

import SSBX.Foundation.Wen.Layered.Information
import SSBX.Foundation.Hierarchy.Operators.V4.Core
import SSBX.Foundation.Hierarchy.Operators.V4.Temporal
import SSBX.Foundation.Hierarchy.Operators.V4.PreservationLogic

namespace SSBX.Foundation.Wen.Layered

open SSBX.Foundation.Hierarchy.Operators

namespace V4Time

abbrev TimeSpace : Type := BitSpace 8

def bit (n : Nat) (h : n < 8) : Slot 8 :=
  ⟨n, h⟩

def y7 : Slot 8 := bit 6 (by decide)
def y8 : Slot 8 := bit 7 (by decide)

def timeY7Mask : TimeSpace := BitSpace.single y7
def timeY8Mask : TimeSpace := BitSpace.single y8
def parityMask : TimeSpace := BitSpace.xor timeY7Mask timeY8Mask

def andBit (q x : TimeSpace) (i : Slot 8) : Bool :=
  q i && x i

def bxor8 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : Bool :=
  Bool.xor b0
    (Bool.xor b1
      (Bool.xor b2
        (Bool.xor b3
          (Bool.xor b4
            (Bool.xor b5
              (Bool.xor b6 b7))))))

def evalQuery (q x : TimeSpace) : Bool :=
  bxor8
    (andBit q x (bit 0 (by decide)))
    (andBit q x (bit 1 (by decide)))
    (andBit q x (bit 2 (by decide)))
    (andBit q x (bit 3 (by decide)))
    (andBit q x (bit 4 (by decide)))
    (andBit q x (bit 5 (by decide)))
    (andBit q x y7)
    (andBit q x y8)

def offTimeZero (g : TimeSpace) : Prop :=
  ∀ i : Slot 8, i ≠ y7 → i ≠ y8 → g i = false

def v4TimeCarrier (g : TimeSpace) : Prop :=
  offTimeZero g

def v4Time : BitSpace.Subgroup 8 where
  carrier := v4TimeCarrier
  zero_mem := by
    intro i _ _
    rfl
  xor_mem := by
    intro a b ha hb i hi7 hi8
    unfold BitSpace.xor
    rw [ha i hi7 hi8, hb i hi7 hi8]
    rfl

def daoJinCarrier (g : TimeSpace) : Prop :=
  offTimeZero g ∧ g y7 = g y8

def daoJin : BitSpace.Subgroup 8 where
  carrier := daoJinCarrier
  zero_mem := by
    constructor
    · intro i _ _
      rfl
    · rfl
  xor_mem := by
    intro a b ha hb
    constructor
    · intro i hi7 hi8
      unfold BitSpace.xor
      rw [ha.1 i hi7 hi8, hb.1 i hi7 hi8]
      rfl
    · unfold BitSpace.xor
      rw [ha.2, hb.2]

theorem evalQuery_parityMask_zero :
    evalQuery parityMask BitSpace.zero = false := rfl

theorem evalQuery_parityMask_parityMask :
    evalQuery parityMask parityMask = false := rfl

theorem evalQuery_parityMask (x : TimeSpace) :
    evalQuery parityMask x = Bool.xor (x y7) (x y8) := by
  unfold evalQuery bxor8 andBit parityMask BitSpace.xor timeY7Mask timeY8Mask
    BitSpace.single y7 y8 bit
  cases x ⟨6, by decide⟩ <;> cases x ⟨7, by decide⟩ <;> rfl

theorem daoJin_preserves_parity :
    BitSpace.isInvariant daoJin (evalQuery parityMask) := by
  intro x g hg
  rw [evalQuery_parityMask, evalQuery_parityMask]
  unfold BitSpace.xor
  rw [hg.2]
  cases x y7 <;> cases x y8 <;> cases g y8 <;> rfl

theorem evalQuery_parityMask_timeY7 :
    evalQuery parityMask timeY7Mask = true := by
  rw [evalQuery_parityMask]
  rfl

theorem full_v4_time_does_not_preserve_parity :
    ¬ BitSpace.isInvariant v4Time (evalQuery parityMask) := by
  intro h
  have hmem : v4Time.carrier timeY7Mask := by
    intro i hi7 _hi8
    unfold timeY7Mask BitSpace.single
    simp [hi7]
  have hflip := h BitSpace.zero timeY7Mask hmem
  rw [evalQuery_parityMask, evalQuery_parityMask] at hflip
  unfold BitSpace.xor BitSpace.zero timeY7Mask BitSpace.single y7 y8 bit at hflip
  contradiction

theorem evalQuery_zero (q : TimeSpace) :
    evalQuery q BitSpace.zero = false := by
  simp [evalQuery, bxor8, andBit, BitSpace.zero]

def isInvariant (H : BitSpace.Subgroup 8) (q : TimeSpace) : Prop :=
  BitSpace.isInvariant H (evalQuery q)

def annihilates (H : BitSpace.Subgroup 8) (q : TimeSpace) : Prop :=
  BitSpace.annihilates H (evalQuery q)

def inAnnihilator (H : BitSpace.Subgroup 8) (q : TimeSpace) : Prop :=
  annihilates H q

def orbitDerives (H : BitSpace.Subgroup 8) (q root : TimeSpace) : Prop :=
  BitSpace.orbitDerives H (evalQuery q) root

theorem isInvariant_iff_annihilates (H : BitSpace.Subgroup 8)
    (q : TimeSpace) :
    isInvariant H q ↔ annihilates H q :=
  Iff.rfl

theorem invariant_iff_all_orbits_derive (H : BitSpace.Subgroup 8)
    (q : TimeSpace) :
    isInvariant H q ↔ ∀ root : TimeSpace, orbitDerives H q root :=
  BitSpace.invariant_iff_all_orbits_derive H (evalQuery q)

theorem derivable_iff_invariant (H : BitSpace.Subgroup 8) (q : TimeSpace) :
    (∀ root : TimeSpace, orbitDerives H q root) ↔ isInvariant H q :=
  (invariant_iff_all_orbits_derive H q).symm

/-! ## Checklist compatibility names in the layered namespace -/

def dao_jin_subgroup : BitSpace.Subgroup 8 := daoJin
def parity_y7_y8 : TimeSpace := parityMask

theorem dao_jin_preserves_parity :
    BitSpace.isInvariant dao_jin_subgroup (evalQuery parity_y7_y8) :=
  daoJin_preserves_parity

theorem V4_does_not_preserve_parity :
    ¬ BitSpace.isInvariant v4Time (evalQuery parity_y7_y8) :=
  full_v4_time_does_not_preserve_parity

/-! ## V8 audit compatibility names in the layered namespace -/

def oxYangChar : Char := 'o'
def oxYinChar : Char := 'x'

theorem ox_char_convention :
    oxYangChar = 'o' ∧ oxYinChar = 'x' :=
  ⟨rfl, rfl⟩

inductive CoordinateSort where
  | hexagram
  | temporal
  deriving DecidableEq, Repr

def coordinateSort (i : Slot 8) : CoordinateSort :=
  if i.val < 6 then .hexagram else .temporal

theorem y7_sort_temporal :
    coordinateSort y7 = .temporal := by
  native_decide

theorem y8_sort_temporal :
    coordinateSort y8 = .temporal := by
  native_decide

def identityMask : TimeSpace := BitSpace.zero
def hexagramComplementMask : TimeSpace := fun i => decide (i.val < 6)
def temporalPlaneMask : TimeSpace := fun i => decide (6 ≤ i.val)
def totalComplementMask : TimeSpace := fun _ => true
def compoundTemporalMask : TimeSpace := parityMask

theorem reserved_mask_summary :
    identityMask = BitSpace.zero
    ∧ compoundTemporalMask = parityMask
    ∧ offTimeZero compoundTemporalMask :=
  ⟨rfl, rfl, by
    intro i hi7 hi8
    simp [compoundTemporalMask, parityMask, timeY7Mask, timeY8Mask,
      BitSpace.xor, BitSpace.single, hi7, hi8]⟩

def r6Component
    (c : SSBX.Foundation.Bagua.R8.R8) : SSBX.Foundation.Yi.Yi.Hexagram :=
  c.1

def v4Component (c : SSBX.Foundation.Bagua.R8.R8) : V4 :=
  V4.ofTemporal c.2

def cellOfComponents (h : SSBX.Foundation.Yi.Yi.Hexagram) (g : V4) :
    SSBX.Foundation.Bagua.R8.R8 :=
  (h, V4.toTemporal g)

theorem r6Component_cellOfComponents
    (h : SSBX.Foundation.Yi.Yi.Hexagram) (g : V4) :
    r6Component (cellOfComponents h g) = h := rfl

theorem v4Component_cellOfComponents
    (h : SSBX.Foundation.Yi.Yi.Hexagram) (g : V4) :
    v4Component (cellOfComponents h g) = g := by
  simp [v4Component, cellOfComponents, V4.ofTemporal_toTemporal]

theorem cellOfComponents_components (c : SSBX.Foundation.Bagua.R8.R8) :
    cellOfComponents (r6Component c) (v4Component c) = c := by
  rcases c with ⟨h, temporal⟩
  simp [cellOfComponents, r6Component, v4Component, V4.toTemporal_ofTemporal]

theorem component_metadata_summary :
    (∀ h g, r6Component (cellOfComponents h g) = h)
    ∧ (∀ h g, v4Component (cellOfComponents h g) = g)
    ∧ (∀ c : SSBX.Foundation.Bagua.R8.R8,
        cellOfComponents (r6Component c) (v4Component c) = c) :=
  ⟨r6Component_cellOfComponents, v4Component_cellOfComponents,
   cellOfComponents_components⟩

/-! ## Five-element checker for the y7/y8 time plane -/

def trivial : BitSpace.Subgroup 8 := BitSpace.spanOne BitSpace.zero
def daoJi : BitSpace.Subgroup 8 := BitSpace.spanOne timeY7Mask
def daoWei : BitSpace.Subgroup 8 := BitSpace.spanOne timeY8Mask

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

def subgroup : TimeSubgroupTag → BitSpace.Subgroup 8
  | .dao => trivial
  | .daoJi => V4Time.daoJi
  | .daoWei => V4Time.daoWei
  | .daoJin => V4Time.daoJin
  | .full => V4Time.v4Time

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

def generators : TimeSubgroupTag → List TimeSpace
  | .dao => []
  | .daoJi => [timeY7Mask]
  | .daoWei => [timeY8Mask]
  | .daoJin => [parityMask]
  | .full => [timeY7Mask, timeY8Mask]

end TimeSubgroupTag

def allFalseOn (q : TimeSpace) : List TimeSpace → Bool
  | [] => true
  | g :: rest => (evalQuery q g == false) && allFalseOn q rest

def derivableTime? (tag : TimeSubgroupTag) (q root : TimeSpace) : Option Bool :=
  if allFalseOn q (TimeSubgroupTag.generators tag) then
    some (evalQuery q root)
  else
    none

theorem derivableTime_dao (q root : TimeSpace) :
    derivableTime? .dao q root = some (evalQuery q root) := by
  simp [derivableTime?, TimeSubgroupTag.generators, allFalseOn]

theorem derivableTime_daoJin_parity (root : TimeSpace) :
    derivableTime? .daoJin parityMask root = some (evalQuery parityMask root) := by
  simp [derivableTime?, TimeSubgroupTag.generators, allFalseOn,
    evalQuery_parityMask_parityMask]

theorem dao_jin_derives_parity (root : TimeSpace) :
    derivableTime? .daoJin parityMask root = some (evalQuery parityMask root) :=
  derivableTime_daoJin_parity root

theorem derivableTime_full_rejects_parity (root : TimeSpace) :
    derivableTime? .full parityMask root = none := by
  simp [derivableTime?, TimeSubgroupTag.generators, allFalseOn,
    evalQuery_parityMask_timeY7]

theorem full_v4_rejects_parity (root : TimeSpace) :
    derivableTime? .full parityMask root = none :=
  derivableTime_full_rejects_parity root

theorem derivability_summary :
    (∀ (H : BitSpace.Subgroup 8) (q : TimeSpace),
      (∀ root : TimeSpace, orbitDerives H q root) ↔ isInvariant H q)
    ∧ (∀ (H : BitSpace.Subgroup 8) (q : TimeSpace),
      isInvariant H q ↔ annihilates H q)
    ∧ (∀ (q root : TimeSpace),
      derivableTime? .dao q root = some (evalQuery q root))
    ∧ (∀ root : TimeSpace, derivableTime? .daoJin parityMask root =
      some (evalQuery parityMask root))
    ∧ (∀ root : TimeSpace, derivableTime? .full parityMask root = none)
    ∧ TimeSubgroupTag.all.length = 5 :=
  ⟨derivable_iff_invariant, isInvariant_iff_annihilates,
   derivableTime_dao, derivableTime_daoJin_parity,
   derivableTime_full_rejects_parity, TimeSubgroupTag.all_length⟩

theorem layered_derivability_summary :
    (∀ root : TimeSpace, derivableTime? .daoJin parityMask root =
      some (evalQuery parityMask root))
    ∧ (∀ root : TimeSpace, derivableTime? .full parityMask root = none) :=
  ⟨dao_jin_derives_parity, full_v4_rejects_parity⟩

/-! ## Element-level bridge from canonical V4 -/

def toTimeMask (g : V4) : TimeSpace :=
  fun i =>
    if i = y7 then V4.contentBit g
    else if i = y8 then V4.frameBit g
    else false

@[simp] theorem toTimeMask_y7 (g : V4) :
    toTimeMask g y7 = V4.contentBit g := by
  simp [toTimeMask]

@[simp] theorem toTimeMask_y8 (g : V4) :
    toTimeMask g y8 = V4.frameBit g := by
  simp [toTimeMask, y7, y8, bit]

theorem toTimeMask_offTimeZero (g : V4) :
    offTimeZero (toTimeMask g) := by
  intro i hi7 hi8
  simp [toTimeMask, hi7, hi8]

theorem toTimeMask_mem_v4Time (g : V4) :
    v4Time.carrier (toTimeMask g) :=
  toTimeMask_offTimeZero g

theorem toTimeMask_dao :
    toTimeMask .dao = BitSpace.zero := by
  funext i
  by_cases h7 : i = y7
  · subst i
    rfl
  · by_cases h8 : i = y8
    · subst i
      rfl
    · simp [toTimeMask, BitSpace.zero, h7, h8]

theorem toTimeMask_cuo :
    toTimeMask .cuo = timeY7Mask := by
  funext i
  by_cases h7 : i = y7
  · subst i
    rfl
  · by_cases h8 : i = y8
    · subst i
      rfl
    · simp [toTimeMask, timeY7Mask, BitSpace.single, h7, h8]

theorem toTimeMask_zong :
    toTimeMask .zong = timeY8Mask := by
  funext i
  by_cases h7 : i = y7
  · subst i
    rfl
  · by_cases h8 : i = y8
    · subst i
      rfl
    · simp [toTimeMask, timeY8Mask, BitSpace.single, h7, h8]

theorem toTimeMask_cuoZong :
    toTimeMask .cuoZong = parityMask := by
  funext i
  by_cases h7 : i = y7
  · subst i
    rfl
  · by_cases h8 : i = y8
    · subst i
      rfl
    · simp [toTimeMask, parityMask, timeY7Mask, timeY8Mask, BitSpace.xor,
        BitSpace.single, h7, h8]

theorem toTimeMask_compose (a b : V4) :
    toTimeMask (V4.compose a b) = BitSpace.xor (toTimeMask a) (toTimeMask b) := by
  funext i
  by_cases h7 : i = y7
  · subst i
    cases a <;> cases b <;> rfl
  · by_cases h8 : i = y8
    · subst i
      cases a <;> cases b <;> rfl
    · simp [toTimeMask, BitSpace.xor, h7, h8]

theorem daoJin_carrier_toTimeMask_iff_equalBits (g : V4) :
    daoJin.carrier (toTimeMask g) ↔ V4.contentBit g = V4.frameBit g := by
  constructor
  · intro h
    have hy := h.2
    simpa [toTimeMask, y7, y8, bit] using hy
  · intro heq
    constructor
    · exact toTimeMask_offTimeZero g
    · simp [toTimeMask, y7, y8, bit, heq]

theorem structureAxis_iff_daoJin_carrier (g : V4) :
    daoJin.carrier (toTimeMask g) ↔ V4.structurePreservingAxis g := by
  rw [daoJin_carrier_toTimeMask_iff_equalBits,
    V4.structurePreservingAxis_iff_equalBits]

theorem structureAxis_maps_to_daoJin {g : V4}
    (hg : V4.structurePreservingAxis g) :
    daoJin.carrier (toTimeMask g) :=
  (structureAxis_iff_daoJin_carrier g).mpr hg

theorem daoJin_preimage_is_structureAxis {g : V4}
    (hg : daoJin.carrier (toTimeMask g)) :
    V4.structurePreservingAxis g :=
  (structureAxis_iff_daoJin_carrier g).mp hg

theorem time_lattice_summary :
    TimeSubgroupTag.all.length = 5
    ∧ TimeSubgroupTag.le .dao .full = true
    ∧ TimeSubgroupTag.le .daoJi .full = true
    ∧ TimeSubgroupTag.le .daoWei .full = true
    ∧ TimeSubgroupTag.le .daoJin .full = true
    ∧ TimeSubgroupTag.le .daoJi .daoJin = false :=
  ⟨TimeSubgroupTag.all_length, rfl, rfl, rfl, rfl, rfl⟩

theorem lean_v4_information_summary :
    BitSpace.isInvariant daoJin (evalQuery parityMask)
    ∧ ¬ BitSpace.isInvariant v4Time (evalQuery parityMask)
    ∧ (∀ root, derivableTime? .daoJin parityMask root =
      some (evalQuery parityMask root))
    ∧ (∀ root, derivableTime? .full parityMask root = none)
    ∧ (∀ g : V4, daoJin.carrier (toTimeMask g) ↔ V4.structurePreservingAxis g) :=
  ⟨daoJin_preserves_parity,
   full_v4_time_does_not_preserve_parity,
   dao_jin_derives_parity,
   full_v4_rejects_parity,
   structureAxis_iff_daoJin_carrier⟩

theorem layered_v8info_summary :
    (∀ x : TimeSpace, evalQuery parityMask x = evalQuery parityMask x)
    ∧ BitSpace.isInvariant daoJin (evalQuery parityMask)
    ∧ ¬ BitSpace.isInvariant v4Time (evalQuery parityMask) :=
  ⟨fun _ => rfl, daoJin_preserves_parity,
   full_v4_time_does_not_preserve_parity⟩

theorem v4_time_bridge_summary :
    (∀ g : V4, v4Time.carrier (toTimeMask g))
    ∧ toTimeMask .dao = BitSpace.zero
    ∧ toTimeMask .cuoZong = parityMask
    ∧ (∀ g : V4, daoJin.carrier (toTimeMask g) ↔ V4.structurePreservingAxis g)
    ∧ BitSpace.isInvariant daoJin (evalQuery parityMask)
    ∧ ¬ BitSpace.isInvariant v4Time (evalQuery parityMask) :=
  ⟨toTimeMask_mem_v4Time, toTimeMask_dao, toTimeMask_cuoZong,
   structureAxis_iff_daoJin_carrier, daoJin_preserves_parity,
   full_v4_time_does_not_preserve_parity⟩

theorem v4_v8_bridge_summary :
    (∀ g : V4, v4Time.carrier (toTimeMask g))
    ∧ toTimeMask .dao = BitSpace.zero
    ∧ toTimeMask .cuoZong = parityMask
    ∧ (∀ g : V4, daoJin.carrier (toTimeMask g) ↔ V4.structurePreservingAxis g) :=
  ⟨toTimeMask_mem_v4Time, toTimeMask_dao, toTimeMask_cuoZong,
   structureAxis_iff_daoJin_carrier⟩

end V4Time

end SSBX.Foundation.Wen.Layered
