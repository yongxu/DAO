/-
# Wen.Layered.Runtime.V4Time -- BitVec runtime y7/y8 time-plane mirrors

This file uses `V4` from `Foundation/Hierarchy/Operators/V4/Core.lean`,
which is the constructor-style presentation of `R 2` per
`wen-substrate.md` v1.4 §3.7.8 (distinction monism).  The R-family is the
one mathematical core; `V4` here is the ergonomic 4-constructor surface
over `R 2 = Fin 2 → Bool`.
-/

import SSBX.Foundation.Wen.Layered.Bridges.V4Time
import SSBX.Foundation.Wen.Layered.Runtime.Information

namespace SSBX.Foundation.Wen.Layered.Runtime

open SSBX.Foundation.Hierarchy.Operators

namespace V4Time

abbrev TimeSpace : Type := Cell 8

def bit (n : Nat) (h : n < 8) : Slot 8 :=
  SSBX.Foundation.Wen.Layered.V4Time.bit n h

def y7 : Slot 8 := SSBX.Foundation.Wen.Layered.V4Time.y7
def y8 : Slot 8 := SSBX.Foundation.Wen.Layered.V4Time.y8

def timeY7Mask : TimeSpace :=
  ofSpec SSBX.Foundation.Wen.Layered.V4Time.timeY7Mask

def timeY8Mask : TimeSpace :=
  ofSpec SSBX.Foundation.Wen.Layered.V4Time.timeY8Mask

def parityMask : TimeSpace :=
  ofSpec SSBX.Foundation.Wen.Layered.V4Time.parityMask

@[simp] theorem toSpec_timeY7Mask :
    toSpec timeY7Mask = SSBX.Foundation.Wen.Layered.V4Time.timeY7Mask := by
  simp [timeY7Mask]

@[simp] theorem toSpec_timeY8Mask :
    toSpec timeY8Mask = SSBX.Foundation.Wen.Layered.V4Time.timeY8Mask := by
  simp [timeY8Mask]

@[simp] theorem toSpec_parityMask :
    toSpec parityMask = SSBX.Foundation.Wen.Layered.V4Time.parityMask := by
  simp [parityMask]

def evalQuery (q x : TimeSpace) : Bool :=
  SSBX.Foundation.Wen.Layered.V4Time.evalQuery (toSpec q) (toSpec x)

theorem evalQuery_parityMask (x : TimeSpace) :
    evalQuery parityMask x = Bool.xor ((toSpec x) y7) ((toSpec x) y8) := by
  simpa [evalQuery, y7, y8] using
    SSBX.Foundation.Wen.Layered.V4Time.evalQuery_parityMask (toSpec x)

theorem evalQuery_parityMask_parityMask :
    evalQuery parityMask parityMask = false := by
  simpa [evalQuery] using
    SSBX.Foundation.Wen.Layered.V4Time.evalQuery_parityMask_parityMask

theorem evalQuery_parityMask_timeY7 :
    evalQuery parityMask timeY7Mask = true := by
  simpa [evalQuery] using
    SSBX.Foundation.Wen.Layered.V4Time.evalQuery_parityMask_timeY7

def v4Time : Subgroup 8 :=
  Subgroup.fromSpec SSBX.Foundation.Wen.Layered.V4Time.v4Time

def daoJin : Subgroup 8 :=
  Subgroup.fromSpec SSBX.Foundation.Wen.Layered.V4Time.daoJin

theorem daoJin_preserves_parity :
    isInvariant daoJin (evalQuery parityMask) := by
  intro x g hg y hspec
  unfold evalQuery
  rw [hspec]
  simpa [daoJin] using
    SSBX.Foundation.Wen.Layered.V4Time.daoJin_preserves_parity
      (toSpec x) (toSpec g) hg

theorem full_v4_time_does_not_preserve_parity :
    ¬ isInvariant v4Time (evalQuery parityMask) := by
  intro h
  apply SSBX.Foundation.Wen.Layered.V4Time.full_v4_time_does_not_preserve_parity
  intro x g hg
  have hg_runtime : v4Time.carrier (ofSpec g) := by
    simpa [v4Time, Subgroup.carrier] using hg
  have hspec :
      toSpec (ofSpec (BitSpace.xor x g : BitSpace 8)) =
        BitSpace.xor (toSpec (ofSpec x)) (toSpec (ofSpec g)) := by
    simp
  have hrun := h (ofSpec x) (ofSpec g) hg_runtime
    (ofSpec (BitSpace.xor x g : BitSpace 8)) hspec
  simpa [evalQuery] using hrun

/-! ## Checklist compatibility names in the runtime namespace -/

def dao_jin_subgroup : Subgroup 8 := daoJin
def parity_y7_y8 : TimeSpace := parityMask

theorem dao_jin_preserves_parity :
    isInvariant dao_jin_subgroup (evalQuery parity_y7_y8) :=
  daoJin_preserves_parity

theorem V4_does_not_preserve_parity :
    ¬ isInvariant v4Time (evalQuery parity_y7_y8) :=
  full_v4_time_does_not_preserve_parity

/-! ## Five-element checker for the y7/y8 time plane -/

def trivial : Subgroup 8 :=
  Subgroup.fromSpec SSBX.Foundation.Wen.Layered.V4Time.trivial

def daoJi : Subgroup 8 :=
  Subgroup.fromSpec SSBX.Foundation.Wen.Layered.V4Time.daoJi

def daoWei : Subgroup 8 :=
  Subgroup.fromSpec SSBX.Foundation.Wen.Layered.V4Time.daoWei

abbrev TimeSubgroupTag : Type :=
  SSBX.Foundation.Wen.Layered.V4Time.TimeSubgroupTag

namespace TimeSubgroupTag

def all : List TimeSubgroupTag :=
  SSBX.Foundation.Wen.Layered.V4Time.TimeSubgroupTag.all

theorem all_length : all.length = 5 := by
  simpa [all] using
    SSBX.Foundation.Wen.Layered.V4Time.TimeSubgroupTag.all_length

def subgroup : TimeSubgroupTag → Subgroup 8
  | .dao => trivial
  | .daoJi => V4Time.daoJi
  | .daoWei => V4Time.daoWei
  | .daoJin => V4Time.daoJin
  | .full => V4Time.v4Time

def le (a b : TimeSubgroupTag) : Bool :=
  SSBX.Foundation.Wen.Layered.V4Time.TimeSubgroupTag.le a b

theorem le_refl (tag : TimeSubgroupTag) :
    le tag tag = true := by
  simpa [le] using
    SSBX.Foundation.Wen.Layered.V4Time.TimeSubgroupTag.le_refl tag

theorem atoms_le_full :
    le .daoJi .full = true
    ∧ le .daoWei .full = true
    ∧ le .daoJin .full = true := by
  simpa [le] using
    SSBX.Foundation.Wen.Layered.V4Time.TimeSubgroupTag.atoms_le_full

theorem atoms_incomparable :
    le .daoJi .daoWei = false
    ∧ le .daoJi .daoJin = false
    ∧ le .daoWei .daoJin = false
    ∧ le .daoJin .daoJi = false := by
  simpa [le] using
    SSBX.Foundation.Wen.Layered.V4Time.TimeSubgroupTag.atoms_incomparable

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

/-! ## Element-level bridge from canonical V4 -/

def toTimeMask (g : V4) : TimeSpace :=
  ofSpec (SSBX.Foundation.Wen.Layered.V4Time.toTimeMask g)

@[simp] theorem toSpec_toTimeMask (g : V4) :
    toSpec (toTimeMask g) = SSBX.Foundation.Wen.Layered.V4Time.toTimeMask g := by
  simp [toTimeMask]

theorem toTimeMask_mem_v4Time (g : V4) :
    v4Time.carrier (toTimeMask g) := by
  simpa [v4Time, Subgroup.carrier, toTimeMask] using
    SSBX.Foundation.Wen.Layered.V4Time.toTimeMask_mem_v4Time g

theorem toTimeMask_dao :
    toTimeMask .dao = ofSpec (BitSpace.zero : BitSpace 8) := by
  simp [toTimeMask, SSBX.Foundation.Wen.Layered.V4Time.toTimeMask_dao]

theorem toTimeMask_cuo :
    toTimeMask .cuo = timeY7Mask := by
  simp [toTimeMask, timeY7Mask,
    SSBX.Foundation.Wen.Layered.V4Time.toTimeMask_cuo]

theorem toTimeMask_zong :
    toTimeMask .zong = timeY8Mask := by
  simp [toTimeMask, timeY8Mask,
    SSBX.Foundation.Wen.Layered.V4Time.toTimeMask_zong]

theorem toTimeMask_cuoZong :
    toTimeMask .cuoZong = parityMask := by
  simp [toTimeMask, parityMask,
    SSBX.Foundation.Wen.Layered.V4Time.toTimeMask_cuoZong]

theorem structureAxis_iff_daoJin_carrier (g : V4) :
    daoJin.carrier (toTimeMask g) ↔ V4.structurePreservingAxis g := by
  simpa [daoJin, Subgroup.carrier, toTimeMask] using
    SSBX.Foundation.Wen.Layered.V4Time.structureAxis_iff_daoJin_carrier g

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
    isInvariant daoJin (evalQuery parityMask)
    ∧ ¬ isInvariant v4Time (evalQuery parityMask)
    ∧ (∀ root, derivableTime? .daoJin parityMask root =
      some (evalQuery parityMask root))
    ∧ (∀ root, derivableTime? .full parityMask root = none)
    ∧ (∀ g : V4, daoJin.carrier (toTimeMask g) ↔ V4.structurePreservingAxis g) :=
  ⟨daoJin_preserves_parity,
   full_v4_time_does_not_preserve_parity,
   dao_jin_derives_parity,
   full_v4_rejects_parity,
   structureAxis_iff_daoJin_carrier⟩

theorem v4_time_bridge_summary :
    (∀ g : V4, v4Time.carrier (toTimeMask g))
    ∧ toTimeMask .cuoZong = parityMask
    ∧ (∀ g : V4, daoJin.carrier (toTimeMask g) ↔ V4.structurePreservingAxis g)
    ∧ isInvariant daoJin (evalQuery parityMask)
    ∧ ¬ isInvariant v4Time (evalQuery parityMask) :=
  ⟨toTimeMask_mem_v4Time, toTimeMask_cuoZong,
   structureAxis_iff_daoJin_carrier, daoJin_preserves_parity,
   full_v4_time_does_not_preserve_parity⟩

end V4Time

end SSBX.Foundation.Wen.Layered.Runtime
