/-
# Operators · V4.V8Bridge -- element-level V4 to V8 time-plane bridge

This sidecar connects the element-level `{dao, cuoZong}` preservation axis to
the state-level `{dao, jin}` parity subgroup in `V8Info`.
-/

import SSBX.Foundation.Hierarchy.Operators.V4.PreservationLogic
import SSBX.Foundation.Hierarchy.Operators.V4.Temporal
import SSBX.Foundation.Hierarchy.Operators.V8Info
import SSBX.Foundation.Wen.Layered.Bridges.V4Time

namespace SSBX.Foundation.Hierarchy.Operators

namespace V4

open V8Info

/-- Embed the canonical V4 element into the V8 y7/y8 time plane. -/
def toV8TimeMask (g : V4) : V8 :=
  fun i =>
    if i = V8Info.y7 then contentBit g
    else if i = V8Info.y8 then frameBit g
    else false

theorem toV8TimeMask_offTimeZero (g : V4) :
    V8Info.offTimeZero (toV8TimeMask g) := by
  intro i hi7 hi8
  simp [toV8TimeMask, hi7, hi8]

theorem toV8TimeMask_mem_v4Time (g : V4) :
    V8Info.v4Time.carrier (toV8TimeMask g) :=
  toV8TimeMask_offTimeZero g

theorem toV8TimeMask_dao :
    toV8TimeMask .dao = V8Info.zero := by
  funext i
  by_cases h7 : i = V8Info.y7
  · subst i
    rfl
  · by_cases h8 : i = V8Info.y8
    · subst i
      rfl
    · simp [toV8TimeMask, V8Info.zero, h7, h8]

theorem toV8TimeMask_cuo :
    toV8TimeMask .cuo = V8Info.timeY7Mask := by
  funext i
  by_cases h7 : i = V8Info.y7
  · subst i
    rfl
  · by_cases h8 : i = V8Info.y8
    · subst i
      rfl
    · simp [toV8TimeMask, V8Info.timeY7Mask, V8Info.single, h7, h8]

theorem toV8TimeMask_zong :
    toV8TimeMask .zong = V8Info.timeY8Mask := by
  funext i
  by_cases h7 : i = V8Info.y7
  · subst i
    rfl
  · by_cases h8 : i = V8Info.y8
    · subst i
      rfl
    · simp [toV8TimeMask, V8Info.timeY8Mask, V8Info.single, h7, h8]

theorem toV8TimeMask_cuoZong :
    toV8TimeMask .cuoZong = V8Info.parityMask := by
  funext i
  by_cases h7 : i = V8Info.y7
  · subst i
    rfl
  · by_cases h8 : i = V8Info.y8
    · subst i
      rfl
    · simp [toV8TimeMask, V8Info.parityMask, V8Info.xor, V8Info.single, h7, h8]

theorem daoJin_carrier_toV8TimeMask_iff_equalBits (g : V4) :
    V8Info.daoJin.carrier (toV8TimeMask g) ↔ contentBit g = frameBit g := by
  constructor
  · intro h
    have hy := h.2
    simpa [toV8TimeMask, V8Info.y7, V8Info.y8, V8Info.bit] using hy
  · intro heq
    constructor
    · exact toV8TimeMask_offTimeZero g
    · simp [toV8TimeMask, V8Info.y7, V8Info.y8, V8Info.bit, heq]

/-- Element-level `{dao, cuoZong}` maps exactly to the state-level
`{dao, jin}` parity subgroup. -/
theorem structureAxis_iff_daoJin_carrier (g : V4) :
    V8Info.daoJin.carrier (toV8TimeMask g) ↔ structurePreservingAxis g := by
  rw [daoJin_carrier_toV8TimeMask_iff_equalBits,
    structurePreservingAxis_iff_equalBits]

theorem structureAxis_maps_to_daoJin {g : V4}
    (hg : structurePreservingAxis g) :
    V8Info.daoJin.carrier (toV8TimeMask g) :=
  (structureAxis_iff_daoJin_carrier g).mpr hg

theorem daoJin_preimage_is_structureAxis {g : V4}
    (hg : V8Info.daoJin.carrier (toV8TimeMask g)) :
    structurePreservingAxis g :=
  (structureAxis_iff_daoJin_carrier g).mp hg

/-- The temporal V8 reading of `zong` is a y8 time-plane mask.  This is
separate from hexagram line reversal, which is an action/permutation layer and
not an XOR mask on the six hexagram coordinates. -/
theorem zong_temporal_mask_only :
    toV8TimeMask .zong = V8Info.timeY8Mask :=
  toV8TimeMask_zong

theorem v4_v8_bridge_summary :
    (∀ g : V4, V8Info.v4Time.carrier (toV8TimeMask g))
    ∧ toV8TimeMask .dao = V8Info.zero
    ∧ toV8TimeMask .cuoZong = V8Info.parityMask
    ∧ (∀ g : V4,
      V8Info.daoJin.carrier (toV8TimeMask g) ↔ structurePreservingAxis g) :=
  ⟨toV8TimeMask_mem_v4Time, toV8TimeMask_dao, toV8TimeMask_cuoZong,
   structureAxis_iff_daoJin_carrier⟩

/-! ## Phase 8 layered compatibility anchors -/

theorem toV8TimeMask_eq_layered_toTimeMask (g : V4) :
    toV8TimeMask g =
      SSBX.Foundation.Wen.Layered.V4Time.toTimeMask g := by
  funext i
  cases g <;> fin_cases i <;> rfl

theorem structureAxis_iff_layered_daoJin_carrier (g : V4) :
    SSBX.Foundation.Wen.Layered.V4Time.daoJin.carrier
        (SSBX.Foundation.Wen.Layered.V4Time.toTimeMask g)
      ↔ structurePreservingAxis g :=
  SSBX.Foundation.Wen.Layered.V4Time.structureAxis_iff_daoJin_carrier g

theorem layered_v4_v8_bridge_summary :
    (∀ g : V4,
      toV8TimeMask g =
        SSBX.Foundation.Wen.Layered.V4Time.toTimeMask g)
    ∧ (∀ g : V4,
      SSBX.Foundation.Wen.Layered.V4Time.daoJin.carrier
          (SSBX.Foundation.Wen.Layered.V4Time.toTimeMask g)
        ↔ structurePreservingAxis g) :=
  ⟨toV8TimeMask_eq_layered_toTimeMask,
   structureAxis_iff_layered_daoJin_carrier⟩

end V4

end SSBX.Foundation.Hierarchy.Operators
