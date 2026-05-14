/-
# Operators · V4.Temporal -- temporal-coordinate projection

This file gives the canonical V4 kernel its R8 temporal-coordinate reading.
The underlying R8 carrier is still named `Shi`; the V4 architecture exposes it
through English structural names.
-/

import SSBX.Foundation.Atlas.YiLegacy.Bagua.R8
import SSBX.Foundation.Hierarchy.Operators.V4.Core

namespace SSBX.Foundation.Hierarchy.Operators

open SSBX.Foundation.Bagua.R8

namespace V4

/-- English structural name for the R8 temporal coordinate. -/
abbrev TemporalCoordinate : Type := Shi

/-- The R8 temporal-coordinate reading of the same V4 kernel. -/
def toTemporal : V4 → TemporalCoordinate
  | .dao => Shi.dao
  | .cuo => Shi.ji
  | .zong => Shi.wei
  | .cuoZong => Shi.jin

def ofTemporal (s : TemporalCoordinate) : V4 :=
  ofBits s.1 s.2

theorem ofTemporal_toTemporal (g : V4) :
    ofTemporal (toTemporal g) = g := by
  cases g <;> rfl

theorem toTemporal_ofTemporal (s : TemporalCoordinate) :
    toTemporal (ofTemporal s) = s := by
  rcases s with ⟨content, frame⟩
  cases content <;> cases frame <;> rfl

theorem toTemporal_contentBit (g : V4) :
    (toTemporal g).1 = contentBit g := by
  cases g <;> rfl

theorem toTemporal_frameBit (g : V4) :
    (toTemporal g).2 = frameBit g := by
  cases g <;> rfl

theorem toTemporal_compose (a b : V4) :
    toTemporal (compose a b) =
      (Bool.xor (toTemporal a).1 (toTemporal b).1,
       Bool.xor (toTemporal a).2 (toTemporal b).2) := by
  cases a <;> cases b <;> rfl

/-- R8's temporal coordinate is exactly the V4 two-axis coordinate. -/
theorem temporal_v4_projection :
    (∀ s : TemporalCoordinate, toTemporal (ofTemporal s) = s)
    ∧ (∀ g : V4, ofTemporal (toTemporal g) = g) :=
  ⟨toTemporal_ofTemporal, ofTemporal_toTemporal⟩

end V4

end SSBX.Foundation.Hierarchy.Operators
