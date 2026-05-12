/-
# Operators · Interlace -- non-V4 inner-trigram projection

Interlace is deliberately outside the V4 module tree.  It is a canonical
outer Hexagram operation, but it is not an element of the Klein-four group:
it is not modeled here as a V4 action.
-/

import SSBX.Foundation.Bagua.R8
import SSBX.Foundation.Bagua.R7

namespace SSBX.Foundation.Hierarchy.Operators.Interlace

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.R7

/-- Interlace: inner-trigram extraction. -/
def hex_hu (h : Hexagram) : Hexagram := Hexagram.interlace h

/-- Interlace lifted to R7. -/
def cell128_hu (c : R7) : R7 := hexHu c

/-- Interlace lifted to R8. -/
def cell256_hu (c : R8) : R8 := R8.hexHu c

theorem hu_fixed_iff (h : Hexagram) :
    hex_hu h = h ↔ h = Hexagram.heaven ∨ h = Hexagram.earth :=
  Hexagram.interlace_fixed_point h

theorem interlace_summary :
    (∀ h : Hexagram, hex_hu h = h ↔ h = Hexagram.heaven ∨ h = Hexagram.earth)
    ∧ (∀ c : R7, cell128_hu c = hexHu c)
    ∧ (∀ c : R8, cell256_hu c = R8.hexHu c) :=
  ⟨hu_fixed_iff, fun _ => rfl, fun _ => rfl⟩

end SSBX.Foundation.Hierarchy.Operators.Interlace
