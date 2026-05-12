/-
# Operators · V4.Orbit -- dao row and Hexagram orbit readings
-/

import SSBX.Foundation.Hierarchy.Operators.V4.Hexagram

namespace SSBX.Foundation.Hierarchy.Operators

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8

namespace V4

/-- The R8 dao row embeds each Hexagram at the V4 identity coordinate. -/
def daoRowCell (h : Hexagram) : R8 :=
  (h, Shi.dao)

def daoRow : List R8 :=
  Hexagram.allHex.map daoRowCell

theorem daoRow_length :
    daoRow.length = 64 := by
  native_decide

/-- The four V4 readings of one hexagram.  The list may have duplicates for
frame-symmetric hexagrams; orbit quotienting is a later calculation. -/
def hexOrbit (h : Hexagram) : List Hexagram :=
  all.map (fun g => actHex g h)

theorem hexOrbit_length (h : Hexagram) :
    (hexOrbit h).length = 4 := rfl

theorem heaven_orbit_has_two_readings :
    hexOrbit Hexagram.heaven =
      [Hexagram.heaven, Hexagram.earth, Hexagram.heaven, Hexagram.earth] := rfl

theorem orbit_summary :
    daoRow.length = 64
    ∧ (∀ h : Hexagram, (hexOrbit h).length = 4)
    ∧ hexOrbit Hexagram.heaven =
      [Hexagram.heaven, Hexagram.earth, Hexagram.heaven, Hexagram.earth] :=
  ⟨daoRow_length, hexOrbit_length, heaven_orbit_has_two_readings⟩

end V4

end SSBX.Foundation.Hierarchy.Operators
