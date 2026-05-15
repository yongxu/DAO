/-
# Operators · V4.OrbitBurnside -- finite fixed counts and orbit count

This sidecar keeps the 64-hexagram orbit calculation executable.  The raw
four-reading list may contain duplicates for symmetric hexagrams; distinct
readings are obtained by `eraseDups` before quotient-style counting.
-/

import SSBX.Foundation.Hierarchy.Operators.V4.Orbit

namespace SSBX.Foundation.Hierarchy.Operators

open SSBX.Foundation.Yi.Yi

namespace V4

/-- Hexagrams fixed by a V4 position, enumerated inside `Hexagram.allHex`. -/
def fixedBy (g : V4) : List Hexagram :=
  Hexagram.allHex.filter (fun h => decide (actHex g h = h))

def fixedByCount (g : V4) : Nat :=
  (fixedBy g).length

/-- The V4 readings of one hexagram with duplicate readings collapsed. -/
def hexOrbitDistinct (h : Hexagram) : List Hexagram :=
  (hexOrbit h).eraseDups

def hexOrbitDistinctCount (h : Hexagram) : Nat :=
  (hexOrbitDistinct h).length

theorem fixedBy_dao_count :
    fixedByCount .dao = 64 := by
  native_decide

theorem fixedBy_cuo_count :
    fixedByCount .cuo = 0 := by
  native_decide

theorem fixedBy_zong_count :
    fixedByCount .zong = 8 := by
  native_decide

theorem fixedBy_cuoZong_count :
    fixedByCount .cuoZong = 8 := by
  native_decide

/-- Symmetric hexagrams can have duplicate readings in the raw four-term list. -/
theorem heaven_orbit_distinct_count :
    hexOrbitDistinctCount Hexagram.heaven = 2 := by
  native_decide

/-- A concrete nonsymmetric witness has all four V4 readings distinct. -/
def freeOrbitWitness : Hexagram :=
  Hexagram.mk .yang .yang .yang .yang .yang .yin

theorem freeOrbitWitness_distinct_count :
    hexOrbitDistinctCount freeOrbitWitness = 4 := by
  native_decide

def burnsideFixedTotal : Nat :=
  fixedByCount .dao + fixedByCount .cuo + fixedByCount .zong + fixedByCount .cuoZong

def burnsideOrbitCount : Nat :=
  burnsideFixedTotal / V4.all.length

theorem burnside_fixed_total :
    burnsideFixedTotal = 80 := by
  native_decide

/-- Burnside-style finite count for the V4 action on the 64 hexagrams. -/
theorem burnside_orbit_count :
    burnsideOrbitCount = 20 := by
  native_decide

theorem orbit_burnside_summary :
    fixedByCount .dao = 64
    ∧ fixedByCount .cuo = 0
    ∧ fixedByCount .zong = 8
    ∧ fixedByCount .cuoZong = 8
    ∧ burnsideOrbitCount = 20
    ∧ hexOrbitDistinctCount Hexagram.heaven = 2
    ∧ hexOrbitDistinctCount freeOrbitWitness = 4 :=
  ⟨fixedBy_dao_count, fixedBy_cuo_count, fixedBy_zong_count,
   fixedBy_cuoZong_count, burnside_orbit_count, heaven_orbit_distinct_count,
   freeOrbitWitness_distinct_count⟩

end V4

end SSBX.Foundation.Hierarchy.Operators
