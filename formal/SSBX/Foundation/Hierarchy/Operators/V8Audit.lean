/-
# Operators · V8Audit -- naming and metadata boundary for V8/R8 views

This module records implementation-facing audit facts for the V8 = R6 + V4
view without renaming the existing R8 carrier or changing VM semantics.
-/

import SSBX.Foundation.Bagua.R8
import SSBX.Foundation.Hierarchy.Operators.V4.V8Bridge

namespace SSBX.Foundation.Hierarchy.Operators

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8

namespace V8Audit

/-! ## OX convention -/

/-- In OX strings, `o` is the Yang bit, encoded as `false`. -/
def oxYangChar : Char := 'o'

/-- In OX strings, `x` is the Yin bit, encoded as `true`. -/
def oxYinChar : Char := 'x'

theorem ox_char_convention :
    oxYangChar = 'o' ∧ oxYinChar = 'x' :=
  ⟨rfl, rfl⟩

/-! ## Coordinate sort separation -/

inductive CoordinateSort where
  | hexagram
  | temporal
  deriving DecidableEq, Repr

/-- V8 coordinates 0..5 are the R6 hexagram component; 6..7 are the V4
temporal component. -/
def coordinateSort (i : Fin 8) : CoordinateSort :=
  if i.val < 6 then .hexagram else .temporal

theorem y7_sort_temporal :
    coordinateSort V8Info.y7 = .temporal := by
  native_decide

theorem y8_sort_temporal :
    coordinateSort V8Info.y8 = .temporal := by
  native_decide

/-! ## Reserved high-symmetry masks -/

def identityMask : V8 := V8Info.zero

/-- Toggle all six R6 hexagram bits and leave the temporal V4 component fixed. -/
def hexagramComplementMask : V8 :=
  fun i => decide (i.val < 6)

/-- Toggle only the V4 temporal component. -/
def temporalPlaneMask : V8 :=
  fun i => decide (6 ≤ i.val)

def totalComplementMask : V8 :=
  fun _ => true

def compoundTemporalMask : V8 := V8Info.parityMask

theorem reserved_mask_summary :
    identityMask = V8Info.zero
    ∧ compoundTemporalMask = V8Info.parityMask
    ∧ V8Info.offTimeZero compoundTemporalMask :=
  ⟨rfl, rfl, by
    intro i hi7 hi8
    simp [compoundTemporalMask, V8Info.parityMask, V8Info.xor, V8Info.single,
      hi7, hi8]⟩

/-! ## R8 component metadata -/

/-- Existing R8 cells expose an R6 hexagram component. -/
def r6Component (c : R8) : Hexagram := c.1

/-- Existing R8 cells expose a canonical V4 temporal component. -/
def v4Component (c : R8) : V4 := V4.ofTemporal c.2

def cellOfComponents (h : Hexagram) (g : V4) : R8 :=
  (h, V4.toTemporal g)

theorem r6Component_cellOfComponents (h : Hexagram) (g : V4) :
    r6Component (cellOfComponents h g) = h := rfl

theorem v4Component_cellOfComponents (h : Hexagram) (g : V4) :
    v4Component (cellOfComponents h g) = g := by
  simp [v4Component, cellOfComponents, V4.ofTemporal_toTemporal]

theorem cellOfComponents_components (c : R8) :
    cellOfComponents (r6Component c) (v4Component c) = c := by
  rcases c with ⟨h, temporal⟩
  simp [cellOfComponents, r6Component, v4Component, V4.toTemporal_ofTemporal]

theorem component_metadata_summary :
    (∀ h g, r6Component (cellOfComponents h g) = h)
    ∧ (∀ h g, v4Component (cellOfComponents h g) = g)
    ∧ (∀ c : R8, cellOfComponents (r6Component c) (v4Component c) = c) :=
  ⟨r6Component_cellOfComponents, v4Component_cellOfComponents,
   cellOfComponents_components⟩

end V8Audit

end SSBX.Foundation.Hierarchy.Operators

