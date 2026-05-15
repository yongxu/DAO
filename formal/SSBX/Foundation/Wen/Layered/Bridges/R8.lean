/-
# Wen.Layered.Bridges.R8 -- existing R8 carrier as an eight-bit space

The coordinate order is the v3 OX/R8 order:
`y1 y2 y3 y4 y5 y6 yin guo`, with `false = o/yang`.
-/

import SSBX.Foundation.Atlas.Yi.Classical.Cells.R8
import SSBX.Foundation.Hierarchy.Operators.V4.Temporal
import SSBX.Foundation.Wen.Layered.BitSpace

namespace SSBX.Foundation.Wen.Layered.Bridges

namespace R8

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Hierarchy.Operators

abbrev Carrier : Type := SSBX.Foundation.Bagua.R8.R8
abbrev Yao : Type := SSBX.Foundation.Yi.Yi.Yao

/-! ## OX convention and coordinate audit -/

/-- In OX strings, `o` is the Yang bit, encoded as `false`. -/
def oxYangChar : Char := 'o'

/-- In OX strings, `x` is the Yin bit, encoded as `true`. -/
def oxYinChar : Char := 'x'

theorem ox_char_convention :
    oxYangChar = 'o' ∧ oxYinChar = 'x' :=
  ⟨rfl, rfl⟩

inductive CoordinateSort where
  | hexagram
  | temporal
  deriving DecidableEq, Repr

/-- R8 coordinates 0..5 are the R6 hexagram component; 6..7 are the V4
temporal component. -/
def coordinateSort (i : Slot 8) : CoordinateSort :=
  if i.val < 6 then .hexagram else .temporal

def y7 : Slot 8 := ⟨6, by decide⟩
def y8 : Slot 8 := ⟨7, by decide⟩

theorem y7_sort_temporal :
    coordinateSort y7 = .temporal := by
  native_decide

theorem y8_sort_temporal :
    coordinateSort y8 = .temporal := by
  native_decide

def identityMask : BitSpace 8 := BitSpace.zero

/-- Toggle all six R6 hexagram bits and leave the temporal V4 component fixed. -/
def hexagramComplementMask : BitSpace 8 :=
  fun i => decide (i.val < 6)

/-- Toggle only the V4 temporal component. -/
def temporalPlaneMask : BitSpace 8 :=
  fun i => decide (6 ≤ i.val)

def totalComplementMask : BitSpace 8 :=
  fun _ => true

def compoundTemporalMask : BitSpace 8 :=
  BitSpace.xor (BitSpace.single y7) (BitSpace.single y8)

def offTimeZero (g : BitSpace 8) : Prop :=
  ∀ i : Slot 8, i ≠ y7 → i ≠ y8 → g i = false

theorem reserved_mask_summary :
    identityMask = BitSpace.zero
    ∧ compoundTemporalMask =
      BitSpace.xor (BitSpace.single y7) (BitSpace.single y8)
    ∧ offTimeZero compoundTemporalMask :=
  ⟨rfl, rfl, by
    intro i hi7 hi8
    simp [compoundTemporalMask, BitSpace.xor, BitSpace.single, hi7, hi8]⟩

def boolOfYao : Yao → Bool
  | .yang => false
  | .yin => true

def yaoOfBool : Bool → Yao
  | false => .yang
  | true => .yin

@[simp] theorem boolOfYao_yaoOfBool (b : Bool) :
    boolOfYao (yaoOfBool b) = b := by
  cases b <;> rfl

@[simp] theorem yaoOfBool_boolOfYao (y : Yao) :
    yaoOfBool (boolOfYao y) = y := by
  cases y <;> rfl

@[simp] theorem boolOfYao_yaoXor (a b : Yao) :
    boolOfYao (SSBX.Foundation.Bagua.R8.R8.yaoXor a b) =
      Bool.xor (boolOfYao a) (boolOfYao b) := by
  cases a <;> cases b <;> rfl

def toBitSpace (c : Carrier) : BitSpace 8 :=
  fun i =>
    match i.val with
    | 0 => boolOfYao c.1.y1
    | 1 => boolOfYao c.1.y2
    | 2 => boolOfYao c.1.y3
    | 3 => boolOfYao c.1.y4
    | 4 => boolOfYao c.1.y5
    | 5 => boolOfYao c.1.y6
    | 6 => c.2.1
    | 7 => c.2.2
    | _ => false

def fromBitSpace (v : BitSpace 8) : Carrier :=
  (SSBX.Foundation.Yi.Yi.Hexagram.mk
     (yaoOfBool (v ⟨0, by decide⟩))
     (yaoOfBool (v ⟨1, by decide⟩))
     (yaoOfBool (v ⟨2, by decide⟩))
     (yaoOfBool (v ⟨3, by decide⟩))
     (yaoOfBool (v ⟨4, by decide⟩))
     (yaoOfBool (v ⟨5, by decide⟩)),
   (v ⟨6, by decide⟩, v ⟨7, by decide⟩))

@[simp] theorem fromBitSpace_toBitSpace (c : Carrier) :
    fromBitSpace (toBitSpace c) = c := by
  rcases c with ⟨h, s⟩
  rcases s with ⟨yin, guo⟩
  have heq : h = SSBX.Foundation.Yi.Yi.Hexagram.mk h.y1 h.y2 h.y3 h.y4 h.y5 h.y6 := by
    apply SSBX.Foundation.Yi.Yi.Hexagram.ext <;> rfl
  show fromBitSpace (toBitSpace (h, yin, guo)) = (h, yin, guo)
  rw [heq]
  cases h.y1 <;> cases h.y2 <;> cases h.y3 <;> cases h.y4 <;>
    cases h.y5 <;> cases h.y6 <;> cases yin <;> cases guo <;> rfl

@[simp] theorem toBitSpace_fromBitSpace (v : BitSpace 8) :
    toBitSpace (fromBitSpace v) = v := by
  funext i
  fin_cases i <;> simp [toBitSpace, fromBitSpace]

@[simp] theorem fromBitSpace_zero :
    fromBitSpace (BitSpace.zero : BitSpace 8) =
      SSBX.Foundation.Bagua.R8.R8.origin := rfl

@[simp] theorem toBitSpace_zero :
    toBitSpace SSBX.Foundation.Bagua.R8.R8.origin =
      (BitSpace.zero : BitSpace 8) := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem toBitSpace_xor (a b : Carrier) :
    toBitSpace (SSBX.Foundation.Bagua.R8.R8.xor a b) =
      BitSpace.xor (toBitSpace a) (toBitSpace b) := by
  funext i
  fin_cases i <;>
    simp [toBitSpace, SSBX.Foundation.Bagua.R8.R8.xor,
      SSBX.Foundation.Bagua.R8.R8.hexXor,
      SSBX.Foundation.Bagua.R8.R8.shiXor,
      SSBX.Foundation.Bagua.R8.Shi.toYinGuo,
      SSBX.Foundation.Bagua.R8.Shi.ofYinGuo, BitSpace.xor]

theorem r8_bridge_summary :
    fromBitSpace (BitSpace.zero : BitSpace 8) =
      SSBX.Foundation.Bagua.R8.R8.origin
    ∧ toBitSpace SSBX.Foundation.Bagua.R8.R8.origin =
      (BitSpace.zero : BitSpace 8)
    ∧ (∀ c : Carrier, fromBitSpace (toBitSpace c) = c)
    ∧ (∀ v : BitSpace 8, toBitSpace (fromBitSpace v) = v)
    ∧ (∀ a b : Carrier,
        toBitSpace (SSBX.Foundation.Bagua.R8.R8.xor a b) =
          BitSpace.xor (toBitSpace a) (toBitSpace b)) :=
  ⟨fromBitSpace_zero, toBitSpace_zero, fromBitSpace_toBitSpace,
   toBitSpace_fromBitSpace, toBitSpace_xor⟩

/-! ## Existing R8 component metadata -/

/-- Existing R8 cells expose an R6 hexagram component. -/
def r6Component (c : Carrier) : Hexagram := c.1

/-- Existing R8 cells expose a canonical V4 temporal component. -/
def v4Component (c : Carrier) : V4 := V4.ofTemporal c.2

def cellOfComponents (h : Hexagram) (g : V4) : Carrier :=
  (h, V4.toTemporal g)

theorem r6Component_cellOfComponents (h : Hexagram) (g : V4) :
    r6Component (cellOfComponents h g) = h := rfl

theorem v4Component_cellOfComponents (h : Hexagram) (g : V4) :
    v4Component (cellOfComponents h g) = g := by
  simp [v4Component, cellOfComponents, V4.ofTemporal_toTemporal]

theorem cellOfComponents_components (c : Carrier) :
    cellOfComponents (r6Component c) (v4Component c) = c := by
  rcases c with ⟨h, temporal⟩
  simp [cellOfComponents, r6Component, v4Component, V4.toTemporal_ofTemporal]

theorem component_metadata_summary :
    (∀ h g, r6Component (cellOfComponents h g) = h)
    ∧ (∀ h g, v4Component (cellOfComponents h g) = g)
    ∧ (∀ c : Carrier, cellOfComponents (r6Component c) (v4Component c) = c) :=
  ⟨r6Component_cellOfComponents, v4Component_cellOfComponents,
   cellOfComponents_components⟩

end R8

end SSBX.Foundation.Wen.Layered.Bridges
