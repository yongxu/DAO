/-
# Wen.Layered.Bridges.RootCell256 -- RootCell256 as an eight-bit space

`RootCell256 = Word64 x V4 = V4^4`, read as the six Word64 bits followed by
the two temporal V4 bits.
-/

import SSBX.Foundation.Wen.Layered.Bridges.Word64
import SSBX.Foundation.Wen.V4Kernel.Root512

namespace SSBX.Foundation.Wen.Layered.Bridges

namespace RootCell256

abbrev Carrier : Type := SSBX.Foundation.Wen.V4Kernel.Root512.RootCell256

def toExistingR8 (cell : Carrier) : SSBX.Foundation.Bagua.R8.R8 :=
  SSBX.Foundation.Wen.V4Kernel.Mode16.r8OfView cell

def fromExistingR8 (cell : SSBX.Foundation.Bagua.R8.R8) : Carrier :=
  SSBX.Foundation.Wen.V4Kernel.Mode16.viewOfR8 cell

@[simp] theorem toExistingR8_fromExistingR8
    (cell : SSBX.Foundation.Bagua.R8.R8) :
    toExistingR8 (fromExistingR8 cell) = cell :=
  SSBX.Foundation.Wen.V4Kernel.Mode16.r8OfView_viewOfR8 cell

@[simp] theorem fromExistingR8_toExistingR8 (cell : Carrier) :
    fromExistingR8 (toExistingR8 cell) = cell :=
  SSBX.Foundation.Wen.V4Kernel.Mode16.viewOfR8_r8OfView cell

def toBitSpace (cell : Carrier) : BitSpace 8 :=
  fun i =>
    match i.val with
    | 0 => SSBX.Foundation.Hierarchy.Operators.V4.contentBit cell.word.first
    | 1 => SSBX.Foundation.Hierarchy.Operators.V4.frameBit cell.word.first
    | 2 => SSBX.Foundation.Hierarchy.Operators.V4.contentBit cell.word.second
    | 3 => SSBX.Foundation.Hierarchy.Operators.V4.frameBit cell.word.second
    | 4 => SSBX.Foundation.Hierarchy.Operators.V4.contentBit cell.word.third
    | 5 => SSBX.Foundation.Hierarchy.Operators.V4.frameBit cell.word.third
    | 6 => SSBX.Foundation.Hierarchy.Operators.V4.contentBit cell.temporal
    | 7 => SSBX.Foundation.Hierarchy.Operators.V4.frameBit cell.temporal
    | _ => false

def fromBitSpace (v : BitSpace 8) : Carrier :=
  ⟨⟨SSBX.Foundation.Hierarchy.Operators.V4.ofBits
        (v ⟨0, by decide⟩) (v ⟨1, by decide⟩),
      SSBX.Foundation.Hierarchy.Operators.V4.ofBits
        (v ⟨2, by decide⟩) (v ⟨3, by decide⟩),
      SSBX.Foundation.Hierarchy.Operators.V4.ofBits
        (v ⟨4, by decide⟩) (v ⟨5, by decide⟩)⟩,
    SSBX.Foundation.Hierarchy.Operators.V4.ofBits
      (v ⟨6, by decide⟩) (v ⟨7, by decide⟩)⟩

@[simp] theorem fromBitSpace_toBitSpace (cell : Carrier) :
    fromBitSpace (toBitSpace cell) = cell := by
  cases cell with
  | mk word temporal =>
      cases word with
      | mk first second third =>
          cases first <;> cases second <;> cases third <;>
            cases temporal <;> rfl

@[simp] theorem toBitSpace_fromBitSpace (v : BitSpace 8) :
    toBitSpace (fromBitSpace v) = v := by
  funext i
  fin_cases i <;>
    simp [toBitSpace, fromBitSpace,
      SSBX.Foundation.Hierarchy.Operators.V4.contentBit_ofBits,
      SSBX.Foundation.Hierarchy.Operators.V4.frameBit_ofBits]

@[simp] theorem fromBitSpace_zero :
    fromBitSpace (BitSpace.zero : BitSpace 8) =
      SSBX.Foundation.Wen.V4Kernel.Root512.originCell := rfl

@[simp] theorem toBitSpace_zero :
    toBitSpace SSBX.Foundation.Wen.V4Kernel.Root512.originCell =
      (BitSpace.zero : BitSpace 8) := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem toBitSpace_xor (a b : Carrier) :
    toBitSpace (SSBX.Foundation.Wen.V4Kernel.Root512.composeCell a b) =
      BitSpace.xor (toBitSpace a) (toBitSpace b) := by
  funext i
  fin_cases i <;>
    simp [toBitSpace, BitSpace.xor,
      SSBX.Foundation.Wen.V4Kernel.Root512.composeCell,
      SSBX.Foundation.Wen.V4Kernel.Word64.compose,
      SSBX.Foundation.Hierarchy.Operators.V4.compose,
      SSBX.Foundation.Hierarchy.Operators.V4.contentBit_ofBits,
      SSBX.Foundation.Hierarchy.Operators.V4.frameBit_ofBits]

theorem rootCell256_bridge_summary :
    fromBitSpace (BitSpace.zero : BitSpace 8) =
      SSBX.Foundation.Wen.V4Kernel.Root512.originCell
    ∧ (∀ cell : SSBX.Foundation.Bagua.R8.R8,
      toExistingR8 (fromExistingR8 cell) = cell)
    ∧ (∀ cell : Carrier, fromExistingR8 (toExistingR8 cell) = cell)
    ∧ toBitSpace SSBX.Foundation.Wen.V4Kernel.Root512.originCell =
      (BitSpace.zero : BitSpace 8)
    ∧ (∀ cell : Carrier, fromBitSpace (toBitSpace cell) = cell)
    ∧ (∀ v : BitSpace 8, toBitSpace (fromBitSpace v) = v)
    ∧ (∀ a b : Carrier,
        toBitSpace (SSBX.Foundation.Wen.V4Kernel.Root512.composeCell a b) =
          BitSpace.xor (toBitSpace a) (toBitSpace b)) :=
  ⟨fromBitSpace_zero, toExistingR8_fromExistingR8, fromExistingR8_toExistingR8,
   toBitSpace_zero, fromBitSpace_toBitSpace,
   toBitSpace_fromBitSpace, toBitSpace_xor⟩

end RootCell256

end SSBX.Foundation.Wen.Layered.Bridges
