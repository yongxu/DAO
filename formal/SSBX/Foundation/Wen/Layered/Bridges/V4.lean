/-
# Wen.Layered.Bridges.V4 -- canonical V4 as a two-bit space

This file uses `V4` from `Foundation/Hierarchy/Operators/V4/Core.lean`,
which is the constructor-style presentation of `R 2` per
`wen-substrate.md` v1.4 §3.7.8 (distinction monism).  The R-family is the
one mathematical core; `V4` here is the ergonomic 4-constructor surface
over `R 2 = Fin 2 → Bool`.

This bridge is intentionally thin: it reads the existing V4 carrier through
the layered `BitSpace 2` API without changing the V4 kernel.  Since
`BitSpace 2` is itself `Fin 2 → Bool = R 2`, the `toBitSpace`/`fromBitSpace`
pair is exactly `V4.equivR2` exposed under the layered name.
-/

import SSBX.Foundation.Hierarchy.Operators.V4.Core
import SSBX.Foundation.Wen.Layered.BitSpace

namespace SSBX.Foundation.Wen.Layered.Bridges

namespace V4

abbrev Carrier : Type := SSBX.Foundation.Hierarchy.Operators.V4

def toBitSpace (g : Carrier) : BitSpace 2 :=
  fun i =>
    match i.val with
    | 0 => SSBX.Foundation.Hierarchy.Operators.V4.contentBit g
    | 1 => SSBX.Foundation.Hierarchy.Operators.V4.frameBit g
    | _ => false

def fromBitSpace (v : BitSpace 2) : Carrier :=
  SSBX.Foundation.Hierarchy.Operators.V4.ofBits
    (v ⟨0, by decide⟩)
    (v ⟨1, by decide⟩)

@[simp] theorem fromBitSpace_toBitSpace (g : Carrier) :
    fromBitSpace (toBitSpace g) = g := by
  cases g <;> rfl

@[simp] theorem toBitSpace_fromBitSpace (v : BitSpace 2) :
    toBitSpace (fromBitSpace v) = v := by
  funext i
  fin_cases i <;>
    simp [toBitSpace, fromBitSpace,
      SSBX.Foundation.Hierarchy.Operators.V4.contentBit_ofBits,
      SSBX.Foundation.Hierarchy.Operators.V4.frameBit_ofBits]

@[simp] theorem fromBitSpace_zero :
    fromBitSpace (BitSpace.zero : BitSpace 2) =
      SSBX.Foundation.Hierarchy.Operators.V4.dao := rfl

@[simp] theorem toBitSpace_zero :
    toBitSpace SSBX.Foundation.Hierarchy.Operators.V4.dao =
      (BitSpace.zero : BitSpace 2) := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem toBitSpace_xor (a b : Carrier) :
    toBitSpace (SSBX.Foundation.Hierarchy.Operators.V4.compose a b) =
      BitSpace.xor (toBitSpace a) (toBitSpace b) := by
  funext i
  fin_cases i <;> cases a <;> cases b <;> rfl

theorem v4_bridge_summary :
    fromBitSpace (BitSpace.zero : BitSpace 2) =
      SSBX.Foundation.Hierarchy.Operators.V4.dao
    ∧ toBitSpace SSBX.Foundation.Hierarchy.Operators.V4.dao =
      (BitSpace.zero : BitSpace 2)
    ∧ (∀ g : Carrier, fromBitSpace (toBitSpace g) = g)
    ∧ (∀ v : BitSpace 2, toBitSpace (fromBitSpace v) = v)
    ∧ (∀ a b : Carrier,
        toBitSpace (SSBX.Foundation.Hierarchy.Operators.V4.compose a b) =
          BitSpace.xor (toBitSpace a) (toBitSpace b)) :=
  ⟨fromBitSpace_zero, toBitSpace_zero, fromBitSpace_toBitSpace,
   toBitSpace_fromBitSpace, toBitSpace_xor⟩

end V4

end SSBX.Foundation.Wen.Layered.Bridges
