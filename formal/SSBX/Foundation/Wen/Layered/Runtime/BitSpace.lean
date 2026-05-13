/-
# Wen.Layered.Runtime.BitSpace -- runtime bit-space operations
-/

import SSBX.Foundation.Wen.Layered.Runtime.Cell

namespace SSBX.Foundation.Wen.Layered.Runtime

def zero {n : Nat} : Cell n :=
  ofSpec BitSpace.zero

def xor {n : Nat} (a b : Cell n) : Cell n :=
  ofSpec (BitSpace.xor (toSpec a) (toSpec b))

def single {n : Nat} (i : Slot n) : Cell n :=
  ofSpec (BitSpace.single i)

@[simp] theorem toSpec_zero {n : Nat} :
    toSpec (zero : Cell n) = BitSpace.zero := by
  simp [zero]

@[simp] theorem toSpec_xor {n : Nat} (a b : Cell n) :
    toSpec (xor a b) = BitSpace.xor (toSpec a) (toSpec b) := by
  simp [xor]

@[simp] theorem toSpec_single {n : Nat} (i : Slot n) :
    toSpec (single i) = BitSpace.single i := by
  simp [single]

end SSBX.Foundation.Wen.Layered.Runtime
