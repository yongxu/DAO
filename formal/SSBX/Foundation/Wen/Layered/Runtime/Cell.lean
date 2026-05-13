/-
# Wen.Layered.Runtime.Cell -- BitVec-backed runtime cells
-/

import Batteries.Data.BitVec
import SSBX.Foundation.Wen.Layered.BitSpace

namespace SSBX.Foundation.Wen.Layered.Runtime

/-- Runtime carrier for an `n`-bit cell. -/
abbrev Cell (n : Nat) : Type := BitVec n

/-- Read a runtime cell as the Layered specification bit-space. -/
def toSpec {n : Nat} (c : Cell n) : BitSpace n :=
  fun i => c.getLsb i

/-- Pack a Layered specification bit-space into the runtime cell carrier. -/
def ofSpec {n : Nat} (v : BitSpace n) : Cell n :=
  BitVec.ofFnLE v

@[simp] theorem toSpec_ofSpec {n : Nat} (v : BitSpace n) :
  toSpec (ofSpec v) = v := by
  funext i
  simp [toSpec, ofSpec]

@[simp] theorem ofSpec_toSpec {n : Nat} (c : Cell n) :
    ofSpec (toSpec c) = c := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp [toSpec, ofSpec, BitVec.getLsb_eq_getElem]

theorem eq_of_toSpec_eq {n : Nat} {a b : Cell n}
    (h : toSpec a = toSpec b) : a = b := by
  rw [← ofSpec_toSpec a, h, ofSpec_toSpec b]

theorem toSpec_injective {n : Nat} :
    Function.Injective (toSpec : Cell n → BitSpace n) :=
  fun _ _ h => eq_of_toSpec_eq h

end SSBX.Foundation.Wen.Layered.Runtime
