/-
# Wen.Layered.Runtime.Split -- runtime outer/inner decomposition
-/

import SSBX.Foundation.Wen.Layered.Runtime.BitSpace
import SSBX.Foundation.Wen.Layered.Split

namespace SSBX.Foundation.Wen.Layered.Runtime

def outer {n : Nat} (v : Cell (2 * n)) : Cell n :=
  ofSpec (BitSpace.outer (toSpec v))

def inner {n : Nat} (v : Cell (2 * n)) : Cell n :=
  ofSpec (BitSpace.inner (toSpec v))

def split {n : Nat} (v : Cell (2 * n)) : Cell n × Cell n :=
  (outer v, inner v)

def combine {n : Nat} (o i : Cell n) : Cell (2 * n) :=
  ofSpec (BitSpace.combine (toSpec o) (toSpec i))

@[simp] theorem toSpec_outer {n : Nat} (v : Cell (2 * n)) :
    toSpec (outer v) = BitSpace.outer (toSpec v) := by
  simp [outer]

@[simp] theorem toSpec_inner {n : Nat} (v : Cell (2 * n)) :
    toSpec (inner v) = BitSpace.inner (toSpec v) := by
  simp [inner]

@[simp] theorem toSpec_split {n : Nat} (v : Cell (2 * n)) :
    (toSpec (split v).1, toSpec (split v).2) =
      (BitSpace.outer (toSpec v), BitSpace.inner (toSpec v)) := by
  simp [split]

@[simp] theorem toSpec_combine {n : Nat} (o i : Cell n) :
    toSpec (combine o i) = BitSpace.combine (toSpec o) (toSpec i) := by
  simp [combine]

@[simp] theorem outer_combine {n : Nat} (o i : Cell n) :
    outer (combine o i) = o := by
  apply eq_of_toSpec_eq
  simp

@[simp] theorem inner_combine {n : Nat} (o i : Cell n) :
    inner (combine o i) = i := by
  apply eq_of_toSpec_eq
  simp

@[simp] theorem combine_outer_inner {n : Nat} (v : Cell (2 * n)) :
    combine (outer v) (inner v) = v := by
  apply eq_of_toSpec_eq
  simp

end SSBX.Foundation.Wen.Layered.Runtime
