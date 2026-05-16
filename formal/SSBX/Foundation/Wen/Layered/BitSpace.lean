/-
# Wen.Layered.BitSpace -- classical bit-space carrier

This is the low-level classical carrier used by the layered Wen semantics.
It intentionally does not import R8, RKernel, WenSurface, MetaInterp, or Text
modules.
-/

import SSBX.Foundation.Wen.Layered.Slot

namespace SSBX.Foundation.Wen.Layered

/-- Classical `n`-bit space.  `false` is the `o`/yang coordinate and `true`
is the `x`/yin coordinate when read through OX/R8 bridges. -/
abbrev BitSpace (n : Nat) : Type := Slot n → Bool

namespace BitSpace

def zero {n : Nat} : BitSpace n :=
  fun _ => false

def xor {n : Nat} (a b : BitSpace n) : BitSpace n :=
  fun i => Bool.xor (a i) (b i)

def single {n : Nat} (i : Slot n) : BitSpace n :=
  fun j => decide (j = i)

@[simp] theorem zero_apply {n : Nat} (i : Slot n) :
    (zero : BitSpace n) i = false := rfl

@[simp] theorem xor_apply {n : Nat} (a b : BitSpace n) (i : Slot n) :
    xor a b i = Bool.xor (a i) (b i) := rfl

@[simp] theorem single_self {n : Nat} (i : Slot n) :
    single i i = true := by
  simp [single]

theorem single_ne {n : Nat} {i j : Slot n} (h : j ≠ i) :
    single i j = false := by
  simp [single, h]

@[simp] theorem xor_zero_left {n : Nat} (x : BitSpace n) :
    xor zero x = x := by
  funext i
  simp [xor, zero]

@[simp] theorem xor_zero_right {n : Nat} (x : BitSpace n) :
    xor x zero = x := by
  funext i
  simp [xor, zero]

@[simp] theorem xor_self {n : Nat} (x : BitSpace n) :
    xor x x = zero := by
  funext i
  simp [xor, zero]

theorem xor_comm {n : Nat} (a b : BitSpace n) :
    xor a b = xor b a := by
  funext i
  simp [xor, Bool.xor_comm]

theorem xor_assoc {n : Nat} (a b c : BitSpace n) :
    xor (xor a b) c = xor a (xor b c) := by
  funext i
  cases a i <;> cases b i <;> cases c i <;> simp [xor]

theorem bitspace_summary (n : Nat) :
    (∀ x : BitSpace n, xor zero x = x)
    ∧ (∀ x : BitSpace n, xor x zero = x)
    ∧ (∀ x : BitSpace n, xor x x = zero)
    ∧ (∀ a b : BitSpace n, xor a b = xor b a)
    ∧ (∀ a b c : BitSpace n, xor (xor a b) c = xor a (xor b c)) :=
  ⟨xor_zero_left, xor_zero_right, xor_self, xor_comm, xor_assoc⟩

end BitSpace

end SSBX.Foundation.Wen.Layered
