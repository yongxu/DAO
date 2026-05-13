/-
# Wen.Layered.VnRn -- final Vn/Rn facade

This file exposes the spec-level `(Z/2)^n` surface over the canonical
`BitSpace` carrier.  `Vn n` is the acting XOR group and `Rn n` is the same
bit carrier read as an R-layer state space.
-/

import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Action.Defs
import SSBX.Foundation.Wen.Layered.BitSpace
import SSBX.Foundation.Wen.Layered.Bridges.V4

namespace SSBX.Foundation.Wen.Layered

/-- R-layer state space: the canonical `n`-bit carrier. -/
abbrev Rn (n : Nat) : Type := BitSpace n

/-- V-layer translation group: the same canonical `n`-bit carrier. -/
abbrev Vn (n : Nat) : Type := BitSpace n

namespace Vn

/-! ## Pointwise XOR operations -/

/-- The neutral translation. -/
def zero {n : Nat} : Vn n := BitSpace.zero

/-- Pointwise XOR, exposed under the V-layer name. -/
def xor {n : Nat} (a b : Vn n) : Vn n := BitSpace.xor a b

/-- Multiplication in `Vn n` is pointwise XOR. -/
def mul {n : Nat} (a b : Vn n) : Vn n := xor a b

/-- In `(Z/2)^n`, every translation is its own inverse. -/
def self {n : Nat} (g : Vn n) : Vn n := g

/-- The inverse operation, definitionally the self map. -/
def inv {n : Nat} (g : Vn n) : Vn n := self g

/-- The regular action of `Vn n` on `Rn n`, by XOR translation. -/
def act {n : Nat} (g : Vn n) (x : Rn n) : Rn n :=
  BitSpace.xor g x

@[simp] theorem zero_eq_bitSpace_zero {n : Nat} :
    (zero : Vn n) = BitSpace.zero := rfl

@[simp] theorem xor_eq_bitSpace_xor {n : Nat} (a b : Vn n) :
    xor a b = BitSpace.xor a b := rfl

@[simp] theorem mul_eq_xor {n : Nat} (a b : Vn n) :
    mul a b = BitSpace.xor a b := rfl

@[simp] theorem self_eq {n : Nat} (g : Vn n) :
    self g = g := rfl

@[simp] theorem inv_eq_self {n : Nat} (g : Vn n) :
    inv g = g := rfl

@[simp] theorem act_eq_xor {n : Nat} (g : Vn n) (x : Rn n) :
    act g x = BitSpace.xor g x := rfl

@[simp] theorem xor_zero_left {n : Nat} (x : Vn n) :
    xor zero x = x :=
  BitSpace.xor_zero_left x

@[simp] theorem xor_zero_right {n : Nat} (x : Vn n) :
    xor x zero = x :=
  BitSpace.xor_zero_right x

@[simp] theorem xor_self {n : Nat} (x : Vn n) :
    xor x x = zero :=
  BitSpace.xor_self x

theorem xor_comm {n : Nat} (a b : Vn n) :
    xor a b = xor b a :=
  BitSpace.xor_comm a b

theorem xor_assoc {n : Nat} (a b c : Vn n) :
    xor (xor a b) c = xor a (xor b c) :=
  BitSpace.xor_assoc a b c

@[simp] theorem act_zero {n : Nat} (x : Rn n) :
    act (zero : Vn n) x = x :=
  BitSpace.xor_zero_left x

@[simp] theorem act_self {n : Nat} (g : Vn n) (x : Rn n) :
    act g (act g x) = x := by
  rw [act, act, ← BitSpace.xor_assoc, BitSpace.xor_self, BitSpace.xor_zero_left]

theorem act_mul {n : Nat} (g h : Vn n) (x : Rn n) :
    act (mul g h) x = act g (act h x) :=
  BitSpace.xor_assoc g h x

/-! ## Mathlib-facing group and action instances -/

instance instOne (n : Nat) : One (Vn n) := ⟨zero⟩
instance instMul (n : Nat) : Mul (Vn n) := ⟨mul⟩
instance instInv (n : Nat) : Inv (Vn n) := ⟨inv⟩

@[simp] theorem one_eq_zero {n : Nat} :
    (1 : Vn n) = zero := rfl

@[simp] theorem mul_def {n : Nat} (a b : Vn n) :
    a * b = xor a b := rfl

@[simp] theorem inv_def {n : Nat} (g : Vn n) :
    g⁻¹ = g := rfl

instance instCommGroup (n : Nat) : CommGroup (Vn n) where
  mul := (· * ·)
  one := 1
  inv := Inv.inv
  npow := npowRec
  zpow := zpowRec
  mul_assoc := by
    intro a b c
    exact BitSpace.xor_assoc a b c
  one_mul := by
    intro a
    exact BitSpace.xor_zero_left a
  mul_one := by
    intro a
    exact BitSpace.xor_zero_right a
  inv_mul_cancel := by
    intro a
    exact BitSpace.xor_self a
  mul_comm := by
    intro a b
    exact BitSpace.xor_comm a b

@[simp] theorem div_def {n : Nat} (a b : Vn n) :
    a / b = xor a b := by
  simp [div_eq_mul_inv]

instance instSMulRn (n : Nat) : SMul (Vn n) (Rn n) := ⟨act⟩

@[simp] theorem smul_def {n : Nat} (g : Vn n) (x : Rn n) :
    g • x = act g x := rfl

instance instMulActionRn (n : Nat) : MulAction (Vn n) (Rn n) where
  one_smul := by
    intro x
    change act (1 : Vn n) x = x
    simp
  mul_smul := by
    intro g h x
    change act (g * h) x = act g (act h x)
    simpa using act_mul g h x

theorem action_law {n : Nat} (g h : Vn n) (x : Rn n) :
    ((g * h) • x : Rn n) = (g • (h • x : Rn n) : Rn n) :=
  mul_smul g h x

/-! ## Two-bit bridge to the canonical Klein four carrier -/

/-- The existing Klein-four carrier is equivalent to the two-bit V-layer. -/
def twoBitBridgeEquiv : Vn 2 ≃ Bridges.V4.Carrier where
  toFun := Bridges.V4.fromBitSpace
  invFun := Bridges.V4.toBitSpace
  left_inv := by
    intro v
    exact Bridges.V4.toBitSpace_fromBitSpace v
  right_inv := by
    intro g
    exact Bridges.V4.fromBitSpace_toBitSpace g

@[simp] theorem twoBitBridgeEquiv_apply (v : Vn 2) :
    twoBitBridgeEquiv v = Bridges.V4.fromBitSpace v := rfl

@[simp] theorem twoBitBridgeEquiv_symm_apply (g : Bridges.V4.Carrier) :
    twoBitBridgeEquiv.symm g = Bridges.V4.toBitSpace g := rfl

@[simp] theorem twoBitBridge_from_to (g : Bridges.V4.Carrier) :
    Bridges.V4.fromBitSpace (Bridges.V4.toBitSpace g) = g :=
  Bridges.V4.fromBitSpace_toBitSpace g

@[simp] theorem twoBitBridge_to_from (v : Vn 2) :
    Bridges.V4.toBitSpace (Bridges.V4.fromBitSpace v) = v :=
  Bridges.V4.toBitSpace_fromBitSpace v

theorem twoBitBridge_compose_mul (a b : Bridges.V4.Carrier) :
    Bridges.V4.toBitSpace
        (SSBX.Foundation.Hierarchy.Operators.V4.compose a b) =
      ((Bridges.V4.toBitSpace a : Vn 2) *
        (Bridges.V4.toBitSpace b : Vn 2)) := by
  simp [Bridges.V4.toBitSpace_xor]

theorem twoBitBridge_mul_compose (a b : Vn 2) :
    Bridges.V4.fromBitSpace (a * b) =
      SSBX.Foundation.Hierarchy.Operators.V4.compose
        (Bridges.V4.fromBitSpace a)
        (Bridges.V4.fromBitSpace b) := by
  apply twoBitBridgeEquiv.symm.injective
  simp [twoBitBridge_compose_mul (Bridges.V4.fromBitSpace a)
      (Bridges.V4.fromBitSpace b)]

/-! ## Facade summary -/

theorem vnrn_facade_summary (n : Nat) :
    Nonempty (CommGroup (Vn n))
    ∧ Nonempty (MulAction (Vn n) (Rn n))
    ∧ (∀ a b : Vn n, a * b = BitSpace.xor a b)
    ∧ (∀ g : Vn n, g⁻¹ = g)
    ∧ (∀ g : Vn n, ∀ x : Rn n, (g • x : Rn n) = BitSpace.xor g x)
    ∧ (∀ g h : Vn n, ∀ x : Rn n,
        ((g * h) • x : Rn n) = (g • (h • x : Rn n) : Rn n))
    ∧ Nonempty (Vn 2 ≃ Bridges.V4.Carrier)
    ∧ (∀ g : Bridges.V4.Carrier,
        Bridges.V4.fromBitSpace (Bridges.V4.toBitSpace g) = g)
    ∧ (∀ v : Vn 2,
        Bridges.V4.toBitSpace (Bridges.V4.fromBitSpace v) = v)
    ∧ (∀ a b : Bridges.V4.Carrier,
        Bridges.V4.toBitSpace
            (SSBX.Foundation.Hierarchy.Operators.V4.compose a b) =
          ((Bridges.V4.toBitSpace a : Vn 2) *
            (Bridges.V4.toBitSpace b : Vn 2))) :=
  ⟨⟨instCommGroup n⟩,
   ⟨instMulActionRn n⟩,
   by intro a b; rfl,
   by intro g; rfl,
   by intro g x; rfl,
   by intro g h x; exact action_law g h x,
   ⟨twoBitBridgeEquiv⟩,
   twoBitBridge_from_to,
   twoBitBridge_to_from,
   twoBitBridge_compose_mul⟩

end Vn

end SSBX.Foundation.Wen.Layered
