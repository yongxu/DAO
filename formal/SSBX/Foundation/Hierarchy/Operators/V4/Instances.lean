/-
# Operators · V4.Instances -- Mathlib-facing interface for canonical V4

This sidecar binds the algebra-first V4 kernel to Mathlib typeclasses.  It
does not add any domain reading to `V4.Core`; multiplication is exactly
`V4.compose`.
-/

import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Fintype.Basic
import SSBX.Foundation.Hierarchy.Operators.V4.Core

namespace SSBX.Foundation.Hierarchy.Operators

namespace V4

/-! ## Finite carrier surface -/

instance instInhabited : Inhabited V4 := ⟨.dao⟩

instance instBEq : BEq V4 where
  beq a b := decide (a = b)

instance instFintype : Fintype V4 where
  elems := all.toFinset
  complete := by
    intro g
    cases g <;> simp [all]

/-! ## Multiplicative Klein-four surface -/

instance instOne : One V4 := ⟨.dao⟩
instance instMul : Mul V4 := ⟨compose⟩
instance instInv : Inv V4 := ⟨inv⟩

@[simp] theorem one_eq_dao : (1 : V4) = .dao := rfl

@[simp] theorem mul_eq_compose (a b : V4) :
    a * b = compose a b := rfl

@[simp] theorem inv_eq_self (g : V4) :
    g⁻¹ = g := rfl

instance instCommGroup : CommGroup V4 where
  mul := (· * ·)
  one := 1
  inv := Inv.inv
  npow := npowRec
  zpow := zpowRec
  mul_assoc := by
    intro a b c
    exact compose_assoc a b c
  one_mul := by
    intro a
    exact compose_dao_left a
  mul_one := by
    intro a
    exact compose_dao_right a
  inv_mul_cancel := by
    intro a
    exact compose_self a
  mul_comm := by
    intro a b
    exact compose_comm a b

/-! ## Boolean coordinate equivalence -/

/-- Canonical coordinates for the Klein four group: content bit × frame bit. -/
def boolPairEquiv : V4 ≃ Bool × Bool where
  toFun := fun g => (contentBit g, frameBit g)
  invFun := fun p => ofBits p.1 p.2
  left_inv := ofBits_content_frame
  right_inv := by
    intro p
    rcases p with ⟨content, frame⟩
    cases content <;> cases frame <;> rfl

@[simp] theorem boolPairEquiv_apply (g : V4) :
    boolPairEquiv g = (contentBit g, frameBit g) := rfl

@[simp] theorem boolPairEquiv_symm_apply (content frame : Bool) :
    boolPairEquiv.symm (content, frame) = ofBits content frame := rfl

theorem boolPairEquiv_mul (a b : V4) :
    boolPairEquiv (a * b) =
      (Bool.xor (boolPairEquiv a).1 (boolPairEquiv b).1,
       Bool.xor (boolPairEquiv a).2 (boolPairEquiv b).2) := by
  cases a <;> cases b <;> rfl

/-- Phase-1 finite group surface, without importing any domain action module. -/
theorem finite_group_surface :
    Nonempty (Fintype V4)
    ∧ Nonempty (CommGroup V4)
    ∧ Nonempty (V4 ≃ Bool × Bool)
    ∧ (∀ a b : V4, a * b = compose a b)
    ∧ (∀ g : V4, g⁻¹ = g) :=
  ⟨⟨instFintype⟩, ⟨instCommGroup⟩, ⟨boolPairEquiv⟩, mul_eq_compose, inv_eq_self⟩

end V4

end SSBX.Foundation.Hierarchy.Operators
