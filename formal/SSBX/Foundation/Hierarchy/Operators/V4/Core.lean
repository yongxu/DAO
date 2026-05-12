/-
# Operators · V4.Core -- pure Klein-four kernel

This file is the algebraic center of the two-axis V4 structure.  It does not
know about Shi, Hexagram, Turing machines, or any atlas reading.  Those modules
project this carrier into their own domains.
-/

namespace SSBX.Foundation.Hierarchy.Operators

/-! ## Carrier -/

inductive V4 where
  | dao
  | cuo
  | zong
  | cuoZong
  deriving DecidableEq, Repr

namespace V4

def all : List V4 := [.dao, .cuo, .zong, .cuoZong]

theorem all_length : all.length = 4 := rfl

/-- First coordinate: content/value duality. -/
def contentBit : V4 → Bool
  | .dao | .zong => false
  | .cuo | .cuoZong => true

/-- Second coordinate: frame/order duality. -/
def frameBit : V4 → Bool
  | .dao | .cuo => false
  | .zong | .cuoZong => true

def ofBits : Bool → Bool → V4
  | false, false => .dao
  | true, false => .cuo
  | false, true => .zong
  | true, true => .cuoZong

def compose (a b : V4) : V4 :=
  ofBits (Bool.xor (contentBit a) (contentBit b))
    (Bool.xor (frameBit a) (frameBit b))

def inv (g : V4) : V4 := g

theorem ofBits_content_frame (g : V4) :
    ofBits (contentBit g) (frameBit g) = g := by
  cases g <;> rfl

theorem contentBit_ofBits (content frame : Bool) :
    contentBit (ofBits content frame) = content := by
  cases content <;> cases frame <;> rfl

theorem frameBit_ofBits (content frame : Bool) :
    frameBit (ofBits content frame) = frame := by
  cases content <;> cases frame <;> rfl

theorem compose_dao_left (g : V4) :
    compose .dao g = g := by
  cases g <;> rfl

theorem compose_dao_right (g : V4) :
    compose g .dao = g := by
  cases g <;> rfl

theorem compose_self (g : V4) :
    compose g g = .dao := by
  cases g <;> rfl

theorem compose_comm (a b : V4) :
    compose a b = compose b a := by
  cases a <;> cases b <;> rfl

theorem compose_assoc (a b c : V4) :
    compose (compose a b) c = compose a (compose b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem cuo_zong_eq_cuoZong :
    compose .cuo .zong = .cuoZong := rfl

theorem zong_cuo_eq_cuoZong :
    compose .zong .cuo = .cuoZong := rfl

theorem cuoZong_self :
    compose .cuoZong .cuoZong = .dao := rfl

theorem v4_core_summary :
    all.length = 4
    ∧ (∀ g : V4, compose .dao g = g)
    ∧ (∀ g : V4, compose g .dao = g)
    ∧ (∀ g : V4, compose g g = .dao)
    ∧ (∀ a b : V4, compose a b = compose b a)
    ∧ (∀ a b c : V4, compose (compose a b) c = compose a (compose b c))
    ∧ compose .cuo .zong = .cuoZong := by
  exact
    ⟨ all_length
    , compose_dao_left
    , compose_dao_right
    , compose_self
    , compose_comm
    , compose_assoc
    , rfl
    ⟩

end V4

end SSBX.Foundation.Hierarchy.Operators
