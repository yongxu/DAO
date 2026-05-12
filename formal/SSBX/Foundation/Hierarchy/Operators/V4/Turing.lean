/-
# Operators · V4.Turing -- reversible two-symbol local action

The Turing-machine local action is a projection into the canonical V4 kernel:
one bit flips the tape symbol, the other flips the move direction.
-/

import SSBX.Foundation.Hierarchy.Operators.V4.Temporal

namespace SSBX.Foundation.Hierarchy.Operators

inductive TapeBit where
  | zero
  | one
  deriving DecidableEq, Repr

namespace TapeBit

def flip : TapeBit → TapeBit
  | .zero => .one
  | .one => .zero

theorem flip_flip (b : TapeBit) : flip (flip b) = b := by
  cases b <;> rfl

end TapeBit

inductive MoveDir where
  | left
  | right
  deriving DecidableEq, Repr

namespace MoveDir

def flip : MoveDir → MoveDir
  | .left => .right
  | .right => .left

theorem flip_flip (d : MoveDir) : flip (flip d) = d := by
  cases d <;> rfl

end MoveDir

/-- Minimal reversible local action: flip written bit and/or move direction. -/
abbrev TMV4Action : Type :=
  Bool × Bool

namespace TMV4Action

def nop : TMV4Action := (false, false)
def flipBit : TMV4Action := (true, false)
def flipDir : TMV4Action := (false, true)
def flipBoth : TMV4Action := (true, true)

def compose (a b : TMV4Action) : TMV4Action :=
  (Bool.xor a.1 b.1, Bool.xor a.2 b.2)

def apply (a : TMV4Action) (s : TapeBit × MoveDir) : TapeBit × MoveDir :=
  (if a.1 then TapeBit.flip s.1 else s.1,
   if a.2 then MoveDir.flip s.2 else s.2)

def toV4 : TMV4Action → V4
  | (false, false) => .dao
  | (true, false) => .cuo
  | (false, true) => .zong
  | (true, true) => .cuoZong

def ofV4 : V4 → TMV4Action
  | .dao => nop
  | .cuo => flipBit
  | .zong => flipDir
  | .cuoZong => flipBoth

theorem toV4_ofV4 (g : V4) :
    toV4 (ofV4 g) = g := by
  cases g <;> rfl

theorem ofV4_toV4 (a : TMV4Action) :
    ofV4 (toV4 a) = a := by
  rcases a with ⟨x, z⟩
  cases x <;> cases z <;> rfl

theorem toV4_compose (a b : TMV4Action) :
    toV4 (compose a b) = V4.compose (toV4 a) (toV4 b) := by
  rcases a with ⟨x1, z1⟩
  rcases b with ⟨x2, z2⟩
  cases x1 <;> cases z1 <;> cases x2 <;> cases z2 <;> rfl

theorem compose_nop_right (a : TMV4Action) :
    compose a nop = a := by
  rcases a with ⟨x, z⟩
  cases x <;> cases z <;> rfl

theorem compose_nop_left (a : TMV4Action) :
    compose nop a = a := by
  rcases a with ⟨x, z⟩
  cases x <;> cases z <;> rfl

theorem compose_self (a : TMV4Action) :
    compose a a = nop := by
  rcases a with ⟨x, z⟩
  cases x <;> cases z <;> rfl

theorem compose_comm (a b : TMV4Action) :
    compose a b = compose b a := by
  rcases a with ⟨x1, z1⟩
  rcases b with ⟨x2, z2⟩
  cases x1 <;> cases z1 <;> cases x2 <;> cases z2 <;> rfl

theorem compose_assoc (a b c : TMV4Action) :
    compose (compose a b) c = compose a (compose b c) := by
  rcases a with ⟨x1, z1⟩
  rcases b with ⟨x2, z2⟩
  rcases c with ⟨x3, z3⟩
  cases x1 <;> cases z1 <;> cases x2 <;> cases z2 <;>
    cases x3 <;> cases z3 <;> rfl

theorem apply_compose (a b : TMV4Action) (s : TapeBit × MoveDir) :
    apply (compose a b) s = apply a (apply b s) := by
  rcases a with ⟨x1, z1⟩
  rcases b with ⟨x2, z2⟩
  rcases s with ⟨bit, dir⟩
  cases x1 <;> cases z1 <;> cases x2 <;> cases z2 <;>
    cases bit <;> cases dir <;> rfl

/-- Reversible TM local actions use the same R8 temporal-coordinate V4 carrier. -/
def toTemporal (a : TMV4Action) : V4.TemporalCoordinate :=
  V4.toTemporal (toV4 a)

theorem toTemporal_nop :
    toTemporal nop = SSBX.Foundation.Bagua.R8.Shi.dao := rfl

theorem toTemporal_flipBit :
    toTemporal flipBit = SSBX.Foundation.Bagua.R8.Shi.ji := rfl

theorem toTemporal_flipDir :
    toTemporal flipDir = SSBX.Foundation.Bagua.R8.Shi.wei := rfl

theorem toTemporal_flipBoth :
    toTemporal flipBoth = SSBX.Foundation.Bagua.R8.Shi.jin := rfl

theorem toTemporal_compose (a b : TMV4Action) :
    toTemporal (compose a b) =
      (Bool.xor (toTemporal a).1 (toTemporal b).1,
       Bool.xor (toTemporal a).2 (toTemporal b).2) := by
  rcases a with ⟨x1, z1⟩
  rcases b with ⟨x2, z2⟩
  cases x1 <;> cases z1 <;> cases x2 <;> cases z2 <;> rfl

/-- A lightweight permutation record for the state-controller skeleton. -/
structure StatePerm (Q : Type) where
  toFun : Q → Q
  invFun : Q → Q
  left_inv : ∀ q, invFun (toFun q) = q
  right_inv : ∀ q, toFun (invFun q) = q

/-- Adding a finite state controller gives the usual wreath-product carrier:
one local V4 action per state, together with a state permutation. -/
abbrev WreathCarrier (Q : Type) : Type :=
  Prod (Q → TMV4Action) (StatePerm Q)

theorem reversible_tm_v4_summary :
    (toV4 flipBoth = V4.cuoZong)
    ∧ (∀ a : TMV4Action, compose a nop = a)
    ∧ (∀ a : TMV4Action, compose a a = nop)
    ∧ (∀ a b : TMV4Action, compose a b = compose b a)
    ∧ (∀ a b c : TMV4Action, compose (compose a b) c = compose a (compose b c))
    ∧ (∀ a b : TMV4Action, toV4 (compose a b) = V4.compose (toV4 a) (toV4 b))
    ∧ (∀ a b s, apply (compose a b) s = apply a (apply b s))
    ∧ (toTemporal flipBit = SSBX.Foundation.Bagua.R8.Shi.ji)
    ∧ (toTemporal flipDir = SSBX.Foundation.Bagua.R8.Shi.wei)
    ∧ (toTemporal flipBoth = SSBX.Foundation.Bagua.R8.Shi.jin) := by
  exact
    ⟨ rfl
    , compose_nop_right
    , compose_self
    , compose_comm
    , compose_assoc
    , toV4_compose
    , apply_compose
    , rfl
    , rfl
    , rfl
    ⟩

end TMV4Action

end SSBX.Foundation.Hierarchy.Operators
