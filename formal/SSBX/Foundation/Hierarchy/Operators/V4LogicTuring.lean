/-
# V4LogicTuring -- logical duality skeleton and reversible TM atoms

The four operators `dao / cuo / zong / cuoZong` are not merely four labels.
They are the two-axis V4 skeleton:

* `dao`     = identity
* `cuo`     = content duality
* `zong`    = frame duality
* `cuoZong` = compound duality

The same V4 appears as the minimal reversible two-symbol Turing-machine local
action: flip the written bit, flip the move direction, or flip both.
-/
import SSBX.Foundation.Hierarchy.Operators.V4Core

namespace SSBX.Foundation.Hierarchy.Operators.V4LogicTuring

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Hierarchy.Operators.V4Core
open SSBX.Foundation.Hierarchy.Operators.V4Outer

/-! ## Logical V4 skeleton -/

inductive LogicalV4 where
  | dao
  | cuo
  | zong
  | cuoZong
  deriving DecidableEq, Repr

namespace LogicalV4

/-- First V4 coordinate: content duality. -/
def contentBit : LogicalV4 → Bool
  | .dao | .zong => false
  | .cuo | .cuoZong => true

/-- Second V4 coordinate: frame duality. -/
def frameBit : LogicalV4 → Bool
  | .dao | .cuo => false
  | .zong | .cuoZong => true

def ofBits : Bool → Bool → LogicalV4
  | false, false => .dao
  | true, false => .cuo
  | false, true => .zong
  | true, true => .cuoZong

def compose (a b : LogicalV4) : LogicalV4 :=
  ofBits (Bool.xor (contentBit a) (contentBit b))
    (Bool.xor (frameBit a) (frameBit b))

def actHex : LogicalV4 → Hexagram → Hexagram
  | .dao, h => h
  | .cuo, h => hex_cuo h
  | .zong, h => hex_zong h
  | .cuoZong, h => hex_cuoZong h

theorem ofBits_content_frame (x : LogicalV4) :
    ofBits (contentBit x) (frameBit x) = x := by
  cases x <;> rfl

theorem contentBit_ofBits (c f : Bool) :
    contentBit (ofBits c f) = c := by
  cases c <;> cases f <;> rfl

theorem frameBit_ofBits (c f : Bool) :
    frameBit (ofBits c f) = f := by
  cases c <;> cases f <;> rfl

private theorem bool_xor_false (b : Bool) : Bool.xor b false = b := by
  cases b <;> rfl

private theorem bool_xor_self (b : Bool) : Bool.xor b b = false := by
  cases b <;> rfl

private theorem bool_xor_assoc (a b c : Bool) :
    Bool.xor (Bool.xor a b) c = Bool.xor a (Bool.xor b c) := by
  cases a <;> cases b <;> cases c <;> rfl

private theorem bool_xor_comm (a b : Bool) :
    Bool.xor a b = Bool.xor b a := by
  cases a <;> cases b <;> rfl

theorem compose_dao_right (x : LogicalV4) :
    compose x .dao = x := by
  cases x <;> rfl

theorem compose_dao_left (x : LogicalV4) :
    compose .dao x = x := by
  cases x <;> rfl

theorem compose_self (x : LogicalV4) :
    compose x x = .dao := by
  cases x <;> rfl

theorem compose_comm (a b : LogicalV4) :
    compose a b = compose b a := by
  cases a <;> cases b <;> rfl

theorem compose_assoc (a b c : LogicalV4) :
    compose (compose a b) c = compose a (compose b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem cuo_zong_eq_cuoZong :
    compose .cuo .zong = .cuoZong := rfl

theorem actHex_compose (a b : LogicalV4) (h : Hexagram) :
    actHex (compose a b) h = actHex a (actHex b h) := by
  cases a <;> cases b <;>
    cases h with
    | mk y1 y2 y3 y4 y5 y6 =>
        cases y1 <;> cases y2 <;> cases y3 <;>
          cases y4 <;> cases y5 <;> cases y6 <;> rfl

/-! ## R8 temporal-state bridge -/

/-- Read the logical names through the canonical V4 kernel. -/
def toCore : LogicalV4 → V4
  | .dao => .dao
  | .cuo => .cuo
  | .zong => .zong
  | .cuoZong => .cuoZong

def ofCore : V4 → LogicalV4
  | .dao => .dao
  | .cuo => .cuo
  | .zong => .zong
  | .cuoZong => .cuoZong

theorem ofCore_toCore (x : LogicalV4) :
    ofCore (toCore x) = x := by
  cases x <;> rfl

theorem toCore_ofCore (g : V4) :
    toCore (ofCore g) = g := by
  cases g <;> rfl

theorem toCore_compose (a b : LogicalV4) :
    toCore (compose a b) = V4.compose (toCore a) (toCore b) := by
  cases a <;> cases b <;> rfl

/-- The same two-axis V4 skeleton as an R8 temporal-state tag. -/
def toShi : LogicalV4 → Shi
  | x => V4.toShi (toCore x)

/-- Read an R8 temporal-state tag back as the logical V4 skeleton. -/
def ofShi (s : Shi) : LogicalV4 :=
  ofBits s.1 s.2

theorem toShi_contentBit (x : LogicalV4) :
    (toShi x).1 = contentBit x := by
  cases x <;> rfl

theorem toShi_frameBit (x : LogicalV4) :
    (toShi x).2 = frameBit x := by
  cases x <;> rfl

theorem ofShi_toShi (x : LogicalV4) :
    ofShi (toShi x) = x := by
  cases x <;> rfl

theorem toShi_ofShi (s : Shi) :
    toShi (ofShi s) = s := by
  rcases s with ⟨content, frame⟩
  cases content <;> cases frame <;> rfl

theorem toShi_compose (a b : LogicalV4) :
    toShi (compose a b) =
      (Bool.xor (toShi a).1 (toShi b).1,
       Bool.xor (toShi a).2 (toShi b).2) := by
  cases a <;> cases b <;> rfl

end LogicalV4

/-! ## Reversible two-symbol TM local V4 -/

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

def ofLogical : LogicalV4 → TMV4Action
  | .dao => nop
  | .cuo => flipBit
  | .zong => flipDir
  | .cuoZong => flipBoth

def toLogical : TMV4Action → LogicalV4
  | (false, false) => .dao
  | (true, false) => .cuo
  | (false, true) => .zong
  | (true, true) => .cuoZong

theorem toLogical_ofLogical (x : LogicalV4) :
    toLogical (ofLogical x) = x := by
  cases x <;> rfl

theorem ofLogical_toLogical (a : TMV4Action) :
    ofLogical (toLogical a) = a := by
  rcases a with ⟨x, z⟩
  cases x <;> cases z <;> rfl

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

theorem ofLogical_compose (a b : LogicalV4) :
    ofLogical (LogicalV4.compose a b) =
      compose (ofLogical a) (ofLogical b) := by
  cases a <;> cases b <;> rfl

theorem apply_compose (a b : TMV4Action) (s : TapeBit × MoveDir) :
    apply (compose a b) s = apply a (apply b s) := by
  rcases a with ⟨x1, z1⟩
  rcases b with ⟨x2, z2⟩
  rcases s with ⟨bit, dir⟩
  cases x1 <;> cases z1 <;> cases x2 <;> cases z2 <;>
    cases bit <;> cases dir <;> rfl

/-- Reversible TM local actions use the same R8 temporal-state V4 carrier. -/
def toShi (a : TMV4Action) : Shi :=
  LogicalV4.toShi (toLogical a)

theorem toShi_nop :
    toShi nop = Shi.dao := rfl

theorem toShi_flipBit :
    toShi flipBit = Shi.ji := rfl

theorem toShi_flipDir :
    toShi flipDir = Shi.wei := rfl

theorem toShi_flipBoth :
    toShi flipBoth = Shi.jin := rfl

theorem toShi_compose (a b : TMV4Action) :
    toShi (compose a b) =
      (Bool.xor (toShi a).1 (toShi b).1,
       Bool.xor (toShi a).2 (toShi b).2) := by
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
    (toLogical flipBoth = LogicalV4.cuoZong)
    ∧ (∀ a : TMV4Action, compose a nop = a)
    ∧ (∀ a : TMV4Action, compose a a = nop)
    ∧ (∀ a b : TMV4Action, compose a b = compose b a)
    ∧ (∀ a b c : TMV4Action, compose (compose a b) c = compose a (compose b c))
    ∧ (∀ a b : LogicalV4, ofLogical (LogicalV4.compose a b) =
      compose (ofLogical a) (ofLogical b))
    ∧ (∀ a b s, apply (compose a b) s = apply a (apply b s))
    ∧ (toShi flipBit = Shi.ji)
    ∧ (toShi flipDir = Shi.wei)
    ∧ (toShi flipBoth = Shi.jin) := by
  exact
    ⟨ rfl
    , compose_nop_right
    , compose_self
    , compose_comm
    , compose_assoc
    , ofLogical_compose
    , apply_compose
    , rfl
    , rfl
    , rfl
    ⟩

end TMV4Action

/-! ## Public bridge summary -/

theorem logical_turing_v4_foundation_summary :
    (∀ x : LogicalV4, LogicalV4.compose x .dao = x)
    ∧ (∀ x : LogicalV4, LogicalV4.compose x x = .dao)
    ∧ (LogicalV4.compose .cuo .zong = .cuoZong)
    ∧ (LogicalV4.toShi LogicalV4.dao = Shi.dao)
    ∧ (LogicalV4.toShi LogicalV4.cuo = Shi.ji)
    ∧ (LogicalV4.toShi LogicalV4.zong = Shi.wei)
    ∧ (LogicalV4.toShi LogicalV4.cuoZong = Shi.jin)
    ∧ (∀ h : Hexagram,
      LogicalV4.actHex .cuoZong h =
        LogicalV4.actHex .cuo (LogicalV4.actHex .zong h))
    ∧ (TMV4Action.toLogical TMV4Action.flipBit = LogicalV4.cuo)
    ∧ (TMV4Action.toLogical TMV4Action.flipDir = LogicalV4.zong)
    ∧ (TMV4Action.toLogical TMV4Action.flipBoth = LogicalV4.cuoZong)
    ∧ (TMV4Action.toShi TMV4Action.flipBit = Shi.ji)
    ∧ (TMV4Action.toShi TMV4Action.flipDir = Shi.wei)
    ∧ (TMV4Action.toShi TMV4Action.flipBoth = Shi.jin) := by
  exact
    ⟨ LogicalV4.compose_dao_right
    , LogicalV4.compose_self
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , fun h => rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    , rfl
    ⟩

end SSBX.Foundation.Hierarchy.Operators.V4LogicTuring
