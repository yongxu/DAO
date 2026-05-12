/-
# V4Core -- Wen's two-axis Klein-four kernel

This module is the canonical V4 kernel used by the R-hierarchy operator
surface.  It keeps the abstract four-position skeleton separate from any one
domain reading:

* `dao`     = identity
* `cuo`     = content/value duality
* `zong`    = frame/order duality
* `cuoZong` = compound duality

Domain modules project this kernel into Shi, Hexagram operators, reversible TM
local actions, quantum/Galois analogies, or other atlases.  The core itself is
just two independent bits with XOR composition.
-/
import SSBX.Foundation.Hierarchy.Operators.V4Outer

namespace SSBX.Foundation.Hierarchy.Operators.V4Core

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Hierarchy.Operators.V4Outer

/-! ## Kernel carrier -/

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

theorem cuoZong_self :
    compose .cuoZong .cuoZong = .dao := rfl

/-! ## Shi and Hexagram projections -/

/-- The R8 temporal-state reading of the same V4 kernel. -/
def toShi : V4 → Shi
  | .dao => Shi.dao
  | .cuo => Shi.ji
  | .zong => Shi.wei
  | .cuoZong => Shi.jin

def ofShi (s : Shi) : V4 :=
  ofBits s.1 s.2

theorem ofShi_toShi (g : V4) :
    ofShi (toShi g) = g := by
  cases g <;> rfl

theorem toShi_ofShi (s : Shi) :
    toShi (ofShi s) = s := by
  rcases s with ⟨content, frame⟩
  cases content <;> cases frame <;> rfl

theorem toShi_compose (a b : V4) :
    toShi (compose a b) =
      (Bool.xor (toShi a).1 (toShi b).1,
       Bool.xor (toShi a).2 (toShi b).2) := by
  cases a <;> cases b <;> rfl

/-- Hexagram action: content duality is complement, frame duality is reverse. -/
def actHex : V4 → Hexagram → Hexagram
  | .dao, h => h
  | .cuo, h => hex_cuo h
  | .zong, h => hex_zong h
  | .cuoZong, h => hex_cuoZong h

theorem actHex_dao (h : Hexagram) :
    actHex .dao h = h := rfl

theorem actHex_compose (a b : V4) (h : Hexagram) :
    actHex (compose a b) h = actHex a (actHex b h) := by
  cases a <;> cases b <;>
    cases h with
    | mk y1 y2 y3 y4 y5 y6 =>
        cases y1 <;> cases y2 <;> cases y3 <;>
          cases y4 <;> cases y5 <;> cases y6 <;> rfl

theorem actHex_self_inverse (g : V4) (h : Hexagram) :
    actHex g (actHex g h) = h := by
  rw [← actHex_compose, compose_self, actHex_dao]

/-- The R8 dao row embeds each Hexagram at the V4 identity coordinate. -/
def daoRowCell (h : Hexagram) : R8 :=
  (h, Shi.dao)

def daoRow : List R8 :=
  Hexagram.allHex.map daoRowCell

theorem daoRow_length :
    daoRow.length = 64 := by
  native_decide

/-- The four V4 readings of one hexagram.  The list may have duplicates for
frame-symmetric hexagrams; orbit quotienting is a later calculation. -/
def hexOrbitReadings (h : Hexagram) : List Hexagram :=
  all.map (fun g => actHex g h)

theorem hexOrbitReadings_length (h : Hexagram) :
    (hexOrbitReadings h).length = 4 := rfl

theorem heaven_orbit_has_two_readings :
    hexOrbitReadings Hexagram.heaven =
      [Hexagram.heaven, Hexagram.earth, Hexagram.heaven, Hexagram.earth] := rfl

/-! ## Preservation atlas -/

inductive PreservationLevel where
  | setBijection
  | algebraHom
  | categoricalFunctor
  | implicationTruth
  deriving DecidableEq, Repr

/-- Registry-level preservation marker.

`implicationTruth` means the classical-logic implication slice where
contraposition preserves truth.  It is intentionally not a global truth claim
for arbitrary logical systems. -/
def preservesAt : V4 → PreservationLevel → Bool
  | _, .setBijection => true
  | .dao, .algebraHom => true
  | .cuo, .algebraHom => false
  | .zong, .algebraHom => false
  | .cuoZong, .algebraHom => true
  | _, .categoricalFunctor => true
  | .dao, .implicationTruth => true
  | .cuo, .implicationTruth => false
  | .zong, .implicationTruth => false
  | .cuoZong, .implicationTruth => true

def contentAxis (g : V4) : Prop :=
  g = .dao ∨ g = .cuo

def frameAxis (g : V4) : Prop :=
  g = .dao ∨ g = .zong

/-- The privileged nontrivial structure-preserving subgroup `{dao, cuoZong}`. -/
def structurePreservingAxis (g : V4) : Prop :=
  g = .dao ∨ g = .cuoZong

theorem contentAxis_closed
    {a b : V4} (ha : contentAxis a) (hb : contentAxis b) :
    contentAxis (compose a b) := by
  cases a <;> cases b <;>
    simp [contentAxis, compose, ofBits, contentBit, frameBit] at ha hb ⊢

theorem frameAxis_closed
    {a b : V4} (ha : frameAxis a) (hb : frameAxis b) :
    frameAxis (compose a b) := by
  cases a <;> cases b <;>
    simp [frameAxis, compose, ofBits, contentBit, frameBit] at ha hb ⊢

theorem structurePreservingAxis_closed
    {a b : V4} (ha : structurePreservingAxis a)
    (hb : structurePreservingAxis b) :
    structurePreservingAxis (compose a b) := by
  cases a <;> cases b <;>
    simp [structurePreservingAxis, compose, ofBits, contentBit, frameBit] at ha hb ⊢

theorem preserves_algebraHom_iff (g : V4) :
    preservesAt g .algebraHom = true ↔ structurePreservingAxis g := by
  cases g <;> simp [preservesAt, structurePreservingAxis]

theorem preserves_implicationTruth_iff (g : V4) :
    preservesAt g .implicationTruth = true ↔ structurePreservingAxis g := by
  cases g <;> simp [preservesAt, structurePreservingAxis]

theorem v4_core_summary :
    all.length = 4
    ∧ (∀ g : V4, compose g .dao = g)
    ∧ (∀ g : V4, compose g g = .dao)
    ∧ (∀ a b : V4, compose a b = compose b a)
    ∧ (∀ a b c : V4, compose (compose a b) c = compose a (compose b c))
    ∧ (compose .cuo .zong = .cuoZong)
    ∧ (∀ s : Shi, toShi (ofShi s) = s)
    ∧ (∀ h : Hexagram, actHex .dao h = h)
    ∧ (∀ g h, actHex g (actHex g h) = h)
    ∧ (∀ g, preservesAt g .algebraHom = true ↔ structurePreservingAxis g) := by
  exact
    ⟨ all_length
    , compose_dao_right
    , compose_self
    , compose_comm
    , compose_assoc
    , rfl
    , toShi_ofShi
    , actHex_dao
    , actHex_self_inverse
    , preserves_algebraHom_iff
    ⟩

end V4

end SSBX.Foundation.Hierarchy.Operators.V4Core
