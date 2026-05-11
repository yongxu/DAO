/-
# L5 — R₅ Wuyao layer (32 = (Z/2)⁵)

Wuyao = Mian × Bool — the "5th yao" extension on top of Mian (R₄). Cell space
is the 32-element group (Z/2)⁵, the Cayley action is componentwise XOR:

  apply (m₁, b₁) (m₂, b₂) = (m₁ ⊕ m₂, b₁ ⊕ b₂)

where ⊕ on Mian is componentwise XOR over (Ben × Zheng) ≅ (Z/2)⁴.

## Atomic operators (5 single-bit flips)

  flipBenLo  — flip the low bit of Ben    (thing/motion ↔ interval/shi axis)
  flipBenHi  — flip the high bit of Ben   (thing/interval ↔ motion/shi axis)
  flipZhengLo — flip the low bit of Zheng (jiFaint/shiForce ↔ jiOccasion/shiTime)
  flipZhengHi — flip the high bit of Zheng (jiFaint/jiOccasion ↔ shiForce/shiTime)
  flip5      — flip the 5th-yao Bool bit

## Bridge to L4

The projection `projR5toR4 (m, b) = m` is a layer-forgetting morphism:
flipping the 5th bit alone preserves the Mian projection. Hence L4 rules
defined on Mian-level patterns lift to L5 by ignoring the 5th coordinate.
-/

import SSBX.Foundation.Lang.Core
import SSBX.Foundation.Hierarchy.R5_Wuyao

namespace SSBX.Foundation.Lang.L5

open SSBX.Foundation.Bagua.BenZheng
open SSBX.Foundation.Hierarchy.R5_Wuyao

/-! ## § 1 Cell type alias -/

/-- L5 cell carrier = Wuyao (= Mian × Bool = (Z/2)⁵, 32 atoms). -/
abbrev Cell : Type := Wuyao

/-! ## § 2 (Z/2)⁵ XOR — componentwise -/

/-- XOR on Ben (4 elements as (Z/2)²): thing=00, motion=01, interval=10, shi=11. -/
def Ben.xor : Ben → Ben → Ben
  | .thing,   y => y
  | .motion, .thing => .motion | .motion, .motion => .thing | .motion, .interval => .shi | .motion, .shi => .interval
  | .interval, .thing => .interval | .interval, .motion => .shi | .interval, .interval => .thing | .interval, .shi => .motion
  | .shi,  .thing => .shi  | .shi,  .motion => .interval | .shi, .interval => .motion | .shi, .shi => .thing

/-- XOR on Zheng (4 elements as (Z/2)²): jiFaint=00, shiForce=01, jiOccasion=10, shiTime=11. -/
def Zheng.xor : Zheng → Zheng → Zheng
  | .jiFaint, y => y
  | .shiForce, .jiFaint => .shiForce | .shiForce, .shiForce => .jiFaint
  | .shiForce, .jiOccasion => .shiTime | .shiForce, .shiTime => .jiOccasion
  | .jiOccasion, .jiFaint => .jiOccasion | .jiOccasion, .shiForce => .shiTime
  | .jiOccasion, .jiOccasion => .jiFaint | .jiOccasion, .shiTime => .shiForce
  | .shiTime, .jiFaint => .shiTime | .shiTime, .shiForce => .jiOccasion
  | .shiTime, .jiOccasion => .shiForce | .shiTime, .shiTime => .jiFaint

/-- Cayley action on Wuyao: componentwise XOR over (Z/2)⁵. -/
def apply : Cell → Cell → Cell
  | (⟨b₁, z₁⟩, x₁), (⟨b₂, z₂⟩, x₂) =>
      ((Ben.xor b₁ b₂, Zheng.xor z₁ z₂), Bool.xor x₁ x₂)

/-- The (Z/2)⁵ origin: (thing, jiFaint, false). -/
def origin : Cell := ((.thing, .jiFaint), false)

/-! ## § 3 Cayley action laws (involution + identity) -/

theorem apply_self (c : Cell) : apply c c = origin := by
  rcases c with ⟨⟨b, z⟩, x⟩
  cases b <;> cases z <;> cases x <;> rfl

theorem origin_apply (c : Cell) : apply origin c = c := by
  rcases c with ⟨⟨b, z⟩, x⟩
  cases b <;> cases z <;> cases x <;> rfl

/-! ## § 4 Sexp bridge

Surface form: `(wuyao <ben-char> <zheng-char> <0|1>)`.
-/

/-- Parse `(wuyao <ben> <zheng> <0|1>)`. -/
def parseCell : Sexp → Except String Cell
  | .list [.atom "wuyao", .atom bs, .atom zs, .atom xs] =>
      match Ben.fromChar bs, Zheng.fromChar zs with
      | some b, some z =>
          match xs with
          | "0" | "阴" | "false" => .ok ((b, z), false)
          | "1" | "阳" | "true"  => .ok ((b, z), true)
          | other => .error s!"L5.parseCell: unknown 5th-yao token '{other}'"
      | _, _ => .error s!"L5.parseCell: bad ben/zheng tokens '{bs}' '{zs}'"
  | s => .error s!"L5.parseCell: expected (wuyao <ben> <zheng> <0|1>), got {s.toStr}"

/-- Canonical printer: `(wuyao <ben-char> <zheng-char> <0|1>)`. -/
def printCell : Cell → Sexp
  | ((b, z), x) =>
      .list [.atom "wuyao", .atom b.char, .atom z.char,
             .atom (if x then "1" else "0")]

theorem print_parse_round_trip (c : Cell) : parseCell (printCell c) = .ok c := by
  rcases c with ⟨⟨b, z⟩, x⟩
  cases b <;> cases z <;> cases x <;> rfl

/-! ## § 5 Atomic operators (5 single-bit flips) -/

/-- Flip the low bit of Ben (thing↔motion, interval↔shi). -/
def flipBenLo : Cell := ((.motion, .jiFaint), false)

/-- Flip the high bit of Ben (thing↔interval, motion↔shi). -/
def flipBenHi : Cell := ((.interval, .jiFaint), false)

/-- Flip the low bit of Zheng (jiFaint↔shiForce, jiOccasion↔shiTime). -/
def flipZhengLo : Cell := ((.thing, .shiForce), false)

/-- Flip the high bit of Zheng (jiFaint↔jiOccasion, shiForce↔shiTime). -/
def flipZhengHi : Cell := ((.thing, .jiOccasion), false)

/-- Flip the 5th-yao Bool bit. -/
def flipFifth : Cell := ((.thing, .jiFaint), true)

/-! ## § 6 LangLayer instance -/

instance : LangLayer Cell where
  parseCell    := parseCell
  printCell    := printCell
  apply        := apply
  origin       := origin
  cardinality  := 32
  atomicOps    := [flipBenLo, flipBenHi, flipZhengLo, flipZhengHi, flipFifth]
  apply_self   := apply_self
  origin_apply := origin_apply

/-! ## § 7 Bridge to L4 (Mian projection)

The 5th-yao flip preserves the Mian projection. Hence L5 strictly extends L4
by one independent (Z/2) bit.
-/

theorem flipFifth_preserves_mian (c : Cell) : (apply flipFifth c).1 = c.1 := by
  rcases c with ⟨⟨b, z⟩, x⟩
  cases b <;> cases z <;> cases x <;> rfl

theorem projR5toR4_apply_flipFifth (c : Cell) :
    projR5toR4 (apply flipFifth c) = projR5toR4 c := by
  rcases c with ⟨⟨b, z⟩, x⟩
  cases b <;> cases z <;> cases x <;> rfl

/-! ## § 8 Default rules — 5 atomic flip toggles

For surface-level rewriting we expose just the 5th-yao toggle pair as a
demonstrator (the Ben/Zheng bit toggles would require 8 individual
Mian-pattern rules each; those are deferred to L4's rule set, which lifts
trivially because flipFifth is orthogonal).
-/

/-- Toggle 5th yao 0→1 at (thing, jiFaint). -/
def toggleFifthOff : Rule :=
  Rule.named "wuyao-toggle-fifth-off"
    (.list [.atom "wuyao", .atom "物", .atom "几", .atom "0"])
    (.list [.atom "wuyao", .atom "物", .atom "几", .atom "1"])

/-- Toggle 5th yao 1→0 at (thing, jiFaint). -/
def toggleFifthOn : Rule :=
  Rule.named "wuyao-toggle-fifth-on"
    (.list [.atom "wuyao", .atom "物", .atom "几", .atom "1"])
    (.list [.atom "wuyao", .atom "物", .atom "几", .atom "0"])

def defaultRules : List Rule := [toggleFifthOff, toggleFifthOn]

/-! ## § 9 Smoke tests (native_decide) -/

example : (Eval.runRules defaultRules (printCell origin) 1
            == printCell ((.thing, .jiFaint), true)) = true := by
  native_decide

example : (Eval.runRules defaultRules (printCell origin) 2
            == printCell origin) = true := by
  native_decide

example : (runCell (α := Cell) defaultRules origin 1).toOption.isSome = true := by
  native_decide

example : LangLayer.cardinality (α := Cell) = 32 := rfl

example : (LangLayer.atomicOps (α := Cell)).length = 5 := rfl

/-! ## § 10 L5 summary bundle -/

/-- Public summary of R₅ Wuyao layer:
    cardinality 32, 5 atomic ops, Cayley involution, round-trip parse,
    flipFifth preserves Mian projection. -/
theorem L5_summary :
    LangLayer.cardinality (α := Cell) = 32
    ∧ (LangLayer.atomicOps (α := Cell)).length = 5
    ∧ (∀ c : Cell, apply c c = origin)
    ∧ (∀ c : Cell, parseCell (printCell c) = .ok c)
    ∧ (∀ c : Cell, projR5toR4 (apply flipFifth c) = projR5toR4 c) :=
  ⟨rfl, rfl, apply_self, print_parse_round_trip, projR5toR4_apply_flipFifth⟩

end SSBX.Foundation.Lang.L5
