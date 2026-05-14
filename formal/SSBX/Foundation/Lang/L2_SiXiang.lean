/-
# L2 — R₂ SiXiang layer (the second R-rung)

Cell space `SiXiang = Yao × Yao` (= (Z/2)²). 4 atoms:
`greaterYang ⟨阳,阳⟩ / lesserYin ⟨阳,阴⟩ / lesserYang ⟨阴,阳⟩ / greaterYin ⟨阴,阴⟩`.

The Cayley action is component-wise XOR. Origin = ⟨阴,阴⟩ = `greaterYin`.

## Surface syntax

```
(sixiang 阳 阳)   — greaterYang
(sixiang 阳 阴)   — lesserYin
(sixiang 阴 阳)   — lesserYang
(sixiang 阴 阴)   — greaterYin
```

Tokens accept 阳/yang/1 and 阴/yin/0; canonical printer uses 阳/阴.

## Yao/Yuan duality at L2

Same regular representation as L1, lifted to (Z/2)². Each cell is both a value
and the "XOR-by-mask" operator. Two atomic ops = the two single-bit-flip masks
`⟨阳,阴⟩` (flip bit 1) and `⟨阴,阳⟩` (flip bit 2). Together with the origin and
their sum `greaterYang`, they exhaust the Klein-four group.
-/

import SSBX.Foundation.Lang.Core
import SSBX.Foundation.Atlas.Yi.Classical.Core.Yi
import SSBX.Foundation.Atlas.Yi.Classical.Algebra.BaguaAlgebra

namespace SSBX.Foundation.Lang.L2

open SSBX.Foundation.Yi.Yi (Yao)
open SSBX.Foundation.Bagua.BaguaAlgebra (SiXiang)

/-! ## § 1 Cell type alias + Cayley action -/

/-- L2 cell carrier = SiXiang (= (Z/2)², 4 atoms). -/
abbrev Cell : Type := SiXiang

/-- Cayley action: component-wise XOR (via Yao.neg toggling). -/
def apply : Cell → Cell → Cell
  | ⟨.yin,  .yin⟩,  s => s
  | ⟨.yang, .yin⟩,  s => ⟨s.y1.neg, s.y2⟩
  | ⟨.yin,  .yang⟩, s => ⟨s.y1, s.y2.neg⟩
  | ⟨.yang, .yang⟩, s => ⟨s.y1.neg, s.y2.neg⟩

/-- The (Z/2)² origin = ⟨阴,阴⟩ = greaterYin. -/
def origin : Cell := ⟨.yin, .yin⟩

/-! ## § 2 Cayley action laws -/

theorem apply_self (c : Cell) : apply c c = origin := by
  rcases c with ⟨y1, y2⟩
  cases y1 <;> cases y2 <;> rfl

theorem origin_apply (c : Cell) : apply origin c = c := by
  rcases c with ⟨y1, y2⟩
  cases y1 <;> cases y2 <;> rfl

/-! ## § 3 Sexp bridge -/

/-- Parse one yao token: 阳/yang/1 → yang, 阴/yin/0 → yin. -/
private def parseYao (tok : String) : Except String Yao :=
  match tok with
  | "阳" | "yang" | "1" => .ok .yang
  | "阴" | "yin"  | "0" => .ok .yin
  | other => .error s!"L2.parseCell: unknown yao token '{other}'"

/-- Parse `(sixiang <tok1> <tok2>)` to a SiXiang cell. -/
def parseCell : Sexp → Except String Cell
  | .list [.atom "sixiang", .atom t1, .atom t2] => do
      let y1 ← parseYao t1
      let y2 ← parseYao t2
      .ok ⟨y1, y2⟩
  | s => .error s!"L2.parseCell: expected (sixiang <tok1> <tok2>), got {s.toStr}"

/-- Print one yao to its canonical 阳/阴 atom. -/
private def printYao : Yao → Sexp
  | .yang => .atom "阳"
  | .yin  => .atom "阴"

/-- Canonical printer: `(sixiang 阳/阴 阳/阴)`. -/
def printCell : Cell → Sexp
  | ⟨y1, y2⟩ => .list [.atom "sixiang", printYao y1, printYao y2]

theorem print_parse_round_trip (c : Cell) : parseCell (printCell c) = .ok c := by
  rcases c with ⟨y1, y2⟩
  cases y1 <;> cases y2 <;> rfl

/-! ## § 4 LangLayer instance -/

/-- The two single-bit-flip masks: ⟨阳,阴⟩ flips bit 1, ⟨阴,阳⟩ flips bit 2. -/
def flipBit1 : Cell := ⟨.yang, .yin⟩
def flipBit2 : Cell := ⟨.yin, .yang⟩

instance : LangLayer Cell where
  parseCell    := parseCell
  printCell    := printCell
  apply        := apply
  origin       := origin
  cardinality  := 4
  atomicOps    := [flipBit1, flipBit2]
  apply_self   := apply_self
  origin_apply := origin_apply

/-! ## § 5 Default rules: yin→yang on each bit -/

/-- Flip bit 1 from yin to yang (when bit 2 is yin): ⟨阴,阴⟩ → ⟨阳,阴⟩. -/
def rule_b1_yin_to_yang_at_b2_yin : Rule :=
  Rule.named "b1-yin-to-yang/b2-yin"
    (.list [.atom "sixiang", .atom "阴", .atom "阴"])
    (.list [.atom "sixiang", .atom "阳", .atom "阴"])

/-- Flip bit 1 from yin to yang (when bit 2 is yang): ⟨阴,阳⟩ → ⟨阳,阳⟩. -/
def rule_b1_yin_to_yang_at_b2_yang : Rule :=
  Rule.named "b1-yin-to-yang/b2-yang"
    (.list [.atom "sixiang", .atom "阴", .atom "阳"])
    (.list [.atom "sixiang", .atom "阳", .atom "阳"])

/-- Flip bit 2 from yin to yang (when bit 1 is yang): ⟨阳,阴⟩ → ⟨阳,阳⟩. -/
def rule_b2_yin_to_yang_at_b1_yang : Rule :=
  Rule.named "b2-yin-to-yang/b1-yang"
    (.list [.atom "sixiang", .atom "阳", .atom "阴"])
    (.list [.atom "sixiang", .atom "阳", .atom "阳"])

/-- Flip bit 2 from yin to yang (when bit 1 is yin): ⟨阴,阴⟩ → ⟨阴,阳⟩.
    (Subsumed in rewrite order by the bit-1 rule above; included for completeness
    of the 4-cell cover.) -/
def rule_b2_yin_to_yang_at_b1_yin : Rule :=
  Rule.named "b2-yin-to-yang/b1-yin"
    (.list [.atom "sixiang", .atom "阴", .atom "阴"])
    (.list [.atom "sixiang", .atom "阴", .atom "阳"])

/-- All 4 yin→yang transitions. -/
def defaultRules : List Rule :=
  [rule_b1_yin_to_yang_at_b2_yin,
   rule_b1_yin_to_yang_at_b2_yang,
   rule_b2_yin_to_yang_at_b1_yang,
   rule_b2_yin_to_yang_at_b1_yin]

/-! ## § 6 Smoke tests -/

example :
    (Eval.runRules defaultRules (printCell ⟨.yin, .yin⟩) 1
       == printCell ⟨.yang, .yin⟩) = true := by
  native_decide

example :
    (Eval.runRules defaultRules (printCell ⟨.yin, .yin⟩) 2
       == printCell ⟨.yang, .yang⟩) = true := by
  native_decide

example :
    (Eval.runRules defaultRules (printCell ⟨.yin, .yang⟩) 1
       == printCell ⟨.yang, .yang⟩) = true := by
  native_decide

example : (runCell (α := Cell) defaultRules ⟨.yin, .yin⟩ 2).toOption.isSome = true := by
  native_decide

example : (runCell (α := Cell) defaultRules ⟨.yang, .yang⟩ 1).toOption.isSome = true := by
  native_decide

/-! ## § 7 L2 summary bundle -/

/-- Public summary of R₂ SiXiang layer:
    cardinality = 4, two atomic ops (the bit-flip masks), Cayley involutivity,
    parse round-trip, Cayley = apply by definition. -/
theorem L2_summary :
    LangLayer.cardinality (α := Cell) = 4
    ∧ (LangLayer.atomicOps (α := Cell)).length = 2
    ∧ (∀ c : Cell, apply c c = origin)
    ∧ (∀ c : Cell, parseCell (printCell c) = .ok c)
    ∧ (∀ c s : Cell, cayley c s = apply c s) :=
  ⟨rfl, rfl, apply_self, print_parse_round_trip, fun _ _ => rfl⟩

end SSBX.Foundation.Lang.L2
