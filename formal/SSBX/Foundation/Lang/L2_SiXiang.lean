/-
# L2 — R₂ SiXiang layer (the second R-rung)

Cell space `SiXiang = R 2 = Fin 2 → Bool` (= Shi). 4 atoms:
`taiyang ⟨阳,阳⟩ / shaoyin ⟨阳,阴⟩ / shaoyang ⟨阴,阳⟩ / taiyin ⟨阴,阴⟩`.

The Cayley action is component-wise XOR (R-Family `+` on R 2). Origin = ⟨阴,阴⟩ = `taiyin`.

## Surface syntax

```
(sixiang 阳 阳)   — taiyang
(sixiang 阳 阴)   — shaoyin
(sixiang 阴 阳)   — shaoyang
(sixiang 阴 阴)   — taiyin
```

Tokens accept 阳/yang/1 and 阴/yin/0; canonical printer uses 阳/阴.

## Yao/Yuan duality at L2

Same regular representation as L1, lifted to (Z/2)². Each cell is both a value
and the "XOR-by-mask" operator. Two atomic ops = the two single-bit-flip masks
`shaoyin` (flip bit 1) and `shaoyang` (flip bit 2). Together with the origin and
their sum `taiyang`, they exhaust the Klein-four group.
-/

import SSBX.Foundation.Lang.Core
import SSBX.Foundation.Atlas.Yi

namespace SSBX.Foundation.Lang.L2

open SSBX.Foundation.Atlas.Yi (Yao Shi)
open SSBX.Foundation.Atlas.Yi.Sheng (SiXiang)

/-! ## § 1 Cell type alias + Cayley action -/

/-- L2 cell carrier = SiXiang (= Shi = R 2, 4 atoms). -/
abbrev Cell : Type := SiXiang

/-- Read y1 of a SiXiang cell (= bit 0 of the underlying R 2). -/
@[inline] def y1 (c : Cell) : Yao := c ⟨0, by decide⟩
/-- Read y2 of a SiXiang cell (= bit 1 of the underlying R 2). -/
@[inline] def y2 (c : Cell) : Yao := c ⟨1, by decide⟩

/-- Build a SiXiang from two Yao components. -/
@[inline] def mk (a b : Yao) : Cell := fun i =>
  match i with
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b

/-- Extensionality through y1 / y2. -/
theorem ext (c d : Cell) (h1 : y1 c = y1 d) (h2 : y2 c = y2 d) : c = d := by
  funext i
  match i with
  | ⟨0, _⟩ => exact h1
  | ⟨1, _⟩ => exact h2

/-- Componentwise yao-XOR (yin acts as 0 = identity, yang acts as 1 = flip).
    This convention matches the legacy `BaguaAlgebra` so that
    `origin = ⟨yin, yin⟩ = taiyin` acts as identity in the Cayley action. -/
@[inline] def xorY : Yao → Yao → Yao
  | .yin,  y => y
  | .yang, y => Yao.neg y

/-- Cayley action: component-wise XOR via `xorY`. -/
def apply (a b : Cell) : Cell :=
  mk (xorY (y1 a) (y1 b)) (xorY (y2 a) (y2 b))

/-- The (Z/2)² origin = ⟨阴,阴⟩ = taiyin. -/
def origin : Cell := SiXiang.taiyin

/-! ## § 2 Cayley action laws -/

theorem apply_self (c : Cell) : apply c c = origin := by
  apply ext
  · show y1 (apply c c) = y1 origin
    show xorY (y1 c) (y1 c) = y1 origin
    cases hy : y1 c <;> rfl
  · show y2 (apply c c) = y2 origin
    show xorY (y2 c) (y2 c) = y2 origin
    cases hy : y2 c <;> rfl

theorem origin_apply (c : Cell) : apply origin c = c := by
  apply ext
  · show y1 (apply origin c) = y1 c
    show xorY (y1 origin) (y1 c) = y1 c
    rfl
  · show y2 (apply origin c) = y2 c
    show xorY (y2 origin) (y2 c) = y2 c
    rfl

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
      let a ← parseYao t1
      let b ← parseYao t2
      .ok (mk a b)
  | s => .error s!"L2.parseCell: expected (sixiang <tok1> <tok2>), got {s.toStr}"

/-- Print one yao to its canonical 阳/阴 atom. -/
private def printYao : Yao → Sexp
  | .yang => .atom "阳"
  | .yin  => .atom "阴"

/-- Canonical printer: `(sixiang 阳/阴 阳/阴)`. -/
def printCell (c : Cell) : Sexp :=
  .list [.atom "sixiang", printYao (y1 c), printYao (y2 c)]

theorem print_parse_round_trip (c : Cell) : parseCell (printCell c) = .ok c := by
  have hc : c = mk (y1 c) (y2 c) := by
    apply ext <;> rfl
  rw [hc]
  cases h1 : y1 c <;> cases h2 : y2 c <;> rfl

/-! ## § 4 LangLayer instance -/

/-- The two single-bit-flip masks: shaoyin flips bit 1, shaoyang flips bit 2. -/
def flipBit1 : Cell := SiXiang.shaoyin   -- ⟨yang, yin⟩
def flipBit2 : Cell := SiXiang.shaoyang  -- ⟨yin, yang⟩

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
    (Eval.runRules defaultRules (printCell (mk .yin .yin)) 1
       == printCell (mk .yang .yin)) = true := by
  native_decide

example :
    (Eval.runRules defaultRules (printCell (mk .yin .yin)) 2
       == printCell (mk .yang .yang)) = true := by
  native_decide

example :
    (Eval.runRules defaultRules (printCell (mk .yin .yang)) 1
       == printCell (mk .yang .yang)) = true := by
  native_decide

example : (runCell (α := Cell) defaultRules (mk .yin .yin) 2).toOption.isSome = true := by
  native_decide

example : (runCell (α := Cell) defaultRules (mk .yang .yang) 1).toOption.isSome = true := by
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
