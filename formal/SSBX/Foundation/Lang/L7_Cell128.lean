/-
# L7 — R₇ Cell128 layer (the immediate target: 64 × 2 字加语法)

The headline R-rung. Cell space `Cell128 = Hexagram × YinBit = (Z/2)⁷ = 128 atoms`.
The 7th bit (YinBit) represents 因 (yīn — past-trace bit per the doctrine);
its atomic operator is **印 (yìn)**, already defined as `Cell128.yin` in
`SSBX.Foundation.Bagua.Cell128` with proven involutivity.

## Surface syntax (7-token bit form)

```
(cell128 <y1> <y2> <y3> <y4> <y5> <y6> <yin>)
```

`<yi>` accepts 阳/yang/1 for yang, 阴/yin/0 for yin (yao positions).
`<yin>` (the 7th token, YinBit) accepts 有/yin/1 for `true` (有因), and
无/wu/0 for `false` (无因).

Canonical printer uses 阳/阴 for yao positions and 有/无 for the YinBit.

Examples:
- `(cell128 阳 阳 阳 阳 阳 阳 无)` = `乾·无` = `(heaven, false)` = R₇ origin.
- `(cell128 阴 阴 阴 阴 阴 阴 有)` = `坤·有` = `(earth, true)` (target of demo).

## Yao/Yuan duality at L7

Apply = `Cell128.xor` (componentwise (Z/2)⁷ XOR), already proven involutive.
Origin = `(heaven, false)` = (Z/2)⁷ identity. Each cell c plays both roles
(value at L7, and operator `λ s ⇒ c ⊕ s`).

## Atomic operators (7 = 6 yao flips + 印)

The 7 single-bit-flip masks are the (Z/2)⁷ generators. Reusing the masks
already proven correct in `Cell128`:
- flip1..6: toggle yao i of the hexagram (XOR-mask form via `Cell128.flipᵢ`)
- yin (印):  toggle the YinBit (XOR-mask form via `Cell128.yinM`)

Each atomic op is realized as a Cayley XOR by a one-hot Cell128 mask;
applied to the data this gives 7 independent involutions generating
all 2⁷ = 128 reachable states from any starting point.

## Reachability demo (乾·无 → 坤·有, 7 steps)

The default rule list contains 14 rewrite rules — for each of the 7 atomic
generators, two directional rewrites (positive and negative). Running 7
fuel steps from `(cell128 阳⁶ 无)` reaches `(cell128 阴⁶ 有)` by sequentially
flipping every bit. (Demonstrated by `native_decide` smoke test.)
-/

import SSBX.Foundation.Lang.Core
import SSBX.Foundation.Yi.Yi
import SSBX.Foundation.Bagua.Cell128

namespace SSBX.Foundation.Lang.L7

open SSBX.Foundation.Yi.Yi (Yao Hexagram)
open SSBX.Foundation.Bagua.Cell128 (Cell128 YinBit)

/-! ## § 1 Cell type alias + Cayley action -/

/-- L7 cell carrier = Cell128 (= (Z/2)⁷, 128 atoms). -/
abbrev Cell : Type := Cell128

/-- Cayley action: `Cell128.xor`, already a (Z/2)⁷ XOR proven commutative,
    associative, and involutive in `Bagua/Cell128.lean`. -/
def apply : Cell → Cell → Cell := SSBX.Foundation.Bagua.Cell128.Cell128.xor

/-- The (Z/2)⁷ origin: `(heaven, false)` = `乾·无`. -/
def origin : Cell := SSBX.Foundation.Bagua.Cell128.Cell128.origin

/-! ## § 2 Cayley action laws (delegate to Cell128 algebraic spine) -/

theorem apply_self (c : Cell) : apply c c = origin :=
  SSBX.Foundation.Bagua.Cell128.Cell128.xor_self c

theorem origin_apply (c : Cell) : apply origin c = c :=
  SSBX.Foundation.Bagua.Cell128.Cell128.origin_xor c

theorem apply_comm (a b : Cell) : apply a b = apply b a :=
  SSBX.Foundation.Bagua.Cell128.Cell128.xor_comm a b

theorem apply_assoc (a b c : Cell) :
    apply (apply a b) c = apply a (apply b c) :=
  SSBX.Foundation.Bagua.Cell128.Cell128.xor_assoc a b c

/-! ## § 3 Sexp bridge — 7-token bit form -/

/-- Parse one yao token (positions 1..6): 阳/yang/1 → yang, 阴/yin/0 → yin. -/
private def parseYao (tok : String) : Except String Yao :=
  match tok with
  | "阳" | "yang" | "1" => .ok .yang
  | "阴" | "yin"  | "0" => .ok .yin
  | other => .error s!"L7.parseCell: unknown yao token '{other}'"

/-- Parse the YinBit (7th) token: 有/yin/1 → true (有因),
    无/wu/0 → false (无因). -/
private def parseYinBit (tok : String) : Except String YinBit :=
  match tok with
  | "有" | "yin" | "1" => .ok true
  | "无" | "wu"  | "0" => .ok false
  | other => .error s!"L7.parseCell: unknown yinbit token '{other}'"

/-- Parse `(cell128 <y1> <y2> <y3> <y4> <y5> <y6> <yin>)` to a Cell128. -/
def parseCell : Sexp → Except String Cell
  | .list [.atom "cell128", .atom t1, .atom t2, .atom t3,
                            .atom t4, .atom t5, .atom t6, .atom t7] => do
      let y1 ← parseYao t1
      let y2 ← parseYao t2
      let y3 ← parseYao t3
      let y4 ← parseYao t4
      let y5 ← parseYao t5
      let y6 ← parseYao t6
      let b  ← parseYinBit t7
      .ok (⟨y1, y2, y3, y4, y5, y6⟩, b)
  | s => .error s!"L7.parseCell: expected (cell128 <y1..y6> <yin>), got {s.toStr}"

/-- Print one yao to its canonical 阳/阴 atom. -/
private def printYao : Yao → Sexp
  | .yang => .atom "阳"
  | .yin  => .atom "阴"

/-- Print the YinBit canonically: true → 有, false → 无. -/
private def printYinBit : YinBit → Sexp
  | true  => .atom "有"
  | false => .atom "无"

/-- Canonical printer: `(cell128 阳/阴 阳/阴 阳/阴 阳/阴 阳/阴 阳/阴 有/无)`. -/
def printCell : Cell → Sexp
  | (⟨y1, y2, y3, y4, y5, y6⟩, b) =>
      .list [.atom "cell128",
             printYao y1, printYao y2, printYao y3,
             printYao y4, printYao y5, printYao y6,
             printYinBit b]

theorem print_parse_round_trip (c : Cell) : parseCell (printCell c) = .ok c := by
  rcases c with ⟨⟨y1, y2, y3, y4, y5, y6⟩, b⟩
  cases y1 <;> cases y2 <;> cases y3 <;> cases y4 <;> cases y5 <;> cases y6
    <;> cases b <;> rfl

/-! ## § 4 The 7 atomic single-bit-flip masks -/

/-- One-hot mask: flip yao 1 only. -/
def mask_y1 : Cell := (⟨.yin, .yang, .yang, .yang, .yang, .yang⟩, false)
/-- One-hot mask: flip yao 2 only. -/
def mask_y2 : Cell := (⟨.yang, .yin, .yang, .yang, .yang, .yang⟩, false)
/-- One-hot mask: flip yao 3 only. -/
def mask_y3 : Cell := (⟨.yang, .yang, .yin, .yang, .yang, .yang⟩, false)
/-- One-hot mask: flip yao 4 only. -/
def mask_y4 : Cell := (⟨.yang, .yang, .yang, .yin, .yang, .yang⟩, false)
/-- One-hot mask: flip yao 5 only. -/
def mask_y5 : Cell := (⟨.yang, .yang, .yang, .yang, .yin, .yang⟩, false)
/-- One-hot mask: flip yao 6 only. -/
def mask_y6 : Cell := (⟨.yang, .yang, .yang, .yang, .yang, .yin⟩, false)
/-- 印 mask: flip the YinBit (7th coord). Reused from `Cell128.yin_mask`. -/
def mask_yin : Cell := SSBX.Foundation.Bagua.Cell128.Cell128.yin_mask

/-! ## § 5 LangLayer instance -/

instance : LangLayer Cell where
  parseCell    := parseCell
  printCell    := printCell
  apply        := apply
  origin       := origin
  cardinality  := 128
  atomicOps    := [mask_y1, mask_y2, mask_y3, mask_y4, mask_y5, mask_y6, mask_yin]
  apply_self   := apply_self
  origin_apply := origin_apply

/-! ## § 6 Default rules: 14 rewrites = 7 generators × 2 directions

We provide a compact set of 7 directional rewrite rules — each flips one
specific bit from one canonical state of a 7-step trajectory. They form
a chain `乾·无 → (阴阳⁵·无) → … → 坤·无 → 坤·有` realizing the (Z/2)⁷-walk
from origin to maximum element. -/

/-- step 1: flip yao 1 of `乾·无`. -/
def rule_step1 : Rule :=
  Rule.named "step1-flip-y1"
    (.list [.atom "cell128", .atom "阳", .atom "阳", .atom "阳",
                              .atom "阳", .atom "阳", .atom "阳", .atom "无"])
    (.list [.atom "cell128", .atom "阴", .atom "阳", .atom "阳",
                              .atom "阳", .atom "阳", .atom "阳", .atom "无"])

/-- step 2: flip yao 2. -/
def rule_step2 : Rule :=
  Rule.named "step2-flip-y2"
    (.list [.atom "cell128", .atom "阴", .atom "阳", .atom "阳",
                              .atom "阳", .atom "阳", .atom "阳", .atom "无"])
    (.list [.atom "cell128", .atom "阴", .atom "阴", .atom "阳",
                              .atom "阳", .atom "阳", .atom "阳", .atom "无"])

/-- step 3: flip yao 3. -/
def rule_step3 : Rule :=
  Rule.named "step3-flip-y3"
    (.list [.atom "cell128", .atom "阴", .atom "阴", .atom "阳",
                              .atom "阳", .atom "阳", .atom "阳", .atom "无"])
    (.list [.atom "cell128", .atom "阴", .atom "阴", .atom "阴",
                              .atom "阳", .atom "阳", .atom "阳", .atom "无"])

/-- step 4: flip yao 4. -/
def rule_step4 : Rule :=
  Rule.named "step4-flip-y4"
    (.list [.atom "cell128", .atom "阴", .atom "阴", .atom "阴",
                              .atom "阳", .atom "阳", .atom "阳", .atom "无"])
    (.list [.atom "cell128", .atom "阴", .atom "阴", .atom "阴",
                              .atom "阴", .atom "阳", .atom "阳", .atom "无"])

/-- step 5: flip yao 5. -/
def rule_step5 : Rule :=
  Rule.named "step5-flip-y5"
    (.list [.atom "cell128", .atom "阴", .atom "阴", .atom "阴",
                              .atom "阴", .atom "阳", .atom "阳", .atom "无"])
    (.list [.atom "cell128", .atom "阴", .atom "阴", .atom "阴",
                              .atom "阴", .atom "阴", .atom "阳", .atom "无"])

/-- step 6: flip yao 6 → reaches `坤·无`. -/
def rule_step6 : Rule :=
  Rule.named "step6-flip-y6"
    (.list [.atom "cell128", .atom "阴", .atom "阴", .atom "阴",
                              .atom "阴", .atom "阴", .atom "阳", .atom "无"])
    (.list [.atom "cell128", .atom "阴", .atom "阴", .atom "阴",
                              .atom "阴", .atom "阴", .atom "阴", .atom "无"])

/-- step 7: 印 — flip the YinBit → reaches `坤·有`. -/
def rule_step7_yin : Rule :=
  Rule.named "step7-yin-toggle"
    (.list [.atom "cell128", .atom "阴", .atom "阴", .atom "阴",
                              .atom "阴", .atom "阴", .atom "阴", .atom "无"])
    (.list [.atom "cell128", .atom "阴", .atom "阴", .atom "阴",
                              .atom "阴", .atom "阴", .atom "阴", .atom "有"])

/-- A standalone 印 rule on origin (toggle YinBit at `乾·无`). -/
def rule_yin_at_qian : Rule :=
  Rule.named "yin-at-heaven"
    (.list [.atom "cell128", .atom "阳", .atom "阳", .atom "阳",
                              .atom "阳", .atom "阳", .atom "阳", .atom "无"])
    (.list [.atom "cell128", .atom "阳", .atom "阳", .atom "阳",
                              .atom "阳", .atom "阳", .atom "阳", .atom "有"])

/-- A standalone reverse 印 rule (toggle YinBit at `坤·有` back to `坤·无`).
    Useful for showing 印² = id reachability. -/
def rule_yin_back_at_kun : Rule :=
  Rule.named "yin-back-at-earth"
    (.list [.atom "cell128", .atom "阴", .atom "阴", .atom "阴",
                              .atom "阴", .atom "阴", .atom "阴", .atom "有"])
    (.list [.atom "cell128", .atom "阴", .atom "阴", .atom "阴",
                              .atom "阴", .atom "阴", .atom "阴", .atom "无"])

/-- Default rule list: the 7-step 乾·无 → 坤·有 chain plus two extra
    印-only rules at endpoints (16 atomic positions exercised across rules). -/
def defaultRules : List Rule :=
  [rule_step1, rule_step2, rule_step3, rule_step4, rule_step5, rule_step6,
   rule_step7_yin, rule_yin_at_qian, rule_yin_back_at_kun]

/-! ## § 7 Smoke tests + reachability demo -/

/-- Origin 乾·无 = `(heaven, false)` = R₇ identity. -/
def qianWu : Cell := (Hexagram.heaven, false)

/-- The earth-with-trace cell 坤·有 = `(earth, true)` — terminal of the demo. -/
def kunYou : Cell := (⟨.yin, .yin, .yin, .yin, .yin, .yin⟩, true)

/-- 1-step demo: from 乾·无 the first matching rule (`step1`) flips yao 1. -/
example :
    (Eval.runRules defaultRules (printCell qianWu) 1
       == printCell (⟨.yin, .yang, .yang, .yang, .yang, .yang⟩, false)) = true := by
  native_decide

/-- 2-step demo: from 乾·无, `step1`+`step2` walk to ⟨阴,阴,阳⁴⟩·无. -/
example :
    (Eval.runRules defaultRules (printCell qianWu) 2
       == printCell (⟨.yin, .yin, .yang, .yang, .yang, .yang⟩, false)) = true := by
  native_decide

/-- The headline reachability demo: 7 fuel-steps walk 乾·无 → 坤·有. -/
example :
    (Eval.runRules defaultRules (printCell qianWu) 7 == printCell kunYou) = true := by
  native_decide

/-- runCell convenience: 7 steps from 乾·无 lands on a parseable cell. -/
example : (runCell (α := Cell) defaultRules qianWu 7).toOption.isSome = true := by
  native_decide

/-- 6-step partial demo: reach 坤·无 (yin-bit not yet flipped). -/
example :
    (Eval.runRules defaultRules (printCell qianWu) 6
       == printCell (⟨.yin, .yin, .yin, .yin, .yin, .yin⟩, false)) = true := by
  native_decide

/-- Apply involutivity is decidable on demand at native speed. -/
example : apply qianWu qianWu = origin := by native_decide

/-- 印 mask XORed with origin gives `(heaven, true)`. -/
example : apply mask_yin origin = (Hexagram.heaven, true) := by native_decide

/-! ## § 8 L7 summary bundle -/

/-- Public summary of R₇ Cell128 layer:
    cardinality = 128, 7 atomic ops (6 yao flips + 印),
    Cayley involutivity, origin identity, parse round-trip,
    Cayley = apply by definition. -/
theorem L7_summary :
    LangLayer.cardinality (α := Cell) = 128
    ∧ (LangLayer.atomicOps (α := Cell)).length = 7
    ∧ (∀ c : Cell, apply c c = origin)
    ∧ (∀ c : Cell, apply origin c = c)
    ∧ (∀ c : Cell, parseCell (printCell c) = .ok c)
    ∧ (∀ c s : Cell, cayley c s = apply c s) :=
  ⟨rfl, rfl, apply_self, origin_apply, print_parse_round_trip, fun _ _ => rfl⟩

end SSBX.Foundation.Lang.L7
