/-
# L3 — R₃ Trigram layer (八卦)

Cell space `Trigram = (Z/2)³ = 8 atoms`. The Cayley action is componentwise
XOR on the three yao positions. The 3 atomic operators are the three
single-yao flips (basis of (Z/2)³).

## Surface syntax (both forms accepted)

Bit form (canonical printer output):
```
(trigram 阳 阳 阳)   — 乾
(trigram 阴 阴 阴)   — 坤
```

Named form (also accepted by parser):
```
(trigram-named 乾)   — heaven
(trigram-named 坤)   — earth
…
```

Tokens accepted per yao slot: 阳/yang/1 or 阴/yin/0.

## The 8 trigrams (Yao-tuple bit-pattern, y1 y2 y3)

  乾 heaven (阳阳阳) ☰   兑 lake  (阳阳阴) ☱   离 fire   (阳阴阳) ☲   震 thunder (阳阴阴) ☳
  巽 wind  (阴阳阳) ☴   坎 water  (阴阳阴) ☵   艮 mountain  (阴阴阳) ☶   坤 earth  (阴阴阴) ☷

`origin = 坤` (the (Z/2)³ zero).
-/

import SSBX.Foundation.Lang.Core
import SSBX.Foundation.Yi.Yi

namespace SSBX.Foundation.Lang.L3

open SSBX.Foundation.Yi.Yi  (Yao Trigram)

/-! ## § 1 Cell type alias + Cayley action -/

/-- L3 cell carrier = Trigram (= (Z/2)³, 8 atoms). -/
abbrev Cell : Type := Trigram

/-- Componentwise XOR realized as `Yao.neg`-mask: yang flips, yin keeps. -/
@[inline] def xorYao : Yao → Yao → Yao
  | .yin,  y => y
  | .yang, y => y.neg

/-- Cayley action: `apply x y = x ⊕ y` componentwise on the 3 yao positions. -/
def apply : Cell → Cell → Cell
  | ⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩ =>
      ⟨xorYao a1 b1, xorYao a2 b2, xorYao a3 b3⟩

/-- The (Z/2)³ origin / identity = 坤 (all yin). -/
def origin : Cell := ⟨.yin, .yin, .yin⟩

/-! ## § 2 Cayley action laws -/

theorem apply_self (c : Cell) : apply c c = origin := by
  rcases c with ⟨a, b, d⟩
  cases a <;> cases b <;> cases d <;> rfl

theorem origin_apply (c : Cell) : apply origin c = c := by
  rcases c with ⟨a, b, d⟩
  cases a <;> cases b <;> cases d <;> rfl

/-! ## § 3 Sexp bridge

The parser accepts BOTH the bit form `(trigram 阳 阳 阳)` and the named form
`(trigram-named 乾)`. The printer always emits the canonical bit form, which
guarantees `parse ∘ print = id`.
-/

/-- Parse a yao token (阳/yang/1 → yang; 阴/yin/0 → yin). -/
def parseYao : String → Except String Yao
  | "阳" | "yang" | "1" => .ok .yang
  | "阴" | "yin"  | "0" => .ok .yin
  | other => .error s!"L3.parseYao: unknown yao token '{other}'"

/-- Print a yao to its canonical 阳/阴 atom. -/
def printYaoAtom : Yao → Sexp
  | .yang => .atom "阳"
  | .yin  => .atom "阴"

/-- Parse a named trigram atom (single CJK char). -/
def parseNamed : String → Except String Cell
  | "乾" => .ok Trigram.heaven
  | "兑" => .ok Trigram.lake
  | "离" => .ok Trigram.fire
  | "震" => .ok Trigram.thunder
  | "巽" => .ok Trigram.wind
  | "坎" => .ok Trigram.water
  | "艮" => .ok Trigram.mountain
  | "坤" => .ok Trigram.earth
  | other => .error s!"L3.parseNamed: unknown trigram name '{other}'"

/-- Parse `(trigram t1 t2 t3)` (bit form) or `(trigram-named 乾)` (named). -/
def parseCell : Sexp → Except String Cell
  | .list [.atom "trigram", .atom t1, .atom t2, .atom t3] => do
      let y1 ← parseYao t1
      let y2 ← parseYao t2
      let y3 ← parseYao t3
      .ok ⟨y1, y2, y3⟩
  | .list [.atom "trigram-named", .atom name] => parseNamed name
  | s => .error s!"L3.parseCell: expected (trigram <y1> <y2> <y3>) or (trigram-named <name>), got {s.toStr}"

/-- Canonical printer: emits bit form `(trigram 阳 阳 阳)`. -/
def printCell : Cell → Sexp
  | ⟨y1, y2, y3⟩ =>
      .list [.atom "trigram", printYaoAtom y1, printYaoAtom y2, printYaoAtom y3]

theorem print_parse_round_trip (c : Cell) : parseCell (printCell c) = .ok c := by
  rcases c with ⟨y1, y2, y3⟩
  cases y1 <;> cases y2 <;> cases y3 <;> rfl

/-! ## § 4 Atomic ops (3 single-yao flips, the (Z/2)³ basis) -/

/-- Flip the bottom yao (y1). -/
def flip1 : Cell := ⟨.yang, .yin,  .yin⟩
/-- Flip the middle yao (y2). -/
def flip2 : Cell := ⟨.yin,  .yang, .yin⟩
/-- Flip the top yao (y3). -/
def flip3 : Cell := ⟨.yin,  .yin,  .yang⟩

/-! ## § 5 LangLayer instance -/

instance : LangLayer Cell where
  parseCell    := parseCell
  printCell    := printCell
  apply        := apply
  origin       := origin
  cardinality  := 8
  atomicOps    := [flip1, flip2, flip3]
  apply_self   := apply_self
  origin_apply := origin_apply

/-! ## § 6 Example rules + smoke tests

Three atomic flip rules (one per yao position; here flipping a yin → yang),
plus a few named-transition examples. -/

/-- Atomic: 坤 → 震 (flip y1). -/
def flipY1Atomic : Rule :=
  Rule.named "flip-y1"
    (.list [.atom "trigram", .atom "阴", .atom "阴", .atom "阴"])
    (.list [.atom "trigram", .atom "阳", .atom "阴", .atom "阴"])

/-- Atomic: 坤 → 坎 (flip y2). -/
def flipY2Atomic : Rule :=
  Rule.named "flip-y2"
    (.list [.atom "trigram", .atom "阳", .atom "阴", .atom "阴"])
    (.list [.atom "trigram", .atom "阳", .atom "阳", .atom "阴"])

/-- Atomic: flip y3. -/
def flipY3Atomic : Rule :=
  Rule.named "flip-y3"
    (.list [.atom "trigram", .atom "阳", .atom "阳", .atom "阴"])
    (.list [.atom "trigram", .atom "阳", .atom "阳", .atom "阳"])

/-- Named transition: 乾 → 坤 (full 错). -/
def qianToKun : Rule :=
  Rule.named "heaven-to-earth"
    (.list [.atom "trigram", .atom "阳", .atom "阳", .atom "阳"])
    (.list [.atom "trigram", .atom "阴", .atom "阴", .atom "阴"])

/-- Named transition: 离 → 坎 (complement of 离). -/
def liToKan : Rule :=
  Rule.named "fire-to-water"
    (.list [.atom "trigram", .atom "阳", .atom "阴", .atom "阳"])
    (.list [.atom "trigram", .atom "阴", .atom "阳", .atom "阴"])

/-- Default rule list: 3 atomic flips + 2 named transitions. -/
def defaultRules : List Rule :=
  [flipY1Atomic, flipY2Atomic, flipY3Atomic, qianToKun, liToKan]

/-- Smoke test: from 坤 (origin), 1 step lands on 震 (y1 flip). -/
example :
    (Eval.runRules defaultRules (printCell origin) 1
        == printCell Trigram.thunder) = true := by
  native_decide

/-- 3 steps from 坤 reach 乾 (y1 → y2 → y3 chain). -/
example :
    (Eval.runRules defaultRules (printCell origin) 3
        == printCell Trigram.heaven) = true := by
  native_decide

/-- 4 steps from 坤: hits 乾 (3 steps) then `heaven-to-earth` fires → back to 坤. -/
example :
    (Eval.runRules defaultRules (printCell origin) 4
        == printCell Trigram.earth) = true := by
  native_decide

/-- runCell convenience produces an OK result starting from 坤. -/
example : (runCell (α := Cell) defaultRules origin 1).toOption.isSome = true := by
  native_decide

/-- Round-trip via printer for 乾 (uses `print_parse_round_trip`). -/
example : parseCell (printCell Trigram.heaven) = .ok Trigram.heaven :=
  print_parse_round_trip Trigram.heaven

/-- Named-form parser: `(trigram-named 离)` parses to 离. -/
example :
    parseCell (.list [.atom "trigram-named", .atom "离"]) = .ok Trigram.fire := rfl

/-! ## § 7 L3 summary bundle -/

/-- Public summary of R₃ Trigram layer:
    cardinality = 8, three atomic single-yao flips, Cayley involutivity,
    round-trip parse, Cayley-as-apply identity. -/
theorem L3_summary :
    LangLayer.cardinality (α := Cell) = 8
    ∧ (LangLayer.atomicOps (α := Cell)).length = 3
    ∧ (∀ c : Cell, apply c c = origin)
    ∧ (∀ c : Cell, parseCell (printCell c) = .ok c)
    ∧ (∀ c s : Cell, cayley c s = apply c s) :=
  ⟨rfl, rfl, apply_self, print_parse_round_trip, fun _ _ => rfl⟩

end SSBX.Foundation.Lang.L3
