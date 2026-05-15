/-
# L6 — R₆ Hexagram layer (周易 64 卦 / (Z/2)⁶)

R₆ = Hexagram = `R 6 = Fin 6 → Bool` = 64 atoms = the 64 hexagrams of 周易.
Cayley action is componentwise XOR (R-Family `+` on `R 6`).

## Carrier convention

Per `Atlas/Yi/Names.lean`, **乾 (heaven) = qianqian = mk yang yang yang yang yang yang**
is the (Z/2)⁶ identity (`o = false = yang`; `x = true = yin`). So
`origin = Hexagram.heaven = qianqian`.

## Surface syntax

Bit form: `(hex y1 y2 y3 y4 y5 y6)` — six yao tokens, 阳/阴 (or yang/yin or 1/0),
y1 = 初爻 (bottom), y6 = 上爻 (top). Canonical printer uses 阳/阴.

## Atomic ops

Six single-yao flips (y1..y6), each obtained by XOR with the corresponding
unit-mask hexagram. atomicOps lists those 6 unit masks.

## Test programs

A handful of small smoke tests + 2-3 named transitions (e.g. 乾 → 坤).
-/

import SSBX.Foundation.Lang.Core
import SSBX.Foundation.Atlas.Yi

namespace SSBX.Foundation.Lang.L6

open SSBX.Foundation.Atlas.Yi (Yao Hexagram)
open SSBX.Foundation.R

/-! ## § 1 Cell type alias -/

/-- L6 cell carrier = Hexagram (= R 6, 64 atoms). -/
abbrev Cell : Type := Hexagram

/-- Cayley action = componentwise XOR via R-Family `+`. -/
def apply (a b : Cell) : Cell := a + b

/-- (Z/2)⁶ origin = 乾 (qianqian = all-yang = identity). -/
def origin : Cell := Hexagram.qianqian

/-! ## § 2 Cayley action laws -/

/-- `qianqian = 0` as element of `Hexagram = R 6`. -/
private theorem qianqian_eq_zero : (Hexagram.qianqian : Hexagram) = 0 := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl
  | ⟨5, _⟩ => rfl

theorem apply_self (c : Cell) : apply c c = origin := by
  show c + c = Hexagram.qianqian
  rw [R.add_self, ← qianqian_eq_zero]

theorem origin_apply (c : Cell) : apply origin c = c := by
  show Hexagram.qianqian + c = c
  rw [qianqian_eq_zero, zero_add]

/-! ## § 3 Atomic single-yao flip masks (6 generators of (Z/2)⁶) -/

/-- Mask flipping only y1 (初爻). -/
def mask1 : Cell := Hexagram.mk .yin .yang .yang .yang .yang .yang
def mask2 : Cell := Hexagram.mk .yang .yin .yang .yang .yang .yang
def mask3 : Cell := Hexagram.mk .yang .yang .yin .yang .yang .yang
def mask4 : Cell := Hexagram.mk .yang .yang .yang .yin .yang .yang
def mask5 : Cell := Hexagram.mk .yang .yang .yang .yang .yin .yang
/-- Mask flipping only y6 (上爻). -/
def mask6 : Cell := Hexagram.mk .yang .yang .yang .yang .yang .yin

/-! ## § 4 Sexp bridge -/

/-- Parse a single yao token. -/
def parseYao : String → Except String Yao
  | "阳" | "yang" | "1" => .ok .yang
  | "阴" | "yin"  | "0" => .ok .yin
  | other => .error s!"L6.parseYao: unknown yao token '{other}'"

/-- Print a single yao as 阳/阴. -/
def printYao : Yao → String
  | .yang => "阳"
  | .yin  => "阴"

/-- Parse `(hex y1 y2 y3 y4 y5 y6)` to a Hexagram (y1 = 初爻, y6 = 上爻). -/
def parseCell : Sexp → Except String Cell
  | .list [.atom "hex", .atom a1, .atom a2, .atom a3, .atom a4, .atom a5, .atom a6] => do
      let y1 ← parseYao a1
      let y2 ← parseYao a2
      let y3 ← parseYao a3
      let y4 ← parseYao a4
      let y5 ← parseYao a5
      let y6 ← parseYao a6
      .ok (Hexagram.mk y1 y2 y3 y4 y5 y6)
  | s => .error s!"L6.parseCell: expected (hex y1 .. y6), got {s.toStr}"

/-- Canonical printer: `(hex 阳/阴 ×6)`. -/
def printCell (h : Cell) : Sexp :=
  .list [.atom "hex",
         .atom (printYao h.y1), .atom (printYao h.y2), .atom (printYao h.y3),
         .atom (printYao h.y4), .atom (printYao h.y5), .atom (printYao h.y6)]

theorem print_parse_round_trip (c : Cell) : parseCell (printCell c) = .ok c := by
  have hc : c = Hexagram.mk c.y1 c.y2 c.y3 c.y4 c.y5 c.y6 := by
    apply Hexagram.ext <;> rfl
  rw [hc]
  cases c.y1 <;> cases c.y2 <;> cases c.y3 <;>
    cases c.y4 <;> cases c.y5 <;> cases c.y6 <;> rfl

/-! ## § 5 LangLayer instance -/

instance : LangLayer Cell where
  parseCell    := parseCell
  printCell    := printCell
  apply        := apply
  origin       := origin
  cardinality  := 64
  atomicOps    := [mask1, mask2, mask3, mask4, mask5, mask6]
  apply_self   := apply_self
  origin_apply := origin_apply

/-! ## § 6 Default rules: 6 atomic flips + named transitions -/

/-- Atomic flip rule at yao-i: pattern `(hex … <yi> …)` rewrites that one yao. -/
private def hexSexp (h : Hexagram) : Sexp := printCell h

def flip1Rule : Rule :=
  Rule.named "flip-y1-yang→yin"
    (.list [.atom "hex", .atom "阳", .atom "?b", .atom "?c", .atom "?d", .atom "?e", .atom "?f"])
    (.list [.atom "hex", .atom "阴", .atom "?b", .atom "?c", .atom "?d", .atom "?e", .atom "?f"])

def flip2Rule : Rule :=
  Rule.named "flip-y2-yang→yin"
    (.list [.atom "hex", .atom "?a", .atom "阳", .atom "?c", .atom "?d", .atom "?e", .atom "?f"])
    (.list [.atom "hex", .atom "?a", .atom "阴", .atom "?c", .atom "?d", .atom "?e", .atom "?f"])

def flip3Rule : Rule :=
  Rule.named "flip-y3-yang→yin"
    (.list [.atom "hex", .atom "?a", .atom "?b", .atom "阳", .atom "?d", .atom "?e", .atom "?f"])
    (.list [.atom "hex", .atom "?a", .atom "?b", .atom "阴", .atom "?d", .atom "?e", .atom "?f"])

def flip4Rule : Rule :=
  Rule.named "flip-y4-yang→yin"
    (.list [.atom "hex", .atom "?a", .atom "?b", .atom "?c", .atom "阳", .atom "?e", .atom "?f"])
    (.list [.atom "hex", .atom "?a", .atom "?b", .atom "?c", .atom "阴", .atom "?e", .atom "?f"])

def flip5Rule : Rule :=
  Rule.named "flip-y5-yang→yin"
    (.list [.atom "hex", .atom "?a", .atom "?b", .atom "?c", .atom "?d", .atom "阳", .atom "?f"])
    (.list [.atom "hex", .atom "?a", .atom "?b", .atom "?c", .atom "?d", .atom "阴", .atom "?f"])

def flip6Rule : Rule :=
  Rule.named "flip-y6-yang→yin"
    (.list [.atom "hex", .atom "?a", .atom "?b", .atom "?c", .atom "?d", .atom "?e", .atom "阳"])
    (.list [.atom "hex", .atom "?a", .atom "?b", .atom "?c", .atom "?d", .atom "?e", .atom "阴"])

/-- Named transition: 乾 (all-yang) → 坤 (all-yin). -/
def qianToKun : Rule :=
  Rule.named "乾→坤" (hexSexp Hexagram.heaven) (hexSexp Hexagram.earth)

/-- Named transition: 坤 → 乾. -/
def kunToQian : Rule :=
  Rule.named "坤→乾" (hexSexp Hexagram.earth) (hexSexp Hexagram.heaven)

/-- Named transition: 既济 → 未济 (yao-by-yao swap pattern). -/
def jijiToWeiji : Rule :=
  Rule.named "既济→未济" (hexSexp Hexagram.complete) (hexSexp Hexagram.incomplete)

/-- Default rule list: 6 atomic flips + 3 named transitions. -/
def defaultRules : List Rule :=
  [flip1Rule, flip2Rule, flip3Rule, flip4Rule, flip5Rule, flip6Rule,
   qianToKun, kunToQian, jijiToWeiji]

/-! ## § 7 Smoke tests -/

/-- 乾 → 坤 in one step (the named rule is reachable; pattern matches first
    on flip1 which converts 阳→阴 at y1). After enough fuel we reach 坤. -/
example :
    (Eval.runRules defaultRules (printCell Hexagram.heaven) 6 == printCell Hexagram.earth) = true := by
  native_decide

/-- 坤 → 乾 via the named rule (pattern is more specific than per-yao flips). -/
example :
    (Eval.runRules defaultRules (printCell Hexagram.earth) 1 == printCell Hexagram.heaven) = true := by
  native_decide

/-- runCell convenience: starting at 乾 returns OK. -/
example : (runCell (α := Cell) defaultRules Hexagram.heaven 1).toOption.isSome = true := by
  native_decide

/-- Round-trip via printCell ∘ parseCell at 乾. -/
example : parseCell (printCell Hexagram.heaven) = .ok Hexagram.heaven :=
  print_parse_round_trip _

/-- Round-trip at 既济. -/
example : parseCell (printCell Hexagram.complete) = .ok Hexagram.complete :=
  print_parse_round_trip _

/-! ## § 8 L6 summary bundle -/

/-- Public summary of R₆ Hexagram layer:
    cardinality = 64, 6 atomic generators, Cayley involution + identity, round-trip parse. -/
theorem L6_summary :
    LangLayer.cardinality (α := Cell) = 64
    ∧ (LangLayer.atomicOps (α := Cell)).length = 6
    ∧ (∀ c : Cell, apply c c = origin)
    ∧ (∀ c : Cell, apply origin c = c)
    ∧ (∀ c : Cell, parseCell (printCell c) = .ok c)
    ∧ (∀ c s : Cell, cayley c s = apply c s) :=
  ⟨rfl, rfl, apply_self, origin_apply, print_parse_round_trip, fun _ _ => rfl⟩

end SSBX.Foundation.Lang.L6
