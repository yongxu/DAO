/-
# L1 — R₁ Yao layer (the smoke test)

The smallest non-trivial R-layer. Cell space `Yao = {yang, yin}` (= (Z/2)¹).
The Cayley action is XOR-with-yang = negation; XOR-with-yin = identity.

## Surface syntax

```
(yao 阳)  or  (yao yang)  or  (yao 1)        — the yang cell
(yao 阴)  or  (yao yin)   or  (yao 0)        — the yin cell
```

Canonical printer output uses 阳/阴.

## Yao/Yuan duality at L1

- **yin** is both the *yin position* (a value in Yao) and the *identity operator*
  (its Cayley action is `λ y => yin ⊕ y = y`).
- **yang** is both the *yang position* and the *negation operator* (its Cayley
  action is `λ y => yang ⊕ y = y.neg`).

This is established by `apply_eq_neg_when_yang` and `apply_eq_id_when_yin`,
which together pin down the Cayley regular representation.

## Test programs

Two example rules are pre-defined (`toggleYin`, `toggleYang`); a smoke test
program reaches a fixed point in 1 step.
-/

import SSBX.Foundation.Lang.Core
import SSBX.Foundation.Atlas.Yi.Names

namespace SSBX.Foundation.Lang.L1

open SSBX.Foundation.Atlas.Yi (Yao)

/-! ## § 1 Cell type alias + Cayley action -/

/-- L1 cell carrier = Yao (= (Z/2)¹, 2 atoms). -/
abbrev Cell : Type := Yao

/-- Cayley action: `apply x y = x ⊕ y` realized on the 2-element Yao. -/
def apply : Cell → Cell → Cell
  | .yin,  y => y
  | .yang, y => y.neg

/-- The (Z/2)¹ origin / identity. -/
def origin : Cell := .yin

/-! ## § 2 Cayley action laws -/

theorem apply_self (c : Cell) : apply c c = origin := by
  cases c <;> rfl

theorem origin_apply (c : Cell) : apply origin c = c := by
  cases c <;> rfl

theorem apply_eq_neg_when_yang (y : Cell) : apply .yang y = y.neg := rfl

theorem apply_eq_id_when_yin (y : Cell) : apply .yin y = y := rfl

/-! ## § 3 Sexp bridge -/

/-- Parse `(yao …)` to a Yao cell. Accepts 阳/yang/1 for yang, 阴/yin/0 for yin. -/
def parseCell : Sexp → Except String Cell
  | .list [.atom "yao", .atom token] =>
      match token with
      | "阳" | "yang" | "1" => .ok .yang
      | "阴" | "yin"  | "0" => .ok .yin
      | other => .error s!"L1.parseCell: unknown yao token '{other}'"
  | s => .error s!"L1.parseCell: expected (yao <token>), got {s.toStr}"

/-- Canonical printer: 阳/阴. -/
def printCell : Cell → Sexp
  | .yang => .list [.atom "yao", .atom "阳"]
  | .yin  => .list [.atom "yao", .atom "阴"]

theorem print_parse_round_trip (c : Cell) : parseCell (printCell c) = .ok c := by
  cases c <;> rfl

/-! ## § 4 LangLayer instance -/

instance : LangLayer Cell where
  parseCell    := parseCell
  printCell    := printCell
  apply        := apply
  origin       := origin
  cardinality  := 2
  atomicOps    := [.yang]
  apply_self   := apply_self
  origin_apply := origin_apply

/-! ## § 5 Example rules + smoke test -/

/-- The two atomic rewrite rules at L1: toggle a yin to yang, and back. -/
def toggleYin : Rule :=
  Rule.named "toggle-yin"
    (.list [.atom "yao", .atom "阴"])
    (.list [.atom "yao", .atom "阳"])

def toggleYang : Rule :=
  Rule.named "toggle-yang"
    (.list [.atom "yao", .atom "阳"])
    (.list [.atom "yao", .atom "阴"])

/-- Default rule list at L1: both toggles. -/
def defaultRules : List Rule := [toggleYin, toggleYang]

/-- Single step from yin lands at yang. -/
example :
    (Eval.runRules defaultRules (printCell .yin) 1 == printCell .yang) = true := by
  native_decide

/-- Five steps alternates: yin → yang → yin → yang → yin → yang. -/
example :
    (Eval.runRules defaultRules (printCell .yin) 5 == printCell .yang) = true := by
  native_decide

/-- Two steps from yin returns to yin (involution closure). -/
example :
    (Eval.runRules defaultRules (printCell .yin) 2 == printCell .yin) = true := by
  native_decide

/-- runCell convenience produces an OK result. -/
example : (runCell (α := Cell) defaultRules .yin 1).toOption.isSome = true := by
  native_decide

example : (runCell (α := Cell) defaultRules .yin 4).toOption.isSome = true := by
  native_decide

/-! ## § 6 L1 summary bundle -/

/-- Public summary of R₁ Yao layer:
    cardinality = 2, single atomic op (yang), Cayley duality, round-trip parse. -/
theorem L1_summary :
    LangLayer.cardinality (α := Cell) = 2
    ∧ (LangLayer.atomicOps (α := Cell)).length = 1
    ∧ (∀ c : Cell, apply c c = origin)
    ∧ (∀ c : Cell, parseCell (printCell c) = .ok c)
    ∧ (∀ c s : Cell, cayley c s = apply c s) :=
  ⟨rfl, rfl, apply_self, print_parse_round_trip, fun _ _ => rfl⟩

end SSBX.Foundation.Lang.L1
