/-
# L4 — R₄ Mian layer (Ben × Zheng = (Z/2)⁴ = 16)

R₄ Cell space: `Mian = Ben × Zheng`, the 16-cell 本征 product.
The Cayley action is componentwise XOR on the (Bool × Bool) × (Bool × Bool)
encoding. 4 atomic single-bit-flip masks span the group.

## Bool encoding

```
Ben.thing   ↔ (F,F)    Zheng.trace    ↔ (F,F)
Ben.motion ↔ (T,F)    Zheng.momentum   ↔ (T,F)
Ben.interval ↔ (F,T)    Zheng.pivot ↔ (F,T)
Ben.event  ↔ (T,T)    Zheng.occasion    ↔ (T,T)
```

XOR is per-component `xor`. Origin = `(thing, trace)` = (F,F,F,F).

## Surface syntax

```
(mian <ben-char> <zheng-char>)
```

e.g. `(mian 物 几)` is the origin. The two character columns reuse the
chars from `BenZheng.lean` (`Ben.char` / `Zheng.char`).
-/

import SSBX.Foundation.Lang.Core
import SSBX.Foundation.Bagua.BenZheng

namespace SSBX.Foundation.Lang.L4

open SSBX.Foundation.Bagua.BenZheng

/-! ## § 1 Cell carrier -/

/-- L4 cell carrier = Mian = Ben × Zheng (16 cells). -/
abbrev Cell : Type := Mian

/-! ## § 2 Bool encoding + XOR -/

/-- Ben → (Bool, Bool) (low, high). -/
def benToBits : Ben → Bool × Bool
  | .thing   => (false, false)
  | .motion => (true,  false)
  | .interval => (false, true)
  | .event  => (true,  true)

/-- (Bool, Bool) → Ben. -/
def benFromBits : Bool × Bool → Ben
  | (false, false) => .thing
  | (true,  false) => .motion
  | (false, true)  => .interval
  | (true,  true)  => .event

/-- Zheng → (Bool, Bool). -/
def zhengToBits : Zheng → Bool × Bool
  | .trace    => (false, false)
  | .momentum   => (true,  false)
  | .pivot => (false, true)
  | .occasion    => (true,  true)

/-- (Bool, Bool) → Zheng. -/
def zhengFromBits : Bool × Bool → Zheng
  | (false, false) => .trace
  | (true,  false) => .momentum
  | (false, true)  => .pivot
  | (true,  true)  => .occasion

/-- XOR on Ben (componentwise). -/
def benXor (a b : Ben) : Ben :=
  let (a0, a1) := benToBits a
  let (b0, b1) := benToBits b
  benFromBits (xor a0 b0, xor a1 b1)

/-- XOR on Zheng (componentwise). -/
def zhengXor (a b : Zheng) : Zheng :=
  let (a0, a1) := zhengToBits a
  let (b0, b1) := zhengToBits b
  zhengFromBits (xor a0 b0, xor a1 b1)

/-- Cayley action on Mian: componentwise XOR. -/
def apply : Cell → Cell → Cell
  | (b1, z1), (b2, z2) => (benXor b1 b2, zhengXor z1 z2)

/-- The (Z/2)⁴ origin. -/
def origin : Cell := (.thing, .trace)

/-! ## § 3 Cayley action laws -/

theorem apply_self (c : Cell) : apply c c = origin := by
  rcases c with ⟨b, z⟩
  cases b <;> cases z <;> rfl

theorem origin_apply (c : Cell) : apply origin c = c := by
  rcases c with ⟨b, z⟩
  cases b <;> cases z <;> rfl

/-! ## § 4 Sexp bridge -/

/-- Parse `(mian <ben-token> <zheng-token>)`. Tokens use `Ben.char` /
    `Zheng.char` (or their traditional variants, via `fromChar`). -/
def parseCell : Sexp → Except String Cell
  | .list [.atom "mian", .atom bTok, .atom zTok] =>
      match Ben.fromChar bTok, Zheng.fromChar zTok with
      | some b, some z => .ok (b, z)
      | none,   _      => .error s!"L4.parseCell: unknown ben token '{bTok}'"
      | _,      none   => .error s!"L4.parseCell: unknown zheng token '{zTok}'"
  | s => .error s!"L4.parseCell: expected (mian <ben> <zheng>), got {s.toStr}"

/-- Canonical printer: `(mian <ben.char> <zheng.char>)`. -/
def printCell : Cell → Sexp
  | (b, z) => .list [.atom "mian", .atom b.char, .atom z.char]

theorem print_parse_round_trip (c : Cell) : parseCell (printCell c) = .ok c := by
  rcases c with ⟨b, z⟩
  cases b <;> cases z <;> rfl

/-! ## § 5 LangLayer instance -/

/-- The 4 atomic single-bit-flip masks (yao bases of (Z/2)⁴). -/
def atomicOps : List Cell :=
  [ (.motion, .trace)    -- flip Ben bit 0
  , (.interval, .trace)    -- flip Ben bit 1
  , (.thing,   .momentum)   -- flip Zheng bit 0
  , (.thing,   .pivot) -- flip Zheng bit 1
  ]

instance : LangLayer Cell where
  parseCell    := parseCell
  printCell    := printCell
  apply        := apply
  origin       := origin
  cardinality  := 16
  atomicOps    := atomicOps
  apply_self   := apply_self
  origin_apply := origin_apply

/-! ## § 6 Default rules + smoke tests -/

/-- Helper: build a `(mian b z)` Sexp. -/
private def mianSexp (b : Ben) (z : Zheng) : Sexp :=
  .list [.atom "mian", .atom b.char, .atom z.char]

/-- Atomic flip: 物几 → 动几 (toggle Ben bit 0). -/
def flipBen0 : Rule :=
  Rule.named "flip-ben0"
    (mianSexp .thing   .trace)
    (mianSexp .motion .trace)

/-- Atomic flip: 物几 → 间几 (toggle Ben bit 1). -/
def flipBen1 : Rule :=
  Rule.named "flip-ben1"
    (mianSexp .thing   .trace)
    (mianSexp .interval .trace)

/-- Atomic flip: 物几 → 物势 (toggle Zheng bit 0). -/
def flipZheng0 : Rule :=
  Rule.named "flip-zheng0"
    (mianSexp .thing .trace)
    (mianSexp .thing .momentum)

/-- Atomic flip: 物几 → 物机 (toggle Zheng bit 1). -/
def flipZheng1 : Rule :=
  Rule.named "flip-zheng1"
    (mianSexp .thing .trace)
    (mianSexp .thing .pivot)

/-- Compound example: 动几 → 动势 (advance Zheng bit 0 within Ben.motion row). -/
def benDongAdvance : Rule :=
  Rule.named "ben-motion-advance"
    (mianSexp .motion .trace)
    (mianSexp .motion .momentum)

/-- Compound example: 动势 → 事势 (climb Ben column from motion to event). -/
def zhengShiForceClimb : Rule :=
  Rule.named "zheng-shiforce-climb"
    (mianSexp .motion .momentum)
    (mianSexp .event  .momentum)

/-- Default rule list at L4: 4 atomic flips + 2 compound steps. -/
def defaultRules : List Rule :=
  [flipBen0, flipBen1, flipZheng0, flipZheng1,
   benDongAdvance, zhengShiForceClimb]

/-- Single step from origin reaches (动, 几). -/
example :
    (Eval.runRules defaultRules (printCell origin) 1
      == printCell (.motion, .trace)) = true := by
  native_decide

/-- Two steps: origin → (动, 几) → (动, 势). -/
example :
    (Eval.runRules defaultRules (printCell origin) 2
      == printCell (.motion, .momentum)) = true := by
  native_decide

/-- Three steps reach (事, 势). -/
example :
    (Eval.runRules defaultRules (printCell origin) 3
      == printCell (.event, .momentum)) = true := by
  native_decide

/-- runCell convenience produces an OK result. -/
example : (runCell (α := Cell) defaultRules origin 3).toOption.isSome = true := by
  native_decide

/-- Round-trip on a non-trivial cell (间, 时). -/
example : parseCell (printCell (.interval, .occasion)) = .ok (.interval, .occasion) := rfl

/-! ## § 7 L4 summary bundle -/

/-- Public summary of R₄ Mian layer:
    cardinality = 16, 4 atomic ops, Cayley involution, round-trip parse. -/
theorem L4_summary :
    LangLayer.cardinality (α := Cell) = 16
    ∧ (LangLayer.atomicOps (α := Cell)).length = 4
    ∧ (∀ c : Cell, apply c c = origin)
    ∧ (∀ c : Cell, parseCell (printCell c) = .ok c)
    ∧ (∀ c s : Cell, cayley c s = apply c s) :=
  ⟨rfl, rfl, apply_self, print_parse_round_trip, fun _ _ => rfl⟩

end SSBX.Foundation.Lang.L4
