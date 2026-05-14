/-
# Wen.SquaringTower.OX — `OX!"..."` literal for `X k` (image-level)

The bit-pattern primary literal of the kernel.  `OX!` accepts an
even-length string of `'o'` and `'x'`, decoded **two characters at a
time** into a single `Image` atom; the resulting cell has type `X k`
where `k = string.length / 2`.

| literal                | type   | cell                                              |
|------------------------|--------|---------------------------------------------------|
| `OX!"oo"`              | `X 1`  | `(Image.oo,)`                              = 道·  |
| `OX!"xo"`              | `X 1`  | `(Image.xo,)`                              = 错·  |
| `OX!"oxox"`            | `X 2`  | `(.ox, .ox)`                               = 综综  |
| `OX!"oooooo"`          | `X 3`  | all-道 hexagram (= 乾)                            |
| `OX!"oxoxox"`          | `X 3`  | all-综 hexagram (= 既济)                          |
| `OX!"xoxoxo"`          | `X 3`  | all-错 hexagram (= 未济)                          |
| `OX!"xxxxxx"`          | `X 3`  | all-错综 hexagram (= 坤)                          |
| `OX!"oooooooo"`        | `X 4`  | the multiplicative identity of `TemporalHexagram` |

## Char-pair decoding

Within each pair `(c₀, c₁)`:

* `c₀ = 'o' / 'x'` is the **α-coordinate** (= the V₄ content-axis bit).
* `c₁ = 'o' / 'x'` is the **β-coordinate** (= the V₄ frame-axis bit).
* Pair → `Image` via `Image.ofPair`:

      "oo" → Image.oo (= 道, e, I)
      "xo" → Image.xo (= 错, a, X)
      "ox" → Image.ox (= 综, b, Z)
      "xx" → Image.xx (= 错综, ab, Y)

## Macro contract

`OX!"..."` validates at parse time:

* the string must consist only of `'o'` and `'x'` characters;
* its length must be even (`length % 2 = 0`).

A length-0 literal `OX!""` is **rejected** to avoid the (legal but
content-free) `X 0`; use `Origin.taiji` from `Layers.lean` instead.
-/

import SSBX.Foundation.Wen.SquaringTower.X
import Lean.Elab.Term

namespace SSBX.Foundation.Wen.SquaringTower

open Lean

/-! ## § 1 Char-pair decoder -/

namespace Image

/-- Decode a pair of `o`/`x` characters into an `Image`.  Used by both
    `X.ofString` and the `OX!` macro.  Anything other than the four
    valid pairs decodes to `Image.oo`; the macro validates the input. -/
@[inline] def ofPair : Char → Char → Image
  | 'o', 'o' => .oo
  | 'x', 'o' => .xo
  | 'o', 'x' => .ox
  | 'x', 'x' => .xx
  | _,   _   => .oo

@[simp] theorem ofPair_oo : ofPair 'o' 'o' = .oo := rfl
@[simp] theorem ofPair_xo : ofPair 'x' 'o' = .xo := rfl
@[simp] theorem ofPair_ox : ofPair 'o' 'x' = .ox := rfl
@[simp] theorem ofPair_xx : ofPair 'x' 'x' = .xx := rfl

end Image

/-! ## § 2 String-level decode helper

`X.ofString` is the runtime helper called by the `OX!` macro after
parse-time validation.  The arity `k` is supplied explicitly by the
macro so that no string-length elaboration is needed at the call site;
characters past position `2 * k - 1` are silently ignored, and missing
positions (k larger than supplied) default to `'o'` (= `Image.oo`).
The macro validates `2 * k = s.length`, so the well-formed case is
exactly the well-typed image. -/

namespace X

/-- Decode the first `2k` characters of an o/x string into an `X k`
    cell.

    Bit-ordering convention: pair `(s_{2i}, s_{2i+1})` decodes to
    `Image.ofPair` at coordinate `i`.  The `OX!` macro guarantees
    `s.length = 2 * k` and the charset is `{'o','x'}` at parse time. -/
def ofString (k : Nat) (s : String) : X k :=
  fun i =>
    let chars := s.toList
    Image.ofPair (chars.getD (2 * i.val) 'o')
                 (chars.getD (2 * i.val + 1) 'o')

end X

/-! ## § 3 The `OX!` macro

Validates length-positive-even and charset, then expands to a
`X.ofString` call typed as `X k` with `k` a numeric literal computed at
parse time. -/

/-- `OX!"oxoxox..."` — bit-pattern primary literal of type `X k` where
    `k = stringLength / 2`.  Validated at parse time:
    only `'o'` / `'x'` characters allowed, length must be positive and
    even. -/
syntax (name := oxBangLit) "OX!" str : term

@[macro oxBangLit]
def expandOxBangLit : Macro := fun stx => do
  match stx with
  | `(OX! $s:str) =>
    let str := s.getString
    let len := str.length
    if len = 0 then
      Macro.throwError "OX! string must be non-empty (use Origin.taiji for X 0)"
    if len % 2 ≠ 0 then
      Macro.throwError s!"OX! string must have even length, got {len} (\"{str}\")"
    for c in str.toList do
      unless c = 'o' || c = 'x' do
        Macro.throwError
          s!"OX! invalid char '{c}' in \"{str}\" (only 'o' and 'x' allowed)"
    let k := len / 2
    let kStx := Lean.quote k
    `(SSBX.Foundation.Wen.SquaringTower.X.ofString $kStx $s)
  | _ => Macro.throwUnsupported

end SSBX.Foundation.Wen.SquaringTower
