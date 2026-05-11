/-
# OXNotation — `OX["..."]` 8-char string literal for R8

Encodes a `R8 = Hexagram × Shi` as an 8-character ASCII string of
`o` and `x`:

  - chars 0..5 (positions 1..6): six yao of the Hexagram, **inner-to-outer**
                                  (string[0] = y1 = 初爻, string[5] = y6 = 上爻).
                                  `o` → identity bit → `Yao.yang`,
                                  `x` →   set    bit → `Yao.yin`.
                                  This convention makes
                                  `OX["oooooo··"] = Hexagram.heaven` (the (Z/2)⁶
                                  identity / origin) and
                                  `OX["xxxxxx··"] = Hexagram.earth`.
  - char 6 : YinBit (因 axis, R5)   `o` → false, `x` → true.
  - char 7 : GuoBit (果 axis, R6)   `o` → false, `x` → true.

  Shi is recovered via `Shi.ofYinGuo (yinBit, guoBit)` :
    "oo" → 道 (dao,  V₄ identity)
    "xo" → 已 (ji)
    "ox" → 未 (wei)
    "xx" → 今 (jin, PT)

So `OX["oooooooo"] = (Hexagram.heaven, Shi.dao) = R8.origin`,
the (Z/2)⁸ identity element / 道 of the 256-cell algebra.

Errors at parse time on any string of length ≠ 8 or containing chars
other than `o`/`x`.
-/
import SSBX.Foundation.Bagua.R8

namespace SSBX.Foundation.Notation.OXNotation

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open Lean

/-! ## § 1 String → R8 helpers (used by the macro at elaboration time) -/

/-- Map an `o`/`x` char to its `Yao`: `o` → yang (identity), `x` → yin. -/
@[inline] def yaoOfChar : Char → Yao
  | 'x' => Yao.yin
  | _   => Yao.yang  -- treats 'o' (and anything else, validated by macro) as yang

/-- Map an `o`/`x` char to its `Bool`: `o` → false, `x` → true. -/
@[inline] def boolOfChar : Char → Bool
  | 'x' => true
  | _   => false

/-- Decode an 8-char `o`/`x` string to `R8 = Hexagram × Shi`.
    The macro validates length and charset; this helper handles short
    strings by defaulting unspecified positions to `o` (yang / false bit). -/
def cellOfString (s : String) : R8 :=
  match s.toList with
  | [c0, c1, c2, c3, c4, c5, c6, c7] =>
      (⟨yaoOfChar c0, yaoOfChar c1, yaoOfChar c2,
        yaoOfChar c3, yaoOfChar c4, yaoOfChar c5⟩,
       Shi.ofYinGuo (boolOfChar c6, boolOfChar c7))
  | _ => (Hexagram.heaven, Shi.dao)  -- unreachable when macro validates length

/-! ## § 2 Macro `OX["..."]` — parse-time validation + R8 term -/

/-- `OX[" o/x ×8 "]` term-level macro producing a `R8`. -/
syntax (name := oxLit) "OX[" str "]" : term

/-- Build a syntactic `Yao` term: `Yao.yang` for `o`, `Yao.yin` for `x`. -/
private def yaoStxOfChar (c : Char) : MacroM (TSyntax `term) :=
  match c with
  | 'o' => `(SSBX.Foundation.Yi.Yi.Yao.yang)
  | 'x' => `(SSBX.Foundation.Yi.Yi.Yao.yin)
  | _   => Macro.throwError s!"OX: invalid char '{c}' (only 'o' and 'x' allowed)"

/-- Build a syntactic `Bool` term: `false` for `o`, `true` for `x`. -/
private def boolStxOfChar (c : Char) : MacroM (TSyntax `term) :=
  match c with
  | 'o' => `(false)
  | 'x' => `(true)
  | _   => Macro.throwError s!"OX: invalid char '{c}' (only 'o' and 'x' allowed)"

@[macro oxLit]
def expandOxLit : Macro := fun stx => do
  match stx with
  | `(OX[ $s:str ]) =>
    let str := s.getString
    match str.toList with
    | [c0, c1, c2, c3, c4, c5, c6, c7] =>
      -- Validate: every char must be 'o' or 'x'
      for c in [c0, c1, c2, c3, c4, c5, c6, c7] do
        unless c = 'o' || c = 'x' do
          Macro.throwError
            s!"OX: invalid char '{c}' in \"{str}\" (only 'o' and 'x' allowed)"
      let y1 ← yaoStxOfChar c0
      let y2 ← yaoStxOfChar c1
      let y3 ← yaoStxOfChar c2
      let y4 ← yaoStxOfChar c3
      let y5 ← yaoStxOfChar c4
      let y6 ← yaoStxOfChar c5
      let yinB ← boolStxOfChar c6
      let guoB ← boolStxOfChar c7
      `((SSBX.Foundation.Yi.Yi.Hexagram.mk
            $y1 $y2 $y3 $y4 $y5 $y6,
         SSBX.Foundation.Bagua.R8.Shi.ofYinGuo ($yinB, $guoB)))
    | _ =>
      Macro.throwError
        s!"OX: string must have length 8, got {str.length} (\"{str}\")"
  | _ => Macro.throwUnsupported

/-! ## § 3 Examples / tests — verifies macro evaluates by `rfl` -/

/-- All-`o` 8-string = (heaven, dao) = R8.origin = (Z/2)⁸ identity. -/
example : OX["oooooooo"] = (Hexagram.heaven, Shi.dao) := rfl

/-- Char 7 = `x` flips YinBit only ⇒ Shi.ji (已). -/
example : OX["ooooooxo"] = (Hexagram.heaven, Shi.ji) := rfl

/-- Char 8 = `x` flips GuoBit only ⇒ Shi.wei (未). -/
example : OX["ooooooox"] = (Hexagram.heaven, Shi.wei) := rfl

/-- Both Shi bits set ⇒ Shi.jin (今, PT central element). -/
example : OX["ooooooxx"] = (Hexagram.heaven, Shi.jin) := rfl

/-- All-`x` Hexagram part = Hexagram.earth (all yin); Shi.jin (PT). -/
example : OX["xxxxxxxx"] = (Hexagram.earth, Shi.jin) := rfl

/-- Hexagram only (Shi = dao): char 0 = y1 = `x` flips initial yao only.
    Result is Hexagram with y1 = yin, y2..y6 = yang. -/
example :
    OX["xooooooo"] =
      (Hexagram.mk Yao.yin Yao.yang Yao.yang Yao.yang Yao.yang Yao.yang,
       Shi.dao) := rfl

/-- char 5 = y6 = `x` flips top yao only. -/
example :
    OX["oooooxoo"] =
      (Hexagram.mk Yao.yang Yao.yang Yao.yang Yao.yang Yao.yang Yao.yin,
       Shi.dao) := rfl

/-- Mixed cell: hexagram-internal flip + Shi.wei. -/
example :
    OX["xoxoxoox"] =
      (Hexagram.mk Yao.yin Yao.yang Yao.yin Yao.yang Yao.yin Yao.yang,
       Shi.wei) := rfl

/-! ## § 4 Origin sanity check via R8 algebra -/

/-- `OX["oooooooo"]` is exactly `R8.origin`. -/
example : OX["oooooooo"] = (R8.origin : R8) := rfl

end SSBX.Foundation.Notation.OXNotation
