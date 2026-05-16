/-
# Lang.Partial.Core — PartialCell-based Lang substrate (proof of concept)

A NEW Lang layer that, unlike `Lang.L1..L7` (which compile S-expressions
into rewrite rules over total `R n` cells), targets the PartialCell-native
`Wen.Core` ISA directly.  A "sentence" in this surface is a sequence of
PartialCell-shaped tokens; parsing yields a `List Wen.Core.Instr` that
the `Wen.Core` machine can execute via `runFuel`.

## Surface tokens (six core forms)

| Token Sexp                  | Compiles to `Instr`                          |
|-----------------------------|----------------------------------------------|
| `(pin <i> <b>)`             | `.mergeBit ⟨i, _⟩ b`  (= `.merge (pinBit i b)`) |
| `(forget <i>)`              | `.forget ⟨i, _⟩`      (= `.restrict (univ.erase i)`) |
| `(flip <i>)`                | `.flipBit ⟨i, _⟩`                            |
| `(write <i> <b>)`           | `.writeBit ⟨i, _⟩ b`                         |
| `(push)` / `(pop)`          | `.push` / `.pop`                             |
| `(halt)`                    | `.halt`                                      |

`<i>` is a decimal digit `0..7`; `<b>` is `0` / `1` (or 阴/阳).  This is
the *minimal* PartialCell surface — enough to drive the entire `Wen.Core`
ISA on its principal primitives (`merge` / `restrict` for §3.7 operation
monism, plus the legacy-parity instructions).

## Yao/Yuan duality at the partial level

Each `Cell := PartialCell 8` simultaneously *is*

* a **yao** (partial datum: a face of the 8-cube of dimension `8 - |support|`)
* a **yuan** (an operator: the pointwise `merge` map `λ c => merge c this`).

Unlike the total-cell layers L1..L7 (where apply = XOR), the PartialCell
apply is `merge` and it can FAIL (`不通` = `none`).  This is the algebraic
root of `Wen.Core`'s `merge` halting semantics.

## What this file shows

* `parseTok` / `printTok` — token-level Sexp bridge for partial-cell ops
* `compile` — sentence (`List Sexp`) → `List Wen.Core.Instr`
* `run` / `runOnInput` — convenience runners that thread through `Wen.Core.runFuel`
* `apply` (PartialCell yuan-as-operator) + `apply_self` (idempotency of self-merge)

No `LangLayer` instance is provided — `LangLayer` requires `apply : α → α → α`
(total), but partial-cell merge is `α → α → Option α`.  The PartialCell
surface is a *fundamentally different* shape from L1..L7; this is the
point of §3.7 operation monism.
-/

import SSBX.Foundation.Lang.Sexp
import SSBX.Foundation.Wen.Core

namespace SSBX.Foundation.Lang.Partial

open SSBX.Foundation.R
open SSBX.Foundation.Wen.Core

/-! ## § 1 Cell type alias + partial Cayley (= merge) -/

/-- The Lang.Partial carrier: a partial cell on 8 positions. -/
abbrev Cell : Type := PartialCell 8

/-- Origin = 道 (the empty partial assignment).  Identity for `apply`. -/
def origin : Cell := PartialCell.dao

/-- Partial Cayley action: `merge`-as-application.  Returns `none` if
    `c` and `s` disagree on a shared specified position (= 不通). -/
def apply (c s : Cell) : Option Cell := PartialCell.merge c s

/-! ## § 2 Partial-cell algebra laws (delegated) -/

theorem apply_dao_left (c : Cell) : apply origin c = some c :=
  PartialCell.dao_merge c

theorem apply_dao_right (c : Cell) : apply c origin = some c :=
  PartialCell.merge_dao c

theorem apply_self (c : Cell) : apply c c = some c :=
  PartialCell.merge_self c

theorem apply_comm (a b : Cell) : apply a b = apply b a :=
  PartialCell.merge_comm a b

/-! ## § 3 Sexp surface — token parser -/

/-- Parse a decimal digit `"0".."7"` into `Fin 8`. -/
private def parseFin8 : String → Except String (Fin 8)
  | "0" => .ok ⟨0, by decide⟩
  | "1" => .ok ⟨1, by decide⟩
  | "2" => .ok ⟨2, by decide⟩
  | "3" => .ok ⟨3, by decide⟩
  | "4" => .ok ⟨4, by decide⟩
  | "5" => .ok ⟨5, by decide⟩
  | "6" => .ok ⟨6, by decide⟩
  | "7" => .ok ⟨7, by decide⟩
  | s   => .error s!"Partial.parseFin8: expected digit 0-7, got '{s}'"

/-- Parse a bit token: `0` / `阴` / `false` → false; `1` / `阳` / `true` → true. -/
private def parseBit : String → Except String Bool
  | "0" | "阴" | "false" => .ok false
  | "1" | "阳" | "true"  => .ok true
  | s   => .error s!"Partial.parseBit: expected bit, got '{s}'"

/-- Parse a single surface token (one Sexp) into a `Wen.Core.Instr`.

    Accepts the six core forms documented in the file header. -/
def parseTok : Sexp → Except String Instr
  | .list [.atom "pin",    .atom si, .atom sb] => do
      let i ← parseFin8 si
      let b ← parseBit sb
      .ok (.mergeBit i b)
  | .list [.atom "forget", .atom si]            => do
      let i ← parseFin8 si
      .ok (.forget i)
  | .list [.atom "flip",   .atom si]            => do
      let i ← parseFin8 si
      .ok (.flipBit i)
  | .list [.atom "write",  .atom si, .atom sb]  => do
      let i ← parseFin8 si
      let b ← parseBit sb
      .ok (.writeBit i b)
  | .list [.atom "push"]                        => .ok .push
  | .list [.atom "pop"]                         => .ok .pop
  | .list [.atom "halt"]                        => .ok .halt
  | s => .error s!"Partial.parseTok: unrecognized token {s.toStr}"

/-! ## § 4 Sexp surface — token printer -/

/-- Print a `Fin 8` index as a decimal-digit atom. -/
private def printFin8 : Fin 8 → Sexp
  | ⟨0, _⟩ => .atom "0"  | ⟨1, _⟩ => .atom "1"
  | ⟨2, _⟩ => .atom "2"  | ⟨3, _⟩ => .atom "3"
  | ⟨4, _⟩ => .atom "4"  | ⟨5, _⟩ => .atom "5"
  | ⟨6, _⟩ => .atom "6"  | ⟨7, _⟩ => .atom "7"

private def printBit : Bool → Sexp
  | true  => .atom "阳"
  | false => .atom "阴"

/-- Canonical printer for the v1 surface.  Total `Instr` values that
    correspond to a v1 surface token are printed back to their canonical
    Sexp; non-surface constructors (arbitrary `.merge` / `.restrict`,
    `.nop`, `.jump`, `.branchBitEq`, `.xorMask`) are printed in a
    diagnostic placeholder form (not round-trippable — those are exposed
    to the host machine but not exposed in the user-facing surface).

    `mergeBit` is exposed via the dedicated `printPin` helper, because
    reverse-decoding an arbitrary `PartialCell 8` to recover its pin
    shape would require non-`rfl` Finset reasoning. -/
def printTok : Instr → Sexp
  | .merge _        => .list [.atom "merge", .atom "<partial>"]
  | .restrict _     => .list [.atom "forget", .atom "<mask>"]
  | .flipBit i      => .list [.atom "flip", printFin8 i]
  | .writeBit i b   => .list [.atom "write", printFin8 i, printBit b]
  | .push           => .list [.atom "push"]
  | .pop            => .list [.atom "pop"]
  | .halt           => .list [.atom "halt"]
  | .nop            => .list [.atom "nop"]
  | .jump t         => .list [.atom "jump", .atom (toString t)]
  | .branchBitEq i b t =>
      .list [.atom "br", printFin8 i, printBit b, .atom (toString t)]
  | .xorMask _      => .list [.atom "xor", .atom "<mask>"]
  | .mergePrior     => .list [.atom "mergePrior"]

/-- Dedicated canonical printer for the `(pin i b)` surface, since the
    underlying `Instr.mergeBit i b = .merge (pinBit i b)` does not
    syntactically expose `i` and `b` to the generic `printTok`. -/
def printPin (i : Fin 8) (b : Bool) : Sexp :=
  .list [.atom "pin", printFin8 i, printBit b]

/-! ## § 5 Compile a sentence -/

/-- Compile a sentence (list of surface tokens) into a `Wen.Core` program.
    Short-circuits on the first malformed token. -/
def compile : List Sexp → Except String (List Instr)
  | []      => .ok []
  | t :: ts => do
      let i  ← parseTok t
      let is ← compile ts
      .ok (i :: is)

/-- Inner driver for `parseSentence` — recursive, marked `partial`
    because `Parser.parseOne` itself is `partial`. -/
partial def parseSentenceLoop : List Char → List Sexp →
    Except String (List Sexp) := fun cs acc =>
  let cs := Parser.skipWS cs
  match cs with
  | []     => .ok acc.reverse
  | _      =>
      match Parser.parseOne cs with
      | .error _      => .error "Partial.parseSentence: parse failure"
      | .ok (s, rest) => parseSentenceLoop rest (s :: acc)

/-- Parse a flat string of whitespace-separated tokens.  Each top-level
    Sexp form is one token; the whole input must parse cleanly. -/
def parseSentence (src : String) : Except String (List Sexp) :=
  parseSentenceLoop src.toList []

/-! ## § 6 Run a compiled program

These convenience runners thread an Sexp sentence all the way through
parse → compile → execute → final partial cell. -/

/-- Compile + run on the empty `initial` state for the given fuel budget. -/
def runFromOrigin (prog : List Instr) (fuel : Nat) : State :=
  runFuel prog fuel State.initial

/-- Compile + run on input lifted to a fully-specified `PartialCell`. -/
def runFromInput (prog : List Instr) (input : R 8) (fuel : Nat) : State :=
  runFuel prog fuel (State.init input)

/-- End-to-end: tokens → program → final state (or compile error). -/
def runTokens (toks : List Sexp) (fuel : Nat) : Except String State := do
  let prog ← compile toks
  .ok (runFromOrigin prog fuel)

/-! ## § 7 Self-consistency theorems (no sorry) -/

/-- The dedicated `printPin i b` token parses back to `.mergeBit i b`. -/
theorem parseTok_pin (i : Fin 8) (b : Bool) :
    parseTok (printPin i b) = .ok (.mergeBit i b) := by
  fin_cases i <;> cases b <;> rfl

/-- `(flip <i>)` printed by `printTok` parses back to `.flipBit i`. -/
theorem parseTok_flip (i : Fin 8) :
    parseTok (printTok (.flipBit i)) = .ok (.flipBit i) := by
  fin_cases i <;> rfl

/-- `(write <i> <b>)` is round-trippable. -/
theorem parseTok_write (i : Fin 8) (b : Bool) :
    parseTok (printTok (.writeBit i b)) = .ok (.writeBit i b) := by
  fin_cases i <;> cases b <;> rfl

/-- `(push)` is round-trippable. -/
theorem parseTok_push : parseTok (printTok .push) = .ok .push := rfl

/-- `(pop)` is round-trippable. -/
theorem parseTok_pop : parseTok (printTok .pop) = .ok .pop := rfl

/-- `(halt)` is round-trippable. -/
theorem parseTok_halt : parseTok (printTok .halt) = .ok .halt := rfl

/-! ## § 8 Public summary bundle -/

/-- Partial-cell Lang substrate summary:
    * cell space = `PartialCell 8` (256-vertex 8-cube, every face)
    * 道 is the origin = merge identity = empty assignment
    * apply = `merge`, partial (returns `none` on 不通 conflict)
    * round-trip parse/print holds on the v1 surface (pin/flip/write/push/pop/halt). -/
theorem partial_summary :
    apply origin origin = some (origin : Cell)
    ∧ (∀ c : Cell, apply origin c = some c)
    ∧ (∀ c : Cell, apply c c = some c)
    ∧ (∀ i : Fin 8, ∀ b : Bool,
        parseTok (printPin i b) = .ok (.mergeBit i b))
    ∧ parseTok (printTok .halt) = .ok .halt :=
  ⟨apply_self origin, apply_dao_left, apply_self,
   parseTok_pin, parseTok_halt⟩

end SSBX.Foundation.Lang.Partial
