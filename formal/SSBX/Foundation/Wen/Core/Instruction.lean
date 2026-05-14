/-
# Foundation.Wen.Core.Instruction — language-independent instruction set on R 8

Per `wen-algebra` v0.6 (especially §10.7 "Interpreter Foundation") and
`r8.md` v0.2 §15.10 "Interpreter primitives", the canonical interpreter
core operates **directly on `R 8 = Fin 8 → Bool`** as a pure F_2^8
bit-machine.  Any semantic naming (Yi 爻/时态, Pauli I/X/Y/Z, Boolean
operators, …) is **Atlas**-level overlay (lives in `Foundation/Atlas/`);
nothing in this subtree carries names from any tradition.

## What is here

* `Instr` — the 8-constructor instruction set, language-independent:
  * `nop`            — no-op, advance pc
  * `flipBit i`      — XOR bit `i` (involutive single-bit toggle)
  * `writeBit i b`   — set bit `i` to literal `b` (idempotent)
  * `branchBitEq i b t` — conditional jump if bit `i` = `b`
  * `jump t`         — unconditional jump
  * `push`           — push current cell onto history
  * `pop`            — pop top of history into current cell (no-op if empty)
  * `halt`           — halt
* `Instr.xorMask m` — convenience constructor (`xorMask` would normally
  XOR with a mask; here we expose it as a primitive macro that decomposes
  into `flipBit` for each set bit when interpreted, but it lives as a
  first-class instruction so that `R 8`-add can be invoked atomically).

This set is universal-Turing: jumps + data-dependent branch + unbounded
`history` list + unbounded program length already give universal
computation by the standard Minsky/two-counter argument.

## What is **not** here

* No `Hexagram`, `Shi`, `Yao`, `Yi*` names.
* No Atlas overlays.
* No Yi-flavoured `interlace / complement / reverse` (those belong to
  `Foundation/Atlas/Yi/`).

## Doctrinal anchor

* `wen-algebra.md` v0.6 §10.7 (Interpreter Foundation primitives).
* `r8.md` v0.2 §15.10 (Interpreter primitives).
* Language-independence principle: `wen-algebra` v0.6 §0.3,
  `r8.md` v0.2 §0.4.
-/

import SSBX.Foundation.R.Basic

namespace SSBX.Foundation.Wen.Core

open SSBX.Foundation.R

/-! ## § 1 The instruction type

`Instr` is the 8-constructor language-independent ISA for the `R 8`
bit-machine.  Each constructor's parameters are typed with only
language-independent kinds: `Fin 8`, `Bool`, `Nat`, and `R 8` itself.

Per `wen-algebra` v0.6 doctrine, **no constructor uses Yi-style or any
other tradition-named domain**.
-/

/-- The 8-constructor language-independent instruction set on `R 8`.

    Each instruction operates on `Foundation.Wen.Core.State` (see
    `State.lean`).  Bit indices live in `Fin 8`; data values are `Bool`;
    pc / jump targets are `Nat`.

    Per `wen-algebra` v0.6 §10.7 and `r8.md` v0.2 §15.10. -/
inductive Instr : Type where
  /-- No-op.  Advance pc by 1. -/
  | nop
  /-- Toggle bit `i` of the current cell.  XOR with `basis i`. -/
  | flipBit (i : Fin 8)
  /-- Set bit `i` of the current cell to the literal `b`. -/
  | writeBit (i : Fin 8) (b : Bool)
  /-- Branch to `target` if bit `i` of the current cell equals `b`;
      otherwise advance pc by 1. -/
  | branchBitEq (i : Fin 8) (b : Bool) (target : Nat)
  /-- Unconditional jump to `target`. -/
  | jump (target : Nat)
  /-- Push the current cell onto the history stack. -/
  | push
  /-- Pop the history stack into the current cell.  No-op if empty
      (advances pc by 1). -/
  | pop
  /-- XOR the current cell with the constant mask `m : R 8`.

      Macro-level convenience: equivalent (under interpretation) to a
      sequence of `flipBit` for each set bit of `m`, but exposed as a
      first-class instruction so the algebraic `R 8`-add can be invoked
      atomically (one fuel unit). -/
  | xorMask (m : R 8)
  /-- Halt. -/
  | halt

/-- Manual `Repr` for `Instr`.  `R 8` is `Fin 8 → Bool` (a function
    type), so `deriving Repr` cannot auto-synthesise; we print the
    `xorMask m` payload as the 8-bit pattern. -/
instance : Repr Instr where
  reprPrec := fun i _ => match i with
    | .nop => "Instr.nop"
    | .flipBit i => s!"Instr.flipBit {i.val}"
    | .writeBit i b => s!"Instr.writeBit {i.val} {b}"
    | .branchBitEq i b t => s!"Instr.branchBitEq {i.val} {b} {t}"
    | .jump t => s!"Instr.jump {t}"
    | .push => "Instr.push"
    | .pop => "Instr.pop"
    | .xorMask m =>
        let bits := (List.range 8).map fun k =>
          if h : k < 8 then m ⟨k, h⟩ else false
        s!"Instr.xorMask {bits}"
    | .halt => "Instr.halt"

namespace Instr

/-! ## § 2 Convenience constructors

These are *macros at the source-level*: they expand into the primitive
`Instr` constructors but read more naturally for common patterns.
-/

/-- Set bit `i` to `true`. -/
@[reducible] def setBit (i : Fin 8) : Instr := .writeBit i true

/-- Clear bit `i` (set to `false`). -/
@[reducible] def clearBit (i : Fin 8) : Instr := .writeBit i false

/-- Branch to `target` if bit `i` is set (true). -/
@[reducible] def branchIfSet (i : Fin 8) (target : Nat) : Instr :=
  .branchBitEq i true target

/-- Branch to `target` if bit `i` is clear (false). -/
@[reducible] def branchIfClear (i : Fin 8) (target : Nat) : Instr :=
  .branchBitEq i false target

end Instr

/-! ## § 3 ISA summary

The eight primitives are:

| # | Constructor       | Effect on `cur : R 8`                  | pc update |
|---|-------------------|----------------------------------------|-----------|
| 1 | `nop`             | unchanged                              | pc+1      |
| 2 | `flipBit i`       | `cur i := !cur i`                      | pc+1      |
| 3 | `writeBit i b`    | `cur i := b`                           | pc+1      |
| 4 | `branchBitEq i b t` | unchanged                            | t or pc+1 |
| 5 | `jump t`          | unchanged                              | t         |
| 6 | `push`            | unchanged, history := cur :: history   | pc+1      |
| 7 | `pop`             | cur := head of history (or unchanged)  | pc+1      |
| 8 | `xorMask m`       | `cur := cur + m` (F_2^8 XOR)           | pc+1      |
| 9 | `halt`            | sets halted := true                    | unchanged |

(Counted: 8 primitives in the table, plus `xorMask` and `halt` for 10
constructors total; `xorMask` is a macro-level convenience kept as a
first-class instruction.  The doctrine number "8" refers to the
**semantic primitive count** {nop, flipBit, writeBit, branchBitEq,
jump, push, pop, halt}; `xorMask` is the optional `R 8`-add primitive
that lets a program leverage the F_2^8 algebra atomically.)
-/

end SSBX.Foundation.Wen.Core
