/-
# Foundation.Wen.CorePartial.Instruction — PartialCell-native ISA

Per §3.7 operation monism (操作 ≡ 位 ≡ 内容) and the `PartialCell` doctrine
(Foundation/R/PartialCell.lean), this is the **PartialCell-native** rewrite
of `Foundation/Wen/Core/Instruction.lean`.

Key differences from the legacy `Wen.Core` ISA:

* State carries a `PartialCell 8`, not an `R 8`.  Partial (under-specified)
  states are now **first-class** — the system can represent "unknown bit".
* `merge` and `restrict` are **primitive instructions**.  These are the
  partial-cell algebra primitives (Phase D) elevated to ISA citizens —
  the language no longer makes a category split between "data ops" and
  "control ops"; both are simply ways to manipulate the cell.
* The `不通 / ungrammatical` outcome of `merge` is interpreted as **halt**:
  a program is *stuck* when its next operation would conflict with state.

## ISA (11 primitives — Phase E.3 feature-parity with `Wen.Core`)

| # | Constructor          | Effect on `cur : PartialCell 8` | pc update |
|---|----------------------|----------------------------------|-----------|
| 1 | `nop`                | unchanged                        | pc+1      |
| 2 | `merge c`            | `cur ⊔ c` (or halt if 不通)      | pc+1      |
| 3 | `restrict s`         | `cur ↾ s` (forget bits ∉ s)      | pc+1      |
| 4 | `push`               | history := cur :: history        | pc+1      |
| 5 | `pop`                | cur := head of history (or no-op)| pc+1      |
| 6 | `flipBit i`          | flip cur i if defined; no-op if `none` | pc+1 |
| 7 | `writeBit i b`       | `cur i := some b` (overwrite)    | pc+1      |
| 8 | `xorMask m`          | flip each defined bit `i` where `m i = true` | pc+1 |
| 9 | `branchBitEq i b t`  | unchanged                        | t if `cur i = some b`, else pc+1 |
| 10| `jump t`             | unchanged                        | t         |
| 11| `halt`               | unchanged                        | unchanged + halted |

`merge` and `restrict` (#2, #3) are the PartialCell-native primitives;
they have no analogue in legacy `Wen.Core` (where state is total `R 8`).
The other 9 are direct PartialCell-aware liftings of `Wen.Core`'s ISA.

### PartialCell-aware adaptations

* `flipBit i`: in legacy core, always toggles; here, **toggles only if
  bit is defined** (`cur i = some b → some !b`); leaves `none` alone.
  This preserves the doctrine that partial cells encode *commitment*,
  and "no commitment" is not toggled by negation.
* `writeBit i b`: overwrites unconditionally — definitionally
  equivalent to `restrict (univ.erase i); merge (pinBit i b)` but
  exposed as a single instruction for parity.
* `xorMask m` (where `m : R 8`): for each i, `cur i = some b → some
  (b ⊕ m i)` if `m i = true`, otherwise unchanged.  `none` bits stay
  `none`.
* `branchBitEq i b t`: fires only on `cur i = some b`; `none` falls
  through (partial commitment policy).
* `pop`: replaces `cur` with history head (legacy semantics; lose
  current refinement).  If history empty, no-op.

These adaptations are *forced* by the PartialCell substrate — they're
the only sensible extension of `Wen.Core` semantics to partial states.

## Why so much smaller than `Wen.Core` (which had 8 primitives)?

Because `flipBit`, `writeBit`, `xorMask`, `push`, `pop` are all
*expressible* via `merge` with appropriately-shaped partial cells.  The
ISA shrank because the substrate is more expressive: one operation
(merge) replaces multiple bespoke primitives.

## Doctrinal anchor

* `wen-substrate.md` v1.2 §3.7 (Operation Monism).
* `Foundation/R/PartialCell.lean` (Phase A-D partial-cell algebra).
-/

import SSBX.Foundation.R.PartialCell

namespace SSBX.Foundation.Wen.CorePartial

open SSBX.Foundation.R

/-- The 11-constructor PartialCell-native instruction type.

    Per §3.7 operation monism, all "operations" are now expressed in
    terms of the partial-cell algebra; control flow (`jump`, `halt`,
    `branchBitEq`) is orthogonal.  See file header for the full ISA
    table. -/
inductive Instr where
  /-- No-op.  Equivalent to `merge dao` (merging the empty assignment
      leaves the state unchanged). -/
  | nop
  /-- Merge a constant partial cell `c` into the current state.
      If the merge is incompatible (`不通`), the machine halts. -/
  | merge (c : PartialCell 8)
  /-- Restrict the current state to the sub-mask `s`: positions outside
      `s` become `none` (codim-increasing). -/
  | restrict (s : Finset (Fin 8))
  /-- Push the current `cur` onto the history stack.  Snapshot for
      later `pop` (legacy `Wen.Core` parity). -/
  | push
  /-- Pop the top of the history stack into `cur`, replacing current
      state.  No-op if history is empty. -/
  | pop
  /-- Flip bit `i` of `cur` — only if defined.  `some b ↔ some !b`;
      `none` stays `none` (PartialCell-aware: partial commitment is
      not toggled). -/
  | flipBit (i : Fin 8)
  /-- Overwrite bit `i` to `some b` regardless of current value.
      (Equivalent to `restrict (univ.erase i); merge (pinBit i b)` but
      exposed atomically for legacy parity.) -/
  | writeBit (i : Fin 8) (b : Bool)
  /-- XOR `cur` with full mask `m : R 8`.  For each `i` with `m i =
      true`, flip `cur i` if defined; leave `none` alone. -/
  | xorMask (m : R 8)
  /-- Conditional branch: jump to `t` if `cur i = some b` (the bit is
      explicitly specified to `b`); fall through to pc+1 otherwise.
      In particular, when `cur i = none`, the branch does NOT fire. -/
  | branchBitEq (i : Fin 8) (b : Bool) (t : Nat)
  /-- Unconditional jump to instruction index `t`. -/
  | jump (t : Nat)
  /-- Halt. -/
  | halt

namespace Instr

/-! ## § Convenience constructors -/

/-- Single-bit partial cell: pins position `i` to value `b`, leaves
    other positions unspecified.  Useful for `merge (pinBit i b)`. -/
def pinBit (i : Fin 8) (b : Bool) : PartialCell 8 :=
  fun j => if j = i then some b else none

/-- `mergeBit i b` — `merge` with a single-bit pin. -/
@[reducible] def mergeBit (i : Fin 8) (b : Bool) : Instr :=
  .merge (pinBit i b)

/-- `forget i` — restrict to the complement of `{i}`, i.e., un-specify
    position `i` (codim-1 forgetting). -/
@[reducible] def forget (i : Fin 8) : Instr :=
  .restrict ((Finset.univ : Finset (Fin 8)).erase i)

/-- Branch if bit `i` is explicitly `true`. -/
@[reducible] def branchIfSet (i : Fin 8) (t : Nat) : Instr :=
  .branchBitEq i true t

/-- Branch if bit `i` is explicitly `false`. -/
@[reducible] def branchIfClear (i : Fin 8) (t : Nat) : Instr :=
  .branchBitEq i false t

end Instr

end SSBX.Foundation.Wen.CorePartial
