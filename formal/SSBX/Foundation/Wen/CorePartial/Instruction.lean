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

## ISA (5 primitives)

| # | Constructor          | Effect on `cur : PartialCell 8` | pc update |
|---|----------------------|----------------------------------|-----------|
| 1 | `nop`                | unchanged                        | pc+1      |
| 2 | `merge c`            | `cur ⊔ c` (or halt if 不通)      | pc+1      |
| 3 | `restrict s`         | `cur ↾ s` (forget bits ∉ s)      | pc+1      |
| 4 | `jump t`             | unchanged                        | t         |
| 5 | `halt`               | unchanged                        | unchanged + halted |

Five primitives suffice for Phase E.1: `merge` + `restrict` already give
the full partial-cell lattice; `jump` + `halt` give linear-ish control.
Conditional branches arrive in Phase E.2.

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

/-- The 5-constructor PartialCell-native instruction type.

    Per §3.7 operation monism, all "operations" are now expressed in
    terms of the partial-cell algebra (`merge`, `restrict`); control
    flow (`jump`, `halt`) is orthogonal.  `nop` is included for
    convenience but is definitionally `merge PartialCell.dao`. -/
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

end Instr

end SSBX.Foundation.Wen.CorePartial
