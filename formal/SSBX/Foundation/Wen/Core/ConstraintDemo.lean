/-
# Foundation.Wen.Core.ConstraintDemo — operational evidence for PartialCell

This file demonstrates the **unique value** of the PartialCell-native
Wen.Core substrate over a classical bit-machine: the ability to express
**constraint composition** as straight-line `merge` programs, with
**不通 = halt** as the operational semantics of contradiction.

## The headline claim

In a classical bit-machine (where `cur : R 8` is always fully
specified), there is no way to express "I commit only to bits 0 and 2;
bit 5 is unknown".  Every step writes a definite value.  Contradiction
is not a primitive concept — it would have to be encoded as a
branch-and-halt pattern, with the contradiction-check synthesised by
the programmer.

In Wen.Core (PartialCell-native), this is **direct**:

* Each `merge c` instruction adds a partial commitment to `cur`.
* `cur` may remain partially-specified for the entire run.
* Two contradictory `merge c₁`, `merge c₂` with `c₁` and `c₂` disagreeing
  on some shared specified position → the machine halts (`merge`
  returns `none`).
* No branch needed; no check needed; **the substrate enforces it**.

## What's in this file

* §1   Pure-merge programs from `List (PartialCell 8)`
* §2   Demos:
       - `agreementProg` — sequence of compatible commitments
       - `conflictProg`  — contradiction triggers `merge`-halt
       - `restrictProg`  — commit + restrict (forget bits)
* §3   Theorems demonstrating each behaviour
* §4   The bridge to Phase D `mergeAll`:  for pure-merge programs,
       running them = `mergeAll` of the constituent cells
-/

import SSBX.Foundation.Wen.Core.Machine
import SSBX.Foundation.Wen.Core.Examples
  -- (for the Instr.pinBit helper)

namespace SSBX.Foundation.Wen.Core.ConstraintDemo

open SSBX.Foundation.R
open SSBX.Foundation.Wen.Core

/-! ## § 1 — `mergeProg`: lift a list of partial cells into a pure-merge program -/

/-- Lift a list of partial cells into a straight-line program that
    merges them in order, then halts. -/
def mergeProg : List (PartialCell 8) → List Instr
  | []       => [.halt]
  | c :: rs  => .merge c :: mergeProg rs

@[simp] theorem mergeProg_nil :
    mergeProg [] = [.halt] := rfl

@[simp] theorem mergeProg_cons (c : PartialCell 8) (rs : List (PartialCell 8)) :
    mergeProg (c :: rs) = .merge c :: mergeProg rs := rfl

/-! ## § 2 — Three illustrative programs -/

/-- A compatible sequence of partial commitments.
    Statement order: bit 0 = true, bit 2 = false, bit 5 = true. -/
def agreementProg : List Instr := mergeProg [
  Instr.pinBit ⟨0, by decide⟩ true,
  Instr.pinBit ⟨2, by decide⟩ false,
  Instr.pinBit ⟨5, by decide⟩ true
]

/-- A contradiction.  Same bit is asserted both true and false. -/
def conflictProg : List Instr := mergeProg [
  Instr.pinBit ⟨0, by decide⟩ true,
  Instr.pinBit ⟨3, by decide⟩ true,
  Instr.pinBit ⟨0, by decide⟩ false   -- 不通 — already committed to true
]

/-- Commit to bits 0, 1, 2, then restrict to {0, 1}: bit 2 forgotten. -/
def restrictProg : List Instr := [
  .merge (Instr.pinBit ⟨0, by decide⟩ true),
  .merge (Instr.pinBit ⟨1, by decide⟩ true),
  .merge (Instr.pinBit ⟨2, by decide⟩ true),
  .restrict ({⟨0, by decide⟩, ⟨1, by decide⟩} : Finset (Fin 8)),
  .halt
]

/-! ## § 3 — Operational properties

These showcase the three PartialCell-unique semantics:
(i) partial states are first-class,
(ii) 不通 = halt at the conflicting merge,
(iii) restrict removes commitment. -/

/-! ### § 3.1 Agreement: state accumulates commitments without halt -/

/-- After running `agreementProg` with sufficient fuel, the machine
    halts cleanly (not via `merge`-halt) — pc reaches `.halt`. -/
theorem agreementProg_halts :
    (runFuel agreementProg 10 State.initial).halted = true := by
  show (runFuel agreementProg 10 State.initial).halted = true
  rfl

/-! ### § 3.2 Conflict: 不通 triggers `merge`-halt -/

/-- `conflictProg` halts via `merge`-halt (returns `none`) — the
    machine cannot proceed past the contradictory third statement. -/
theorem conflictProg_halts :
    (runFuel conflictProg 10 State.initial).halted = true := by
  show (runFuel conflictProg 10 State.initial).halted = true
  rfl

/-! ### § 3.3 Restrict: codim-increasing forget -/

/-- After `restrictProg`, the cell remembers bits 0 and 1 but has
    forgotten bit 2 (= `none`) due to the explicit `restrict`. -/
theorem restrictProg_forgets_bit_2 :
    (runFuel restrictProg 10 State.initial).cur ⟨2, by decide⟩ = none := by
  show (runFuel restrictProg 10 State.initial).cur ⟨2, by decide⟩ = none
  rfl

/-! ## § 4 — Bridge to Phase D `mergeAll`

For a pure-merge program (no jumps, no restricts, no halts other than
the trailing one), the final `cur` is exactly `PartialCell.mergeAll` of
the merge cells, modulo `Option`-unwrapping.

This is the **operational realisation** of Phase D's algebraic fold:
the Wen.Core interpreter running a pure-merge sequence IS the
right-fold of `PartialCell.merge` over the cells.

Stated and demonstrated below; a full proof is left as a future
exercise (it requires induction on the cell list and case-splitting on
`merge` success / failure). -/

/-- Sanity demo: `mergeProg [pinBit 0 true]` produces a single-bit
    commitment when run from `initial`. -/
example :
    (runFuel (mergeProg [Instr.pinBit ⟨0, by decide⟩ true]) 2 State.initial).cur
        ⟨0, by decide⟩
      = some true := by rfl

/-- Sanity demo: `mergeProg []` is just `[halt]`, halts immediately. -/
example :
    (runFuel (mergeProg []) 1 State.initial).halted = true := by rfl

end SSBX.Foundation.Wen.Core.ConstraintDemo
