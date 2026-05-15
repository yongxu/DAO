/-
# Foundation.Wen.CorePartial.Examples — demo programs

A small gallery showing the PartialCell-native interpreter in action.
For Phase E.1 we keep the demos at the *definition* level only — they
verify that the ISA + interpreter typecheck and produce structurally
sensible programs.  Theorems about concrete execution traces are
deferred to Phase E.2 (where we add the equivalence proof against
`Wen.Core` and gain machinery for unrolling `runFuel`).
-/

import SSBX.Foundation.Wen.CorePartial.Machine

namespace SSBX.Foundation.Wen.CorePartial.Examples

open SSBX.Foundation.R
open SSBX.Foundation.Wen.CorePartial

/-! ## § Demo 1 — empty program -/

/-- The empty program.  From `initial`, halts in one step (pc past end). -/
def emptyProg : List Instr := []

/-! ## § Demo 2 — single halt -/

/-- Trivial program that just halts. -/
def haltProg : List Instr := [.halt]

/-! ## § Demo 3 — pin a single bit then halt

Builds a cell with bit 0 = true, then halts.  The state after running
this from `initial` has `cur ⟨0⟩ = some true` and all other bits = none. -/
def pinBit0Prog : List Instr := [
  .mergeBit ⟨0, by decide⟩ true,
  .halt
]

/-! ## § Demo 4 — 不通 halt via incompatible merge

After pinning bit 0 = true, attempting to merge bit 0 = false triggers
the 不通 halt (PartialCell.merge returns none → halted := true). -/
def contradictProg : List Instr := [
  .mergeBit ⟨0, by decide⟩ true,
  .mergeBit ⟨0, by decide⟩ false,
  .halt
]

/-! ## § Demo 5 — incremental specification

Pin all 8 bits to `true` in sequence.  After running with sufficient
fuel, the state's `cur` should be the all-`some true` cell (= `ofFull`
of the all-true `R 8` vector). -/
def buildAllTrueProg : List Instr := [
  .mergeBit ⟨0, by decide⟩ true,
  .mergeBit ⟨1, by decide⟩ true,
  .mergeBit ⟨2, by decide⟩ true,
  .mergeBit ⟨3, by decide⟩ true,
  .mergeBit ⟨4, by decide⟩ true,
  .mergeBit ⟨5, by decide⟩ true,
  .mergeBit ⟨6, by decide⟩ true,
  .mergeBit ⟨7, by decide⟩ true,
  .halt
]

/-! ## § Demo 6 — restrict back to subspace

Pin bits 0, 1, 2 to true, then restrict to {0, 1} only.  Final state
has cur ⟨0⟩ = some true, cur ⟨1⟩ = some true, cur ⟨2⟩ = none. -/
def pinThenRestrictProg : List Instr := [
  .mergeBit ⟨0, by decide⟩ true,
  .mergeBit ⟨1, by decide⟩ true,
  .mergeBit ⟨2, by decide⟩ true,
  .restrict ({⟨0, by decide⟩, ⟨1, by decide⟩} : Finset (Fin 8)),
  .halt
]

/-! ## § Demo 7 — jump loop (degenerate)

`jump 0` from pc=0 loops forever.  Combined with finite fuel, the
machine doesn't halt within budget. -/
def jumpLoopProg : List Instr := [.jump 0]

end SSBX.Foundation.Wen.CorePartial.Examples
