/-
# Foundation.Wen.Core.Examples — demo programs

A small gallery showing the PartialCell-native interpreter in action.
For Phase E.1 we keep the demos at the *definition* level only — they
verify that the ISA + interpreter typecheck and produce structurally
sensible programs.  Theorems about concrete execution traces are
deferred to Phase E.2 (where we add the equivalence proof against
`Wen.Core` and gain machinery for unrolling `runFuel`).
-/

import SSBX.Foundation.Wen.Core.Machine

namespace SSBX.Foundation.Wen.Core.Examples

open SSBX.Foundation.R
open SSBX.Foundation.Wen.Core

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

/-! ## § Demo 8 — branch on partial state (E.2)

If bit 0 is set, jump over the second merge; otherwise fall through.
From `initial` (cur = 道), bit 0 is `none`, so the branch does NOT
fire (partial commitment policy: ambiguity = fall through).  This
distinguishes CorePartial from a classical bit-machine where bit 0
would have a definite value. -/
def branchOnBit0Prog : List Instr := [
  .branchIfSet ⟨0, by decide⟩ 3,    -- skip to pc 3 if bit 0 set
  .mergeBit ⟨1, by decide⟩ true,    -- only runs if branch did NOT fire
  .halt,                             -- pc 2 — halt after merging bit 1
  .halt                              -- pc 3 — halt after skip
]

/-! ## § Demo 9 — pin-then-branch

Pin bit 0 = true, then branch on bit 0.  Now the branch DOES fire. -/
def pinThenBranchProg : List Instr := [
  .mergeBit ⟨0, by decide⟩ true,    -- pc 0: pin bit 0 = true
  .branchIfSet ⟨0, by decide⟩ 4,    -- pc 1: should jump to 4
  .mergeBit ⟨1, by decide⟩ true,    -- pc 2: skipped
  .halt,                             -- pc 3: skipped
  .halt                              -- pc 4: jumped here
]

/-! ## § Demo 10 — push/pop save-restore (Phase E.3)

Pin bit 0, push state, pin bit 1, pop (restoring to "only bit 0 pinned"). -/
def saveRestoreProg : List Instr := [
  .mergeBit ⟨0, by decide⟩ true,
  .push,
  .mergeBit ⟨1, by decide⟩ true,
  .pop,
  .halt
]

/-! ## § Demo 11 — writeBit overrides (Phase E.3)

`merge` of bit 0 = true would normally CONFLICT with bit 0 = false in
a subsequent merge.  But `writeBit` overwrites, so the program proceeds
without halting. -/
def writeOverrideProg : List Instr := [
  .mergeBit ⟨0, by decide⟩ true,    -- bit 0 = true
  .writeBit ⟨0, by decide⟩ false,   -- bit 0 := false (overwrite!)
  .halt
]

/-! ## § Demo 12 — flipBit on defined / undefined bits (Phase E.3)

Bit 0 starts unspecified.  `flipBit 0` leaves it `none` (partial
commitment policy).  Then we pin bit 0 = true, flip it, bit 0 becomes
false. -/
def flipOnPartialProg : List Instr := [
  .flipBit ⟨0, by decide⟩,           -- bit 0 still none (flipped 0 times)
  .mergeBit ⟨0, by decide⟩ true,    -- bit 0 = true
  .flipBit ⟨0, by decide⟩,           -- bit 0 = false
  .halt
]

/-! ## § Demo 13 — xorMask flips defined bits (Phase E.3)

Build cur with bit 0 = true and bit 1 = false, then xorMask with the
all-true mask — defined bits flip, undefined stay none. -/
def xorMaskDemo : List Instr := [
  .mergeBit ⟨0, by decide⟩ true,
  .mergeBit ⟨1, by decide⟩ false,
  .xorMask (fun _ => true),          -- flip all bits where m i = true
  .halt
]

/-! ## § Demo 14 — `mergePrior` cross-substrate refinement (Phase E.4)

Saves bit 0 = true as context, restricts away to forget it locally,
pins bit 1 = true in the "forgotten" workspace, then `mergePrior`
re-imposes the saved bit 0 = true.  Final `cur` has BOTH bit 0 = true
(restored from history) AND bit 1 = true (added locally) — a true
join of saved context with current refinement that neither `merge` nor
`pop` alone could achieve. -/
def mergePriorRefineProg : List Instr := [
  .mergeBit ⟨0, by decide⟩ true,                                    -- pc 0: bit 0 = true
  .push,                                                             -- pc 1: save (bit 0 = true)
  .forget ⟨0, by decide⟩,                                            -- pc 2: locally forget bit 0
  .mergeBit ⟨1, by decide⟩ true,                                    -- pc 3: pin bit 1 = true
  .mergePrior,                                                       -- pc 4: re-merge saved context — now both bits set
  .halt
]

end SSBX.Foundation.Wen.Core.Examples
