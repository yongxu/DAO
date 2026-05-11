/-
# DispatchRestore -- saved-cur bridge between dispatch tags and block preconditions

F.7c exposes a single-register tension: fetch/dispatch need `META.cur` to hold
the opcode tag, while execute blocks expect `META.cur = sim.cur`. The minimal
bridge is to save `sim.cur` on history before clobbering `META.cur`; after
dispatch routes to a block, a uniform leading `pop` restores `META.cur` and the
canonical history before the existing block body begins.

This file proves that bridge shape. It does not rewire `metaInterpProg`; it
fixes the target invariant for the next assembly pass.
-/

import SSBX.Foundation.Wen.MetaInterp.Dispatch
import SSBX.Foundation.Wen.MetaInterp.ExecuteBlock

namespace SSBX.Foundation.Wen.MetaInterp.DispatchRestore

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.MetaInterp
open SSBX.Foundation.Wen.MetaInterp.Dispatch
open SSBX.Foundation.Wen.MetaInterp.ExecuteBlock

/-! ## Saved-cur block entry -/

/-- State after dispatch has routed on an opcode tag while `sim.cur` is saved
on top of history. -/
def savedCurBlockEntryState
    (regHex : Hexagram) (sim : YiState) (metaProg : List YiInstr)
    (blockOffset : Nat) (instr : YiInstr) : YiState :=
  { cur := dispatchTagOfInstr instr
  , history := sim.cur :: encMetaHistory regHex sim
  , pc := blockOffset
  , prog := metaProg
  , halted := false }

/-- State expected immediately after the uniform restore `pop`. -/
def restoredBlockPreState
    (regHex : Hexagram) (sim : YiState) (metaProg : List YiInstr)
    (bodyOffset : Nat) : YiState :=
  { cur := sim.cur
  , history := encMetaHistory regHex sim
  , pc := bodyOffset
  , prog := metaProg
  , halted := false }

/-- A leading `pop` restores `META.cur = sim.cur` and removes the saved cell,
leaving the canonical encoded history for the existing block contract. -/
theorem restoreSavedCur_step
    (regHex : Hexagram) (sim : YiState) (metaProg : List YiInstr)
    (blockOffset : Nat) (instr : YiInstr)
    (h_popAt : metaProg[blockOffset]? = some YiInstr.pop) :
    (savedCurBlockEntryState regHex sim metaProg blockOffset instr).runFuel 1 =
      restoredBlockPreState regHex sim metaProg (blockOffset + 1) := by
  unfold YiState.runFuel YiState.step
  simp [YiState.runFuel, savedCurBlockEntryState, restoredBlockPreState,
    h_popAt, YiState.execute]

/-- The restored state satisfies the existing execute-block precondition at the
body offset. -/
theorem restoredBlockPreState_satisfies_BlockPre
    (regHex : Hexagram) (sim : YiState) (metaProg : List YiInstr)
    (bodyOffset : Nat) :
    BlockPre regHex sim bodyOffset metaProg
      (restoredBlockPreState regHex sim metaProg bodyOffset) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- One-fuel restore prelude converts a saved-cur dispatch target into the
existing `BlockPre` shape for the real block body. -/
theorem restoreSavedCur_yields_BlockPre
    (regHex : Hexagram) (sim : YiState) (metaProg : List YiInstr)
    (blockOffset : Nat) (instr : YiInstr)
    (h_popAt : metaProg[blockOffset]? = some YiInstr.pop) :
    BlockPre regHex sim (blockOffset + 1) metaProg
      ((savedCurBlockEntryState regHex sim metaProg blockOffset instr).runFuel 1) := by
  rw [restoreSavedCur_step regHex sim metaProg blockOffset instr h_popAt]
  exact restoredBlockPreState_satisfies_BlockPre regHex sim metaProg (blockOffset + 1)

/-- The saved-cur convention preserves the canonical history exactly after the
restore prelude. -/
theorem restoreSavedCur_history
    (regHex : Hexagram) (sim : YiState) (metaProg : List YiInstr)
    (blockOffset : Nat) (instr : YiInstr)
    (h_popAt : metaProg[blockOffset]? = some YiInstr.pop) :
    ((savedCurBlockEntryState regHex sim metaProg blockOffset instr).runFuel 1).history =
      encMetaHistory regHex sim := by
  rw [restoreSavedCur_step regHex sim metaProg blockOffset instr h_popAt]
  rfl

/-- The saved-cur convention restores the loop's `META.cur = sim.cur`
invariant before the block body begins. -/
theorem restoreSavedCur_cur
    (regHex : Hexagram) (sim : YiState) (metaProg : List YiInstr)
    (blockOffset : Nat) (instr : YiInstr)
    (h_popAt : metaProg[blockOffset]? = some YiInstr.pop) :
    ((savedCurBlockEntryState regHex sim metaProg blockOffset instr).runFuel 1).cur =
      sim.cur := by
  rw [restoreSavedCur_step regHex sim metaProg blockOffset instr h_popAt]
  rfl

/-! ## Public summary -/

theorem dispatch_restore_summary :
    ∀ regHex sim metaProg blockOffset instr,
      metaProg[blockOffset]? = some YiInstr.pop →
        BlockPre regHex sim (blockOffset + 1) metaProg
          ((savedCurBlockEntryState regHex sim metaProg blockOffset instr).runFuel 1)
        ∧ ((savedCurBlockEntryState regHex sim metaProg blockOffset instr).runFuel 1).cur =
            sim.cur
        ∧ ((savedCurBlockEntryState regHex sim metaProg blockOffset instr).runFuel 1).history =
            encMetaHistory regHex sim := by
  intro regHex sim metaProg blockOffset instr h_popAt
  exact
    ⟨ restoreSavedCur_yields_BlockPre regHex sim metaProg blockOffset instr h_popAt
    , restoreSavedCur_cur regHex sim metaProg blockOffset instr h_popAt
    , restoreSavedCur_history regHex sim metaProg blockOffset instr h_popAt
    ⟩

end SSBX.Foundation.Wen.MetaInterp.DispatchRestore
