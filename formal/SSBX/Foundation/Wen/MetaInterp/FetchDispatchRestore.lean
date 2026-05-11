/-
# FetchDispatchRestore -- compose saved-cur fetch with restored dispatch

This sidecar proves the reusable F.7c handoff:

* fetch leaves `META.cur` as the opcode tag and saves `sim.cur` on history;
* restored dispatch routes by that tag to a uniform restore prelude;
* the restore prelude recovers the existing execute-block `BlockPre` shape.
-/

import SSBX.Foundation.Wen.MetaInterp.FetchSavedCur
import SSBX.Foundation.Wen.MetaInterp.AssemblyRestorePlan

namespace SSBX.Foundation.Wen.MetaInterp.FetchDispatchRestore

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.MetaInterp
open SSBX.Foundation.Wen.MetaInterp.Dispatch
open SSBX.Foundation.Wen.MetaInterp.FetchSavedCur
open SSBX.Foundation.Wen.MetaInterp.AssemblyRestorePlan

/-! ## Saved-cur fetch to restored dispatch -/

/-- A saved-current-cell fetch outcome exposes exactly the dispatch tag for the
current source instruction. -/
theorem savedCurFetchOutcome_cur_eq_dispatchTag
    (regHex : Hexagram) (sim : YiState) (μ : YiState)
    (instr : YiInstr)
    (h_fetch :
      SavedCurFetchOutcome regHex sim restoredMetaInterpProg dispatchOffset μ)
    (h_get : sim.prog[sim.pc]? = some instr) :
    μ.cur = dispatchTagOfInstr instr := by
  have h_mem := h_fetch.cur_is_tag instr h_get
  rw [encInstr_head?_eq_dispatchTagOfInstr] at h_mem
  simpa using h_mem.symm

/-- A saved-current-cell fetch outcome for the restored assembly is exactly the
record shape expected by restored dispatch. -/
theorem savedCurFetchOutcome_eq_dispatchEntry
    (regHex : Hexagram) (sim : YiState) (μ : YiState)
    (instr : YiInstr)
    (h_fetch :
      SavedCurFetchOutcome regHex sim restoredMetaInterpProg dispatchOffset μ)
    (h_get : sim.prog[sim.pc]? = some instr) :
    μ =
      { cur := dispatchTagOfInstr instr
      , history := sim.cur :: encMetaHistory regHex sim
      , pc := dispatchOffset
      , prog := restoredMetaInterpProg
      , halted := false } := by
  have h_cur :=
    savedCurFetchOutcome_cur_eq_dispatchTag regHex sim μ instr h_fetch h_get
  cases μ with
  | mk cur history pc prog halted =>
      have h_history := h_fetch.history
      have h_pc := h_fetch.pc
      have h_prog := h_fetch.prog
      have h_halted := h_fetch.halted
      simp at h_cur h_history h_pc h_prog h_halted
      subst cur
      subst history
      subst pc
      subst prog
      subst halted
      rfl

/-- Running restored dispatch from a saved-current-cell fetch outcome routes to
the restored target while preserving the saved current cell on history. -/
theorem savedCurFetch_dispatch_routes_to_restore
    (regHex : Hexagram) (sim : YiState) (μ : YiState)
    (instr : YiInstr)
    (h_fetch :
      SavedCurFetchOutcome regHex sim restoredMetaInterpProg dispatchOffset μ)
    (h_get : sim.prog[sim.pc]? = some instr) :
    let μ' := μ.runFuel (dispatchFuelOfInstr instr)
    μ'.pc = dispatchTargetOfInstr restoredDispatchOffsets instr
      ∧ μ'.cur = dispatchTagOfInstr instr
      ∧ μ'.history = sim.cur :: encMetaHistory regHex sim
      ∧ μ'.prog = restoredMetaInterpProg
      ∧ μ'.halted = false := by
  have h_entry :=
    savedCurFetchOutcome_eq_dispatchEntry regHex sim μ instr h_fetch h_get
  rw [h_entry]
  simpa using
    restoredMetaInterpProg_dispatch_routes_instr_at_fuel
      (sim.cur :: encMetaHistory regHex sim) instr

/-- Field equality form: after dispatch, the state is exactly the saved-cur
restore-prelude entry state. -/
theorem savedCurFetch_dispatch_state_eq_savedCurBlockEntry
    (regHex : Hexagram) (sim : YiState) (μ : YiState)
    (instr : YiInstr)
    (h_fetch :
      SavedCurFetchOutcome regHex sim restoredMetaInterpProg dispatchOffset μ)
    (h_get : sim.prog[sim.pc]? = some instr) :
    μ.runFuel (dispatchFuelOfInstr instr) =
      DispatchRestore.savedCurBlockEntryState regHex sim restoredMetaInterpProg
        (dispatchTargetOfInstr restoredDispatchOffsets instr) instr := by
  have h_route :=
    savedCurFetch_dispatch_routes_to_restore regHex sim μ instr h_fetch h_get
  rcases h_route with ⟨h_pc, h_cur, h_history, h_prog, h_halted⟩
  cases hν : μ.runFuel (dispatchFuelOfInstr instr) with
  | mk cur history pc prog halted =>
      simp [hν] at h_pc h_cur h_history h_prog h_halted
      subst pc
      subst cur
      subst history
      subst prog
      subst halted
      simp [DispatchRestore.savedCurBlockEntryState]

/-- The full saved-cur handoff: saved-cur fetch, restored dispatch, then the
one-instruction restore prelude yield the existing block precondition. -/
theorem savedCurFetch_dispatch_restore_yields_BlockPre
    (regHex : Hexagram) (sim : YiState) (μ : YiState)
    (instr : YiInstr)
    (h_fetch :
      SavedCurFetchOutcome regHex sim restoredMetaInterpProg dispatchOffset μ)
    (h_get : sim.prog[sim.pc]? = some instr) :
    ExecuteBlock.BlockPre regHex sim
      (dispatchTargetOfInstr restoredDispatchOffsets instr + 1)
      restoredMetaInterpProg
      ((μ.runFuel (dispatchFuelOfInstr instr)).runFuel 1) := by
  rw [savedCurFetch_dispatch_state_eq_savedCurBlockEntry
    regHex sim μ instr h_fetch h_get]
  exact restoredMetaInterpProg_savedCur_target_yields_BlockPre regHex sim instr

/-- First exact restored end-to-end opcode path: saved-current fetch, restored
dispatch, restore prelude, then the aligned `nop` body witness. -/
theorem savedCurFetch_dispatch_restore_execute_nop_simulates_aligned
    (regHex : Hexagram) (sim : YiState) (μ : YiState)
    (h_fetch :
      SavedCurFetchOutcome regHex sim restoredMetaInterpProg dispatchOffset μ)
    (h_alive : sim.halted = false)
    (h_nop : sim.prog[sim.pc]? = some .nop)
    (h_curAligned : sim.cur = regDataCell regHex) :
    ExecuteBlock.BlockPost regHex sim fetchOffset restoredMetaInterpProg
      (((μ.runFuel (dispatchFuelOfInstr .nop)).runFuel 1).runFuel 2) false := by
  have h_pre :=
    savedCurFetch_dispatch_restore_yields_BlockPre regHex sim μ .nop h_fetch h_nop
  exact restoredMetaInterpProg_execute_nop_simulates_aligned
    regHex sim ((μ.runFuel (dispatchFuelOfInstr .nop)).runFuel 1)
    h_alive h_nop h_curAligned
    (by simpa [bodyOffset] using h_pre)

/-! ## Public summary -/

theorem fetch_dispatch_restore_summary :
    (∀ regHex sim μ instr,
      SavedCurFetchOutcome regHex sim restoredMetaInterpProg dispatchOffset μ →
      sim.prog[sim.pc]? = some instr →
        μ.cur = dispatchTagOfInstr instr)
    ∧ (∀ regHex sim μ instr,
      SavedCurFetchOutcome regHex sim restoredMetaInterpProg dispatchOffset μ →
      sim.prog[sim.pc]? = some instr →
        ExecuteBlock.BlockPre regHex sim
          (dispatchTargetOfInstr restoredDispatchOffsets instr + 1)
          restoredMetaInterpProg
          ((μ.runFuel (dispatchFuelOfInstr instr)).runFuel 1))
    ∧ (∀ regHex sim μ,
      SavedCurFetchOutcome regHex sim restoredMetaInterpProg dispatchOffset μ →
      sim.halted = false →
      sim.prog[sim.pc]? = some .nop →
      sim.cur = regDataCell regHex →
        ExecuteBlock.BlockPost regHex sim fetchOffset restoredMetaInterpProg
          (((μ.runFuel (dispatchFuelOfInstr .nop)).runFuel 1).runFuel 2)
          false) := by
  exact
    ⟨ savedCurFetchOutcome_cur_eq_dispatchTag
    , savedCurFetch_dispatch_restore_yields_BlockPre
    , savedCurFetch_dispatch_restore_execute_nop_simulates_aligned
    ⟩

end SSBX.Foundation.Wen.MetaInterp.FetchDispatchRestore
