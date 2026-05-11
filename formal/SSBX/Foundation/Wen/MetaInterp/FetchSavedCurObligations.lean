/-
# FetchSavedCurObligations -- frontier for the real saved-current fetch walker

The current concrete `fetchProgWithPeel` reaches dispatch with the halted-flag
cell in `META.cur` and the post-peel tail in history.  It cannot be re-read as
the restored-dispatch handoff.  This sidecar records the narrow evidence a real
fetch walker must provide, then composes that evidence with the restored
dispatch/restore/`nop` body path.
-/

import SSBX.Foundation.Wen.MetaInterp.FetchDispatchRestore

namespace SSBX.Foundation.Wen.MetaInterp.FetchSavedCurObligations

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.MetaInterp
open SSBX.Foundation.Wen.MetaInterp.Dispatch
open SSBX.Foundation.Wen.MetaInterp.FetchSavedCur
open SSBX.Foundation.Wen.MetaInterp.FetchDispatchRestore
open SSBX.Foundation.Wen.MetaInterp.AssemblyRestorePlan

/-! ## Fuel plumbing -/

theorem runFuel_add (s : YiState) (m n : Nat) :
    s.runFuel (m + n) = (s.runFuel m).runFuel n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      have h1 : s.runFuel (m + (k + 1)) = (s.runFuel (m + k)).step := by
        have : m + (k + 1) = (m + k) + 1 := by omega
        rw [this, SSBX.Foundation.Bagua.GodelLi.runFuel_succ_right]
      have h2 :
          (s.runFuel m).runFuel (k + 1) =
            ((s.runFuel m).runFuel k).step :=
        SSBX.Foundation.Bagua.GodelLi.runFuel_succ_right _ _
      rw [h1, h2, ih]

def restoredNopTailFuel : Nat :=
  dispatchFuelOfInstr .nop + (1 + 2)

theorem runFuel_restored_nop_tail (μ : YiState) :
    μ.runFuel restoredNopTailFuel =
      (((μ.runFuel (dispatchFuelOfInstr .nop)).runFuel 1).runFuel 2) := by
  unfold restoredNopTailFuel
  rw [runFuel_add μ (dispatchFuelOfInstr .nop) (1 + 2)]
  rw [runFuel_add (μ.runFuel (dispatchFuelOfInstr .nop)) 1 2]

/-! ## Saved-current fetch obligation -/

/-- Minimal running-arm evidence expected from the future real fetch walker for
the restored layout.  It is deliberately specialized to `restoredMetaInterpProg`
so the old Strategy-B assembly remains untouched until the restored path has
enough witnesses to replace it cleanly. -/
structure RestoredSavedCurFetchObligations : Prop where
  running :
    ∀ regHex sim instr,
      sim.halted = false →
      sim.prog[sim.pc]? = some instr →
        ∃ fetchFuel,
          SavedCurFetchOutcome regHex sim restoredMetaInterpProg dispatchOffset
            ((Fetch.fetchEntryState regHex sim restoredMetaInterpProg fetchOffset).runFuel
              fetchFuel)

/-- If the future saved-current fetch walker reaches the required handoff, then
the restored `.nop` path already gives an exact block postcondition under the
same aligned data-cell invariant as the existing `nop` witness. -/
theorem restoredSavedCurFetch_nop_to_BlockPost_at_fuel
    (O : RestoredSavedCurFetchObligations)
    (regHex : Hexagram) (sim : YiState)
    (h_alive : sim.halted = false)
    (h_nop : sim.prog[sim.pc]? = some .nop)
    (h_curAligned : sim.cur = regDataCell regHex) :
    ∃ fuel,
      ExecuteBlock.BlockPost regHex sim fetchOffset restoredMetaInterpProg
        ((Fetch.fetchEntryState regHex sim restoredMetaInterpProg fetchOffset).runFuel
          fuel)
        false := by
  obtain ⟨fetchFuel, h_fetch⟩ := O.running regHex sim .nop h_alive h_nop
  let entry := Fetch.fetchEntryState regHex sim restoredMetaInterpProg fetchOffset
  let μ := entry.runFuel fetchFuel
  refine ⟨fetchFuel + restoredNopTailFuel, ?_⟩
  have h_post :=
    savedCurFetch_dispatch_restore_execute_nop_simulates_aligned
      regHex sim μ h_fetch h_alive h_nop h_curAligned
  change ExecuteBlock.BlockPost regHex sim fetchOffset restoredMetaInterpProg
    (entry.runFuel (fetchFuel + restoredNopTailFuel)) false
  rw [runFuel_add entry fetchFuel restoredNopTailFuel]
  change ExecuteBlock.BlockPost regHex sim fetchOffset restoredMetaInterpProg
    (μ.runFuel restoredNopTailFuel) false
  rw [runFuel_restored_nop_tail μ]
  exact h_post

/-- Field form matching the steady-iteration part of
`Universal.SemanticLoopObligations`, specialized to the first restored exact
opcode path. -/
theorem restoredSavedCurFetch_nop_steady_fields
    (O : RestoredSavedCurFetchObligations)
    (regHex : Hexagram) (sim : YiState)
    (h_alive : sim.halted = false)
    (h_nop : sim.prog[sim.pc]? = some .nop)
    (h_curAligned : sim.cur = regDataCell regHex) :
    ∃ fuel,
      let μ' :=
        (Fetch.fetchEntryState regHex sim restoredMetaInterpProg fetchOffset).runFuel
          fuel
      μ'.history = encMetaHistory regHex sim.step
        ∧ μ'.halted = false
        ∧ μ'.pc = fetchOffset := by
  obtain ⟨fuel, h_post⟩ :=
    restoredSavedCurFetch_nop_to_BlockPost_at_fuel
      O regHex sim h_alive h_nop h_curAligned
  refine ⟨fuel, ?_⟩
  exact ⟨h_post.history, h_post.halted, h_post.pc⟩

/-! ## Public summary -/

theorem fetch_saved_cur_obligation_frontier_summary :
    (RestoredSavedCurFetchObligations →
      ∀ regHex sim,
        sim.halted = false →
        sim.prog[sim.pc]? = some .nop →
        sim.cur = regDataCell regHex →
          ∃ fuel,
            ExecuteBlock.BlockPost regHex sim fetchOffset restoredMetaInterpProg
              ((Fetch.fetchEntryState regHex sim restoredMetaInterpProg fetchOffset).runFuel
                fuel)
              false)
    ∧ (RestoredSavedCurFetchObligations →
      ∀ regHex sim,
        sim.halted = false →
        sim.prog[sim.pc]? = some .nop →
        sim.cur = regDataCell regHex →
          ∃ fuel,
            let μ' :=
              (Fetch.fetchEntryState regHex sim restoredMetaInterpProg fetchOffset).runFuel
                fuel
            μ'.history = encMetaHistory regHex sim.step
              ∧ μ'.halted = false
              ∧ μ'.pc = fetchOffset) := by
  exact
    ⟨ restoredSavedCurFetch_nop_to_BlockPost_at_fuel
    , restoredSavedCurFetch_nop_steady_fields
    ⟩

end SSBX.Foundation.Wen.MetaInterp.FetchSavedCurObligations
