/-
# FetchSavedCurBoundary -- old fetch route is not the saved-current handoff

This sidecar records the exact boundary exposed by F.7c: the current
`Assembly.metaInterpProg` running fetch route reaches dispatch with the
halted-flag cell in `META.cur` and a post-peel history tail.  That state cannot
be re-read as `SavedCurFetchOutcome`.
-/

import SSBX.Foundation.Wen.MetaInterp.Assembly
import SSBX.Foundation.Wen.MetaInterp.AssemblyRestorePlan
import SSBX.Foundation.Wen.MetaInterp.FetchSavedCur

namespace SSBX.Foundation.Wen.MetaInterp.FetchSavedCurBoundary

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.MetaInterp
open SSBX.Foundation.Wen.MetaInterp.Fetch
open SSBX.Foundation.Wen.MetaInterp.FetchSavedCur
open SSBX.Foundation.Wen.MetaInterp.Assembly

theorem haltFlagTailAfterPeel_ne_savedCurHistory
    (regHex : Hexagram) (sim : YiState) :
    haltFlagTailAfterPeel regHex sim ≠
      sim.cur :: encMetaHistory regHex sim := by
  intro h
  have hlen := congrArg List.length h
  simp only [List.length_cons] at hlen
  rw [encMetaHistory_length_eq_pcCounter_haltFlag_tail_length] at hlen
  omega

/-- The current Strategy-B running fetch route is route-only.  It cannot supply
the restored saved-current handoff because its history is the post-peel tail,
not `sim.cur :: encMetaHistory regHex sim`. -/
theorem currentAssembly_running_fetch_not_savedCurOutcome
    (regHex : Hexagram) (sim : YiState)
    (h_running : sim.halted = false) :
    let fuel := (3 * sim.pc + 3) + (1 + (FetchProg.walkerLen + 1))
    let μ :=
      (fetchEntryState regHex sim metaInterpProg fetchOffset).runFuel fuel
    ¬ SavedCurFetchOutcome regHex sim metaInterpProg dispatchOffset μ := by
  intro fuel μ h_saved
  have h_shape :=
    metaInterpProg_fetch_running_current_shape_exact regHex sim h_running
  have h_history := h_saved.history
  dsimp [fuel, μ] at h_history
  rw [h_shape] at h_history
  exact haltFlagTailAfterPeel_ne_savedCurHistory regHex sim h_history

theorem restoredAssembly_running_fetch_not_savedCurOutcome
    (regHex : Hexagram) (sim : YiState)
    (h_running : sim.halted = false) :
    let fuel := (3 * sim.pc + 3) + (1 + (FetchProg.walkerLen + 1))
    let μ :=
      (fetchEntryState regHex sim
        AssemblyRestorePlan.restoredMetaInterpProg
        AssemblyRestorePlan.fetchOffset).runFuel fuel
    ¬ SavedCurFetchOutcome regHex sim
        AssemblyRestorePlan.restoredMetaInterpProg
        AssemblyRestorePlan.dispatchOffset μ := by
  intro fuel μ h_saved
  have h_shape :=
    AssemblyRestorePlan.restoredMetaInterpProg_fetch_running_current_shape_exact
      regHex sim h_running
  have h_history := h_saved.history
  dsimp [fuel, μ] at h_history
  rw [h_shape] at h_history
  exact haltFlagTailAfterPeel_ne_savedCurHistory regHex sim h_history

/-! ## Public summary -/

theorem fetch_saved_cur_boundary_summary :
    (∀ regHex sim,
      sim.halted = false →
        let fuel := (3 * sim.pc + 3) + (1 + (FetchProg.walkerLen + 1))
        let μ :=
          (fetchEntryState regHex sim metaInterpProg fetchOffset).runFuel fuel
        ¬ SavedCurFetchOutcome regHex sim metaInterpProg dispatchOffset μ)
    ∧ (∀ regHex sim,
      sim.halted = false →
        let fuel := (3 * sim.pc + 3) + (1 + (FetchProg.walkerLen + 1))
        let μ :=
          (fetchEntryState regHex sim
            AssemblyRestorePlan.restoredMetaInterpProg
            AssemblyRestorePlan.fetchOffset).runFuel fuel
        ¬ SavedCurFetchOutcome regHex sim
            AssemblyRestorePlan.restoredMetaInterpProg
            AssemblyRestorePlan.dispatchOffset μ) := by
  exact
    ⟨ currentAssembly_running_fetch_not_savedCurOutcome
    , restoredAssembly_running_fetch_not_savedCurOutcome
    ⟩

end SSBX.Foundation.Wen.MetaInterp.FetchSavedCurBoundary
