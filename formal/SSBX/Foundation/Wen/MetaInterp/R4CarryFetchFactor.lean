/-
# R4CarryFetchFactor -- decoded fetch is enough for R4-squared carry

The old saved-current-cell frontier needed a finite re-emitter after decoded
fetch.  Under the R4-squared carry architecture, decoded fetch already has the
right runtime shape: `META.cur` holds the dispatch tag and `META.history` is
canonical.  The saved current is carried as proof/control data, so no runtime
history prefix is needed at this contract layer.
-/
import SSBX.Foundation.Wen.MetaInterp.R4CarryFetchObligations
import SSBX.Foundation.Wen.MetaInterp.FetchSavedCurProg

namespace SSBX.Foundation.Wen.MetaInterp.R4CarryFetchFactor

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.MetaInterp
open SSBX.Foundation.Wen.MetaInterp.Fetch
open SSBX.Foundation.Wen.MetaInterp.R4Carry
open SSBX.Foundation.Wen.MetaInterp.R4CarryRestore
open SSBX.Foundation.Wen.MetaInterp.R4CarryFetchObligations
open SSBX.Foundation.Wen.MetaInterp.FetchSavedCurProg
open SSBX.Foundation.Wen.MetaInterp.AssemblyRestorePlan

theorem r4CarryFetchOutcome_of_fetchOutcome
    (regHex : Hexagram) (sim μ : YiState) (metaProg : List YiInstr)
    (handoffOffset : Nat)
    (h_fetch : FetchOutcome regHex sim metaProg handoffOffset μ) :
    R4CarryFetchOutcome regHex sim metaProg handoffOffset (carryOfCell sim.cur) μ := by
  exact
    ⟨ h_fetch.cur_is_tag
    , rfl
    , h_fetch.history
    , h_fetch.pc
    , h_fetch.prog
    , h_fetch.halted
    ⟩

/-- A decoded restored fetch walker directly supplies the R4-squared carry
fetch frontier.  This replaces the old saved-cell reemit layer at the contract
level; the concrete walker proof remains a later phase. -/
theorem restoredR4CarryFetchObligations_of_decoded_fetch
    (D :
      DecodedRestoredFetchObligations restoredMetaInterpProg fetchOffset dispatchOffset) :
    RestoredR4CarryFetchObligations where
  running := by
    intro regHex sim instr h_alive h_get
    obtain ⟨fetchFuel, h_fetch⟩ :=
      D.running regHex sim instr h_alive h_get
    refine ⟨fetchFuel, ?_⟩
    exact
      r4CarryFetchOutcome_of_fetchOutcome regHex sim
        ((Fetch.fetchEntryState regHex sim restoredMetaInterpProg fetchOffset).runFuel
          fetchFuel)
        restoredMetaInterpProg dispatchOffset h_fetch

/-! ## Public summary -/

theorem r4_carry_fetch_factor_summary :
    (∀ regHex sim μ metaProg handoffOffset,
      FetchOutcome regHex sim metaProg handoffOffset μ →
        R4CarryFetchOutcome regHex sim metaProg handoffOffset
          (carryOfCell sim.cur) μ)
    ∧ (DecodedRestoredFetchObligations restoredMetaInterpProg fetchOffset dispatchOffset →
        RestoredR4CarryFetchObligations) := by
  exact
    ⟨ r4CarryFetchOutcome_of_fetchOutcome
    , restoredR4CarryFetchObligations_of_decoded_fetch
    ⟩

end SSBX.Foundation.Wen.MetaInterp.R4CarryFetchFactor
