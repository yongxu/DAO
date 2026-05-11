/-
# FetchSavedCurProg -- factor the real saved-current fetch walker

F.7c.28 should not fill `RestoredSavedCurFetchObligations.running` by
weakening `sim.cur` to an aligned-cell invariant.  A universal interpreter must
preserve arbitrary R8 current cells.

This sidecar factors the future executable walker into two contracts:

* decode/restore: the walker reaches canonical `FetchOutcome` with the opcode
  tag in `META.cur`;
* re-emit: finite R8 control re-emits the saved simulated current cell onto
  history, restores the opcode tag in `META.cur`, and jumps to restored
  dispatch.

The theorem below proves that these two contracts are sufficient for the public
restored saved-current fetch obligation.  It is intentionally not an executable
fetch program yet; it keeps the architecture honest while the concrete segment
is filled in.
-/

import SSBX.Foundation.Wen.MetaInterp.FetchSavedCurObligations

namespace SSBX.Foundation.Wen.MetaInterp.FetchSavedCurProg

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.MetaInterp
open SSBX.Foundation.Wen.MetaInterp.Fetch
open SSBX.Foundation.Wen.MetaInterp.FetchSavedCur
open SSBX.Foundation.Wen.MetaInterp.FetchSavedCurObligations
open SSBX.Foundation.Wen.MetaInterp.AssemblyRestorePlan

/-! ## Factored saved-current fetch contracts -/

/-- First half of the future walker: from the restored fetch entry, reach a
canonical restored fetch outcome with the decoded opcode tag in `META.cur`.

The `handoffOffset` is not dispatch yet.  It is the entry point for the finite
R8 re-emitter that will preserve arbitrary `sim.cur`. -/
structure DecodedRestoredFetchObligations
    (metaProg : List YiInstr) (fetchOffset handoffOffset : Nat) : Prop where
  running :
    ∀ regHex sim instr,
      sim.halted = false →
      sim.prog[sim.pc]? = some instr →
        ∃ fetchFuel,
          FetchOutcome regHex sim metaProg handoffOffset
            ((Fetch.fetchEntryState regHex sim metaProg fetchOffset).runFuel
              fetchFuel)

/-- Second half of the future walker: starting from a canonical decoded fetch
outcome, re-emit the original simulated current cell onto history and restore
the opcode tag in `META.cur` before jumping to dispatch.

This is where the finite R8 control-state strategy belongs.  It must not become
a new interpreter layer; it is just the missing saved-current handoff segment. -/
structure SavedCurrentReemitObligations
    (metaProg : List YiInstr) (handoffOffset dispatchOffset : Nat) : Prop where
  running :
    ∀ regHex sim instr μ,
      FetchOutcome regHex sim metaProg handoffOffset μ →
      sim.prog[sim.pc]? = some instr →
        ∃ reemitFuel,
          SavedCurFetchOutcome regHex sim metaProg dispatchOffset
            (μ.runFuel reemitFuel)

/-- Composition lemma for F.7c.28: a real decode/restore walker plus a finite
R8 saved-current re-emitter supplies the public restored saved-current fetch
obligation expected by the downstream dispatch/restore/block proofs. -/
theorem restoredSavedCurFetchObligations_of_decode_reemit
    (handoffOffset : Nat)
    (D :
      DecodedRestoredFetchObligations
        restoredMetaInterpProg fetchOffset handoffOffset)
    (R :
      SavedCurrentReemitObligations
        restoredMetaInterpProg handoffOffset dispatchOffset) :
    RestoredSavedCurFetchObligations := by
  refine ⟨?_⟩
  intro regHex sim instr h_alive h_get
  obtain ⟨fetchFuel, h_decode⟩ :=
    D.running regHex sim instr h_alive h_get
  let entry := Fetch.fetchEntryState regHex sim restoredMetaInterpProg fetchOffset
  let μ := entry.runFuel fetchFuel
  obtain ⟨reemitFuel, h_reemit⟩ :=
    R.running regHex sim instr μ h_decode h_get
  refine ⟨fetchFuel + reemitFuel, ?_⟩
  change SavedCurFetchOutcome regHex sim restoredMetaInterpProg dispatchOffset
    (entry.runFuel (fetchFuel + reemitFuel))
  rw [FetchSavedCurObligations.runFuel_add entry fetchFuel reemitFuel]
  exact h_reemit

/-! ## Public summary -/

theorem fetch_saved_cur_prog_factor_summary :
    ∀ handoffOffset,
      DecodedRestoredFetchObligations
          restoredMetaInterpProg fetchOffset handoffOffset →
      SavedCurrentReemitObligations
          restoredMetaInterpProg handoffOffset dispatchOffset →
        RestoredSavedCurFetchObligations :=
  restoredSavedCurFetchObligations_of_decode_reemit

end SSBX.Foundation.Wen.MetaInterp.FetchSavedCurProg
