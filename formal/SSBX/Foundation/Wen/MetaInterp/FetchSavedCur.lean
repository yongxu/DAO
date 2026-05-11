/-
# FetchSavedCur -- fetch outcome for restored-dispatch assembly

The original `Fetch.FetchOutcome` restores canonical history before dispatch.
The restored-dispatch layout needs one extra saved cell: `sim.cur` is kept on
top of canonical history while `META.cur` carries the opcode tag. Dispatch can
route on the tag, then the target restore prelude pops `sim.cur` back into
`META.cur` and recovers the existing block precondition.
-/

import SSBX.Foundation.Wen.MetaInterp.Fetch
import SSBX.Foundation.Wen.MetaInterp.DispatchRestore

namespace SSBX.Foundation.Wen.MetaInterp.FetchSavedCur

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.MetaInterp
open SSBX.Foundation.Wen.MetaInterp.Fetch
open SSBX.Foundation.Wen.MetaInterp.SkipInstr

/-! ## Saved-current-cell fetch outcome -/

/-- Fetch outcome used by the restored-dispatch assembly. `META.cur` holds the
opcode tag; the simulated current cell is saved on top of canonical history. -/
structure SavedCurFetchOutcome
    (regHex : Hexagram) (sim : YiState) (metaProg : List YiInstr)
    (dispatchOffset : Nat) (μ' : YiState) : Prop where
  cur_is_tag :
    ∀ instr, sim.prog[sim.pc]? = some instr →
      μ'.cur ∈ (YiInstrEnc.encInstr instr).head?
  history :
    μ'.history = sim.cur :: encMetaHistory regHex sim
  pc :
    μ'.pc = dispatchOffset
  prog :
    μ'.prog = metaProg
  halted :
    μ'.halted = false

/-- Constructor for the saved-current-cell fetch target shape. -/
theorem savedCurFetchOutcome_tag_state
    (regHex : Hexagram) (sim : YiState) (metaProg : List YiInstr)
    (dispatchOffset : Nat) (instr : YiInstr) (tag : R8)
    (h_get : sim.prog[sim.pc]? = some instr)
    (h_tag : (YiInstrEnc.encInstr instr).head? = some tag) :
    SavedCurFetchOutcome regHex sim metaProg dispatchOffset
      { cur := tag
      , history := sim.cur :: encMetaHistory regHex sim
      , pc := dispatchOffset
      , prog := metaProg
      , halted := false } := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  intro instr' h_instr'
  rw [h_get] at h_instr'
  cases h_instr'
  simp [h_tag]

/-- Zero-arity specialization, using the existing encoded-tag theorem. -/
theorem savedCurFetchOutcome_zeroArity_tag_state
    (regHex : Hexagram) (sim : YiState) (metaProg : List YiInstr)
    (dispatchOffset : Nat) (instr : YiInstr)
    (h_get : sim.prog[sim.pc]? = some instr)
    (h_zero : IsZeroArity instr) :
    SavedCurFetchOutcome regHex sim metaProg dispatchOffset
      { cur := zeroArityTag instr h_zero
      , history := sim.cur :: encMetaHistory regHex sim
      , pc := dispatchOffset
      , prog := metaProg
      , halted := false } := by
  exact savedCurFetchOutcome_tag_state regHex sim metaProg dispatchOffset instr
    (zeroArityTag instr h_zero) h_get
    (by rw [encInstr_zeroArity_eq instr h_zero]; rfl)

/-- Forgetting the saved-current-cell prefix gives the old canonical-history
shape only after the restore prelude, not at dispatch handoff. This theorem
records the exact saved prefix for downstream composition. -/
theorem savedCurFetchOutcome_history_head
    (regHex : Hexagram) (sim : YiState) (metaProg : List YiInstr)
    (dispatchOffset : Nat) (μ' : YiState)
    (h : SavedCurFetchOutcome regHex sim metaProg dispatchOffset μ') :
    μ'.history.head? = some sim.cur := by
  rw [h.history]
  rfl

/-- The saved-current-cell fetch target still exposes the same opcode tag as the
old `FetchOutcome`; the only contract difference is the extra saved history
cell. -/
theorem savedCurFetchOutcome_tag_matches_instr
    (regHex : Hexagram) (sim : YiState) (metaProg : List YiInstr)
    (dispatchOffset : Nat) (μ' : YiState)
    (h : SavedCurFetchOutcome regHex sim metaProg dispatchOffset μ')
    (instr : YiInstr)
    (h_get : sim.prog[sim.pc]? = some instr) :
    μ'.cur ∈ (YiInstrEnc.encInstr instr).head? :=
  h.cur_is_tag instr h_get

/-! ## Public summary -/

theorem fetch_saved_cur_summary :
    (∀ regHex sim metaProg dispatchOffset instr tag,
      sim.prog[sim.pc]? = some instr →
      (YiInstrEnc.encInstr instr).head? = some tag →
        SavedCurFetchOutcome regHex sim metaProg dispatchOffset
          { cur := tag
          , history := sim.cur :: encMetaHistory regHex sim
          , pc := dispatchOffset
          , prog := metaProg
          , halted := false })
    ∧ (∀ regHex sim metaProg dispatchOffset μ',
        SavedCurFetchOutcome regHex sim metaProg dispatchOffset μ' →
          μ'.history.head? = some sim.cur) := by
  exact
    ⟨ savedCurFetchOutcome_tag_state
    , savedCurFetchOutcome_history_head
    ⟩

end SSBX.Foundation.Wen.MetaInterp.FetchSavedCur
