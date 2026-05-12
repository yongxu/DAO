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
import SSBX.Foundation.Wen.WenyanQuineEmitter

namespace SSBX.Foundation.Wen.MetaInterp.FetchSavedCurProg

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.MetaInterp
open SSBX.Foundation.Wen.MetaInterp.Fetch
open SSBX.Foundation.Wen.MetaInterp.FetchSavedCur
open SSBX.Foundation.Wen.MetaInterp.FetchSavedCurObligations
open SSBX.Foundation.Wen.MetaInterp.AssemblyRestorePlan
open SSBX.Foundation.Wen.WenyanQuineEmitter

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

/-! ## Executable finite-R8 re-emitter core -/

private def yao0 : Fin 6 := ⟨0, by omega⟩
private def yao1 : Fin 6 := ⟨1, by omega⟩
private def yao2 : Fin 6 := ⟨2, by omega⟩
private def yao3 : Fin 6 := ⟨3, by omega⟩
private def yao4 : Fin 6 := ⟨4, by omega⟩
private def yao5 : Fin 6 := ⟨5, by omega⟩

/-- Program fragment that mutates `META.cur` from a known cell to a known
target cell without touching history.  It is the non-pushing half of
`WenyanQuineEmitter.emitCellFrom`. -/
def setCellFrom (cur target : R8) : List YiInstr :=
  flipIfDiff cur.1 target.1 yao0 ++
  flipIfDiff cur.1 target.1 yao1 ++
  flipIfDiff cur.1 target.1 yao2 ++
  flipIfDiff cur.1 target.1 yao3 ++
  flipIfDiff cur.1 target.1 yao4 ++
  flipIfDiff cur.1 target.1 yao5 ++
  [YiInstr.setShi target.2]

/-- Macro-level saved-current re-emitter for a fixed finite R8 case:
set `cur` to the saved simulated cell, push it, restore the opcode tag, then
jump to restored dispatch.  The full fetch walker will reach this by a finite
R8 control dispatch over the incoming current cell. -/
def reemitSavedCurProg (tag saved : R8) (dispatchOffset : Nat) : List YiInstr :=
  setCellFrom tag saved ++
  [YiInstr.push] ++
  setCellFrom saved tag ++
  [YiInstr.jump dispatchOffset]

def reemitSavedCurPrefix (tag saved : R8) : List YiInstr :=
  setCellFrom tag saved ++
  [YiInstr.push] ++
  setCellFrom saved tag

def reemitSavedCurProg16 (tag saved : R8) (dispatchOffset : Nat) : List YiInstr :=
  reemitSavedCurPrefix tag saved ++
  List.replicate (15 - (reemitSavedCurPrefix tag saved).length) YiInstr.nop ++
  [YiInstr.jump dispatchOffset]

theorem setCellFrom_length_le (cur target : R8) :
    (setCellFrom cur target).length ≤ 7 := by
  have h0 := flipIfDiff_length_le cur.1 target.1 yao0
  have h1 := flipIfDiff_length_le cur.1 target.1 yao1
  have h2 := flipIfDiff_length_le cur.1 target.1 yao2
  have h3 := flipIfDiff_length_le cur.1 target.1 yao3
  have h4 := flipIfDiff_length_le cur.1 target.1 yao4
  have h5 := flipIfDiff_length_le cur.1 target.1 yao5
  simp only [setCellFrom, List.length_append, List.length_cons, List.length_nil]
  omega

theorem reemitSavedCurProg_length_le
    (tag saved : R8) (dispatchOffset : Nat) :
    (reemitSavedCurProg tag saved dispatchOffset).length ≤ 16 := by
  have h_saved := setCellFrom_length_le tag saved
  have h_tag := setCellFrom_length_le saved tag
  simp only [reemitSavedCurProg, List.length_append, List.length_cons,
    List.length_nil]
  omega

theorem reemitSavedCurProg_push_at_saved_boundary
    (tag saved : R8) (dispatchOffset : Nat) :
    (reemitSavedCurProg tag saved dispatchOffset)[(setCellFrom tag saved).length]? =
      some YiInstr.push := by
  simp [reemitSavedCurProg]

theorem reemitSavedCurProg_nonempty
    (tag saved : R8) (dispatchOffset : Nat) :
    (reemitSavedCurProg tag saved dispatchOffset).length > 0 := by
  simp [reemitSavedCurProg, setCellFrom]
  omega

theorem reemitSavedCurPrefix_length_le (tag saved : R8) :
    (reemitSavedCurPrefix tag saved).length ≤ 15 := by
  have h_saved := setCellFrom_length_le tag saved
  have h_tag := setCellFrom_length_le saved tag
  simp only [reemitSavedCurPrefix, List.length_append, List.length_cons,
    List.length_nil]
  omega

theorem reemitSavedCurProg16_length
    (tag saved : R8) (dispatchOffset : Nat) :
    (reemitSavedCurProg16 tag saved dispatchOffset).length = 16 := by
  have h_prefix := reemitSavedCurPrefix_length_le tag saved
  unfold reemitSavedCurProg16
  simp [List.length_append]
  omega

@[simp] private theorem yao_neg_eq_of_ne {a b : Yao} (h : a ≠ b) :
    a.neg = b := by
  cases a <;> cases b <;> simp [Yao.neg] at h ⊢

@[simp] private theorem yao_neg_eq_iff_ne (a b : Yao) :
    a.neg = b ↔ a ≠ b := by
  cases a <;> cases b <;> simp [Yao.neg]

@[simp] private theorem yao_eq_neg_iff_ne (a b : Yao) :
    b = a.neg ↔ a ≠ b := by
  cases a <;> cases b <;> simp [Yao.neg]

theorem setCellFrom_runFuel_state
    (cur target : R8) (history : List R8) (suffix : List YiInstr) :
    ({ cur := cur
      , history := history
      , pc := 0
      , prog := setCellFrom cur target ++ suffix
      , halted := false } : YiState).runFuel (setCellFrom cur target).length =
      { cur := target
      , history := history
      , pc := (setCellFrom cur target).length
      , prog := setCellFrom cur target ++ suffix
      , halted := false } := by
  rcases cur with ⟨ch, cs⟩
  rcases target with ⟨th, ts⟩
  rcases ch with ⟨c0, c1, c2, c3, c4, c5⟩
  rcases th with ⟨t0, t1, t2, t3, t4, t5⟩
  unfold setCellFrom flipIfDiff
  by_cases h0 : c0 = t0 <;>
    by_cases h1 : c1 = t1 <;>
    by_cases h2 : c2 = t2 <;>
    by_cases h3 : c3 = t3 <;>
    by_cases h4 : c4 = t4 <;>
    by_cases h5 : c5 = t5 <;>
    simp [yao0, yao1, yao2, yao3, yao4, yao5, h0, h1, h2, h3, h4, h5,
      Hexagram.yaoAt, Hexagram.flipPos,
      YiState.runFuel, YiState.step, YiState.execute]
  all_goals
    simp [yao_neg_eq_iff_ne, yao_eq_neg_iff_ne, Yao.neg_neg, *]

theorem reemitSavedCurProg_runFuel_state
    (tag saved : R8) (dispatchOffset : Nat) (history : List R8) :
    ({ cur := tag
      , history := history
      , pc := 0
      , prog := reemitSavedCurProg tag saved dispatchOffset
      , halted := false } : YiState).runFuel
        (reemitSavedCurProg tag saved dispatchOffset).length =
      { cur := tag
      , history := saved :: history
      , pc := dispatchOffset
      , prog := reemitSavedCurProg tag saved dispatchOffset
      , halted := false } := by
  rcases tag with ⟨tagHex, tagShi⟩
  rcases saved with ⟨savedHex, savedShi⟩
  rcases tagHex with ⟨a0, a1, a2, a3, a4, a5⟩
  rcases savedHex with ⟨b0, b1, b2, b3, b4, b5⟩
  unfold reemitSavedCurProg setCellFrom flipIfDiff
  by_cases h0 : a0 = b0 <;>
    by_cases h1 : a1 = b1 <;>
    by_cases h2 : a2 = b2 <;>
    by_cases h3 : a3 = b3 <;>
    by_cases h4 : a4 = b4 <;>
    by_cases h5 : a5 = b5 <;>
    simp [yao0, yao1, yao2, yao3, yao4, yao5, h0, h1, h2, h3, h4, h5,
      eq_comm, Hexagram.yaoAt, Hexagram.flipPos,
      YiState.runFuel, YiState.step, YiState.execute]
  all_goals
    simp [yao_neg_eq_iff_ne, yao_eq_neg_iff_ne, Yao.neg_neg, *]

theorem reemitSavedCurProg16_runFuel_state
    (tag saved : R8) (dispatchOffset : Nat) (history : List R8) :
    ({ cur := tag
      , history := history
      , pc := 0
      , prog := reemitSavedCurProg16 tag saved dispatchOffset
      , halted := false } : YiState).runFuel
        (reemitSavedCurProg16 tag saved dispatchOffset).length =
      { cur := tag
      , history := saved :: history
      , pc := dispatchOffset
      , prog := reemitSavedCurProg16 tag saved dispatchOffset
      , halted := false } := by
  rcases tag with ⟨tagHex, tagShi⟩
  rcases saved with ⟨savedHex, savedShi⟩
  rcases tagHex with ⟨a0, a1, a2, a3, a4, a5⟩
  rcases savedHex with ⟨b0, b1, b2, b3, b4, b5⟩
  unfold reemitSavedCurProg16 reemitSavedCurPrefix setCellFrom flipIfDiff
  by_cases h0 : a0 = b0 <;>
    by_cases h1 : a1 = b1 <;>
    by_cases h2 : a2 = b2 <;>
    by_cases h3 : a3 = b3 <;>
    by_cases h4 : a4 = b4 <;>
    by_cases h5 : a5 = b5 <;>
    simp [yao0, yao1, yao2, yao3, yao4, yao5, h0, h1, h2, h3, h4, h5,
      eq_comm, Hexagram.yaoAt, Hexagram.flipPos,
      YiState.runFuel, YiState.step, YiState.execute]
  all_goals
    simp [yao_neg_eq_iff_ne, yao_eq_neg_iff_ne, Yao.neg_neg, *]

theorem reemitSavedCurProg_from_fetchOutcome_yields_savedCur
    (regHex : Hexagram) (sim μ : YiState) (dispatchOffset : Nat)
    (h_fetch :
      FetchOutcome regHex sim
        (reemitSavedCurProg μ.cur sim.cur dispatchOffset) 0 μ) :
    SavedCurFetchOutcome regHex sim
      (reemitSavedCurProg μ.cur sim.cur dispatchOffset)
      dispatchOffset
      (μ.runFuel (reemitSavedCurProg μ.cur sim.cur dispatchOffset).length) := by
  cases μ with
  | mk cur history pc prog halted =>
      have h_history := h_fetch.history
      have h_pc := h_fetch.pc
      have h_prog := h_fetch.prog
      have h_halted := h_fetch.halted
      simp at h_history h_pc h_prog h_halted
      subst history
      subst pc
      subst prog
      subst halted
      rw [reemitSavedCurProg_runFuel_state]
      refine ⟨?_, rfl, rfl, rfl, rfl⟩
      intro instr h_get
      exact h_fetch.cur_is_tag instr h_get

theorem reemitSavedCurProg16_from_fetchOutcome_yields_savedCur
    (regHex : Hexagram) (sim μ : YiState) (dispatchOffset : Nat)
    (h_fetch :
      FetchOutcome regHex sim
        (reemitSavedCurProg16 μ.cur sim.cur dispatchOffset) 0 μ) :
    SavedCurFetchOutcome regHex sim
      (reemitSavedCurProg16 μ.cur sim.cur dispatchOffset)
      dispatchOffset
      (μ.runFuel (reemitSavedCurProg16 μ.cur sim.cur dispatchOffset).length) := by
  cases μ with
  | mk cur history pc prog halted =>
      have h_history := h_fetch.history
      have h_pc := h_fetch.pc
      have h_prog := h_fetch.prog
      have h_halted := h_fetch.halted
      simp at h_history h_pc h_prog h_halted
      subst history
      subst pc
      subst prog
      subst halted
      rw [reemitSavedCurProg16_runFuel_state]
      refine ⟨?_, rfl, rfl, rfl, rfl⟩
      intro instr h_get
      exact h_fetch.cur_is_tag instr h_get

theorem fetch_saved_cur_reemit_macro_summary :
    (∀ cur target : R8, (setCellFrom cur target).length ≤ 7)
    ∧ (∀ tag saved : R8, ∀ dispatchOffset : Nat,
        (reemitSavedCurProg tag saved dispatchOffset).length ≤ 16)
    ∧ (∀ tag saved : R8, ∀ dispatchOffset : Nat,
        (reemitSavedCurProg16 tag saved dispatchOffset).length = 16)
    ∧ (∀ tag saved : R8, ∀ dispatchOffset : Nat,
        (reemitSavedCurProg tag saved dispatchOffset)[
          (setCellFrom tag saved).length]? = some YiInstr.push)
    ∧ (∀ tag saved : R8, ∀ dispatchOffset : Nat, ∀ history : List R8,
        ({ cur := tag
          , history := history
          , pc := 0
          , prog := reemitSavedCurProg tag saved dispatchOffset
          , halted := false } : YiState).runFuel
            (reemitSavedCurProg tag saved dispatchOffset).length =
          { cur := tag
          , history := saved :: history
          , pc := dispatchOffset
          , prog := reemitSavedCurProg tag saved dispatchOffset
          , halted := false })
    ∧ (∀ regHex sim μ dispatchOffset,
        FetchOutcome regHex sim
          (reemitSavedCurProg μ.cur sim.cur dispatchOffset) 0 μ →
          SavedCurFetchOutcome regHex sim
            (reemitSavedCurProg μ.cur sim.cur dispatchOffset)
            dispatchOffset
            (μ.runFuel
              (reemitSavedCurProg μ.cur sim.cur dispatchOffset).length))
    ∧ (∀ regHex sim μ dispatchOffset,
        FetchOutcome regHex sim
          (reemitSavedCurProg16 μ.cur sim.cur dispatchOffset) 0 μ →
          SavedCurFetchOutcome regHex sim
            (reemitSavedCurProg16 μ.cur sim.cur dispatchOffset)
            dispatchOffset
            (μ.runFuel
              (reemitSavedCurProg16 μ.cur sim.cur dispatchOffset).length)) := by
  exact
    ⟨ setCellFrom_length_le
    , reemitSavedCurProg_length_le
    , reemitSavedCurProg16_length
    , reemitSavedCurProg_push_at_saved_boundary
    , reemitSavedCurProg_runFuel_state
    , reemitSavedCurProg_from_fetchOutcome_yields_savedCur
    , reemitSavedCurProg16_from_fetchOutcome_yields_savedCur
    ⟩

def reemitSmokeTag : R8 :=
  (Hexagram.heaven, Shi.dao)

def reemitSmokeSaved : R8 :=
  (Hexagram.heaven, Shi.jin)

theorem reemitSavedCurProg_smoke :
    let tag := reemitSmokeTag
    let saved := reemitSmokeSaved
    let prog := reemitSavedCurProg tag saved 7
    let μ : YiState :=
      { cur := tag
      , history := []
      , pc := 0
      , prog := prog
      , halted := false }
    let μ' := μ.runFuel prog.length
    μ'.cur = tag
      ∧ μ'.history = [saved]
      ∧ μ'.pc = 7
      ∧ μ'.halted = false := by
  native_decide

end SSBX.Foundation.Wen.MetaInterp.FetchSavedCurProg
