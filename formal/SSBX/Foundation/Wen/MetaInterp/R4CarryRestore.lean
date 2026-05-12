/-
# R4CarryRestore -- restore an R4-squared carried current cell

This is the executable half of the R4-squared saved-current architecture.  A
future fetch walker may reuse `META.cur` to read the opcode tag while carrying
the original current cell as `R4 x R4` control data.  Once dispatch has selected
the block body, this fragment restores the carried cell into `META.cur` and
lands on the existing `BlockPre` contract.

The module deliberately does not build a flat 256 table and does not change the
VM.  The current cell is represented through `R4Carry.SavedCurrentCarry`, whose
round-trip is backed by `SelfSimilarity.r8_eq_r4_squared`.
-/
import SSBX.Foundation.Wen.MetaInterp.R4Carry
import SSBX.Foundation.Wen.MetaInterp.FetchSavedCurProg

namespace SSBX.Foundation.Wen.MetaInterp.R4CarryRestore

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.MetaInterp
open SSBX.Foundation.Wen.MetaInterp.ExecuteBlock
open SSBX.Foundation.Wen.MetaInterp.Fetch
open SSBX.Foundation.Wen.MetaInterp.R4Carry

/-! ## Fuel helpers -/

private theorem runFuel_add (s : YiState) (m n : Nat) :
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

private theorem nops_advance
    (s : YiState) (n k : Nat) (hk : k ≤ n)
    (h_halted : s.halted = false)
    (h_nopSlots : ∀ j (_ : j < n), s.prog[s.pc + j]? = some YiInstr.nop) :
    ∃ s', s.runFuel k = s'
      ∧ s'.pc = s.pc + k
      ∧ s'.halted = false
      ∧ s'.prog = s.prog
      ∧ s'.cur = s.cur
      ∧ s'.history = s.history := by
  induction k with
  | zero =>
      refine ⟨s, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [YiState.runFuel, h_halted]
  | succ k ih =>
      have hk' : k ≤ n := Nat.le_of_succ_le hk
      have hk_lt : k < n := hk
      obtain ⟨s', hrun, hpc', hhalt', hprog', hcur', hhist'⟩ := ih hk'
      have hstep : s.runFuel (k + 1) = s'.step := by
        rw [SSBX.Foundation.Bagua.GodelLi.runFuel_succ_right, hrun]
      have h_lookup : s'.prog[s'.pc]? = some YiInstr.nop := by
        rw [hpc', hprog']
        exact h_nopSlots k hk_lt
      have h_step_pc : s'.step.pc = s'.pc + 1 := by
        unfold YiState.step
        rw [hhalt']; simp only [Bool.false_eq_true, if_false]
        rw [h_lookup]; rfl
      have h_step_halted : s'.step.halted = false := by
        unfold YiState.step
        rw [hhalt']; simp only [Bool.false_eq_true, if_false]
        rw [h_lookup]; show (YiState.execute YiInstr.nop s').halted = false
        unfold YiState.execute; exact hhalt'
      have h_step_prog : s'.step.prog = s.prog := by
        unfold YiState.step
        rw [hhalt']; simp only [Bool.false_eq_true, if_false]
        rw [h_lookup]; show (YiState.execute YiInstr.nop s').prog = s.prog
        unfold YiState.execute; exact hprog'
      have h_step_cur : s'.step.cur = s.cur := by
        unfold YiState.step
        rw [hhalt']; simp only [Bool.false_eq_true, if_false]
        rw [h_lookup]; show (YiState.execute YiInstr.nop s').cur = s.cur
        unfold YiState.execute; exact hcur'
      have h_step_history : s'.step.history = s.history := by
        unfold YiState.step
        rw [hhalt']; simp only [Bool.false_eq_true, if_false]
        rw [h_lookup]; show (YiState.execute YiInstr.nop s').history = s.history
        unfold YiState.execute; exact hhist'
      refine ⟨s'.step, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hstep
      · rw [h_step_pc, hpc']; omega
      · exact h_step_halted
      · exact h_step_prog
      · exact h_step_cur
      · exact h_step_history

private theorem nops_then_jump
    (s : YiState) (n target : Nat)
    (h_halted : s.halted = false)
    (h_nopSlots : ∀ j (_ : j < n), s.prog[s.pc + j]? = some YiInstr.nop)
    (h_jumpAt : s.prog[s.pc + n]? = some (YiInstr.jump target)) :
    s.runFuel (n + 1) =
      { cur := s.cur
      , history := s.history
      , pc := target
      , prog := s.prog
      , halted := false } := by
  obtain ⟨s', hrun, hpc', hhalt', hprog', hcur', hhist'⟩ :=
    nops_advance s n n (Nat.le_refl n) h_halted h_nopSlots
  have hstep : s.runFuel (n + 1) = s'.step := by
    rw [SSBX.Foundation.Bagua.GodelLi.runFuel_succ_right, hrun]
  have h_lookup : s'.prog[s'.pc]? = some (YiInstr.jump target) := by
    rw [hpc', hprog']; exact h_jumpAt
  rw [hstep]
  unfold YiState.step
  rw [hhalt']; simp only [Bool.false_eq_true, if_false]
  rw [h_lookup]
  simp [YiState.execute, hcur', hhist', hprog', hhalt']

/-! ## R4-squared restore program -/

/-- Mutate `META.cur` from a known source tag to the R8 cell carried as R4 x R4. -/
def setCellFromCarry (source : R8) (carry : SavedCurrentCarry) : List YiInstr :=
  FetchSavedCurProg.setCellFrom source (cellOfCarry carry)

theorem setCellFromCarry_length_le (source : R8) (carry : SavedCurrentCarry) :
    (setCellFromCarry source carry).length ≤ 7 := by
  simpa [setCellFromCarry] using
    FetchSavedCurProg.setCellFrom_length_le source (cellOfCarry carry)

theorem setCellFromCarry_runFuel_state
    (source : R8) (carry : SavedCurrentCarry) (history : List R8)
    (suffix : List YiInstr) :
    ({ cur := source
      , history := history
      , pc := 0
      , prog := setCellFromCarry source carry ++ suffix
      , halted := false } : YiState).runFuel (setCellFromCarry source carry).length =
      { cur := cellOfCarry carry
      , history := history
      , pc := (setCellFromCarry source carry).length
      , prog := setCellFromCarry source carry ++ suffix
      , halted := false } := by
  simpa [setCellFromCarry] using
    FetchSavedCurProg.setCellFrom_runFuel_state source (cellOfCarry carry) history suffix

/-- Fixed 8-slot restore fragment:

1. set `META.cur` from the opcode tag to the carried current cell;
2. pad with no-ops to a fixed 7-slot prefix;
3. jump to the existing block body offset.
-/
def restoreCarryProg8 (tag : R8) (carry : SavedCurrentCarry) (bodyOffset : Nat) :
    List YiInstr :=
  setCellFromCarry tag carry ++
    (List.replicate (7 - (setCellFromCarry tag carry).length) YiInstr.nop ++
      [YiInstr.jump bodyOffset])

theorem restoreCarryProg8_length
    (tag : R8) (carry : SavedCurrentCarry) (bodyOffset : Nat) :
    (restoreCarryProg8 tag carry bodyOffset).length = 8 := by
  have h_prefix := setCellFromCarry_length_le tag carry
  unfold restoreCarryProg8
  simp [List.length_append]
  omega

private theorem restoreCarryProg8_nop_slot
    (tag : R8) (carry : SavedCurrentCarry) (bodyOffset j : Nat)
    (h_j : j < 7 - (setCellFromCarry tag carry).length) :
    (restoreCarryProg8 tag carry bodyOffset)[(setCellFromCarry tag carry).length + j]? =
      some YiInstr.nop := by
  unfold restoreCarryProg8
  rw [List.getElem?_append_right]
  · have h_sub :
        (setCellFromCarry tag carry).length + j -
            (setCellFromCarry tag carry).length = j := by
      omega
    have h_rep :
        j <
          (List.replicate
            (7 - (setCellFromCarry tag carry).length) YiInstr.nop).length := by
      simpa using h_j
    rw [h_sub]
    rw [List.getElem?_append_left (l₂ := [YiInstr.jump bodyOffset]) h_rep]
    rw [List.getElem?_replicate]
    simp [h_j]
  · omega

private theorem restoreCarryProg8_jump_at_seven
    (tag : R8) (carry : SavedCurrentCarry) (bodyOffset : Nat) :
    (restoreCarryProg8 tag carry bodyOffset)[7]? =
      some (YiInstr.jump bodyOffset) := by
  have h_pref := setCellFromCarry_length_le tag carry
  unfold restoreCarryProg8
  rw [List.getElem?_append_right]
  · have h_sub :
        7 - (setCellFromCarry tag carry).length =
          (7 - (setCellFromCarry tag carry).length) := rfl
    rw [h_sub]
    rw [List.getElem?_append_right]
    · simp
    · simp
  · exact h_pref

theorem restoreCarryProg8_runFuel_state
    (tag : R8) (carry : SavedCurrentCarry) (bodyOffset : Nat) (history : List R8) :
    ({ cur := tag
      , history := history
      , pc := 0
      , prog := restoreCarryProg8 tag carry bodyOffset
      , halted := false } : YiState).runFuel
        (restoreCarryProg8 tag carry bodyOffset).length =
      { cur := cellOfCarry carry
      , history := history
      , pc := bodyOffset
      , prog := restoreCarryProg8 tag carry bodyOffset
      , halted := false } := by
  let pref := setCellFromCarry tag carry
  let padLen := 7 - pref.length
  let suffix := List.replicate padLen YiInstr.nop ++ [YiInstr.jump bodyOffset]
  let entry : YiState :=
    { cur := tag
    , history := history
    , pc := 0
    , prog := restoreCarryProg8 tag carry bodyOffset
    , halted := false }
  have h_prog : restoreCarryProg8 tag carry bodyOffset = pref ++ suffix := by
    simp [pref, suffix, padLen, restoreCarryProg8]
  have h_len : (restoreCarryProg8 tag carry bodyOffset).length = pref.length + (padLen + 1) := by
    rw [restoreCarryProg8_length]
    have h_pref := setCellFromCarry_length_le tag carry
    simp [pref, padLen]
    omega
  have h_set :
      entry.runFuel pref.length =
        { cur := cellOfCarry carry
        , history := history
        , pc := pref.length
        , prog := restoreCarryProg8 tag carry bodyOffset
        , halted := false } := by
    unfold entry
    rw [h_prog]
    simpa [pref, suffix] using
      setCellFromCarry_runFuel_state tag carry history suffix
  have h_nops :
      ({ cur := cellOfCarry carry
        , history := history
        , pc := pref.length
        , prog := restoreCarryProg8 tag carry bodyOffset
        , halted := false } : YiState).runFuel (padLen + 1) =
        { cur := cellOfCarry carry
        , history := history
        , pc := bodyOffset
        , prog := restoreCarryProg8 tag carry bodyOffset
        , halted := false } := by
    apply nops_then_jump
    · rfl
    · intro j h_j
      simpa [pref, padLen] using
        restoreCarryProg8_nop_slot tag carry bodyOffset j h_j
    · have h_pref := setCellFromCarry_length_le tag carry
      have h_index : pref.length + padLen = 7 := by
        simp [pref, padLen]
        omega
      rw [h_index]
      exact restoreCarryProg8_jump_at_seven tag carry bodyOffset
  rw [h_len, runFuel_add entry pref.length (padLen + 1), h_set]
  exact h_nops

/-! ## Carry-level contracts -/

/-- Fetch has decoded the opcode tag in `META.cur` while the original current
cell is carried in the proof/control path as `R4 x R4`. -/
structure R4CarryFetchOutcome
    (regHex : Hexagram) (sim : YiState) (metaProg : List YiInstr)
    (handoffOffset : Nat) (carry : SavedCurrentCarry) (μ' : YiState) : Prop where
  cur_is_tag :
    ∀ instr, sim.prog[sim.pc]? = some instr →
      μ'.cur ∈ (YiInstrEnc.encInstr instr).head?
  carry_eq :
    carry = carryOfCell sim.cur
  history :
    μ'.history = encMetaHistory regHex sim
  pc :
    μ'.pc = handoffOffset
  prog :
    μ'.prog = metaProg
  halted :
    μ'.halted = false

theorem restoreCarryProg8_yields_BlockPre
    (regHex : Hexagram) (sim : YiState) (tag : R8)
    (carry : SavedCurrentCarry) (bodyOffset : Nat)
    (hcarry : carry = carryOfCell sim.cur) :
    BlockPre regHex sim bodyOffset (restoreCarryProg8 tag carry bodyOffset)
      (({ cur := tag
        , history := encMetaHistory regHex sim
        , pc := 0
        , prog := restoreCarryProg8 tag carry bodyOffset
        , halted := false } : YiState).runFuel
          (restoreCarryProg8 tag carry bodyOffset).length) := by
  rw [restoreCarryProg8_runFuel_state]
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  rw [hcarry]
  exact cellOfCarry_carryOfCell sim.cur

/-- Contract surface for composing a carry-aware fetch/dispatch/restore path. -/
structure R4CarryDispatchRestoreObligations : Prop where
  restores :
    ∀ regHex sim tag carry bodyOffset,
      carry = carryOfCell sim.cur →
        BlockPre regHex sim bodyOffset (restoreCarryProg8 tag carry bodyOffset)
          (({ cur := tag
            , history := encMetaHistory regHex sim
            , pc := 0
            , prog := restoreCarryProg8 tag carry bodyOffset
            , halted := false } : YiState).runFuel
              (restoreCarryProg8 tag carry bodyOffset).length)

theorem r4_carry_dispatch_restore_obligations :
    R4CarryDispatchRestoreObligations where
  restores := restoreCarryProg8_yields_BlockPre

theorem restoreCarryProg8_from_fetchOutcome_yields_BlockPre
    (regHex : Hexagram) (sim μ : YiState)
    (carry : SavedCurrentCarry) (bodyOffset : Nat)
    (h_fetch :
      R4CarryFetchOutcome regHex sim
        (restoreCarryProg8 μ.cur carry bodyOffset) 0 carry μ) :
    BlockPre regHex sim bodyOffset (restoreCarryProg8 μ.cur carry bodyOffset)
      (μ.runFuel (restoreCarryProg8 μ.cur carry bodyOffset).length) := by
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
      exact restoreCarryProg8_yields_BlockPre regHex sim cur carry bodyOffset h_fetch.carry_eq

/-! ## Public summary -/

theorem r4_carry_restore_summary :
    (∀ source carry, (setCellFromCarry source carry).length ≤ 7)
    ∧ (∀ tag carry bodyOffset, (restoreCarryProg8 tag carry bodyOffset).length = 8)
    ∧ (∀ regHex sim tag carry bodyOffset,
        carry = carryOfCell sim.cur →
          BlockPre regHex sim bodyOffset (restoreCarryProg8 tag carry bodyOffset)
            (({ cur := tag
              , history := encMetaHistory regHex sim
              , pc := 0
              , prog := restoreCarryProg8 tag carry bodyOffset
              , halted := false } : YiState).runFuel
                (restoreCarryProg8 tag carry bodyOffset).length)) := by
  exact
    ⟨ setCellFromCarry_length_le
    , restoreCarryProg8_length
    , restoreCarryProg8_yields_BlockPre
    ⟩

end SSBX.Foundation.Wen.MetaInterp.R4CarryRestore
