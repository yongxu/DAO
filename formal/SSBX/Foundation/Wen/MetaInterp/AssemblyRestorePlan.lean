/-
# AssemblyRestorePlan -- restored-dispatch layout blueprint

This sidecar keeps the current Strategy-B assembly intact while fixing the next
layout target for F.7c. Dispatch targets should land on a uniform `pop`
restore prelude; the real block body begins one instruction later, with the
existing `BlockPre` shape restored by `DispatchRestore`.
-/

import SSBX.Foundation.Wen.MetaInterp.DispatchRestore
import SSBX.Foundation.Wen.MetaInterp.PrologueProg
import SSBX.Foundation.Wen.MetaInterp.OuterLoop
import SSBX.Foundation.Wen.MetaInterp.FetchProg
import SSBX.Foundation.Wen.MetaInterp.DispatchProg
import SSBX.Foundation.Wen.MetaInterp.ExecuteBlocks
import SSBX.Foundation.Wen.MetaInterp.ExecuteBlocksHard

namespace SSBX.Foundation.Wen.MetaInterp.AssemblyRestorePlan

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.MetaInterp
open SSBX.Foundation.Wen.MetaInterp.Dispatch
open SSBX.Foundation.Wen.MetaInterp.ExecuteBlocks.Aggregate
open SSBX.Foundation.Wen.MetaInterp.ExecuteBlocksHard

/-! ## Restored offsets -/

def prologueOffset : Nat := 0
def outerLoopOffset : Nat := 5
def fetchOffset : Nat := 6
def fetchHaltDetectOffset : Nat := fetchOffset + 3
def dispatchOffset : Nat := 20

def block_nop_offset : Nat := 36
def block_setShi_offset : Nat := 39
def block_flipYao_offset : Nat := 42
def block_hu_offset : Nat := 45
def block_cuo_offset : Nat := 48
def block_zong_offset : Nat := 51
def block_branchYaoEq_offset : Nat := 54
def block_branchShiEq_offset : Nat := 65
def block_jump_offset : Nat := 76
def block_push_offset : Nat := 86
def block_pop_offset : Nat := 92
def haltOffset : Nat := 98

def bodyOffset (restoreOffset : Nat) : Nat :=
  restoreOffset + 1

/-! ## Restored blocks -/

def restorePrelude : List YiInstr :=
  [YiInstr.pop]

def withRestore (body : List YiInstr) : List YiInstr :=
  restorePrelude ++ body

theorem restorePrelude_length :
    restorePrelude.length = 1 := rfl

def restoredBlock_nop : List YiInstr :=
  withRestore
    (ExecuteBlocks.Aggregate.executeBlock_nop (bodyOffset block_nop_offset) fetchOffset)

def restoredBlock_setShi : List YiInstr :=
  withRestore (ExecuteBlocks.Aggregate.executeBlock_setShi Shi.dao fetchOffset)

def restoredBlock_flipYao : List YiInstr :=
  withRestore (ExecuteBlocks.Aggregate.executeBlock_flipYao 0 fetchOffset)

def restoredBlock_hu : List YiInstr :=
  withRestore
    (ExecuteBlocks.Aggregate.executeBlock_hu (bodyOffset block_hu_offset) fetchOffset)

def restoredBlock_cuo : List YiInstr :=
  withRestore
    (ExecuteBlocks.Aggregate.executeBlock_cuo (bodyOffset block_cuo_offset) fetchOffset)

def restoredBlock_zong : List YiInstr :=
  withRestore (ExecuteBlocks.Aggregate.executeBlock_zong fetchOffset)

def restoredBlock_branchYaoEq : List YiInstr :=
  withRestore (ExecuteBlocksHard.executeBlock_branchYaoEq 0 0 0 fetchOffset)

def restoredBlock_branchShiEq : List YiInstr :=
  withRestore (ExecuteBlocksHard.executeBlock_branchShiEq Shi.dao 0 fetchOffset)

def restoredBlock_jump : List YiInstr :=
  withRestore (ExecuteBlocksHard.executeBlock_jump 0 fetchOffset)

def restoredBlock_push : List YiInstr :=
  withRestore (ExecuteBlocksHard.executeBlock_push fetchOffset)

def restoredBlock_pop : List YiInstr :=
  withRestore (ExecuteBlocksHard.executeBlock_pop fetchOffset)

def restoredBlock_halt : List YiInstr :=
  withRestore
    (ExecuteBlocks.Aggregate.executeBlock_halt (bodyOffset block_pop_offset) fetchOffset)

theorem restoredBlock_nop_length :
    restoredBlock_nop.length = 3 := rfl

theorem restoredBlock_setShi_length :
    restoredBlock_setShi.length = 3 := rfl

theorem restoredBlock_flipYao_length :
    restoredBlock_flipYao.length = 3 := rfl

theorem restoredBlock_hu_length :
    restoredBlock_hu.length = 3 := rfl

theorem restoredBlock_cuo_length :
    restoredBlock_cuo.length = 3 := rfl

theorem restoredBlock_zong_length :
    restoredBlock_zong.length = 3 := rfl

theorem restoredBlock_branchYaoEq_length :
    restoredBlock_branchYaoEq.length = 11 := by
  native_decide

theorem restoredBlock_branchShiEq_length :
    restoredBlock_branchShiEq.length = 11 := by
  native_decide

theorem restoredBlock_jump_length :
    restoredBlock_jump.length = 10 := by
  native_decide

theorem restoredBlock_push_length :
    restoredBlock_push.length = 6 := by
  native_decide

theorem restoredBlock_pop_length :
    restoredBlock_pop.length = 6 := by
  native_decide

theorem restoredBlock_halt_length :
    restoredBlock_halt.length = 2 := rfl

/-! ## Restored dispatch table and program -/

def restoredDispatchOffsets : DispatchOffsets where
  nop_offset := block_nop_offset
  hu_offset := block_hu_offset
  cuo_offset := block_cuo_offset
  zong_offset := block_zong_offset
  push_offset := block_push_offset
  pop_offset := block_pop_offset
  halt_offset := haltOffset
  jump_offset := block_jump_offset
  setShi_dispatch_offset := block_setShi_offset
  flipYao_dispatch_offset := block_flipYao_offset
  branchYaoEq_dispatch_offset := block_branchYaoEq_offset
  branchShiEq_dispatch_offset := block_branchShiEq_offset

def restoredMetaInterpProg : List YiInstr :=
  PrologueProg.prologueProg
  ++ OuterLoop.outerLoopEntry fetchOffset
  ++ FetchProg.fetchProgWithPeel fetchOffset dispatchOffset haltOffset
  ++ DispatchProg.dispatchProg restoredDispatchOffsets dispatchOffset
  ++ restoredBlock_nop
  ++ restoredBlock_setShi
  ++ restoredBlock_flipYao
  ++ restoredBlock_hu
  ++ restoredBlock_cuo
  ++ restoredBlock_zong
  ++ restoredBlock_branchYaoEq
  ++ restoredBlock_branchShiEq
  ++ restoredBlock_jump
  ++ restoredBlock_push
  ++ restoredBlock_pop
  ++ restoredBlock_halt

theorem restoredMetaInterpProg_length :
    restoredMetaInterpProg.length = 100 := by
  simp only [restoredMetaInterpProg, List.length_append,
    PrologueProg.prologueProg_length,
    OuterLoop.outerLoopEntry_length,
    FetchProg.fetchProgWithPeel_length_concrete,
    DispatchProg.dispatchProg_length,
    restoredBlock_nop_length,
    restoredBlock_setShi_length,
    restoredBlock_flipYao_length,
    restoredBlock_hu_length,
    restoredBlock_cuo_length,
    restoredBlock_zong_length,
    restoredBlock_branchYaoEq_length,
    restoredBlock_branchShiEq_length,
    restoredBlock_jump_length,
    restoredBlock_push_length,
    restoredBlock_pop_length,
    restoredBlock_halt_length]

theorem restoredMetaInterpProg_nop_restore_at_offset :
    restoredMetaInterpProg[block_nop_offset]? = some YiInstr.pop := rfl

theorem restoredMetaInterpProg_setShi_restore_at_offset :
    restoredMetaInterpProg[block_setShi_offset]? = some YiInstr.pop := rfl

theorem restoredMetaInterpProg_flipYao_restore_at_offset :
    restoredMetaInterpProg[block_flipYao_offset]? = some YiInstr.pop := rfl

theorem restoredMetaInterpProg_hu_restore_at_offset :
    restoredMetaInterpProg[block_hu_offset]? = some YiInstr.pop := rfl

theorem restoredMetaInterpProg_cuo_restore_at_offset :
    restoredMetaInterpProg[block_cuo_offset]? = some YiInstr.pop := rfl

theorem restoredMetaInterpProg_zong_restore_at_offset :
    restoredMetaInterpProg[block_zong_offset]? = some YiInstr.pop := rfl

theorem restoredMetaInterpProg_branchYaoEq_restore_at_offset :
    restoredMetaInterpProg[block_branchYaoEq_offset]? = some YiInstr.pop := rfl

theorem restoredMetaInterpProg_branchShiEq_restore_at_offset :
    restoredMetaInterpProg[block_branchShiEq_offset]? = some YiInstr.pop := rfl

theorem restoredMetaInterpProg_jump_restore_at_offset :
    restoredMetaInterpProg[block_jump_offset]? = some YiInstr.pop := rfl

theorem restoredMetaInterpProg_push_restore_at_offset :
    restoredMetaInterpProg[block_push_offset]? = some YiInstr.pop := rfl

theorem restoredMetaInterpProg_pop_restore_at_offset :
    restoredMetaInterpProg[block_pop_offset]? = some YiInstr.pop := rfl

theorem restoredMetaInterpProg_halt_restore_at_offset :
    restoredMetaInterpProg[haltOffset]? = some YiInstr.pop := rfl

/-! ## Restored dispatch routing -/

/-- The restored dispatch tree is spliced into `restoredMetaInterpProg` at the
same dispatch offset as the current Strategy-B assembly. -/
theorem restoredMetaInterpProg_dispatchProg_at_offset :
    ∀ i (_hi : i < 16),
      restoredMetaInterpProg[dispatchOffset + i]? =
        (DispatchProg.dispatchProg restoredDispatchOffsets dispatchOffset)[i]? := by
  intro i hi
  rcases i with _ | i
  · rfl
  rcases i with _ | i
  · rfl
  rcases i with _ | i
  · rfl
  rcases i with _ | i
  · rfl
  rcases i with _ | i
  · rfl
  rcases i with _ | i
  · rfl
  rcases i with _ | i
  · rfl
  rcases i with _ | i
  · rfl
  rcases i with _ | i
  · rfl
  rcases i with _ | i
  · rfl
  rcases i with _ | i
  · rfl
  rcases i with _ | i
  · rfl
  rcases i with _ | i
  · rfl
  rcases i with _ | i
  · rfl
  rcases i with _ | i
  · rfl
  rcases i with _ | i
  · rfl
  omega

/-- Instruction-indexed dispatch routing for the restored layout. Dispatch
lands on the restore prelude, not the block body. -/
theorem restoredMetaInterpProg_dispatch_routes_instr_at_fuel
    (history : List R8) (instr : YiInstr) :
    let μ : YiState :=
      { cur := dispatchTagOfInstr instr
      , history := history
      , pc := dispatchOffset
      , prog := restoredMetaInterpProg
      , halted := false }
    let μ' := μ.runFuel (dispatchFuelOfInstr instr)
    μ'.pc = dispatchTargetOfInstr restoredDispatchOffsets instr
      ∧ μ'.cur = dispatchTagOfInstr instr
      ∧ μ'.history = history
      ∧ μ'.prog = restoredMetaInterpProg
      ∧ μ'.halted = false := by
  simpa using
    dispatchTree_routes_instr_at_segment restoredDispatchOffsets dispatchOffset
      restoredMetaInterpProg history instr restoredMetaInterpProg_dispatchProg_at_offset

/-- Every instruction-indexed dispatch target in the restored layout begins
with the uniform saved-current-cell restore prelude. -/
theorem restoredMetaInterpProg_dispatchTarget_has_restore (instr : YiInstr) :
    restoredMetaInterpProg[dispatchTargetOfInstr restoredDispatchOffsets instr]? =
      some YiInstr.pop := by
  cases instr <;> rfl

theorem restoredMetaInterpProg_savedCur_target_yields_BlockPre
    (regHex : Hexagram) (sim : YiState) (instr : YiInstr) :
    ExecuteBlock.BlockPre regHex sim
      (dispatchTargetOfInstr restoredDispatchOffsets instr + 1)
      restoredMetaInterpProg
      ((DispatchRestore.savedCurBlockEntryState regHex sim restoredMetaInterpProg
        (dispatchTargetOfInstr restoredDispatchOffsets instr) instr).runFuel 1) := by
  exact DispatchRestore.restoreSavedCur_yields_BlockPre
    regHex sim restoredMetaInterpProg
    (dispatchTargetOfInstr restoredDispatchOffsets instr) instr
    (restoredMetaInterpProg_dispatchTarget_has_restore instr)

/-! ## Restored block-body witnesses -/

theorem restoredMetaInterpProg_nop_body_push_at_offset :
    restoredMetaInterpProg[bodyOffset block_nop_offset]? = some YiInstr.push := rfl

theorem restoredMetaInterpProg_nop_body_jump_at_offset :
    restoredMetaInterpProg[bodyOffset block_nop_offset + 1]? =
      some (YiInstr.jump fetchOffset) := rfl

theorem restoredMetaInterpProg_execute_nop_simulates_aligned
    (regHex : Hexagram) (sim μ : YiState)
    (h_alive : sim.halted = false)
    (h_nop : sim.prog[sim.pc]? = some .nop)
    (h_curAligned : sim.cur = regDataCell regHex)
    (h_pre :
      ExecuteBlock.BlockPre regHex sim (bodyOffset block_nop_offset)
        restoredMetaInterpProg μ) :
    ExecuteBlock.BlockPost regHex sim fetchOffset restoredMetaInterpProg
      (μ.runFuel 2) false := by
  exact ExecuteBlock.executeBlock_nop_simulates_aligned
    regHex sim (bodyOffset block_nop_offset) fetchOffset restoredMetaInterpProg μ
    h_alive h_nop h_curAligned
    restoredMetaInterpProg_nop_body_push_at_offset
    restoredMetaInterpProg_nop_body_jump_at_offset
    h_pre

/-! ## Public summary -/

theorem assembly_restore_plan_summary :
    restoredMetaInterpProg.length = 100
    ∧ restoredMetaInterpProg[block_nop_offset]? = some YiInstr.pop
    ∧ restoredMetaInterpProg[block_setShi_offset]? = some YiInstr.pop
    ∧ restoredMetaInterpProg[block_flipYao_offset]? = some YiInstr.pop
    ∧ restoredMetaInterpProg[block_hu_offset]? = some YiInstr.pop
    ∧ restoredMetaInterpProg[block_cuo_offset]? = some YiInstr.pop
    ∧ restoredMetaInterpProg[block_zong_offset]? = some YiInstr.pop
    ∧ restoredMetaInterpProg[block_branchYaoEq_offset]? = some YiInstr.pop
    ∧ restoredMetaInterpProg[block_branchShiEq_offset]? = some YiInstr.pop
    ∧ restoredMetaInterpProg[block_jump_offset]? = some YiInstr.pop
    ∧ restoredMetaInterpProg[block_push_offset]? = some YiInstr.pop
    ∧ restoredMetaInterpProg[block_pop_offset]? = some YiInstr.pop
    ∧ restoredMetaInterpProg[haltOffset]? = some YiInstr.pop
    ∧ (∀ instr : YiInstr,
        restoredMetaInterpProg[dispatchTargetOfInstr restoredDispatchOffsets instr]? =
          some YiInstr.pop)
    ∧ (∀ regHex sim instr,
        ExecuteBlock.BlockPre regHex sim
          (dispatchTargetOfInstr restoredDispatchOffsets instr + 1)
          restoredMetaInterpProg
          ((DispatchRestore.savedCurBlockEntryState regHex sim restoredMetaInterpProg
            (dispatchTargetOfInstr restoredDispatchOffsets instr) instr).runFuel 1))
    ∧ restoredMetaInterpProg[bodyOffset block_nop_offset]? = some YiInstr.push
    ∧ restoredMetaInterpProg[bodyOffset block_nop_offset + 1]? =
        some (YiInstr.jump fetchOffset)
    ∧ (∀ regHex sim μ,
        sim.halted = false →
        sim.prog[sim.pc]? = some .nop →
        sim.cur = regDataCell regHex →
        ExecuteBlock.BlockPre regHex sim (bodyOffset block_nop_offset)
          restoredMetaInterpProg μ →
          ExecuteBlock.BlockPost regHex sim fetchOffset restoredMetaInterpProg
            (μ.runFuel 2) false) := by
  exact
    ⟨ restoredMetaInterpProg_length
    , restoredMetaInterpProg_nop_restore_at_offset
    , restoredMetaInterpProg_setShi_restore_at_offset
    , restoredMetaInterpProg_flipYao_restore_at_offset
    , restoredMetaInterpProg_hu_restore_at_offset
    , restoredMetaInterpProg_cuo_restore_at_offset
    , restoredMetaInterpProg_zong_restore_at_offset
    , restoredMetaInterpProg_branchYaoEq_restore_at_offset
    , restoredMetaInterpProg_branchShiEq_restore_at_offset
    , restoredMetaInterpProg_jump_restore_at_offset
    , restoredMetaInterpProg_push_restore_at_offset
    , restoredMetaInterpProg_pop_restore_at_offset
    , restoredMetaInterpProg_halt_restore_at_offset
    , restoredMetaInterpProg_dispatchTarget_has_restore
    , restoredMetaInterpProg_savedCur_target_yields_BlockPre
    , restoredMetaInterpProg_nop_body_push_at_offset
    , restoredMetaInterpProg_nop_body_jump_at_offset
    , restoredMetaInterpProg_execute_nop_simulates_aligned
    ⟩

end SSBX.Foundation.Wen.MetaInterp.AssemblyRestorePlan
