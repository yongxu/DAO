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
  withRestore (executeBlock_nop (bodyOffset block_nop_offset) fetchOffset)

def restoredBlock_setShi : List YiInstr :=
  withRestore (executeBlock_setShi Shi.dao fetchOffset)

def restoredBlock_flipYao : List YiInstr :=
  withRestore (executeBlock_flipYao 0 fetchOffset)

def restoredBlock_hu : List YiInstr :=
  withRestore (executeBlock_hu (bodyOffset block_hu_offset) fetchOffset)

def restoredBlock_cuo : List YiInstr :=
  withRestore (executeBlock_cuo (bodyOffset block_cuo_offset) fetchOffset)

def restoredBlock_zong : List YiInstr :=
  withRestore (executeBlock_zong fetchOffset)

def restoredBlock_branchYaoEq : List YiInstr :=
  withRestore (executeBlock_branchYaoEq 0 0 0 fetchOffset)

def restoredBlock_branchShiEq : List YiInstr :=
  withRestore (executeBlock_branchShiEq Shi.dao 0 fetchOffset)

def restoredBlock_jump : List YiInstr :=
  withRestore (executeBlock_jump 0 fetchOffset)

def restoredBlock_push : List YiInstr :=
  withRestore (executeBlock_push fetchOffset)

def restoredBlock_pop : List YiInstr :=
  withRestore (executeBlock_pop fetchOffset)

def restoredBlock_halt : List YiInstr :=
  withRestore (executeBlock_halt (bodyOffset block_pop_offset) fetchOffset)

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
    ∧ restoredMetaInterpProg[haltOffset]? = some YiInstr.pop := by
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
    ⟩

end SSBX.Foundation.Wen.MetaInterp.AssemblyRestorePlan
