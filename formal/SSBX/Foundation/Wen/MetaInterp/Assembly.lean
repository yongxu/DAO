/-
# Assembly — concrete `metaInterpProg` (Phase 2.3 redux, base-256)

This file stitches the parameterized building blocks into a SINGLE concrete
`metaInterpProg : List YiInstr` with definite length.

## Layout

```
pc range   region                                length
---------  ------------------------------------  ------
0..4       prologueProg                          5
5          outerLoopEntry fetchOffset            1
6..19      fetchProgWithPeel dispatchOffset haltOffset 14
20..35     dispatchProg offsets dispatchOffset   16
36..37     executeBlock_nop                      2
38..39     executeBlock_setShi  Shi.dao    [B]   2
40..41     executeBlock_flipYao 0          [B]   2
42..43     executeBlock_hu                       2
44..45     executeBlock_cuo                      2
46..47     executeBlock_zong                     2
48..57     executeBlock_branchYaoEq 0 0 0  [B]   10
58..67     executeBlock_branchShiEq Shi.dao 0 [B] 10
68..76     executeBlock_jump 0             [B]   9
77..81     executeBlock_push                     5
82..86     executeBlock_pop                      5
87         executeBlock_halt                     1
                                              ----
                                          total 88
```

`fetchOffset = 6`, `fetchHaltDetectOffset = 9`, `dispatchOffset = 20`,
`haltOffset = 87`.

## Strategy B caveats

For Tier A scope we pick fixed default parameter values for the parameterized
opcodes (marked `[B]` above):

  * `setShi`  → `Shi.dao`
  * `flipYao` → `0` (Fin 6)
  * `branchYaoEq` → `0 0 0`
  * `branchShiEq` → `Shi.dao 0`
  * `jump` → `0`

The assembled program therefore always rewrites simulator `Shi` to `dao`,
flips yao position 0, branches on `(yao 0 = yao 0)` (vacuously true), branches
on `Shi.dao = ...`, and unconditionally jumps to sim-pc 0.  This is **NOT** a
universal interpreter — to make it one, each parameterized arm must be replaced
with a sub-dispatch tree (see `SubDispatch_BranchShiEq`/`SubDispatch_BranchYaoEq`)
that reads the actual parameter cell from META.history and routes to one of N
specialized blocks.

That promotion is the next ticket (B.T4.G universal-compose); see TODOs below.
-/
import SSBX.Foundation.Wen.MetaInterp.PrologueProg
import SSBX.Foundation.Wen.MetaInterp.OuterLoop
import SSBX.Foundation.Wen.MetaInterp.FetchProg
import SSBX.Foundation.Wen.MetaInterp.DispatchProg
import SSBX.Foundation.Wen.MetaInterp.ExecuteBlocks
import SSBX.Foundation.Wen.MetaInterp.ExecuteBlocksHard

namespace SSBX.Foundation.Wen.MetaInterp.Assembly

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Bagua.KleeneInternal
open SSBX.Foundation.Wen.MetaInterp
open SSBX.Foundation.Wen.MetaInterp.Dispatch
open SSBX.Foundation.Wen.MetaInterp.ExecuteBlocks.Aggregate
open SSBX.Foundation.Wen.MetaInterp.ExecuteBlocksHard

/-! ## § 1  Concrete offsets -/

def prologueOffset    : Nat := 0
def outerLoopOffset   : Nat := 5
def fetchOffset       : Nat := 6
def fetchHaltDetectOffset : Nat := fetchOffset + 3
def dispatchOffset    : Nat := 20
def block_nop_offset         : Nat := 36
def block_setShi_offset      : Nat := 38
def block_flipYao_offset     : Nat := 40
def block_hu_offset          : Nat := 42
def block_cuo_offset         : Nat := 44
def block_zong_offset        : Nat := 46
def block_branchYaoEq_offset : Nat := 48
def block_branchShiEq_offset : Nat := 58
def block_jump_offset        : Nat := 68
def block_push_offset        : Nat := 77
def block_pop_offset         : Nat := 82
def haltOffset               : Nat := 87

/-! ## § 2  DispatchOffsets table -/

def metaInterpDispatchOffsets : DispatchOffsets where
  nop_offset                  := block_nop_offset
  hu_offset                   := block_hu_offset
  cuo_offset                  := block_cuo_offset
  zong_offset                 := block_zong_offset
  push_offset                 := block_push_offset
  pop_offset                  := block_pop_offset
  halt_offset                 := haltOffset
  jump_offset                 := block_jump_offset
  setShi_dispatch_offset      := block_setShi_offset
  flipYao_dispatch_offset     := block_flipYao_offset
  branchYaoEq_dispatch_offset := block_branchYaoEq_offset
  branchShiEq_dispatch_offset := block_branchShiEq_offset

/-! ## § 3  The concrete `metaInterpProg`

Strategy B defaults (see file header):
  setShi Shi.dao, flipYao 0, branchYaoEq 0 0 0, branchShiEq Shi.dao 0, jump 0.
-/

def metaInterpProg : List YiInstr :=
  PrologueProg.prologueProg
  ++ OuterLoop.outerLoopEntry fetchOffset
  ++ FetchProg.fetchProgWithPeel fetchOffset dispatchOffset haltOffset
  ++ DispatchProg.dispatchProg metaInterpDispatchOffsets dispatchOffset
  ++ executeBlock_nop block_nop_offset fetchOffset
  ++ executeBlock_setShi Shi.dao fetchOffset
  ++ executeBlock_flipYao 0 fetchOffset
  ++ executeBlock_hu block_hu_offset fetchOffset
  ++ executeBlock_cuo block_cuo_offset fetchOffset
  ++ executeBlock_zong fetchOffset
  ++ executeBlock_branchYaoEq 0 0 0 fetchOffset
  ++ executeBlock_branchShiEq Shi.dao 0 fetchOffset
  ++ executeBlock_jump 0 fetchOffset
  ++ executeBlock_push fetchOffset
  ++ executeBlock_pop fetchOffset
  ++ executeBlock_halt block_pop_offset fetchOffset

/-! ## § 4  Tier A — length lemma -/

theorem metaInterpProg_length : metaInterpProg.length = 88 := by
  -- All component lists are concrete; length reduces by `rfl` modulo
  -- the placeholder bodies built with `List.replicate`.  We unfold
  -- everything and let `simp` close the numeric goal.
  set_option maxHeartbeats 800000 in
  simp only [metaInterpProg, List.length_append,
        PrologueProg.prologueProg_length,
        OuterLoop.outerLoopEntry_length,
        FetchProg.fetchProgWithPeel_length_concrete,
        DispatchProg.dispatchProg_length,
        executeBlock_nop_length,
        executeBlock_setShi_length,
        executeBlock_flipYao_length,
        executeBlock_hu_length,
        executeBlock_cuo_length,
        executeBlock_zong_length,
        executeBlock_branchYaoEq_length,
        executeBlock_branchShiEq_length,
        executeBlock_jump_length,
        executeBlock_push_length,
        executeBlock_pop_length,
        executeBlock_halt_length]

/-! ## § 5  Tier B — fetch reachable from prologue start

After running `metaInterpProg` for `prologueProg.length + 1 = 6` fuel ticks
from the canonical start state (`pc = 0`, `cur` = prologue's expected entry,
`prog = metaInterpProg`), the META machine sits at `pc = fetchOffset`.

For Tier B scope we prove a *structural* version: from a state with
`pc = outerLoopOffset` and the outer-loop entry instruction available at
that index, one fuel tick advances pc to `fetchOffset`.  This is the
composition the prologue→fetch routing relies on; the prologue's own
five-step lift is `MetaInterp.afterPrologue_pc`. -/

theorem metaInterpProg_outerLoop_at_offset :
    metaInterpProg[outerLoopOffset]? =
      some (YiInstr.jump fetchOffset) := by
  -- outerLoopOffset = 5; prologue has length 5, so this is the first
  -- instruction of the outerLoopEntry block.
  rfl

/-- The offset-aware fetch block with pc-counter peel is spliced into
    `metaInterpProg` starting at `fetchOffset`. -/
theorem metaInterpProg_fetchProgWithPeel_at_offset :
    ∀ i (_hi : i < FetchProg.fetchProg_totalLen + 3),
      metaInterpProg[fetchOffset + i]? =
        (FetchProg.fetchProgWithPeel fetchOffset dispatchOffset haltOffset)[i]? := by
  intro i hi
  unfold FetchProg.fetchProg_totalLen FetchProg.walkerLen at hi
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

/-- The halt-detection / placeholder-walker part of fetch begins immediately
    after the pc-counter peel, at `fetchHaltDetectOffset`.  This is the
    segment hypothesis required by the existing `FetchProg.fetchProg`
    route theorems. -/
theorem metaInterpProg_fetchProg_at_offset :
    ∀ i (_hi : i < FetchProg.fetchProg_totalLen),
      metaInterpProg[fetchHaltDetectOffset + i]? =
        (FetchProg.fetchProg dispatchOffset haltOffset)[i]? := by
  intro i hi
  unfold FetchProg.fetchProg_totalLen FetchProg.walkerLen at hi
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

/-- The concrete dispatch tree is spliced into `metaInterpProg` starting at
    `dispatchOffset`.  This is the segment witness needed before standalone
    dispatch routing lemmas can be lifted to absolute pc execution. -/
theorem metaInterpProg_dispatchProg_at_offset :
    ∀ i (_hi : i < 16),
      metaInterpProg[dispatchOffset + i]? =
        (DispatchProg.dispatchProg metaInterpDispatchOffsets dispatchOffset)[i]? := by
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

/-- Tier B routing theorem: from a META state at `pc = outerLoopOffset`
    running `metaInterpProg`, one fuel step lands at `pc = fetchOffset`. -/
theorem metaInterpProg_routes_outerLoop_to_fetch
    (cur : R8) (history : List R8) :
    let μ : YiState :=
      { cur := cur
        history := history
        pc := outerLoopOffset
        prog := metaInterpProg
        halted := false }
    let μ' := μ.runFuel 1
    μ'.pc = fetchOffset := by
  -- Apply the outerLoopEntry_step composition lemma using the structural
  -- hypothesis above.
  have h_entry :
      OuterLoop.MetaProgHasOuterLoopEntryAt outerLoopOffset fetchOffset
        metaInterpProg :=
    metaInterpProg_outerLoop_at_offset
  -- runFuel 1 = step (since halted = false)
  show ((_ : YiState).runFuel 1).pc = fetchOffset
  rw [show (1 : Nat) = 0 + 1 from rfl]
  -- Direct: unfold runFuel and apply outerLoopEntry_step.
  have := OuterLoop.outerLoopEntry_step
              (offset := outerLoopOffset)
              (fetchOffset := fetchOffset)
              (metaProg := metaInterpProg)
              h_entry
              { cur := cur, history := history, pc := outerLoopOffset
                prog := metaInterpProg, halted := false }
              rfl rfl rfl
  simp [YiState.runFuel, this]

/-- The first three instructions of the concrete fetch region are the empty
    counted-loop prefix that peels the encoded simulated pc-counter. -/
theorem metaInterpProg_fetchPeel_loop_at_offset :
    MetaProgHasEmptyCountedLoopAt fetchOffset metaInterpProg := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-- Immediately after the pc-counter peel prefix, the next concrete fetch
    instruction pops the halted flag into `META.cur`. -/
theorem metaInterpProg_fetchPeel_pop_halted_flag_at_offset :
    metaInterpProg[fetchOffset + 3]? = some YiInstr.pop := by
  rfl

/-- Assembly-specialized exact pc-counter peel hand-off.  Starting at the
    concrete fetch-loop entry, the counted-loop prefix consumes the pc-counter
    and the following pop moves the halted flag into `META.cur`, reaching the
    shifted halt-detection state. -/
theorem metaInterpProg_fetch_peel_to_haltDetect_at_fuel
    (regHex : Hexagram) (sim : YiState) :
    (Fetch.fetchEntryState regHex sim metaInterpProg fetchOffset).runFuel
        (3 * sim.pc + 3) =
      FetchProg.fetchProgHaltDetectEntry regHex sim metaInterpProg
        fetchHaltDetectOffset sim.halted := by
  simpa [fetchHaltDetectOffset] using
    FetchProg.fetchEntryState_pc_counter_peel_then_haltDetectEntry_shifted
      regHex sim metaInterpProg fetchOffset
      metaInterpProg_fetchPeel_loop_at_offset
      metaInterpProg_fetchPeel_pop_halted_flag_at_offset

/-- Exact assembly-specialized halted fetch route from the real concrete
    fetch-loop entry.  This composes the pc-counter peel prefix, the
    halted-flag pop, and the halt-detection branch. -/
theorem metaInterpProg_fetch_routes_halted_exact
    (regHex : Hexagram) (sim : YiState)
    (h_halted : sim.halted = true) :
    ((Fetch.fetchEntryState regHex sim metaInterpProg fetchOffset).runFuel
      (3 * sim.pc + 4)).pc = haltOffset := by
  have h_peel :
      (Fetch.fetchEntryState regHex sim metaInterpProg fetchOffset).runFuel
          (3 * sim.pc + 3) =
        FetchProg.fetchProgHaltDetectEntry regHex sim metaInterpProg
          fetchHaltDetectOffset true := by
    simpa [h_halted] using
      metaInterpProg_fetch_peel_to_haltDetect_at_fuel regHex sim
  have h_fuel : 3 * sim.pc + 4 = (3 * sim.pc + 3) + 1 := by omega
  rw [h_fuel, SSBX.Foundation.Bagua.GodelLi.runFuel_succ_right, h_peel]
  have h_branchAt : metaInterpProg[fetchHaltDetectOffset + 1]? =
      some (YiInstr.branchShiEq Shi.ji haltOffset) := by
    rfl
  exact FetchProg.fetchProg_branch_halted_true regHex sim metaInterpProg
    fetchHaltDetectOffset dispatchOffset haltOffset h_branchAt

/-- Assembly-specialized halted fetch route for the inner halt-detection
    segment, with explicit peel fuel supplied by callers. -/
theorem metaInterpProg_fetch_routes_halted_at_fuel
    (regHex : Hexagram) (sim : YiState)
    (h_halted : sim.halted = true)
    (M0 : Nat)
    (h_peel :
      (Fetch.fetchEntryState regHex sim metaInterpProg fetchHaltDetectOffset).runFuel M0 =
        FetchProg.fetchProgHaltDetectEntry regHex sim metaInterpProg
          fetchHaltDetectOffset true) :
    ((Fetch.fetchEntryState regHex sim metaInterpProg fetchHaltDetectOffset).runFuel
      (M0 + 1)).pc = haltOffset := by
  exact FetchProg.fetchProg_routes_halted_at_fuel regHex sim metaInterpProg
    fetchHaltDetectOffset dispatchOffset haltOffset metaInterpProg_fetchProg_at_offset
    h_halted M0 h_peel

/-- Assembly-specialized running fetch route for the inner halt-detection
    segment, with explicit peel fuel supplied by callers. -/
theorem metaInterpProg_fetch_routes_running_to_dispatch_at_fuel
    (regHex : Hexagram) (sim : YiState)
    (h_running : sim.halted = false)
    (h_pcInBounds : sim.pc < sim.prog.length)
    (M0 : Nat)
    (h_peel :
      (Fetch.fetchEntryState regHex sim metaInterpProg fetchHaltDetectOffset).runFuel M0 =
        FetchProg.fetchProgHaltDetectEntry regHex sim metaInterpProg
          fetchHaltDetectOffset false) :
    ((Fetch.fetchEntryState regHex sim metaInterpProg fetchHaltDetectOffset).runFuel
      (M0 + 1 + (FetchProg.walkerLen + 1))).pc = dispatchOffset := by
  exact FetchProg.fetchProg_routes_running_to_dispatch_at_fuel regHex sim metaInterpProg
    fetchHaltDetectOffset dispatchOffset haltOffset metaInterpProg_fetchProg_at_offset
    h_running h_pcInBounds M0 h_peel

/-! ## § 5.5  Dispatch absolute-pc route lift -/

/-- Assembly-specialized dispatch route for the nop tag. -/
theorem metaInterpProg_dispatch_routes_nop_at_fuel
    (history : List R8) :
    let μ : YiState :=
      { cur := Dispatch.nopTag
        history := history
        pc := dispatchOffset
        prog := metaInterpProg
        halted := false }
    let μ' := μ.runFuel 3
    μ'.pc = block_nop_offset
      ∧ μ'.cur = Dispatch.nopTag
      ∧ μ'.history = history
      ∧ μ'.prog = metaInterpProg
      ∧ μ'.halted = false := by
  simpa [metaInterpDispatchOffsets] using
    Dispatch.dispatchTree_routes_nop_at_segment
      metaInterpDispatchOffsets dispatchOffset metaInterpProg history
      (fun i hi => by
        simpa [DispatchProg.dispatchProg] using
          metaInterpProg_dispatchProg_at_offset i hi)

/-- Assembly-specialized dispatch route for the setShi tag. -/
theorem metaInterpProg_dispatch_routes_setShi_at_fuel
    (history : List R8) :
    let μ : YiState :=
      { cur := Dispatch.setShiTag
        history := history
        pc := dispatchOffset
        prog := metaInterpProg
        halted := false }
    let μ' := μ.runFuel 4
    μ'.pc = block_setShi_offset
      ∧ μ'.cur = Dispatch.setShiTag
      ∧ μ'.history = history
      ∧ μ'.prog = metaInterpProg
      ∧ μ'.halted = false := by
  simpa [metaInterpDispatchOffsets] using
    Dispatch.dispatchTree_routes_setShi_at_segment
      metaInterpDispatchOffsets dispatchOffset metaInterpProg history
      (fun i hi => by
        simpa [DispatchProg.dispatchProg] using
          metaInterpProg_dispatchProg_at_offset i hi)

/-- Assembly-specialized dispatch route for the flipYao tag. -/
theorem metaInterpProg_dispatch_routes_flipYao_at_fuel
    (history : List R8) :
    let μ : YiState :=
      { cur := Dispatch.flipYaoTag
        history := history
        pc := dispatchOffset
        prog := metaInterpProg
        halted := false }
    let μ' := μ.runFuel 5
    μ'.pc = block_flipYao_offset
      ∧ μ'.cur = Dispatch.flipYaoTag
      ∧ μ'.history = history
      ∧ μ'.prog = metaInterpProg
      ∧ μ'.halted = false := by
  simpa [metaInterpDispatchOffsets] using
    Dispatch.dispatchTree_routes_flipYao_at_segment
      metaInterpDispatchOffsets dispatchOffset metaInterpProg history
      (fun i hi => by
        simpa [DispatchProg.dispatchProg] using
          metaInterpProg_dispatchProg_at_offset i hi)

/-- Assembly-specialized dispatch route for the interlace tag. -/
theorem metaInterpProg_dispatch_routes_hu_at_fuel
    (history : List R8) :
    let μ : YiState :=
      { cur := Dispatch.huTag
        history := history
        pc := dispatchOffset
        prog := metaInterpProg
        halted := false }
    let μ' := μ.runFuel 6
    μ'.pc = block_hu_offset
      ∧ μ'.cur = Dispatch.huTag
      ∧ μ'.history = history
      ∧ μ'.prog = metaInterpProg
      ∧ μ'.halted = false := by
  simpa [metaInterpDispatchOffsets] using
    Dispatch.dispatchTree_routes_hu_at_segment
      metaInterpDispatchOffsets dispatchOffset metaInterpProg history
      (fun i hi => by
        simpa [DispatchProg.dispatchProg] using
          metaInterpProg_dispatchProg_at_offset i hi)

/-- Assembly-specialized dispatch route for the complement tag. -/
theorem metaInterpProg_dispatch_routes_cuo_at_fuel
    (history : List R8) :
    let μ : YiState :=
      { cur := Dispatch.cuoTag
        history := history
        pc := dispatchOffset
        prog := metaInterpProg
        halted := false }
    let μ' := μ.runFuel 4
    μ'.pc = block_cuo_offset
      ∧ μ'.cur = Dispatch.cuoTag
      ∧ μ'.history = history
      ∧ μ'.prog = metaInterpProg
      ∧ μ'.halted = false := by
  simpa [metaInterpDispatchOffsets] using
    Dispatch.dispatchTree_routes_cuo_at_segment
      metaInterpDispatchOffsets dispatchOffset metaInterpProg history
      (fun i hi => by
        simpa [DispatchProg.dispatchProg] using
          metaInterpProg_dispatchProg_at_offset i hi)

/-- Assembly-specialized dispatch route for the reverse tag. -/
theorem metaInterpProg_dispatch_routes_zong_at_fuel
    (history : List R8) :
    let μ : YiState :=
      { cur := Dispatch.zongTag
        history := history
        pc := dispatchOffset
        prog := metaInterpProg
        halted := false }
    let μ' := μ.runFuel 5
    μ'.pc = block_zong_offset
      ∧ μ'.cur = Dispatch.zongTag
      ∧ μ'.history = history
      ∧ μ'.prog = metaInterpProg
      ∧ μ'.halted = false := by
  simpa [metaInterpDispatchOffsets] using
    Dispatch.dispatchTree_routes_zong_at_segment
      metaInterpDispatchOffsets dispatchOffset metaInterpProg history
      (fun i hi => by
        simpa [DispatchProg.dispatchProg] using
          metaInterpProg_dispatchProg_at_offset i hi)

/-- Assembly-specialized dispatch route for the branchYaoEq tag. -/
theorem metaInterpProg_dispatch_routes_branchYaoEq_at_fuel
    (history : List R8) :
    let μ : YiState :=
      { cur := Dispatch.branchYaoEqTag
        history := history
        pc := dispatchOffset
        prog := metaInterpProg
        halted := false }
    let μ' := μ.runFuel 6
    μ'.pc = block_branchYaoEq_offset
      ∧ μ'.cur = Dispatch.branchYaoEqTag
      ∧ μ'.history = history
      ∧ μ'.prog = metaInterpProg
      ∧ μ'.halted = false := by
  simpa [metaInterpDispatchOffsets] using
    Dispatch.dispatchTree_routes_branchYaoEq_at_segment
      metaInterpDispatchOffsets dispatchOffset metaInterpProg history
      (fun i hi => by
        simpa [DispatchProg.dispatchProg] using
          metaInterpProg_dispatchProg_at_offset i hi)

/-- Assembly-specialized dispatch route for the branchShiEq tag. -/
theorem metaInterpProg_dispatch_routes_branchShiEq_at_fuel
    (history : List R8) :
    let μ : YiState :=
      { cur := Dispatch.branchShiEqTag
        history := history
        pc := dispatchOffset
        prog := metaInterpProg
        halted := false }
    let μ' := μ.runFuel 7
    μ'.pc = block_branchShiEq_offset
      ∧ μ'.cur = Dispatch.branchShiEqTag
      ∧ μ'.history = history
      ∧ μ'.prog = metaInterpProg
      ∧ μ'.halted = false := by
  simpa [metaInterpDispatchOffsets] using
    Dispatch.dispatchTree_routes_branchShiEq_at_segment
      metaInterpDispatchOffsets dispatchOffset metaInterpProg history
      (fun i hi => by
        simpa [DispatchProg.dispatchProg] using
          metaInterpProg_dispatchProg_at_offset i hi)

/-- Assembly-specialized dispatch route for the jump tag. -/
theorem metaInterpProg_dispatch_routes_jump_at_fuel
    (history : List R8) :
    let μ : YiState :=
      { cur := Dispatch.jumpTag
        history := history
        pc := dispatchOffset
        prog := metaInterpProg
        halted := false }
    let μ' := μ.runFuel 3
    μ'.pc = block_jump_offset
      ∧ μ'.cur = Dispatch.jumpTag
      ∧ μ'.history = history
      ∧ μ'.prog = metaInterpProg
      ∧ μ'.halted = false := by
  simpa [metaInterpDispatchOffsets] using
    Dispatch.dispatchTree_routes_jump_at_segment
      metaInterpDispatchOffsets dispatchOffset metaInterpProg history
      (fun i hi => by
        simpa [DispatchProg.dispatchProg] using
          metaInterpProg_dispatchProg_at_offset i hi)

/-- Assembly-specialized dispatch route for the push tag. -/
theorem metaInterpProg_dispatch_routes_push_at_fuel
    (history : List R8) :
    let μ : YiState :=
      { cur := Dispatch.pushTag
        history := history
        pc := dispatchOffset
        prog := metaInterpProg
        halted := false }
    let μ' := μ.runFuel 4
    μ'.pc = block_push_offset
      ∧ μ'.cur = Dispatch.pushTag
      ∧ μ'.history = history
      ∧ μ'.prog = metaInterpProg
      ∧ μ'.halted = false := by
  simpa [metaInterpDispatchOffsets] using
    Dispatch.dispatchTree_routes_push_at_segment
      metaInterpDispatchOffsets dispatchOffset metaInterpProg history
      (fun i hi => by
        simpa [DispatchProg.dispatchProg] using
          metaInterpProg_dispatchProg_at_offset i hi)

/-- Assembly-specialized dispatch route for the pop tag. -/
theorem metaInterpProg_dispatch_routes_pop_at_fuel
    (history : List R8) :
    let μ : YiState :=
      { cur := Dispatch.popTag
        history := history
        pc := dispatchOffset
        prog := metaInterpProg
        halted := false }
    let μ' := μ.runFuel 5
    μ'.pc = block_pop_offset
      ∧ μ'.cur = Dispatch.popTag
      ∧ μ'.history = history
      ∧ μ'.prog = metaInterpProg
      ∧ μ'.halted = false := by
  simpa [metaInterpDispatchOffsets] using
    Dispatch.dispatchTree_routes_pop_at_segment
      metaInterpDispatchOffsets dispatchOffset metaInterpProg history
      (fun i hi => by
        simpa [DispatchProg.dispatchProg] using
          metaInterpProg_dispatchProg_at_offset i hi)

/-- Assembly-specialized dispatch route for the halt tag.  This is the first
    absolute-pc lift of a standalone dispatch theorem: starting at the dispatch
    segment inside `metaInterpProg`, the halt opcode tag routes to the halt
    block in six fuel ticks. -/
theorem metaInterpProg_dispatch_routes_halt_at_fuel
    (history : List R8) :
    let μ : YiState :=
      { cur := Dispatch.haltTag
        history := history
        pc := dispatchOffset
        prog := metaInterpProg
        halted := false }
    let μ' := μ.runFuel 6
    μ'.pc = haltOffset
      ∧ μ'.cur = Dispatch.haltTag
      ∧ μ'.history = history
      ∧ μ'.prog = metaInterpProg
      ∧ μ'.halted = false := by
  exact Dispatch.dispatchTree_routes_halt_at_segment
    metaInterpDispatchOffsets dispatchOffset metaInterpProg history
    (fun i hi => by
      simpa [DispatchProg.dispatchProg] using
        metaInterpProg_dispatchProg_at_offset i hi)

/-- One more fuel tick after `metaInterpProg_dispatch_routes_halt_at_fuel`
    executes the concrete halt instruction at `haltOffset`.  This is still a
    route/VM smoke witness, not a full semantic simulation theorem. -/
theorem metaInterpProg_dispatch_halt_executes_halt
    (history : List R8) :
    let μ : YiState :=
      { cur := Dispatch.haltTag
        history := history
        pc := dispatchOffset
        prog := metaInterpProg
        halted := false }
    let μ' := μ.runFuel 7
    μ'.pc = haltOffset
      ∧ μ'.cur = Dispatch.haltTag
      ∧ μ'.history = history
      ∧ μ'.prog = metaInterpProg
      ∧ μ'.halted = true := by
  let μ : YiState :=
      { cur := Dispatch.haltTag
        history := history
        pc := dispatchOffset
        prog := metaInterpProg
        halted := false }
  let μ6 := μ.runFuel 6
  have hroute := metaInterpProg_dispatch_routes_halt_at_fuel history
  change (μ.runFuel 7).pc = haltOffset
      ∧ (μ.runFuel 7).cur = Dispatch.haltTag
      ∧ (μ.runFuel 7).history = history
      ∧ (μ.runFuel 7).prog = metaInterpProg
      ∧ (μ.runFuel 7).halted = true
  have hpc : μ6.pc = haltOffset := hroute.1
  have hcur : μ6.cur = Dispatch.haltTag := hroute.2.1
  have hhist : μ6.history = history := hroute.2.2.1
  have hprog : μ6.prog = metaInterpProg := hroute.2.2.2.1
  have hhalt : μ6.halted = false := hroute.2.2.2.2
  have h_lookup : μ6.prog[μ6.pc]? = some YiInstr.halt := by
    rw [hprog, hpc]
    rfl
  have hstep : μ6.step = { μ6 with halted := true } := by
    unfold YiState.step
    rw [hhalt]
    simp [h_lookup, YiState.execute]
  have hrun7 : μ.runFuel 7 = { μ6 with halted := true } := by
    rw [show (7 : Nat) = 6 + 1 from rfl,
      SSBX.Foundation.Bagua.GodelLi.runFuel_succ_right]
    exact hstep
  rw [hrun7]
  simp [hpc, hcur, hhist, hprog]

/-! ## § 6  Tier C — single-opcode end-to-end smoke

Stretch goal.  Constructing a fully-encoded META start state for a
non-trivial sim program would require invoking `RunWith` and threading
`encMetaHistory` through 6+14+16+1+1 ≈ 38 fuel ticks; that's beyond
this slot's scope (4-sorry budget).  We record the obligation as a
TODO theorem so callers can target it. -/

/-- **Tier C (structural — Strategy 3 fallback)**: the assembled
    `metaInterpProg` contains the `halt` block at `haltOffset` and
    the dispatch table routes the halt opcode there.  This is the
    structural precondition for the (still-deferred) full semantic
    smoke theorem `metaInterpProg_simulates_one_halt_SEMANTIC`.

    What was originally required (and still TODO):
      starting from `RunWith h metaInterpProg (encProg [YiInstr.halt])`,
      after enough fuel ticks the META machine halts.  Discharging
      that needs the prologue contract, the outer-loop step, the
      fetch decode/restore contract, dispatch routing for the `halt`
      arm, and the `executeBlock_halt` local effect.  We record here
      the structural witness only. -/
theorem metaInterpProg_simulates_one_halt :
    metaInterpProg[haltOffset]? = some YiInstr.halt
      ∧ metaInterpDispatchOffsets.halt_offset = haltOffset := by
  refine ⟨?_, rfl⟩
  -- haltOffset = 87; the executeBlock_halt block at positions 87..87
  -- is the singleton list `[YiInstr.halt]`.
  rfl

/-- Base-256 assembly summary: the concrete meta-interpreter program has fixed
    shape, enters fetch through the outer-loop jump, and contains the halt arm
    required by the structural smoke theorem.

    This does not claim the full universal semantic theorem; parameterized
    sub-dispatch and arbitrary-program simulation remain separate obligations. -/
theorem metaInterpProg_base256_structural_summary :
    metaInterpProg.length = 88
      ∧ metaInterpProg[outerLoopOffset]? = some (YiInstr.jump fetchOffset)
      ∧ (∀ i (_hi : i < FetchProg.fetchProg_totalLen + 3),
          metaInterpProg[fetchOffset + i]? =
            (FetchProg.fetchProgWithPeel fetchOffset dispatchOffset haltOffset)[i]?)
      ∧ (∀ i (_hi : i < FetchProg.fetchProg_totalLen),
          metaInterpProg[fetchHaltDetectOffset + i]? =
            (FetchProg.fetchProg dispatchOffset haltOffset)[i]?)
      ∧ (∀ i (_hi : i < 16),
          metaInterpProg[dispatchOffset + i]? =
            (DispatchProg.dispatchProg metaInterpDispatchOffsets dispatchOffset)[i]?)
      ∧ metaInterpProg[haltOffset]? = some YiInstr.halt
      ∧ metaInterpDispatchOffsets.halt_offset = haltOffset := by
  exact ⟨metaInterpProg_length,
    metaInterpProg_outerLoop_at_offset,
    metaInterpProg_fetchProgWithPeel_at_offset,
    metaInterpProg_fetchProg_at_offset,
    metaInterpProg_dispatchProg_at_offset,
    metaInterpProg_simulates_one_halt.1,
    metaInterpProg_simulates_one_halt.2⟩

end SSBX.Foundation.Wen.MetaInterp.Assembly
