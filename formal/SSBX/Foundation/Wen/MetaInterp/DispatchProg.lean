/-
# DispatchProg — concrete materialization of the dispatch tree as `List YiInstr`

This file re-derives, at base-256, the universal meta-interpreter dispatch
machinery that the Cell192→R8 migration dropped.

The architecture file `MetaInterp/Dispatch.lean` already defines
`dispatchTree : DispatchOffsets → Nat → List YiInstr` along with twelve
routing theorems `dispatchTree_routes_<op>`.  Since `dispatchTree` is *itself*
a `List YiInstr`, the concrete `dispatchProg` is just a thin alias — but
having it under its own name keeps `metaInterpProg` assembly self-documenting
and matches the F.1-era universal-compose interface.

## Contents

* `dispatchProg : DispatchOffsets → Nat → List YiInstr` — Tier 1 alias
* `dispatchProg_length` — length is 16
* `dispatchProg_eq_dispatchTree` — definitional equality
* `dispatchProg_routes_<op>` — 12 routing theorems, by reduction
* `metaInterpProgSkeleton` — Tier 2 stub assembled program (halt-only)
* `metaInterpProgSkeleton_simulates_halt` — Tier 3 smoke test

## TODOs for the universal-compose follow-up

* B-followup: assemble the *full* `metaInterpProg` from
  `prologue ++ outerLoop ++ fetch ++ dispatch ++ 12 executeBlocks ++ halt`
  with concrete offsets and prove the universal-compose simulation theorem
  for an arbitrary YiInstr program.
-/
import SSBX.Foundation.Wen.MetaInterp.Dispatch

namespace SSBX.Foundation.Wen.MetaInterp.DispatchProg

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.MetaInterp
open SSBX.Foundation.Wen.MetaInterp.Dispatch

/-! ## § 1  Tier 1 — concrete `dispatchProg` -/

/-- The concrete dispatch program.  Materializes the 16-instruction dispatch
    tree as a `List YiInstr` given the entry-offset table and the base pc.

    This is a definitional alias for `dispatchTree`; it exists so that
    `metaInterpProg` assembly can refer to a dedicated name without leaking
    the `Dispatch` namespace. -/
def dispatchProg (offsets : DispatchOffsets) (dispatchBase : Nat) : List YiInstr :=
  dispatchTree offsets dispatchBase

@[simp] theorem dispatchProg_eq_dispatchTree
    (offsets : DispatchOffsets) (dispatchBase : Nat) :
    dispatchProg offsets dispatchBase = dispatchTree offsets dispatchBase := rfl

@[simp] theorem dispatchProg_length
    (offsets : DispatchOffsets) (dispatchBase : Nat) :
    (dispatchProg offsets dispatchBase).length = 16 :=
  dispatchTree_length offsets dispatchBase

/-! ## § 2  Tier 1 — twelve routing theorems for `dispatchProg`

Each `dispatchProg_routes_<op>` reduces to the matching `dispatchTree_routes_<op>`.
-/

theorem dispatchProg_routes_nop
    (offsets : DispatchOffsets) (history : List R8) :
    let μ : YiState :=
      { cur := nopTag, history := history, pc := 0
        prog := dispatchProg offsets 0, halted := false }
    let μ' := μ.runFuel 3
    μ'.pc = offsets.nop_offset ∧ μ'.cur = nopTag
    ∧ μ'.history = history ∧ μ'.halted = false :=
  dispatchTree_routes_nop offsets history

theorem dispatchProg_routes_setShi
    (offsets : DispatchOffsets) (history : List R8) :
    let μ : YiState :=
      { cur := setShiTag, history := history, pc := 0
        prog := dispatchProg offsets 0, halted := false }
    let μ' := μ.runFuel 4
    μ'.pc = offsets.setShi_dispatch_offset ∧ μ'.cur = setShiTag
    ∧ μ'.history = history ∧ μ'.halted = false :=
  dispatchTree_routes_setShi offsets history

theorem dispatchProg_routes_flipYao
    (offsets : DispatchOffsets) (history : List R8) :
    let μ : YiState :=
      { cur := flipYaoTag, history := history, pc := 0
        prog := dispatchProg offsets 0, halted := false }
    let μ' := μ.runFuel 5
    μ'.pc = offsets.flipYao_dispatch_offset ∧ μ'.cur = flipYaoTag
    ∧ μ'.history = history ∧ μ'.halted = false :=
  dispatchTree_routes_flipYao offsets history

theorem dispatchProg_routes_hu
    (offsets : DispatchOffsets) (history : List R8) :
    let μ : YiState :=
      { cur := huTag, history := history, pc := 0
        prog := dispatchProg offsets 0, halted := false }
    let μ' := μ.runFuel 6
    μ'.pc = offsets.hu_offset ∧ μ'.cur = huTag
    ∧ μ'.history = history ∧ μ'.halted = false :=
  dispatchTree_routes_hu offsets history

theorem dispatchProg_routes_cuo
    (offsets : DispatchOffsets) (history : List R8) :
    let μ : YiState :=
      { cur := cuoTag, history := history, pc := 0
        prog := dispatchProg offsets 0, halted := false }
    let μ' := μ.runFuel 4
    μ'.pc = offsets.cuo_offset ∧ μ'.cur = cuoTag
    ∧ μ'.history = history ∧ μ'.halted = false :=
  dispatchTree_routes_cuo offsets history

theorem dispatchProg_routes_zong
    (offsets : DispatchOffsets) (history : List R8) :
    let μ : YiState :=
      { cur := zongTag, history := history, pc := 0
        prog := dispatchProg offsets 0, halted := false }
    let μ' := μ.runFuel 5
    μ'.pc = offsets.zong_offset ∧ μ'.cur = zongTag
    ∧ μ'.history = history ∧ μ'.halted = false :=
  dispatchTree_routes_zong offsets history

theorem dispatchProg_routes_branchYaoEq
    (offsets : DispatchOffsets) (history : List R8) :
    let μ : YiState :=
      { cur := branchYaoEqTag, history := history, pc := 0
        prog := dispatchProg offsets 0, halted := false }
    let μ' := μ.runFuel 6
    μ'.pc = offsets.branchYaoEq_dispatch_offset ∧ μ'.cur = branchYaoEqTag
    ∧ μ'.history = history ∧ μ'.halted = false :=
  dispatchTree_routes_branchYaoEq offsets history

theorem dispatchProg_routes_branchShiEq
    (offsets : DispatchOffsets) (history : List R8) :
    let μ : YiState :=
      { cur := branchShiEqTag, history := history, pc := 0
        prog := dispatchProg offsets 0, halted := false }
    let μ' := μ.runFuel 7
    μ'.pc = offsets.branchShiEq_dispatch_offset ∧ μ'.cur = branchShiEqTag
    ∧ μ'.history = history ∧ μ'.halted = false :=
  dispatchTree_routes_branchShiEq offsets history

theorem dispatchProg_routes_jump
    (offsets : DispatchOffsets) (history : List R8) :
    let μ : YiState :=
      { cur := jumpTag, history := history, pc := 0
        prog := dispatchProg offsets 0, halted := false }
    let μ' := μ.runFuel 3
    μ'.pc = offsets.jump_offset ∧ μ'.cur = jumpTag
    ∧ μ'.history = history ∧ μ'.halted = false :=
  dispatchTree_routes_jump offsets history

theorem dispatchProg_routes_push
    (offsets : DispatchOffsets) (history : List R8) :
    let μ : YiState :=
      { cur := pushTag, history := history, pc := 0
        prog := dispatchProg offsets 0, halted := false }
    let μ' := μ.runFuel 4
    μ'.pc = offsets.push_offset ∧ μ'.cur = pushTag
    ∧ μ'.history = history ∧ μ'.halted = false :=
  dispatchTree_routes_push offsets history

theorem dispatchProg_routes_pop
    (offsets : DispatchOffsets) (history : List R8) :
    let μ : YiState :=
      { cur := popTag, history := history, pc := 0
        prog := dispatchProg offsets 0, halted := false }
    let μ' := μ.runFuel 5
    μ'.pc = offsets.pop_offset ∧ μ'.cur = popTag
    ∧ μ'.history = history ∧ μ'.halted = false :=
  dispatchTree_routes_pop offsets history

theorem dispatchProg_routes_halt
    (offsets : DispatchOffsets) (history : List R8) :
    let μ : YiState :=
      { cur := haltTag, history := history, pc := 0
        prog := dispatchProg offsets 0, halted := false }
    let μ' := μ.runFuel 6
    μ'.pc = offsets.halt_offset ∧ μ'.cur = haltTag
    ∧ μ'.history = history ∧ μ'.halted = false :=
  dispatchTree_routes_halt offsets history

/-! ## § 3  Tier 2 — `metaInterpProgSkeleton` and offsets

A minimal assembled meta-interpreter program: just a `dispatchProg` placed at
pc=0 with halt-only offsets, followed by a terminating `halt`.  This is not
the *full* meta-interpreter (it has no prologue, no fetch, no executeBlocks),
but it exercises the assembly path and proves a length-shape theorem.

The full assembly is left as TODO(B-followup).
-/

/-- All-halt offsets table: every dispatch arm routes to the trailing halt
    instruction at pc = 16. -/
def haltOnlyOffsets : DispatchOffsets where
  nop_offset := 16
  hu_offset := 16
  cuo_offset := 16
  zong_offset := 16
  push_offset := 16
  pop_offset := 16
  halt_offset := 16
  jump_offset := 16
  setShi_dispatch_offset := 16
  flipYao_dispatch_offset := 16
  branchYaoEq_dispatch_offset := 16
  branchShiEq_dispatch_offset := 16

/-- Tier 2 skeleton: `dispatchProg` at pc=0 followed by a single `halt`.
    Length = 17. -/
def metaInterpProgSkeleton : List YiInstr :=
  dispatchProg haltOnlyOffsets 0 ++ [YiInstr.halt]

@[simp] theorem metaInterpProgSkeleton_length :
    metaInterpProgSkeleton.length = 17 := by
  unfold metaInterpProgSkeleton dispatchProg
  simp [dispatchTree_length]

/-! ## § 4  Tier 3 — smoke-test simulation theorem

Starting from a state whose `cur` is the `haltTag` (k=11), the skeleton
program reaches a halted state in 7 fuel steps (6 for dispatch routing to
`halt_offset = 16`, plus 1 to execute the trailing `halt`).
-/

/-- **Tier 3 smoke test.**  The skeleton correctly routes a `haltTag` to the
    terminating `halt` and halts. -/
theorem metaInterpProgSkeleton_simulates_halt
    (history : List R8) :
    let μ : YiState :=
      { cur := haltTag, history := history, pc := 0
        prog := metaInterpProgSkeleton, halted := false }
    let μ' := μ.runFuel 7
    μ'.halted = true ∧ μ'.pc = 16 := by
  -- Step through 6 dispatch ticks landing at pc = halt_offset = 16,
  -- then the 7th tick executes `YiInstr.halt`.
  refine ⟨?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
          Shi.dao, Shi.ji, Shi.jin, Shi.wei,
          metaInterpProgSkeleton, dispatchProg, dispatchTree, dispatchShi,
          haltOnlyOffsets, haltTag, cellFromIdx,
          Hexagram.yaoAt, Hexagram.fromIdx, Yao.fromIdx,
          SSBX.Foundation.Bagua.R8.Shi.fromIdx,
          Yao.yang, Yao.yin,
          SSBX.Foundation.Atlas.Yi.Yao.yang,
          SSBX.Foundation.Atlas.Yi.Yao.yin]

end SSBX.Foundation.Wen.MetaInterp.DispatchProg
