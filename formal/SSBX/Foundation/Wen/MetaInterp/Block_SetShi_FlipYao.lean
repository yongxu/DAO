/-
# Block_SetShi_FlipYao — executeBlocks for `setShi sh` and `flipYao i`

These two opcodes carry a runtime parameter — `sh : Shi` for `setShi`,
`i : Fin 6` for `flipYao` — and behave as direct cur-transforms:

  setShi sh : cur := (cur.1, sh)         ; pc := pc + 1
  flipYao i : cur := (cur.1.flipPos i, cur.2) ; pc := pc + 1

`encMetaHistory` does NOT record `cur` (the loop invariant maintains
`META.cur = sim.cur`), so the only history-side change between
`encMetaHistory regHex sim` and `encMetaHistory regHex sim.step` is the
pc-counter advance — exactly one `regDataCell regHex` cell prepended at
the head, identical in shape to `nop` / `interlace` / `complement` / `reverse`.

## §0  Design choice for parameter cells

The contract in `ExecuteBlock.lean` §A.4 says fetch consumes only the
opcode-tag cell, leaving payload cells in `ProgEnc.encProg sim.prog`.
But `encProg sim.prog` lives at the BOTTOM of META.history (per the
layout in `MetaInterp.lean §4`), unreachable from the top without first
consuming the pc-counter, halted-flag, and simhist-len-counter cells.

Rather than adopt a destructive walk (Option D) or per-block scratch
(Option E), this file follows the **Option F** convention — also taken
implicitly by the existing `Block_HuCuoZong.lean` worked blocks:

  > **Per-(opcode × parameter-value) compilation.**  The dispatcher
  > emits one block per concrete `(opcode, param)` pair: 4 blocks for
  > `setShi` (one per `Shi` — now V₄ Klein 4 with `dao/ji/jin/wei`),
  > 6 blocks for `flipYao` (one per `Fin 6`).
  > Each block is therefore parameterized at the *Lean* level by the
  > runtime operand, so it does not need to read the param cell at
  > runtime — fetch+dispatch route control to the right pre-compiled
  > block.  This matches the §4 subagent-guide signature:
  > `executeBlock_setShi (sh : Shi) (offset fetchOffset : Nat)`.

Trade-off: the meta-program grows with the number of (op, param) pairs
(11 + 4 + 6 = 21 blocks vs 12 for tag-only dispatch), but per-block
proofs become trivial cur-mirroring — exactly the pattern proven for
`interlace`/`complement`/`reverse`.  This keeps Phase B local-effect lemmas honest and
defers the destructive-walk question to whichever Phase C dispatcher
design ultimately wins (the bridge lemmas here are independent of that
choice).

## §0.1  What is proven here

For each block we provide:

- `executeBlock_<op>` (definition)
- `executeBlock_<op>_length`
- `executeBlock_<op>_first`, `_second` (instruction enumeration)
- `executeBlock_<op>_local_effect` — abstract simulation under a clean
  block-only YiState
- `encMetaHistory_<op>_step` — sim-side bridge: head-prepend matches
  the pc-counter increment

What's deferred to Phase C: the global `BlockPre → BlockPost` lemma,
which requires the surrounding `metaInterpProg` extract hypothesis (cf.
`ExecuteBlock.lean §A.5`).
-/
import SSBX.Foundation.Wen.MetaInterp.ExecuteBlock

namespace SSBX.Foundation.Wen.MetaInterp.ExecuteBlock

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell256
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.MetaInterp

/-! ## § 1  setShi block (parameterized by sh : Shi) -/

/-- The `setShi sh` execute block: apply `YiInstr.setShi sh` (设时态),
    then jump back to fetch.  Like `interlace`/`complement`/`reverse`, it is a straight-line
    two-instruction program; the Shi transform is applied to META.cur via
    the surrounding loop invariant that maintains `META.cur = sim.cur`.

    There are 4 such blocks (one per `Shi` value: dao, ji, jin, wei —
    the V₄ Klein 4-group); fetch+dispatch routes control to the right
    one based on the runtime param cell.  Note that `setShi Shi.dao`
    is now a valid target (V₄ identity). -/
def executeBlock_setShi (sh : Shi) (_offset fetchOffset : Nat) : List YiInstr :=
  [ YiInstr.setShi sh
  , YiInstr.jump fetchOffset
  ]

theorem executeBlock_setShi_length (sh : Shi) (offset fetchOffset : Nat) :
    (executeBlock_setShi sh offset fetchOffset).length = 2 := rfl

theorem executeBlock_setShi_first (sh : Shi) (offset fetchOffset : Nat) :
    (executeBlock_setShi sh offset fetchOffset)[0]? = some (YiInstr.setShi sh) := rfl

theorem executeBlock_setShi_second (sh : Shi) (offset fetchOffset : Nat) :
    (executeBlock_setShi sh offset fetchOffset)[1]? =
      some (YiInstr.jump fetchOffset) := rfl

/-- **Local effect** for the `setShi sh` block: starting from a META state
    whose cur is `(h, sh₀)`, running the two-step block leaves cur as
    `(h, sh)` and jumps to fetchOffset.  History is unchanged locally
    (the encoding-bridge lemma below relates this to the head-prepend
    expected from the pc-counter advance, but at the level of the block
    itself there is no history modification). -/
theorem executeBlock_setShi_local_effect
    (sh : Shi) (h : Hexagram) (sh₀ : Shi)
    (history : List Cell256) (fetchOffset offset : Nat) :
    let μ : YiState :=
      { cur := (h, sh₀)
        history := history
        pc := 0
        prog := executeBlock_setShi sh offset fetchOffset
        halted := false }
    let μ' := μ.runFuel 2
    μ'.cur = (h, sh)
    ∧ μ'.history = history
    ∧ μ'.pc = fetchOffset
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-- **Sim-side bridge for `setShi sh`**: `sim.step` on a `setShi sh`
    instruction advances `sim.pc` by 1 and sets `sim.cur.2` to `sh`.
    Since `encMetaHistory` does NOT record `cur`, the only history-side
    change is the pc-counter advance — exactly one `regDataCell regHex`
    cell prepended at the head, identical in shape to `nop`/`interlace`/`complement`/`reverse`. -/
theorem encMetaHistory_setShi_step
    (regHex : Hexagram) (sim : YiState) (sh : Shi)
    (h_alive : sim.halted = false)
    (h_setShi : sim.prog[sim.pc]? = some (.setShi sh)) :
    encMetaHistory regHex (sim.step) =
      regDataCell regHex :: encMetaHistory regHex sim := by
  -- sim.step = execute (.setShi sh) sim
  --         = { sim with cur := (sim.cur.1, sh), pc := sim.pc + 1 }
  have h_step : sim.step =
      { sim with cur := (sim.cur.1, sh)
               , pc := sim.pc + 1 } := by
    simp [YiState.step, h_alive, h_setShi, YiState.execute]
  rw [h_step]
  unfold encMetaHistory
  rw [encCounter_succ]
  simp [List.cons_append]

/-! ## § 2  flipYao block (parameterized by i : Fin 6) -/

/-- The `flipYao i` execute block: apply `YiInstr.flipYao i` (翻爻), then
    jump back to fetch.  Like the others, a straight-line two-instruction
    program; the per-yao flip is applied to META.cur via the loop invariant.

    There are 6 such blocks (one per `Fin 6` position); fetch+dispatch
    routes control based on the runtime param cell. -/
def executeBlock_flipYao (i : Fin 6) (_offset fetchOffset : Nat) : List YiInstr :=
  [ YiInstr.flipYao i
  , YiInstr.jump fetchOffset
  ]

theorem executeBlock_flipYao_length (i : Fin 6) (offset fetchOffset : Nat) :
    (executeBlock_flipYao i offset fetchOffset).length = 2 := rfl

theorem executeBlock_flipYao_first (i : Fin 6) (offset fetchOffset : Nat) :
    (executeBlock_flipYao i offset fetchOffset)[0]? = some (YiInstr.flipYao i) := rfl

theorem executeBlock_flipYao_second (i : Fin 6) (offset fetchOffset : Nat) :
    (executeBlock_flipYao i offset fetchOffset)[1]? =
      some (YiInstr.jump fetchOffset) := rfl

/-- **Local effect** for the `flipYao i` block: starting from a META state
    whose cur is `(h, sh)`, running the two-step block leaves cur as
    `(h.flipPos i, sh)` and jumps to fetchOffset. -/
theorem executeBlock_flipYao_local_effect
    (i : Fin 6) (h : Hexagram) (sh : Shi)
    (history : List Cell256) (fetchOffset offset : Nat) :
    let μ : YiState :=
      { cur := (h, sh)
        history := history
        pc := 0
        prog := executeBlock_flipYao i offset fetchOffset
        halted := false }
    let μ' := μ.runFuel 2
    μ'.cur = (h.flipPos i, sh)
    ∧ μ'.history = history
    ∧ μ'.pc = fetchOffset
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-- **Sim-side bridge for `flipYao i`**: `sim.step` on a `flipYao i`
    instruction advances `sim.pc` by 1 and applies `flipPos i` to
    `sim.cur.1`.  As with the other cur-only opcodes, the only
    history-side change is the pc-counter advance. -/
theorem encMetaHistory_flipYao_step
    (regHex : Hexagram) (sim : YiState) (i : Fin 6)
    (h_alive : sim.halted = false)
    (h_flipYao : sim.prog[sim.pc]? = some (.flipYao i)) :
    encMetaHistory regHex (sim.step) =
      regDataCell regHex :: encMetaHistory regHex sim := by
  -- sim.step = execute (.flipYao i) sim
  --         = { sim with cur := (sim.cur.1.flipPos i, sim.cur.2), pc := sim.pc + 1 }
  have h_step : sim.step =
      { sim with cur := (sim.cur.1.flipPos i, sim.cur.2)
               , pc := sim.pc + 1 } := by
    simp [YiState.step, h_alive, h_flipYao, YiState.execute]
  rw [h_step]
  unfold encMetaHistory
  rw [encCounter_succ]
  simp [List.cons_append]

end SSBX.Foundation.Wen.MetaInterp.ExecuteBlock
