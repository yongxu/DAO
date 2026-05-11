/-
# Block_HuCuoZong — executeBlocks for interlace, complement, reverse (trivial cur-transforms)

These three opcodes are structurally near-identical to `nop`: they bump
`sim.pc` by 1 and otherwise differ only in applying a `Hexagram` involution
(`interlace`, `complement`, `reverse` respectively) to `sim.cur.1`.

Crucially, **`encMetaHistory` does not record `cur`** — META.cur ≡ sim.cur
is maintained as the surrounding loop invariant.  Hence the
`encMetaHistory_<op>_step` bridges below have the exact same shape as
`encMetaHistory_nop_step`: the only history-side change is the
`encCounter` advance from `sim.pc` to `sim.pc + 1`, contributing a single
`regDataCell regHex` cell at the head.

The Hex transform itself happens in META.cur (the loop invariant
machinery), not in encMetaHistory.

Each block is a 2-instruction program:

  [ <YiInstr op> ; jump fetchOffset ]

The `local_effect` lemma below abstracts the per-op behavior as a
parametric `transform : Hexagram → Hexagram`; we then specialize to
`interlace`, `complement`, `reverse`.

See `ExecuteBlock.lean` §C for the worked-example prototype this file
mirrors.
-/
import SSBX.Foundation.Wen.MetaInterp.ExecuteBlock

namespace SSBX.Foundation.Wen.MetaInterp.ExecuteBlock

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.MetaInterp

/-! ## § 1  interlace block -/

/-- The `interlace` execute block: apply `YiInstr.interlace` (互), then jump back to fetch.
    Like `nop`, it is a straight-line two-instruction program; the Hex
    transform is applied to META.cur via the surrounding loop invariant
    that maintains `META.cur = sim.cur`. -/
def executeBlock_hu (_offset fetchOffset : Nat) : List YiInstr :=
  [ YiInstr.interlace
  , YiInstr.jump fetchOffset
  ]

theorem executeBlock_hu_length (offset fetchOffset : Nat) :
    (executeBlock_hu offset fetchOffset).length = 2 := rfl

theorem executeBlock_hu_first (offset fetchOffset : Nat) :
    (executeBlock_hu offset fetchOffset)[0]? = some YiInstr.interlace := rfl

theorem executeBlock_hu_second (offset fetchOffset : Nat) :
    (executeBlock_hu offset fetchOffset)[1]? =
      some (YiInstr.jump fetchOffset) := rfl

/-- **Local effect** for the `interlace` block: starting from a META state whose
    cur is `(h, sh)`, running the two-step block leaves cur as
    `(Hexagram.interlace h, sh)` and jumps to fetchOffset.  History is unchanged
    locally (the encoding-bridge lemma below relates this to the head-prepend
    expected from the pc-counter advance, but at the level of the block itself
    there is no history modification). -/
theorem executeBlock_hu_local_effect
    (h : Hexagram) (sh : Shi)
    (history : List R8) (fetchOffset offset : Nat) :
    let μ : YiState :=
      { cur := (h, sh)
        history := history
        pc := 0
        prog := executeBlock_hu offset fetchOffset
        halted := false }
    let μ' := μ.runFuel 2
    μ'.cur = (Hexagram.interlace h, sh)
    ∧ μ'.history = history
    ∧ μ'.pc = fetchOffset
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-- **Sim-side bridge for `interlace`**: `sim.step` on a `interlace` instruction
    advances `sim.pc` by 1 and applies `Hexagram.interlace` to `sim.cur.1`.
    Since `encMetaHistory` does NOT record `cur`, the only history-side
    change is the pc-counter advance — exactly one `regDataCell regHex`
    cell prepended at the head, identical in shape to `nop`. -/
theorem encMetaHistory_hu_step
    (regHex : Hexagram) (sim : YiState)
    (h_alive : sim.halted = false)
    (h_hu : sim.prog[sim.pc]? = some .interlace) :
    encMetaHistory regHex (sim.step) =
      regDataCell regHex :: encMetaHistory regHex sim := by
  -- sim.step = execute .interlace sim
  --         = { sim with cur := (Hexagram.interlace sim.cur.1, sim.cur.2)
  --                    , pc := sim.pc + 1 }
  have h_step : sim.step =
      { sim with cur := (Hexagram.interlace sim.cur.1, sim.cur.2)
               , pc := sim.pc + 1 } := by
    simp [YiState.step, h_alive, h_hu, YiState.execute]
  rw [h_step]
  unfold encMetaHistory
  rw [encCounter_succ]
  simp [List.cons_append]

/-! ## § 2  complement block -/

/-- The `complement` execute block: apply `YiInstr.complement` (错), then jump back to fetch. -/
def executeBlock_cuo (_offset fetchOffset : Nat) : List YiInstr :=
  [ YiInstr.complement
  , YiInstr.jump fetchOffset
  ]

theorem executeBlock_cuo_length (offset fetchOffset : Nat) :
    (executeBlock_cuo offset fetchOffset).length = 2 := rfl

theorem executeBlock_cuo_first (offset fetchOffset : Nat) :
    (executeBlock_cuo offset fetchOffset)[0]? = some YiInstr.complement := rfl

theorem executeBlock_cuo_second (offset fetchOffset : Nat) :
    (executeBlock_cuo offset fetchOffset)[1]? =
      some (YiInstr.jump fetchOffset) := rfl

/-- **Local effect** for the `complement` block: see `executeBlock_hu_local_effect`. -/
theorem executeBlock_cuo_local_effect
    (h : Hexagram) (sh : Shi)
    (history : List R8) (fetchOffset offset : Nat) :
    let μ : YiState :=
      { cur := (h, sh)
        history := history
        pc := 0
        prog := executeBlock_cuo offset fetchOffset
        halted := false }
    let μ' := μ.runFuel 2
    μ'.cur = (Hexagram.complement h, sh)
    ∧ μ'.history = history
    ∧ μ'.pc = fetchOffset
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-- **Sim-side bridge for `complement`**: see `encMetaHistory_hu_step`. -/
theorem encMetaHistory_cuo_step
    (regHex : Hexagram) (sim : YiState)
    (h_alive : sim.halted = false)
    (h_cuo : sim.prog[sim.pc]? = some .complement) :
    encMetaHistory regHex (sim.step) =
      regDataCell regHex :: encMetaHistory regHex sim := by
  have h_step : sim.step =
      { sim with cur := (Hexagram.complement sim.cur.1, sim.cur.2)
               , pc := sim.pc + 1 } := by
    simp [YiState.step, h_alive, h_cuo, YiState.execute]
  rw [h_step]
  unfold encMetaHistory
  rw [encCounter_succ]
  simp [List.cons_append]

/-! ## § 3  reverse block -/

/-- The `reverse` execute block: apply `YiInstr.reverse` (综), then jump back to fetch. -/
def executeBlock_zong (_offset fetchOffset : Nat) : List YiInstr :=
  [ YiInstr.reverse
  , YiInstr.jump fetchOffset
  ]

theorem executeBlock_zong_length (offset fetchOffset : Nat) :
    (executeBlock_zong offset fetchOffset).length = 2 := rfl

theorem executeBlock_zong_first (offset fetchOffset : Nat) :
    (executeBlock_zong offset fetchOffset)[0]? = some YiInstr.reverse := rfl

theorem executeBlock_zong_second (offset fetchOffset : Nat) :
    (executeBlock_zong offset fetchOffset)[1]? =
      some (YiInstr.jump fetchOffset) := rfl

/-- **Local effect** for the `reverse` block: see `executeBlock_hu_local_effect`. -/
theorem executeBlock_zong_local_effect
    (h : Hexagram) (sh : Shi)
    (history : List R8) (fetchOffset offset : Nat) :
    let μ : YiState :=
      { cur := (h, sh)
        history := history
        pc := 0
        prog := executeBlock_zong offset fetchOffset
        halted := false }
    let μ' := μ.runFuel 2
    μ'.cur = (Hexagram.reverse h, sh)
    ∧ μ'.history = history
    ∧ μ'.pc = fetchOffset
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-- **Sim-side bridge for `reverse`**: see `encMetaHistory_hu_step`. -/
theorem encMetaHistory_zong_step
    (regHex : Hexagram) (sim : YiState)
    (h_alive : sim.halted = false)
    (h_zong : sim.prog[sim.pc]? = some .reverse) :
    encMetaHistory regHex (sim.step) =
      regDataCell regHex :: encMetaHistory regHex sim := by
  have h_step : sim.step =
      { sim with cur := (Hexagram.reverse sim.cur.1, sim.cur.2)
               , pc := sim.pc + 1 } := by
    simp [YiState.step, h_alive, h_zong, YiState.execute]
  rw [h_step]
  unfold encMetaHistory
  rw [encCounter_succ]
  simp [List.cons_append]

end SSBX.Foundation.Wen.MetaInterp.ExecuteBlock
