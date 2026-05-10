/-
# Block_HuCuoZong — executeBlocks for hu, cuo, zong (trivial cur-transforms)

These three opcodes are structurally near-identical to `nop`: they bump
`sim.pc` by 1 and otherwise differ only in applying a `Hexagram` involution
(`hu`, `cuo`, `zong` respectively) to `sim.cur.1`.

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
`hu`, `cuo`, `zong`.

See `ExecuteBlock.lean` §C for the worked-example prototype this file
mirrors.
-/
import SSBX.Foundation.Wen.MetaInterp.ExecuteBlock

namespace SSBX.Foundation.Wen.MetaInterp.ExecuteBlock

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell256
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.MetaInterp

/-! ## § 1  hu block -/

/-- The `hu` execute block: apply `YiInstr.hu` (互), then jump back to fetch.
    Like `nop`, it is a straight-line two-instruction program; the Hex
    transform is applied to META.cur via the surrounding loop invariant
    that maintains `META.cur = sim.cur`. -/
def executeBlock_hu (_offset fetchOffset : Nat) : List YiInstr :=
  [ YiInstr.hu
  , YiInstr.jump fetchOffset
  ]

theorem executeBlock_hu_length (offset fetchOffset : Nat) :
    (executeBlock_hu offset fetchOffset).length = 2 := rfl

theorem executeBlock_hu_first (offset fetchOffset : Nat) :
    (executeBlock_hu offset fetchOffset)[0]? = some YiInstr.hu := rfl

theorem executeBlock_hu_second (offset fetchOffset : Nat) :
    (executeBlock_hu offset fetchOffset)[1]? =
      some (YiInstr.jump fetchOffset) := rfl

/-- **Local effect** for the `hu` block: starting from a META state whose
    cur is `(h, sh)`, running the two-step block leaves cur as
    `(Hexagram.hu h, sh)` and jumps to fetchOffset.  History is unchanged
    locally (the encoding-bridge lemma below relates this to the head-prepend
    expected from the pc-counter advance, but at the level of the block itself
    there is no history modification). -/
theorem executeBlock_hu_local_effect
    (h : Hexagram) (sh : Shi)
    (history : List Cell256) (fetchOffset offset : Nat) :
    let μ : YiState :=
      { cur := (h, sh)
        history := history
        pc := 0
        prog := executeBlock_hu offset fetchOffset
        halted := false }
    let μ' := μ.runFuel 2
    μ'.cur = (Hexagram.hu h, sh)
    ∧ μ'.history = history
    ∧ μ'.pc = fetchOffset
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-- **Sim-side bridge for `hu`**: `sim.step` on a `hu` instruction
    advances `sim.pc` by 1 and applies `Hexagram.hu` to `sim.cur.1`.
    Since `encMetaHistory` does NOT record `cur`, the only history-side
    change is the pc-counter advance — exactly one `regDataCell regHex`
    cell prepended at the head, identical in shape to `nop`. -/
theorem encMetaHistory_hu_step
    (regHex : Hexagram) (sim : YiState)
    (h_alive : sim.halted = false)
    (h_hu : sim.prog[sim.pc]? = some .hu) :
    encMetaHistory regHex (sim.step) =
      regDataCell regHex :: encMetaHistory regHex sim := by
  -- sim.step = execute .hu sim
  --         = { sim with cur := (Hexagram.hu sim.cur.1, sim.cur.2)
  --                    , pc := sim.pc + 1 }
  have h_step : sim.step =
      { sim with cur := (Hexagram.hu sim.cur.1, sim.cur.2)
               , pc := sim.pc + 1 } := by
    simp [YiState.step, h_alive, h_hu, YiState.execute]
  rw [h_step]
  unfold encMetaHistory
  rw [encCounter_succ]
  simp [List.cons_append]

/-! ## § 2  cuo block -/

/-- The `cuo` execute block: apply `YiInstr.cuo` (错), then jump back to fetch. -/
def executeBlock_cuo (_offset fetchOffset : Nat) : List YiInstr :=
  [ YiInstr.cuo
  , YiInstr.jump fetchOffset
  ]

theorem executeBlock_cuo_length (offset fetchOffset : Nat) :
    (executeBlock_cuo offset fetchOffset).length = 2 := rfl

theorem executeBlock_cuo_first (offset fetchOffset : Nat) :
    (executeBlock_cuo offset fetchOffset)[0]? = some YiInstr.cuo := rfl

theorem executeBlock_cuo_second (offset fetchOffset : Nat) :
    (executeBlock_cuo offset fetchOffset)[1]? =
      some (YiInstr.jump fetchOffset) := rfl

/-- **Local effect** for the `cuo` block: see `executeBlock_hu_local_effect`. -/
theorem executeBlock_cuo_local_effect
    (h : Hexagram) (sh : Shi)
    (history : List Cell256) (fetchOffset offset : Nat) :
    let μ : YiState :=
      { cur := (h, sh)
        history := history
        pc := 0
        prog := executeBlock_cuo offset fetchOffset
        halted := false }
    let μ' := μ.runFuel 2
    μ'.cur = (Hexagram.cuo h, sh)
    ∧ μ'.history = history
    ∧ μ'.pc = fetchOffset
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-- **Sim-side bridge for `cuo`**: see `encMetaHistory_hu_step`. -/
theorem encMetaHistory_cuo_step
    (regHex : Hexagram) (sim : YiState)
    (h_alive : sim.halted = false)
    (h_cuo : sim.prog[sim.pc]? = some .cuo) :
    encMetaHistory regHex (sim.step) =
      regDataCell regHex :: encMetaHistory regHex sim := by
  have h_step : sim.step =
      { sim with cur := (Hexagram.cuo sim.cur.1, sim.cur.2)
               , pc := sim.pc + 1 } := by
    simp [YiState.step, h_alive, h_cuo, YiState.execute]
  rw [h_step]
  unfold encMetaHistory
  rw [encCounter_succ]
  simp [List.cons_append]

/-! ## § 3  zong block -/

/-- The `zong` execute block: apply `YiInstr.zong` (综), then jump back to fetch. -/
def executeBlock_zong (_offset fetchOffset : Nat) : List YiInstr :=
  [ YiInstr.zong
  , YiInstr.jump fetchOffset
  ]

theorem executeBlock_zong_length (offset fetchOffset : Nat) :
    (executeBlock_zong offset fetchOffset).length = 2 := rfl

theorem executeBlock_zong_first (offset fetchOffset : Nat) :
    (executeBlock_zong offset fetchOffset)[0]? = some YiInstr.zong := rfl

theorem executeBlock_zong_second (offset fetchOffset : Nat) :
    (executeBlock_zong offset fetchOffset)[1]? =
      some (YiInstr.jump fetchOffset) := rfl

/-- **Local effect** for the `zong` block: see `executeBlock_hu_local_effect`. -/
theorem executeBlock_zong_local_effect
    (h : Hexagram) (sh : Shi)
    (history : List Cell256) (fetchOffset offset : Nat) :
    let μ : YiState :=
      { cur := (h, sh)
        history := history
        pc := 0
        prog := executeBlock_zong offset fetchOffset
        halted := false }
    let μ' := μ.runFuel 2
    μ'.cur = (Hexagram.zong h, sh)
    ∧ μ'.history = history
    ∧ μ'.pc = fetchOffset
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-- **Sim-side bridge for `zong`**: see `encMetaHistory_hu_step`. -/
theorem encMetaHistory_zong_step
    (regHex : Hexagram) (sim : YiState)
    (h_alive : sim.halted = false)
    (h_zong : sim.prog[sim.pc]? = some .zong) :
    encMetaHistory regHex (sim.step) =
      regDataCell regHex :: encMetaHistory regHex sim := by
  have h_step : sim.step =
      { sim with cur := (Hexagram.zong sim.cur.1, sim.cur.2)
               , pc := sim.pc + 1 } := by
    simp [YiState.step, h_alive, h_zong, YiState.execute]
  rw [h_step]
  unfold encMetaHistory
  rw [encCounter_succ]
  simp [List.cons_append]

end SSBX.Foundation.Wen.MetaInterp.ExecuteBlock
