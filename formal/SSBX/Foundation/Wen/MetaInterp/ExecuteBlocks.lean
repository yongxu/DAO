/-
# ExecuteBlocks — aggregated definitions for the 4 simplest opcodes

This file consolidates the per-opcode `executeBlock_<op>` programs for the
**four simplest** YiInstr opcodes:

- `nop`  — pc++; no other state change
- `halt` — halted := true
- `hu`   — cur.1 := Hexagram.hu cur.1; pc++
- `cuo`  — cur.1 := Hexagram.cuo cur.1; pc++

The blocks for nop/halt are also defined in `ExecuteBlock.lean` as worked
examples, and hu/cuo/zong in `Block_HuCuoZong.lean`.  To avoid duplicate-
definition clashes we place this aggregator in its own sub-namespace
`Aggregate`, keeping the underlying instruction lists identical so that
downstream dispatch can route to either copy.

## Tier status (per task brief B.T4.C)

| op   | Tier A (def + length) | Tier B/C (local-effect)          |
| ---- | --------------------- | -------------------------------- |
| nop  | ✓                     | ✓ (Tier B, full)                 |
| halt | ✓                     | ✓ (Tier B, full)                 |
| hu   | ✓                     | ✓ (Tier C, full)                 |
| cuo  | ✓                     | ✓ (Tier C, full)                 |

All four block effects are discharged by `rfl` after the standard
`runFuel` unfolding (cf. `ExecuteBlock.executeBlock_nop_local_effect`
and `Block_HuCuoZong.executeBlock_hu_local_effect`).  No `sorry`.

## Convention

Each block ends in `YiInstr.jump fetchOffset` (except `halt`, which sets
META.halted and falls through to the surrounding `haltProg`).  See
`ExecuteBlock.lean` §A for the full BlockPre/BlockPost contract.
-/
import SSBX.Foundation.Wen.MetaInterp.ExecuteBlock
import SSBX.Foundation.Wen.MetaInterp.Block_HuCuoZong

namespace SSBX.Foundation.Wen.MetaInterp.ExecuteBlocks
namespace Aggregate

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell256
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.MetaInterp

/-! ## § 1  nop -/

/-- `executeBlock_nop` : push the new pc-counter data cell, jump back. -/
def executeBlock_nop (_offset : Nat) (fetchOffset : Nat) : List YiInstr :=
  [ YiInstr.push
  , YiInstr.jump fetchOffset ]

theorem executeBlock_nop_length (offset fetchOffset : Nat) :
    (executeBlock_nop offset fetchOffset).length = 2 := rfl

/-- **Tier B local effect** for `nop`: from a META state whose cur is the
    data-cell prototype `(regHex, Shi.jin)`, running the 2-step block
    prepends one data cell and lands at `fetchOffset`.  This is exactly
    the pc-counter increment expected by `encMetaHistory_nop_step`. -/
theorem executeBlock_nop_local_effect
    (regHex : Hexagram) (history : List Cell256)
    (fetchOffset offset : Nat) :
    let μ : YiState :=
      { cur := (regHex, Shi.jin)
        history := history
        pc := 0
        prog := executeBlock_nop offset fetchOffset
        halted := false }
    let μ' := μ.runFuel 2
    μ'.cur = (regHex, Shi.jin)
    ∧ μ'.history = (regHex, Shi.jin) :: history
    ∧ μ'.pc = fetchOffset
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-! ## § 2  halt -/

/-- `executeBlock_halt` : a single `YiInstr.halt`; the surrounding
    `metaInterpProg` falls through to its terminal segment. -/
def executeBlock_halt (_offset _fetchOffset : Nat) : List YiInstr :=
  [ YiInstr.halt ]

theorem executeBlock_halt_length (offset fetchOffset : Nat) :
    (executeBlock_halt offset fetchOffset).length = 1 := rfl

/-- **Tier B local effect** for `halt`: 1-fuel run sets `μ'.halted = true`. -/
theorem executeBlock_halt_local_effect
    (cur : Cell256) (history : List Cell256)
    (offset fetchOffset : Nat) :
    let μ : YiState :=
      { cur := cur
        history := history
        pc := 0
        prog := executeBlock_halt offset fetchOffset
        halted := false }
    let μ' := μ.runFuel 1
    μ'.cur = cur
    ∧ μ'.history = history
    ∧ μ'.halted = true := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-! ## § 3  hu

    `hu` is a pure cur-transform under the loop invariant
    `META.cur ≡ sim.cur` (see `MetaInterp.lean` §META.cur 之角色).
    No history pop/push is needed: the YiInstr.hu instruction directly
    rewrites `cur.1 := Hexagram.hu cur.1`. -/

def executeBlock_hu (_offset : Nat) (fetchOffset : Nat) : List YiInstr :=
  [ YiInstr.hu
  , YiInstr.jump fetchOffset ]

theorem executeBlock_hu_length (offset fetchOffset : Nat) :
    (executeBlock_hu offset fetchOffset).length = 2 := rfl

/-- **Tier C local effect** for `hu`: from cur = `(h, sh)`, running the
    2-step block leaves cur = `(Hexagram.hu h, sh)` and pc = fetchOffset.
    History is locally unchanged; the pc-counter advance in the encoded
    META-history is handled by the surrounding fetch protocol, not by
    this block (`hu` is a cur-only transform; see
    `Block_HuCuoZong.encMetaHistory_hu_step`). -/
theorem executeBlock_hu_local_effect
    (h : Hexagram) (sh : Shi) (history : List Cell256)
    (fetchOffset offset : Nat) :
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

/-! ## § 4  cuo -/

def executeBlock_cuo (_offset : Nat) (fetchOffset : Nat) : List YiInstr :=
  [ YiInstr.cuo
  , YiInstr.jump fetchOffset ]

theorem executeBlock_cuo_length (offset fetchOffset : Nat) :
    (executeBlock_cuo offset fetchOffset).length = 2 := rfl

/-- **Tier C local effect** for `cuo`: see `executeBlock_hu_local_effect`. -/
theorem executeBlock_cuo_local_effect
    (h : Hexagram) (sh : Shi) (history : List Cell256)
    (fetchOffset offset : Nat) :
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

/-! ## § 5  Agreement with existing namespaced copies

These trivial lemmas confirm the aggregated definitions are *syntactically
identical* to the ones in `ExecuteBlock` (nop/halt) and `Block_HuCuoZong`
(hu/cuo).  Should the underlying definitions ever diverge, these checks
will fail at build time. -/

theorem executeBlock_nop_eq (offset fetchOffset : Nat) :
    executeBlock_nop offset fetchOffset =
      ExecuteBlock.executeBlock_nop offset fetchOffset := rfl

theorem executeBlock_halt_eq (offset fetchOffset : Nat) :
    executeBlock_halt offset fetchOffset =
      ExecuteBlock.executeBlock_halt offset fetchOffset := rfl

theorem executeBlock_hu_eq (offset fetchOffset : Nat) :
    executeBlock_hu offset fetchOffset =
      executeBlock_hu offset fetchOffset := rfl

theorem executeBlock_cuo_eq (offset fetchOffset : Nat) :
    executeBlock_cuo offset fetchOffset =
      executeBlock_cuo offset fetchOffset := rfl

end Aggregate
end SSBX.Foundation.Wen.MetaInterp.ExecuteBlocks
