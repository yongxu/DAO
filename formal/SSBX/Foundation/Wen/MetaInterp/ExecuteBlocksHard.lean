/-
# ExecuteBlocksHard — Tier-A structural defs for the 5 hard opcodes

The 5 "hard" YiInstr opcodes whose simulation requires encoded-history
surgery beyond the pure `META.cur ≡ sim.cur` invariant:

  1. `jump t`                — pc-counter region rewrite
  2. `push`                  — simhist-len marker bump + push sim.cur
  3. `pop`                   — simhist-len marker decrement + restore prev cur
  4. `branchYaoEq i j t`     — conditional pc (taken/not-taken converge)
  5. `branchShiEq sh t`      — conditional pc (taken/not-taken converge)

Each is committed at **Tier A** (definite-length `List YiInstr`) with a
**Tier B** `length = rfl` lemma.  **Tier C** local-effect simulation
lemmas are stubbed with `sorry` and `TODO(B.T4.E)` markers — the
encoded-history surgery is deferred to a dedicated wave.

The block shapes here use deliberately-padded `nop` placeholders so that
the surrounding dispatch table can commit to *fixed offsets* now and the
internal logic can be filled in B.T4.E without disturbing those offsets.

## Tier status

| op             | Tier A | Tier B | Tier C            |
| -------------- | ------ | ------ | ----------------- |
| jump           | ✓      | ✓ rfl  | sorry (B.T4.E)    |
| push           | ✓      | ✓ rfl  | sorry (B.T4.E)    |
| pop            | ✓      | ✓ rfl  | sorry (B.T4.E)    |
| branchYaoEq    | ✓      | ✓ rfl  | sorry (B.T4.E)    |
| branchShiEq    | ✓      | ✓ rfl  | sorry (B.T4.E)    |

Total: 5 `sorry`s (one Tier-C local-effect per opcode).
-/
import SSBX.Foundation.Wen.MetaInterp.ExecuteBlock
import SSBX.Foundation.Wen.MetaInterp.Block_Jump
import SSBX.Foundation.Wen.MetaInterp.Block_PushPop
import SSBX.Foundation.Wen.MetaInterp.Block_Branches

namespace SSBX.Foundation.Wen.MetaInterp.ExecuteBlocksHard

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell256
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.MetaInterp

/-! ## § 1  jump t

  Plan (B.T4.E): pop the 4 pc-counter data cells from META.history,
  push 4 freshly-encoded data cells for target `t`, then jump back to
  the outer fetch.  Block length committed at 9 to leave room.
-/

def executeBlock_jump (t : Nat) (fetchOffset : Nat) : List YiInstr :=
  List.replicate 8 YiInstr.nop ++ [YiInstr.jump fetchOffset]
  -- TODO(B.T4.E): replace 8 nops with real pc-counter surgery
  --   instructions targeting encoded pc-region; use `t` to compute
  --   new data cells via `encCounter`/`decCounter` patterns.
  -- The unused `t` parameter is preserved here so the dispatch table
  -- can commit to this signature.

theorem executeBlock_jump_length (t fetchOffset : Nat) :
    (executeBlock_jump t fetchOffset).length = 9 := by
  simp [executeBlock_jump, List.length_append, List.length_replicate]

/-- **Tier C** local effect for `jump`.  Deferred: encoded pc-counter
    region must be rewritten from old pc to `t`.  -/
theorem executeBlock_jump_local_effect
    (t : Nat) (cur : Cell256) (history : List Cell256)
    (fetchOffset : Nat) :
    let μ : YiState :=
      { cur := cur
        history := history
        pc := 0
        prog := executeBlock_jump t fetchOffset
        halted := false }
    let μ' := μ.runFuel 9
    μ'.pc = fetchOffset
    ∧ μ'.halted = false := by
  -- TODO(B.T4.E): jump full local-effect — the placeholder body is 8
  -- nops then `jump fetchOffset`, which actually *does* satisfy the
  -- pc/halted conclusion shown here; the real obligation will include
  -- an encoded-pc-counter-rewrite clause once the body is replaced.
  sorry

/-! ## § 2  push

  Plan (B.T4.E): increment the simhist-len marker cell, then push
  META.cur (= sim.cur under loop invariant) onto META.history.
  Block length committed at 5.
-/

def executeBlock_push (fetchOffset : Nat) : List YiInstr :=
  List.replicate 4 YiInstr.nop ++ [YiInstr.jump fetchOffset]
  -- TODO(B.T4.E): replace 4 nops with marker-bump + push sequence.

theorem executeBlock_push_length (fetchOffset : Nat) :
    (executeBlock_push fetchOffset).length = 5 := by
  simp [executeBlock_push, List.length_append, List.length_replicate]

/-- **Tier C** local effect for `push`.  Deferred: simhist-len marker
    increment + sim.cur appended to encoded sim.history region. -/
theorem executeBlock_push_local_effect
    (cur : Cell256) (history : List Cell256) (fetchOffset : Nat) :
    let μ : YiState :=
      { cur := cur
        history := history
        pc := 0
        prog := executeBlock_push fetchOffset
        halted := false }
    let μ' := μ.runFuel 5
    μ'.pc = fetchOffset
    ∧ μ'.halted = false := by
  -- TODO(B.T4.E): push full local-effect — placeholder body trivially
  -- satisfies the pc/halted clauses; real obligation adds the
  -- simhist-len marker bump and encoded-history surgery.
  sorry

/-! ## § 3  pop

  Plan (B.T4.E): decrement simhist-len marker, drop top encoded sim
  history cell, restore META.cur to the previous sim.cur.  Block
  length committed at 5.
-/

def executeBlock_pop (fetchOffset : Nat) : List YiInstr :=
  List.replicate 4 YiInstr.nop ++ [YiInstr.jump fetchOffset]
  -- TODO(B.T4.E): replace 4 nops with marker-decrement + pop sequence.

theorem executeBlock_pop_length (fetchOffset : Nat) :
    (executeBlock_pop fetchOffset).length = 5 := by
  simp [executeBlock_pop, List.length_append, List.length_replicate]

/-- **Tier C** local effect for `pop`.  Deferred. -/
theorem executeBlock_pop_local_effect
    (cur : Cell256) (history : List Cell256) (fetchOffset : Nat) :
    let μ : YiState :=
      { cur := cur
        history := history
        pc := 0
        prog := executeBlock_pop fetchOffset
        halted := false }
    let μ' := μ.runFuel 5
    μ'.pc = fetchOffset
    ∧ μ'.halted = false := by
  -- TODO(B.T4.E): pop full local-effect.
  sorry

/-! ## § 4  branchYaoEq i j t

  Plan (B.T4.E): inspect sim.cur (= META.cur), compare yao i vs yao j;
  on equal, route to "set encoded pc to t" arm; otherwise advance pc
  by 1.  Both arms converge to `jump fetchOffset`.  Block length
  committed at 10.
-/

def executeBlock_branchYaoEq
    (i j : Fin 6) (t : Nat) (fetchOffset : Nat) : List YiInstr :=
  -- Embed the actual branchYaoEq instruction so dispatch shape is
  -- already faithful at the YiInstr layer.  Surrounding nops are the
  -- placeholder for the encoded-pc-counter arm-and-converge logic.
  List.replicate 4 YiInstr.nop
    ++ [YiInstr.branchYaoEq i j 7]
    ++ List.replicate 4 YiInstr.nop
    ++ [YiInstr.jump fetchOffset]

theorem executeBlock_branchYaoEq_length
    (i j : Fin 6) (t fetchOffset : Nat) :
    (executeBlock_branchYaoEq i j t fetchOffset).length = 10 := by
  simp [executeBlock_branchYaoEq, List.length_append, List.length_replicate]

/-- **Tier C** local effect for `branchYaoEq`.  Deferred: two-arm
    encoded pc-counter rewrite with convergence. -/
theorem executeBlock_branchYaoEq_local_effect
    (i j : Fin 6) (t : Nat) (cur : Cell256) (history : List Cell256)
    (fetchOffset : Nat) :
    let μ : YiState :=
      { cur := cur
        history := history
        pc := 0
        prog := executeBlock_branchYaoEq i j t fetchOffset
        halted := false }
    let μ' := μ.runFuel 16
    μ'.halted = false := by
  -- TODO(B.T4.E): branchYaoEq full local-effect — the conditional
  -- encoded pc-counter rewrite with two arms converging to
  -- `jump fetchOffset`.
  sorry

/-! ## § 5  branchShiEq sh t

  Plan (B.T4.E): same shape as branchYaoEq but compares the shi
  component of sim.cur.  Block length committed at 10.
-/

def executeBlock_branchShiEq
    (sh : Shi) (t : Nat) (fetchOffset : Nat) : List YiInstr :=
  List.replicate 4 YiInstr.nop
    ++ [YiInstr.branchShiEq sh 7]
    ++ List.replicate 4 YiInstr.nop
    ++ [YiInstr.jump fetchOffset]

theorem executeBlock_branchShiEq_length
    (sh : Shi) (t fetchOffset : Nat) :
    (executeBlock_branchShiEq sh t fetchOffset).length = 10 := by
  simp [executeBlock_branchShiEq, List.length_append, List.length_replicate]

/-- **Tier C** local effect for `branchShiEq`.  Deferred. -/
theorem executeBlock_branchShiEq_local_effect
    (sh : Shi) (t : Nat) (cur : Cell256) (history : List Cell256)
    (fetchOffset : Nat) :
    let μ : YiState :=
      { cur := cur
        history := history
        pc := 0
        prog := executeBlock_branchShiEq sh t fetchOffset
        halted := false }
    let μ' := μ.runFuel 16
    μ'.halted = false := by
  -- TODO(B.T4.E): branchShiEq full local-effect.
  sorry

end SSBX.Foundation.Wen.MetaInterp.ExecuteBlocksHard
