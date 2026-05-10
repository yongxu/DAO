/-
# Block_Branches — executeBlocks for `branchYaoEq i j t` and `branchShiEq sh t`

These two opcodes are the conditional pc-update primitives:

  branchYaoEq i j t : if cur.1.yaoAt i = cur.1.yaoAt j
                       then pc := t
                       else pc := pc + 1
  branchShiEq sh t : if cur.2 = sh
                       then pc := t
                       else pc := pc + 1

In META terms, sim.pc updates correspond to **rewriting the pc-counter
prefix** of `encMetaHistory regHex sim` (cf. `encMetaHistory_nop_step`
which only handles the +1 case via `regDataCell` head-prepend).

## §0  Design choice — per-(opcode × params) Lean-level specialization

Following the same **Option F** convention adopted in
`Block_SetShi_FlipYao.lean` and `Block_HuCuoZong.lean`, we Lean-level
parameterize each block by its concrete operands.  For branches that
means a Lean function `executeBlock_branchYaoEq (i j : Fin 6) (t : Nat)
…` that emits one block per `(i, j, t)` triple, and similarly
`executeBlock_branchShiEq (sh : Shi) (t : Nat) …` per `(sh, t)`.

The dispatcher routes control to the right pre-compiled block based on
the runtime param cells (consumed by fetch+dispatch — outside this file).

This trades program size for proof tractability: the meta-program grows
combinatorially in the operand space, but each block becomes a simple
straight-line program whose local effect mirrors the ISA-level branch
opcode directly.

## §0.1  The two execution paths

Each block is a 2-instruction program of the form

  [ <branch op> ; jump fetchOffset ]

There are two dynamic paths:

* **Fall-through** (condition FALSE): the branch op increments META.pc
  by 1 (to position 1), the next instruction `jump fetchOffset` fires,
  META.pc := fetchOffset.  This is structurally identical to a 2-step
  run of `[ nop ; jump fetchOffset ]` from the local-effect standpoint.
  The corresponding sim-side encoding bridge is the **same head-prepend
  of `regDataCell regHex`** as for `nop`/`hu`/`cuo`/`zong`.

* **Branch-taken** (condition TRUE): after the branch op, META.pc := t.
  In the local block-only YiState (where `prog := executeBlock_… 0 …`),
  if `t ≥ 2` execution falls off the end of the block and META halts on
  the next step; if `t < 2` we re-execute one of the block's own
  instructions, which is meaningless absent the surrounding metaProg.

  In the **global** `metaInterpProg` context (deferred to Phase C),
  `t` is an absolute offset into `metaInterpProg`, so the branch
  transfers control to whichever block sits at offset `t` — which is
  the intended semantics.  The sim-side encoding bridge for this case
  requires **dynamic pc-counter rewriting** from
  `encCounter regHex sim.pc` to `encCounter regHex t`, which is a
  multi-cell operation (could shorten or extend the counter).  This
  is the same complication the eventual `Block_Jump.lean` will face.

## §0.2  What is proven in this file

For each block we provide:

- `executeBlock_<op>` — the Lean-level definition (2 instructions).
- `executeBlock_<op>_length`, `_first`, `_second` — structural lemmas.
- `executeBlock_<op>_local_effect_fallthrough` — the FALL-THROUGH case
  (condition FALSE) proven end-to-end on a clean block-only YiState:
  cur unchanged, pc → fetchOffset, history unchanged locally.
- `encMetaHistory_<op>_fallthrough_step` — the sim-side bridge for the
  fall-through case: matches the `nop`-shape head-prepend.

What is **deferred** (with a clear `/-! deferred -/` design note):

- The **branch-taken** local-effect case (TRUE branch jumping to
  absolute `t`).  Locally meaningless without the global metaProg
  context; the global statement requires the surrounding
  `metaInterpProg.extract` hypothesis and lives in Phase C.
- The **branch-taken** sim-side bridge — multi-cell pc-counter rewrite,
  same engineering challenge as `Block_Jump.lean`.
- The combined `BlockPre → BlockPost` simulation lemma for both
  branches, which depends on the pieces above.

## §0.3  Why fall-through is the cleanly provable slice

In the fall-through case, sim.pc is bumped by 1 (just like nop), so the
encoding-bridge head-prepend reuses the *exact same proof* as
`encMetaHistory_nop_step`.  The block also happens to behave like
`[ nop ; jump fetchOffset ]` locally because the ISA-level branch op,
when its condition is false, IS a one-cycle nop on cur and just
increments pc.  Hence both the block-side `local_effect` and the
sim-side `encMetaHistory_…_step` reduce to known proven shapes.
-/
import SSBX.Foundation.Wen.MetaInterp.ExecuteBlock

namespace SSBX.Foundation.Wen.MetaInterp.ExecuteBlock

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell256
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.MetaInterp

/-! ## § 1  branchShiEq block (parameterized by sh : Shi, t : Nat) -/

/-- The `branchShiEq sh t` execute block: a 2-instruction program that
    emits the ISA-level branch opcode, then on the fall-through case
    jumps back to fetch.

    On the **branch-taken** case (`cur.2 = sh`) the inner branch opcode
    sets pc to the absolute target `t`, which in the global metaProg
    context routes to whichever block sits at offset `t`.  In the local
    block-only YiState used by `_local_effect_fallthrough`, that path
    falls off the end of the block (assuming `t ≥ 2`).

    There are |Shi| × |Nat| such blocks at the Lean level (the dispatcher
    routes based on the runtime sh and target cells; the `t` is also
    Lean-level because it is a compile-time absolute offset in the
    eventual metaProg layout). -/
def executeBlock_branchShiEq (sh : Shi) (t : Nat)
    (_offset fetchOffset : Nat) : List YiInstr :=
  [ YiInstr.branchShiEq sh t
  , YiInstr.jump fetchOffset
  ]

theorem executeBlock_branchShiEq_length (sh : Shi) (t : Nat)
    (offset fetchOffset : Nat) :
    (executeBlock_branchShiEq sh t offset fetchOffset).length = 2 := rfl

theorem executeBlock_branchShiEq_first (sh : Shi) (t : Nat)
    (offset fetchOffset : Nat) :
    (executeBlock_branchShiEq sh t offset fetchOffset)[0]? =
      some (YiInstr.branchShiEq sh t) := rfl

theorem executeBlock_branchShiEq_second (sh : Shi) (t : Nat)
    (offset fetchOffset : Nat) :
    (executeBlock_branchShiEq sh t offset fetchOffset)[1]? =
      some (YiInstr.jump fetchOffset) := rfl

/-- **Local effect (fall-through case)** for `branchShiEq sh t`.

    Precondition: the cur shi is **NOT** equal to `sh` (so the inner
    branch op falls through, advancing pc by 1).  Then the second
    instruction `jump fetchOffset` fires.

    Result: cur and history unchanged locally; pc → fetchOffset; not halted.

    This is the structurally identical case to `nop` in pc-update terms;
    the branch-taken case is deferred (see §0). -/
theorem executeBlock_branchShiEq_local_effect_fallthrough
    (sh : Shi) (t : Nat) (h : Hexagram) (sh₀ : Shi)
    (history : List Cell256) (fetchOffset offset : Nat)
    (h_neq : sh₀ ≠ sh) :
    let μ : YiState :=
      { cur := (h, sh₀)
        history := history
        pc := 0
        prog := executeBlock_branchShiEq sh t offset fetchOffset
        halted := false }
    let μ' := μ.runFuel 2
    μ'.cur = (h, sh₀)
    ∧ μ'.history = history
    ∧ μ'.pc = fetchOffset
    ∧ μ'.halted = false := by
  -- Unfold runFuel twice; first instr is `branchShiEq sh t`, condition
  -- is `(h, sh₀).2 = sh` i.e. `sh₀ = sh`, which is FALSE by `h_neq`.
  -- So pc bumps to 1, then `jump fetchOffset` fires.
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
          executeBlock_branchShiEq, h_neq]

/-- **Sim-side bridge for `branchShiEq sh t` (fall-through)**: when the
    sim's cur shi is NOT equal to `sh`, the branch op is a 1-step
    pc-incrementer just like `nop`.  Hence
    `encMetaHistory regHex sim.step` differs from
    `encMetaHistory regHex sim` by exactly one `regDataCell regHex`
    cell prepended at the head — the same shape as
    `encMetaHistory_nop_step`. -/
theorem encMetaHistory_branchShiEq_fallthrough_step
    (regHex : Hexagram) (sim : YiState) (sh : Shi) (t : Nat)
    (h_alive : sim.halted = false)
    (h_branch : sim.prog[sim.pc]? = some (.branchShiEq sh t))
    (h_neq : sim.cur.2 ≠ sh) :
    encMetaHistory regHex (sim.step) =
      regDataCell regHex :: encMetaHistory regHex sim := by
  -- sim.step = execute (.branchShiEq sh t) sim
  --         (condition is `sim.cur.2 = sh`, which is FALSE)
  --         = { sim with pc := sim.pc + 1 }
  have h_step : sim.step = { sim with pc := sim.pc + 1 } := by
    simp [YiState.step, h_alive, h_branch, YiState.execute, h_neq]
  rw [h_step]
  unfold encMetaHistory
  rw [encCounter_succ]
  simp [List.cons_append]

/-! ### Deferred: `branchShiEq sh t` — branch-taken case

The TRUE-branch case requires:

* **Local effect**: when `sim.cur.2 = sh`, the inner branch sets META.pc
  to the absolute target `t`.  In the local block-only YiState (`prog =
  executeBlock_branchShiEq sh t 0 fetchOffset` of length 2), this either:
  - falls off the end (`t ≥ 2`) → next step halts the local META;
  - re-enters the block (`t < 2`) → ill-defined absent the metaProg
    context.

  Neither describes the intended semantics — that arises only in the
  global metaProg where `t` is an offset into `metaInterpProg` and
  routes to another block.  Hence this case has no clean **block-local**
  statement; it is properly stated only as part of the global
  `BlockPre → BlockPost` simulation lemma.

* **Sim-side bridge**: when `sim.cur.2 = sh`, sim.step bumps `sim.pc`
  from its current value to `t`.  The encoding-side equivalent is

    encCounter regHex sim.pc  ↦  encCounter regHex t

  This is a **multi-cell rewrite**: the counter is `t+1` cells long
  vs the previous `sim.pc + 1` cells, which can shrink or grow.  No
  simple `regDataCell ::` head-prepend captures it.  This is the same
  engineering challenge `Block_Jump.lean` will face.

The full statement (left as a comment for Phase C subagents):

```lean
-- theorem encMetaHistory_branchShiEq_taken_step
--     (regHex : Hexagram) (sim : YiState) (sh : Shi) (t : Nat)
--     (h_alive : sim.halted = false)
--     (h_branch : sim.prog[sim.pc]? = some (.branchShiEq sh t))
--     (h_eq : sim.cur.2 = sh) :
--     encMetaHistory regHex sim.step =
--       encCounter regHex t ++
--       [encHaltedFlag regHex sim.halted] ++
--       encCounter regHex sim.history.length ++
--       sim.history ++
--       ProgEnc.encProg sim.prog := …
```
-/

/-! ## § 2  branchYaoEq block (parameterized by i j : Fin 6, t : Nat) -/

/-- The `branchYaoEq i j t` execute block: a 2-instruction program that
    emits the ISA-level branch opcode, then on the fall-through case
    jumps back to fetch.

    On the **branch-taken** case (`cur.1.yaoAt i = cur.1.yaoAt j`) the
    inner branch opcode sets pc to the absolute target `t` (same
    deferral story as `branchShiEq`).

    There are 6 × 6 × |Nat| such blocks at the Lean level (the
    dispatcher routes based on the runtime i, j, and target cells). -/
def executeBlock_branchYaoEq (i j : Fin 6) (t : Nat)
    (_offset fetchOffset : Nat) : List YiInstr :=
  [ YiInstr.branchYaoEq i j t
  , YiInstr.jump fetchOffset
  ]

theorem executeBlock_branchYaoEq_length (i j : Fin 6) (t : Nat)
    (offset fetchOffset : Nat) :
    (executeBlock_branchYaoEq i j t offset fetchOffset).length = 2 := rfl

theorem executeBlock_branchYaoEq_first (i j : Fin 6) (t : Nat)
    (offset fetchOffset : Nat) :
    (executeBlock_branchYaoEq i j t offset fetchOffset)[0]? =
      some (YiInstr.branchYaoEq i j t) := rfl

theorem executeBlock_branchYaoEq_second (i j : Fin 6) (t : Nat)
    (offset fetchOffset : Nat) :
    (executeBlock_branchYaoEq i j t offset fetchOffset)[1]? =
      some (YiInstr.jump fetchOffset) := rfl

/-- **Local effect (fall-through case)** for `branchYaoEq i j t`.

    Precondition: the cur hex's yao at `i` is NOT equal to its yao at
    `j` (so the inner branch op falls through, advancing pc by 1).
    Then the second instruction `jump fetchOffset` fires.

    Result: cur and history unchanged locally; pc → fetchOffset; not halted.

    Same structural shape as `executeBlock_branchShiEq_local_effect_fallthrough`. -/
theorem executeBlock_branchYaoEq_local_effect_fallthrough
    (i j : Fin 6) (t : Nat) (h : Hexagram) (sh : Shi)
    (history : List Cell256) (fetchOffset offset : Nat)
    (h_neq : h.yaoAt i ≠ h.yaoAt j) :
    let μ : YiState :=
      { cur := (h, sh)
        history := history
        pc := 0
        prog := executeBlock_branchYaoEq i j t offset fetchOffset
        halted := false }
    let μ' := μ.runFuel 2
    μ'.cur = (h, sh)
    ∧ μ'.history = history
    ∧ μ'.pc = fetchOffset
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [YiState.runFuel, YiState.step, YiState.execute,
          executeBlock_branchYaoEq, h_neq]

/-- **Sim-side bridge for `branchYaoEq i j t` (fall-through)**: when
    the sim's `cur.1.yaoAt i ≠ cur.1.yaoAt j`, the branch op is a
    1-step pc-incrementer just like `nop`.  Hence
    `encMetaHistory regHex sim.step` differs from
    `encMetaHistory regHex sim` by exactly one `regDataCell regHex`
    cell prepended at the head. -/
theorem encMetaHistory_branchYaoEq_fallthrough_step
    (regHex : Hexagram) (sim : YiState) (i j : Fin 6) (t : Nat)
    (h_alive : sim.halted = false)
    (h_branch : sim.prog[sim.pc]? = some (.branchYaoEq i j t))
    (h_neq : sim.cur.1.yaoAt i ≠ sim.cur.1.yaoAt j) :
    encMetaHistory regHex (sim.step) =
      regDataCell regHex :: encMetaHistory regHex sim := by
  -- sim.step = execute (.branchYaoEq i j t) sim
  --         (condition is `sim.cur.1.yaoAt i = sim.cur.1.yaoAt j`, FALSE)
  --         = { sim with pc := sim.pc + 1 }
  have h_step : sim.step = { sim with pc := sim.pc + 1 } := by
    simp [YiState.step, h_alive, h_branch, YiState.execute, h_neq]
  rw [h_step]
  unfold encMetaHistory
  rw [encCounter_succ]
  simp [List.cons_append]

/-! ### Deferred: `branchYaoEq i j t` — branch-taken case

Same shape as the `branchShiEq` deferred section: locally meaningless
without the metaProg context, and sim-side bridge requires dynamic
pc-counter rewrite (multi-cell, same as Block_Jump.lean). -/

end SSBX.Foundation.Wen.MetaInterp.ExecuteBlock
