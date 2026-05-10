/-
# OuterLoop — entry point + halted-flag discipline

## Role within `metaInterpProg`

Per the Phase B / C architecture (see `ExecuteBlock.lean §A` and the
roadmap in `MetaInterp.lean`), the META program decomposes as:

```
metaInterpProg
  = prologueProg                        -- §6 of MetaInterp.lean
 ++ outerLoopEntry fetchOffset          -- ← THIS FILE
 ++ fetchProg fetchOffset               -- decode opcode at sim.pc
 ++ dispatchProg dispatchOffset         -- 12-way branch on tag
 ++ executeBlock_<op> ...               -- 12 per-opcode blocks
 ++ haltProg                            -- terminal segment when sim halts
```

The **outer loop** is the small block sitting between the prologue and
the fetch.  Its job is to transfer control from prologue-end to fetch
and to give every executeBlock a uniform return target (each block
ends with `YiInstr.jump fetchOffset`, so once the loop is entered the
META-program never re-passes through the prologue).

## Design choice: halt detection lives inside fetch, not here

A naïve outer loop would, every iteration, peek at the halted-flag
cell of `META.history` and branch on it.  But reading that flag
requires a destructive walk through the pc-counter region (Shi.jin ×
sim.pc data cells + 1 marker) to expose it on top of history, then a
restore.  That is the same kind of destructive-walk logic that
`fetchProg` must perform anyway in order to read `prog[sim.pc]`
(buried at the bottom of `META.history`).

We therefore adopt the **fetch-detects-halt** convention:

  > `fetchProg` is the single point of truth for halt detection.
  > During its descent through META.history, if it observes the
  > halted-flag set to `Shi.ji`, it routes META to `haltProg`
  > (which performs `YiInstr.halt`).  Otherwise it continues with
  > opcode decoding and routes to `dispatchProg`.

Under this convention the outer loop entry collapses to a **single
unconditional jump** — exactly the closing instruction every
executeBlock already emits.  The structural loop is therefore the
back-edge `jump fetchOffset` repeated by each block; the entry
"loop block" is just a one-instruction dispatch that gets control
from the prologue into the fetch on the very first iteration.

## What this file proves

1. `outerLoopEntry fetchOffset` is `[YiInstr.jump fetchOffset]`
   (length = 1).
2. Running the entry from a META state at `pc = 0` advances `pc`
   to `fetchOffset` in exactly 1 fuel step, preserving everything
   else.
3. A "loop discipline" lemma showing the back-edge convention:
   any META state whose `pc` is set to `fetchOffset` is, by
   definition, ready for the next fetch iteration — i.e., the
   outer loop is closed by every executeBlock's final
   `jump fetchOffset` instruction.

The halt-detection design is documented but not implemented here;
its proof obligations belong to `fetchProg` (a future Wave 3 file).

## What this file does NOT contain

- A halt-detection subroutine.  See "Design choice" above; this is
  fetch's responsibility.
- A simulation lemma against the encoded sim-state.  Because the
  outer loop is a pure pc-routing block (it does not touch
  `META.cur`, `META.history`, or `META.halted`), there is no
  sim-side bridge to prove — the encoded state is invariant under
  the entry transition.
-/
import SSBX.Foundation.Wen.MetaInterp

namespace SSBX.Foundation.Wen.MetaInterp.OuterLoop

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell256
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.MetaInterp

/-! ## § 1  The outer-loop entry block -/

/-- The outer loop entry: a single unconditional jump to `fetchOffset`.

    This is the **routing block** between the prologue and the fetch.
    On the first iteration it transfers control from the end of the
    prologue (pc = `prologueProg.length` = 5) into the fetch loop;
    on subsequent iterations it is bypassed (each executeBlock's
    closing `YiInstr.jump fetchOffset` jumps directly past it). -/
def outerLoopEntry (fetchOffset : Nat) : List YiInstr :=
  [ YiInstr.jump fetchOffset ]

theorem outerLoopEntry_length (fetchOffset : Nat) :
    (outerLoopEntry fetchOffset).length = 1 := rfl

theorem outerLoopEntry_first (fetchOffset : Nat) :
    (outerLoopEntry fetchOffset)[0]? = some (YiInstr.jump fetchOffset) := rfl

theorem outerLoopEntry_last (fetchOffset : Nat) :
    (outerLoopEntry fetchOffset).getLast? = some (YiInstr.jump fetchOffset) := rfl

/-! ## § 2  Local-effect simulation lemma

The outer-loop entry is a pure pc-transition: in 1 fuel step from
a state at `pc = 0` of `outerLoopEntry fetchOffset`, the META
machine advances to `pc = fetchOffset` with cur, history, and
halted unchanged. -/

/-- **Local effect**: a 1-fuel run of `outerLoopEntry fetchOffset`
    from `pc = 0` of the standalone block program advances `pc` to
    `fetchOffset` and preserves everything else. -/
theorem outerLoopEntry_local_effect
    (cur : Cell256) (history : List Cell256) (fetchOffset : Nat) :
    let μ : YiState :=
      { cur := cur
        history := history
        pc := 0
        prog := outerLoopEntry fetchOffset
        halted := false }
    let μ' := μ.runFuel 1
    μ'.cur = cur
    ∧ μ'.history = history
    ∧ μ'.pc = fetchOffset
    ∧ μ'.prog = outerLoopEntry fetchOffset
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-! ## § 3  Loop-discipline structural hypothesis

We bundle the structural hypothesis "the outer-loop entry sits at
`offset` inside `metaProg`" so downstream proofs can refer to it
uniformly. -/

/-- Predicate: `metaProg` contains `outerLoopEntry fetchOffset` at
    position `offset`.  This is the structural hypothesis a
    composition lemma would assume to discharge `metaProg[offset]?`
    inspection at the entry point. -/
def MetaProgHasOuterLoopEntryAt
    (offset fetchOffset : Nat) (metaProg : List YiInstr) : Prop :=
  metaProg[offset]? = some (YiInstr.jump fetchOffset)

/-! ## § 4  Composition lemma: entry inside a global META program

    With the structural hypothesis in place, one fuel step from
    `pc = offset` advances META to `pc = fetchOffset` exactly as in
    the local-effect lemma.  This is the form composition lemmas
    will use to stitch the prologue → outer-loop-entry → fetch chain
    together. -/

/-- **Composition form** of the entry transition: in any META state
    whose `prog` contains the entry at `offset`, one step from
    `pc = offset` advances pc to `fetchOffset` and preserves all
    other fields. -/
theorem outerLoopEntry_step
    (offset fetchOffset : Nat) (metaProg : List YiInstr)
    (h_entry : MetaProgHasOuterLoopEntryAt offset fetchOffset metaProg)
    (μ : YiState)
    (h_pc      : μ.pc      = offset)
    (h_prog    : μ.prog    = metaProg)
    (h_halted  : μ.halted  = false) :
    μ.step =
      { cur     := μ.cur
        history := μ.history
        pc      := fetchOffset
        prog    := metaProg
        halted  := false } := by
  unfold YiState.step
  rw [h_halted]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [h_pc, h_prog, h_entry]
  -- Goal: YiState.execute (jump fetchOffset) μ = { ..., pc := fetchOffset, ... }.
  -- The execute case for `jump target` is `{ μ with pc := target }`, which
  -- preserves cur, history, halted and overrides pc and (per h_prog) prog.
  show ({ μ with pc := fetchOffset } : YiState) =
    { cur := μ.cur, history := μ.history, pc := fetchOffset,
      prog := metaProg, halted := false }
  rw [← h_prog, ← h_halted]

/-! ## § 5  Loop-back convention

  Each executeBlock closes with `YiInstr.jump fetchOffset`.  The
  outer loop is therefore **structurally closed** by each block —
  there is no separate back-edge instruction in this file.  We
  record this convention as a comment-level invariant; no further
  Lean-level statement is needed beyond the `outerLoopEntry_step`
  lemma (which characterizes the same `jump fetchOffset` transition
  used by every executeBlock).
-/

end SSBX.Foundation.Wen.MetaInterp.OuterLoop
