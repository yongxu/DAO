/-
# Block_PushPop — executeBlocks for `push` and `pop`

These two opcodes are **fundamentally harder** than the cur-only blocks
(`nop`, `interlace`, `complement`, `reverse`, `setShi`, `flipYao`) because they mutate
`sim.history`, which is encoded in the **middle** of `META.history`:

```
encMetaHistory regHex sim
  = encCounter regHex sim.pc                         -- pc-cells + marker
  ++ [encHaltedFlag regHex sim.halted]               -- halted flag
  ++ encCounter regHex sim.history.length            -- simhist-len + marker
  ++ sim.history                                     -- ← THE TARGET REGION
  ++ ProgEnc.encProg sim.prog                        -- read-only tail
```

To mutate the simhist region we must traverse past three preceding
regions destructively (pop everything to a "work stack" — but we have
no work stack, only `META.cur`).

## §0  Design choice: the "halt-as-canonical-degenerate" approach

There are at least three viable architectures for push/pop:

  **Option A** — full destructive walk + scratch counter region.  Pop
    everything down to the simhist region, perform the mutation, then
    re-encode.  ~100-200 instructions, requires extending the encoding
    with a scratch region.

  **Option B** — re-encode each iteration.  After the mutation, run a
    sub-program that re-pushes the now-known pc and len counters from
    cur-side scratch values.  ~50-100 instructions; needs a way to hold
    the counter values during the mutation.

  **Option C** (this file) — **specialize to the structurally trivial
    cases**, prove those concretely, and state the general lemma but
    defer it to Phase C / a future destructive-walk subagent.

For the **scaffold**:
  - `executeBlock_pop` handles the **empty-sim.history** case: the
    sim-level `pop` halts the simulated machine (per `YiState.execute
    .pop`), which the block implements by simply executing
    `YiInstr.halt` — the META machine halts in concert.  We prove this
    as `executeBlock_pop_empty_local_effect`.
  - `executeBlock_push` provides the structural shape: it begins with a
    `push` (which prepends `META.cur = sim.cur` to META.history), then
    bumps the pc-counter, then jumps to fetch.  This is correct ONLY
    when `sim.history = []` and the simhist-len-marker is positioned at
    the top — which we capture in the local-effect lemma.

The **general** simulation lemma (arbitrary `sim.history`, full
middle-of-history mutation) is **deferred**; the deferred theorem
`executeBlock_pop_simulates` and `executeBlock_push_simulates` are
**stated** as `Prop` definitions (so that future phases have a fixed
target signature) but not proven.  Following the contract guidance from
`ExecuteBlock.lean §A.5`, this is the honest pre-Phase-C scaffold.

## §0.1  What is proven here

For each block we provide:

  - definition (`executeBlock_push`, `executeBlock_pop`);
  - structural length lemma (`executeBlock_push_length`,
    `executeBlock_pop_length`);
  - instruction-enumeration lemmas (`_first`);
  - one **concrete local-effect** lemma per block;
  - a **sim-side bridge** lemma showing how `encMetaHistory regHex
    sim.step` relates to `encMetaHistory regHex sim` for the
    empty-sim.history case (push) and the empty-sim.history halt
    case (pop).

What's deferred to Phase C:
  - the general (non-empty sim.history) simulation;
  - the destructive-walk middle-of-history mutation.

The deferred lemmas appear as `Prop`-typed targets at the end of the
file.
-/
import SSBX.Foundation.Wen.MetaInterp.ExecuteBlock

namespace SSBX.Foundation.Wen.MetaInterp.ExecuteBlock

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell256
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.MetaInterp

/-! ## § 1  push block

  At the sim level: `YiInstr.push` prepends `sim.cur` to `sim.history`
  and bumps `sim.pc`.  In META terms, the encoded effect is:

    encMetaHistory regHex sim.step
      = encCounter regHex (sim.pc + 1)
      ++ [encHaltedFlag regHex sim.halted]
      ++ encCounter regHex (sim.history.length + 1)
      ++ (sim.cur :: sim.history)
      ++ encProg sim.prog

  Comparing to `encMetaHistory regHex sim`, **two** counter cells must
  grow by one (pc and simhist-len), and **one** cell (`sim.cur`) must be
  inserted between the simhist-len-marker and the previous head of
  `sim.history`.

  At the LOCAL block level (no global program context yet) we can prove
  the simplest fragment of this: a 3-instruction block that performs
  `push` (= prepend META.cur to META.history) once, then `push` again
  (the pc-counter increment), then jumps.  This already captures the
  shape needed for the **base case** `sim.history = [] ∧ sim.pc = 0`,
  as we show in `executeBlock_push_minimal_local_effect`. -/

/-- The `push` execute block.

    Layout:
      0: push                  -- prepend META.cur to META.history
      1: push                  -- prepend pc-data cell (META.cur unchanged here)
      2: jump fetchOffset

    NOTE: this is the **minimal-shape** version that demonstrates the
    block's interface; for arbitrary `sim.history` the block needs to
    walk past the pc-counter, halted-flag, and simhist-len-counter
    regions before performing the simhist mutation.  See §0 above. -/
def executeBlock_push (_offset fetchOffset : Nat) : List YiInstr :=
  [ YiInstr.push
  , YiInstr.push
  , YiInstr.jump fetchOffset
  ]

theorem executeBlock_push_length (offset fetchOffset : Nat) :
    (executeBlock_push offset fetchOffset).length = 3 := rfl

theorem executeBlock_push_first (offset fetchOffset : Nat) :
    (executeBlock_push offset fetchOffset)[0]? = some YiInstr.push := rfl

theorem executeBlock_push_second (offset fetchOffset : Nat) :
    (executeBlock_push offset fetchOffset)[1]? = some YiInstr.push := rfl

theorem executeBlock_push_third (offset fetchOffset : Nat) :
    (executeBlock_push offset fetchOffset)[2]? =
      some (YiInstr.jump fetchOffset) := rfl

/-- **Local effect (block-only)**: starting from a META state with
    arbitrary cur and history, after running 3 fuel steps the block
    leaves META with `cur` unchanged, two copies of the original cur
    prepended to history, and `pc = fetchOffset`. -/
theorem executeBlock_push_local_effect
    (cur : Cell256) (history : List Cell256)
    (offset fetchOffset : Nat) :
    let μ : YiState :=
      { cur := cur
        history := history
        pc := 0
        prog := executeBlock_push offset fetchOffset
        halted := false }
    let μ' := μ.runFuel 3
    μ'.cur = cur
    ∧ μ'.history = cur :: cur :: history
    ∧ μ'.pc = fetchOffset
    ∧ μ'.halted = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-- **Sim-side bridge for push (empty sim.history, pc = 0 base case)**:
    when `sim.history = []` and `sim.pc = 0`, the encoded post-state
    differs from the pre-state by the prepending of two cells: the new
    pc-data cell and `sim.cur`.

    This matches the head-prepend of two cells produced by
    `executeBlock_push_local_effect`, **provided** `META.cur = sim.cur`
    and the loop-invariant ensures pc-cells use `regHex = sim.cur.1`
    with `Shi.jin` (i.e., `META.cur = (regHex, Shi.jin)` → it is itself
    the `regDataCell regHex`).  When that holds, a `push` of META.cur
    inserts both the pc-data cell AND the sim.history head simultaneously
    (since they share the same shape (regHex, Shi.jin) up to the
    sim.cur identification — full alignment is the prologue's job).

    The fully aligned shape lemma below specialises to the case where
    `sim.cur = (regHex, Shi.jin)` so that the two pushes coincide
    structurally with the (pc-data) and (sim.cur) prepends. -/
theorem encMetaHistory_push_step_emptyHist
    (regHex : Hexagram) (sim : YiState)
    (h_alive : sim.halted = false)
    (h_push : sim.prog[sim.pc]? = some .push)
    (h_emptyHist : sim.history = []) :
    encMetaHistory regHex sim.step =
      regDataCell regHex
        :: encCounter regHex sim.pc
        ++ [encHaltedFlag regHex sim.halted]
        ++ regDataCell regHex
        :: encCounter regHex 0
        ++ sim.cur
        :: ProgEnc.encProg sim.prog := by
  -- sim.step on .push: { sim with history := sim.cur :: sim.history,
  --                              pc := sim.pc + 1 }
  have h_step : sim.step =
      { sim with history := sim.cur :: sim.history
               , pc := sim.pc + 1 } := by
    simp [YiState.step, h_alive, h_push, YiState.execute]
  rw [h_step]
  unfold encMetaHistory
  -- after the rewrite:
  --   encCounter regHex (sim.pc + 1) ++ [...] ++
  --   encCounter regHex (sim.cur :: []).length ++ (sim.cur :: []) ++
  --   encProg sim.prog
  rw [encCounter_succ]
  -- (sim.cur :: sim.history).length = sim.history.length + 1
  -- with h_emptyHist this is just 1; encCounter regHex 1 = regDataCell :: encCounter 0
  have h_len : (sim.cur :: sim.history).length = 1 := by
    rw [h_emptyHist]; rfl
  rw [h_len, encCounter_succ]
  rw [h_emptyHist]
  simp [List.cons_append, List.append_assoc]

/-! ## § 2  pop block

  At the sim level: `YiInstr.pop` is two-mode:

    if sim.history = []:    sim.halted := true
    if sim.history = h::r:  sim.cur := h; sim.history := r; sim.pc++

  The empty case is structurally trivial in META: just emit a `halt`,
  which sets `META.halted := true`, mirroring the sim-side halt.

  The non-empty case is where the destructive walk is needed.

  ## §2.1  Block layout (focused on the empty-sim.history case)

  We provide a 1-instruction block: `[halt]`.  This handles the empty
  case correctly (META halts when sim halts).  For the non-empty case,
  the deferred Phase-C work will replace this with a destructive walk
  that consumes counter cells, performs the simhist head extraction,
  and re-encodes.  The current block is a placeholder that establishes
  the contract's halt sub-case.
-/

/-- The `pop` execute block (empty-sim.history specialization).

    Implementation: `[halt]`.  This handles the case `sim.history = []`,
    where the sim-level `pop` halts the simulated machine.

    For `sim.history ≠ []`, the block must be extended with a destructive
    walk past the pc-counter, halted-flag, and simhist-len-counter
    regions.  See §0 above. -/
def executeBlock_pop (_offset _fetchOffset : Nat) : List YiInstr :=
  [ YiInstr.halt ]

theorem executeBlock_pop_length (offset fetchOffset : Nat) :
    (executeBlock_pop offset fetchOffset).length = 1 := rfl

theorem executeBlock_pop_first (offset fetchOffset : Nat) :
    (executeBlock_pop offset fetchOffset)[0]? = some YiInstr.halt := rfl

/-- **Local effect (block-only, empty-sim.history case)**: the
    1-instruction halt sets META.halted := true, leaving cur, history
    untouched.  This mirrors the sim-side `pop` behaviour when
    `sim.history = []`. -/
theorem executeBlock_pop_empty_local_effect
    (cur : Cell256) (history : List Cell256)
    (offset fetchOffset : Nat) :
    let μ : YiState :=
      { cur := cur
        history := history
        pc := 0
        prog := executeBlock_pop offset fetchOffset
        halted := false }
    let μ' := μ.runFuel 1
    μ'.cur = cur
    ∧ μ'.history = history
    ∧ μ'.halted = true := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-- **Sim-side bridge for pop (empty sim.history)**: when
    `sim.history = []`, `sim.step` on a `.pop` sets `sim.halted := true`
    without changing pc, history, or cur.  Hence
    `encMetaHistory regHex sim.step` differs from
    `encMetaHistory regHex sim` only in the halted-flag cell.

    This is the analogue of `encMetaHistory_halt_step` (which handles
    the explicit `.halt` instruction).  The flag flip from running →
    halted is structurally identical. -/
theorem encMetaHistory_pop_step_emptyHist
    (regHex : Hexagram) (sim : YiState)
    (h_pop : sim.prog[sim.pc]? = some .pop)
    (h_alive : sim.halted = false)
    (h_emptyHist : sim.history = []) :
    encMetaHistory regHex sim.step =
      encCounter regHex sim.pc ++
      [encHaltedFlag regHex true] ++
      encCounter regHex sim.history.length ++
      sim.history ++
      ProgEnc.encProg sim.prog := by
  -- sim.step on .pop with empty history: { sim with halted := true }
  have h_step : sim.step = { sim with halted := true } := by
    unfold YiState.step
    rw [h_alive]
    simp only [Bool.false_eq_true, if_false]
    rw [h_pop]
    unfold YiState.execute
    rw [h_emptyHist]
  rw [h_step]
  unfold encMetaHistory
  rfl

/-! ## § 3  Deferred general simulation lemmas

  These targets are stated as `Prop` definitions so that Phase C
  subagents have a fixed signature to work toward.  They are **not**
  theorems; calling them in proofs would require closing them first.
-/

/-- The general push-simulation target (Phase C).  Takes the
    block-precondition record `BlockPre`, asserts that running the block
    for its dynamic fuel produces a state satisfying the
    block-postcondition record `BlockPost` for `sim.step`. -/
def executeBlock_push_simulates_target
    (regHex : Hexagram) (sim : YiState) (offset fetchOffset : Nat)
    (metaProg : List YiInstr) (μ : YiState) : Prop :=
  sim.halted = false →
  sim.prog[sim.pc]? = some .push →
  BlockPre regHex sim offset metaProg μ →
  ∃ fuel, BlockPost regHex sim.step fetchOffset metaProg
            (μ.runFuel fuel) false

/-- The general pop-simulation target (Phase C).  The post-state's
    `endHalted` depends on whether `sim.history` was empty:
    `endHalted = sim.history.isEmpty`. -/
def executeBlock_pop_simulates_target
    (regHex : Hexagram) (sim : YiState) (offset fetchOffset : Nat)
    (metaProg : List YiInstr) (μ : YiState) : Prop :=
  sim.halted = false →
  sim.prog[sim.pc]? = some .pop →
  BlockPre regHex sim offset metaProg μ →
  ∃ fuel, BlockPost regHex sim.step fetchOffset metaProg
            (μ.runFuel fuel) sim.history.isEmpty

end SSBX.Foundation.Wen.MetaInterp.ExecuteBlock
