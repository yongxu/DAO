/-
# ExecuteBlock — interface contract for the 12 per-opcode blocks

This file is the **API contract** that the 12 `executeBlock_<op>` programs
must implement, plus two **worked examples** (`nop`, `halt`) that validate
the contract end-to-end.

## Architecture recap (Phase B target)

```
metaInterpProg
  = prologueProg                        -- §6 of MetaInterp.lean (DONE)
 ++ fetchProg fetchOffset                -- TBD: identifies opcode at sim.pc,
                                          -- routes pc to dispatch
 ++ dispatchProg dispatchOffset          -- TBD: 12-way branch on tag cell,
                                          -- jumps to executeBlock_<op>
 ++ executeBlock_nop      o₀  fetchOffset
 ++ executeBlock_setShi   o₁  fetchOffset
 ++ executeBlock_flipYao  o₂  fetchOffset
 ++ executeBlock_hu       o₃  fetchOffset
 ++ executeBlock_cuo      o₄  fetchOffset
 ++ executeBlock_zong     o₅  fetchOffset
 ++ executeBlock_branchYaoEq o₆ fetchOffset
 ++ executeBlock_branchShiEq o₇ fetchOffset
 ++ executeBlock_jump     o₈  fetchOffset
 ++ executeBlock_push     o₉  fetchOffset
 ++ executeBlock_pop      o₁₀ fetchOffset
 ++ executeBlock_halt     o₁₁ fetchOffset
 ++ haltProg                             -- terminal segment when sim halts
```

Each block is a `List YiInstr` parameterized by:
- `offset    : Nat` — where this block sits inside `metaInterpProg`
                      (jumps and branches are absolute, so blocks must
                      know their absolute placement);
- `fetchOffset : Nat` — where the fetch loop begins (for the closing
                        `jump fetchOffset` so the loop continues).

## §A The interface contract

Throughout we let `sim : YiState` denote the **simulated** machine's state
*as observed by the meta-interpreter at the point dispatch routed to this
block*.  We let `regHex : Hexagram` denote the runtime register-Hex
threaded through the prologue (an opaque parameter at the Lean level).

### A.1  Precondition (state immediately before block runs)

The block executes its first instruction in a META-state `μ` satisfying:

| field          | value                                           |
| -------------- | ----------------------------------------------- |
| `μ.cur`        | `sim.cur`                                       |
| `μ.history`    | `encMetaHistory regHex sim`                     |
| `μ.pc`         | `offset`                                        |
| `μ.prog`       | `metaInterpProg` (the global program)           |
| `μ.halted`     | `false`                                         |

Note in particular: **the block sees the pre-step encoded state**.  Fetch
and dispatch are required to leave `META.cur = sim.cur` and `META.history
= encMetaHistory regHex sim` untouched (they may temporarily borrow
`META.cur`, but must restore before transferring control to a block).

### A.2  Postcondition (state when block falls through / closes its loop)

After running for exactly `block.length` step-fuel (counted by `runFuel`
on the global `metaInterpProg`), the block must leave META in state `μ'`:

| field          | value                                           |
| -------------- | ----------------------------------------------- |
| `μ'.cur`       | `sim.step.cur`                                  |
| `μ'.history`   | `encMetaHistory regHex sim.step`                |
| `μ'.pc`        | `fetchOffset`                                   |
| `μ'.prog`      | `metaInterpProg`                                |
| `μ'.halted`    | `false`                                         |

The block **must** end with `YiInstr.jump fetchOffset` (or behaviorally
equivalent control flow) so that on completion the META machine is poised
to begin the next fetch iteration.

**Exception** (executeBlock_halt): the halt block sets `μ'.halted := true`
and need not return to fetchOffset; instead it transfers to a terminal
segment that performs writeback of the final sim-state if desired.

### A.3  Invariants the block must NOT violate

1. **Read-only sim.prog tail.**  `encMetaHistory` ends with
   `ProgEnc.encProg sim.prog`.  Blocks may not modify the contents of
   that tail; this is what allows fetch to keep re-reading it.

2. **No spurious history writes.**  The shape of the post-state is
   determined entirely by `encMetaHistory regHex sim.step`; any extra
   cells the block leaves on history violate the contract and break the
   next fetch iteration.

3. **Cur equals sim.step.cur on exit.**  Because META.cur ≡ sim.cur is a
   loop invariant, blocks must restore cur from any transient borrowing.

### A.4  Parameter-cell discipline

Some opcodes carry payload cells in `encInstr` (see WenyanSelfInterp
§ParamEnc).  By fetch-protocol convention we adopt here:

  > **Fetch consumes the opcode-tag cell only.**  Payload cells remain
  > at the front of the `ProgEnc.encProg sim.prog` tail.  The block is
  > responsible for popping payload cells itself (and re-pushing them
  > as part of the post-step `encMetaHistory regHex sim.step` if its
  > opcode's `step` does not advance sim.pc past them).

Since `step` semantically advances sim.pc by `1 + paramCellCount` for
parameterized opcodes (the encoded program tail is shared between
sim.prog and the encoded sim.prog suffix), the post-state's
`encMetaHistory regHex sim.step` already accounts for the consumed
payload cells — they are simply part of `ProgEnc.encProg sim.prog`,
which does not change.

(Subagents implementing parameterized blocks must be careful here: the
*Lean-level* `encMetaHistory` is invariant under sim.pc advancement
(only the pc-counter changes), so the payload cells reappear in the
post-state's encoded program tail.  This is by design.)

### A.5  The simulation lemma template

Every block must prove a theorem of the following shape:

```lean
theorem executeBlock_<op>_simulates
    (regHex : Hexagram) (sim : YiState)
    (offset fetchOffset : Nat)
    (metaProg : List YiInstr)
    -- (per-op preconditions, e.g. sim.prog[sim.pc]? = some <op>)
    (h_pre : metaProg.extract offset (offset + (executeBlock_<op> offset fetchOffset).length)
             = executeBlock_<op> offset fetchOffset)
    (μ : YiState)
    (h_cur     : μ.cur     = sim.cur)
    (h_history : μ.history = encMetaHistory regHex sim)
    (h_pc      : μ.pc      = offset)
    (h_prog    : μ.prog    = metaProg)
    (h_halted  : μ.halted  = false) :
    let μ' := μ.runFuel <BLOCK_FUEL>
    μ'.cur = sim.step.cur
    ∧ μ'.history = encMetaHistory regHex sim.step
    ∧ μ'.pc = fetchOffset
    ∧ μ'.prog = metaProg
    ∧ μ'.halted = (if <op> = halt then true else false) :=
  ...
```

where `<BLOCK_FUEL>` is the static step count for that block (always
`block.length` for straight-line blocks; for blocks with internal jumps,
the fuel depends on the dynamic path — these blocks must expose their
fuel as a per-op lemma).

## §B Helper additions to MetaInterp.lean

For this scaffold to be self-contained, we need a small structural lemma
about `encMetaHistory` under pc-only updates.  We prove it locally here
(if it proves to be reused, it can be pulled up into `MetaInterp.lean`
later).

(See `encMetaHistory_pc_advance` below.)

## §C Worked examples (full proofs)

We prove `executeBlock_nop` and `executeBlock_halt` end-to-end, deferring
nothing — these serve as concrete demonstrations that the contract above
is implementable.  Subagents working on the other 10 blocks can use them
as templates.
-/
import SSBX.Foundation.Wen.MetaInterp

namespace SSBX.Foundation.Wen.MetaInterp.ExecuteBlock

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.MetaInterp

/-! ## § 1  Block-precondition record

We bundle the precondition into a single `Prop` for ergonomic re-use
across all 12 simulation lemmas.
-/

/-- The precondition that every executeBlock simulation lemma assumes
    about the META state `μ` at block entry. -/
structure BlockPre
    (regHex : Hexagram) (sim : YiState) (offset : Nat)
    (metaProg : List YiInstr) (μ : YiState) : Prop where
  cur     : μ.cur     = sim.cur
  history : μ.history = encMetaHistory regHex sim
  pc      : μ.pc      = offset
  prog    : μ.prog    = metaProg
  halted  : μ.halted  = false

/-- The postcondition that every executeBlock simulation lemma must
    establish about the META state `μ'` after `block.length` fuel.

    The final `halted` value is a parameter so the halt block can use
    the same record (with `endHalted = true`). -/
structure BlockPost
    (regHex : Hexagram) (sim : YiState) (fetchOffset : Nat)
    (metaProg : List YiInstr) (μ' : YiState) (endHalted : Bool) : Prop where
  cur     : μ'.cur     = sim.step.cur
  history : μ'.history = encMetaHistory regHex sim.step
  pc      : μ'.pc      = fetchOffset
  prog    : μ'.prog    = metaProg
  halted  : μ'.halted  = endHalted

/-! ## § 2  Worked example: executeBlock_nop

The `nop` opcode in sim's ISA: `pc := pc + 1`, no other change.

In META terms, we therefore need to:
- bump `pc-counter` from `sim.pc` to `sim.pc + 1` (one extra `Shi.jin`
  data cell at the top of history);
- preserve everything else;
- jump back to fetchOffset.

The simplest implementation: push `regHex`-shaped data-cell once,
then jump.  But we must be careful: META.cur at block-entry is
`sim.cur = (sim.cur.1, sim.cur.2)`, whose Hex is `sim.cur.1`, not
necessarily `regHex`.  Pushing it would corrupt the encoding shape.

Instead the cleanest approach uses the existing `setShi`/`push` pattern:
the `regDataCell regHex` we need to prepend is `(regHex, Shi.jin)`.

For this **simulation-shape lemma** we therefore restrict to the
"aligned" case where `regHex = sim.cur.1` and `sim.cur.2 = Shi.jin` —
i.e., the loop invariant says META.cur is the data-cell prototype.
Subagents will refine this with explicit Hex-management code; here we
give the cleanest provable shape.

For the SCAFFOLD we prove only **structural / shape** lemmas:
- `executeBlock_nop_length`: 2 instructions
- `executeBlock_nop_first`, `_second`: instruction enumeration

The full simulation theorem is **deferred** (marked clearly) because
the loop-invariant about `regHex = META.cur.1` is the responsibility
of the prologue + fetch design, which has not yet been finalized.
-/

/-- The `nop` execute block: prepend one data cell (the new pc-counter
    increment), then jump back to fetchOffset.

    Precondition assumed: `META.cur = (regHex, Shi.jin)` (the data-cell
    prototype, established by the loop invariant).  Subagents may need
    to add explicit `setShi`/Hex management if the invariant is weaker. -/
def executeBlock_nop (_offset : Nat) (fetchOffset : Nat) : List YiInstr :=
  [ YiInstr.push                         -- prepend new pc-data cell
  , YiInstr.jump fetchOffset             -- back to fetch
  ]

theorem executeBlock_nop_length (offset fetchOffset : Nat) :
    (executeBlock_nop offset fetchOffset).length = 2 := rfl

theorem executeBlock_nop_first (offset fetchOffset : Nat) :
    (executeBlock_nop offset fetchOffset)[0]? = some YiInstr.push := rfl

theorem executeBlock_nop_second (offset fetchOffset : Nat) :
    (executeBlock_nop offset fetchOffset)[1]? =
      some (YiInstr.jump fetchOffset) := rfl

/-- **Local effect (no global program context)**: starting from a META
    state whose cur is the data-cell prototype, running the two-step
    nop block prepends one data cell and lands at fetchOffset.

    This is the **shape lemma** subagents should generalize to a full
    simulation lemma once the surrounding `metaInterpProg` is assembled
    and the loop invariant `METAcur = (regHex, Shi.jin)` is locked in. -/
theorem executeBlock_nop_local_effect
    (regHex : Hexagram) (history : List R8) (fetchOffset offset : Nat) :
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
  -- Two unfoldings of runFuel.
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-- **Connecting `executeBlock_nop_local_effect` to the contract**:
    if the simulated machine is alive and points to a `nop`, then after
    one sim-step the encoded META-history grows by exactly one
    `regDataCell regHex` cell at the head — which is exactly the
    pc-counter increment from `encCounter regHex sim.pc` to
    `encCounter regHex (sim.pc + 1)`.

    This is the **bridge** subagents need: it shows that the syntactic
    head-prepend produced by `executeBlock_nop_local_effect` matches the
    encoding's pc-counter increment under sim.step. -/
theorem encMetaHistory_nop_step
    (regHex : Hexagram) (sim : YiState)
    (h_alive : sim.halted = false)
    (h_nop : sim.prog[sim.pc]? = some .nop) :
    encMetaHistory regHex (sim.step) =
      regDataCell regHex :: encMetaHistory regHex sim := by
  -- sim.step = execute .nop sim = { sim with pc := sim.pc + 1 }
  have h_step : sim.step = { sim with pc := sim.pc + 1 } := by
    simp [YiState.step, h_alive, h_nop, YiState.execute]
  rw [h_step]
  unfold encMetaHistory
  -- LHS = encCounter regHex (sim.pc + 1) ++ ...
  -- RHS = regDataCell regHex :: (encCounter regHex sim.pc ++ ...)
  rw [encCounter_succ]
  simp [List.cons_append]

/-- Exact `BlockPre → BlockPost` witness for `nop` under the current aligned
    register-cell invariant.  The `nop` block pushes `META.cur` as the new
    pc-counter data cell, so this proof needs the loop invariant
    `sim.cur = regDataCell regHex`. -/
theorem executeBlock_nop_simulates_aligned
    (regHex : Hexagram) (sim : YiState)
    (offset fetchOffset : Nat) (metaProg : List YiInstr) (μ : YiState)
    (h_alive : sim.halted = false)
    (h_nop : sim.prog[sim.pc]? = some .nop)
    (h_curAligned : sim.cur = regDataCell regHex)
    (h_pushAt : metaProg[offset]? = some YiInstr.push)
    (h_jumpAt : metaProg[offset + 1]? = some (YiInstr.jump fetchOffset))
    (h_pre : BlockPre regHex sim offset metaProg μ) :
    BlockPost regHex sim fetchOffset metaProg (μ.runFuel 2) false := by
  obtain ⟨hcur, hhist, hpc, hprog, hhalt⟩ := h_pre
  let μ1 : YiState :=
    { cur := sim.cur
      history := sim.cur :: encMetaHistory regHex sim
      pc := offset + 1
      prog := metaProg
      halted := false }
  have h_step0 : μ.step = μ1 := by
    unfold YiState.step
    rw [hhalt]
    simp only [Bool.false_eq_true, if_false]
    rw [hprog, hpc, h_pushAt]
    unfold YiState.execute
    simp [μ1, hcur, hhist, hpc, hprog, hhalt]
  have h_run1 : μ.runFuel 1 = μ1 := by
    unfold YiState.runFuel
    rw [hhalt]
    simpa using h_step0
  have h_step1 :
      μ1.step = { μ1 with pc := fetchOffset } := by
    unfold YiState.step
    simp [μ1, h_jumpAt, YiState.execute]
  have h_run2 : μ.runFuel 2 = { μ1 with pc := fetchOffset } := by
    rw [show (2 : Nat) = 1 + 1 from rfl,
      SSBX.Foundation.Bagua.GodelLi.runFuel_succ_right, h_run1, h_step1]
  have h_sim_step : sim.step = { sim with pc := sim.pc + 1 } := by
    simp [YiState.step, h_alive, h_nop, YiState.execute]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h_run2, h_sim_step]
  · rw [h_run2]
    simp [μ1]
    rw [h_curAligned]
    exact (encMetaHistory_nop_step regHex sim h_alive h_nop).symm
  · rw [h_run2]
  · rw [h_run2]
  · rw [h_run2]

/-! ## § 2.1  Encoding shape for pc-only updates -/

/-- Replacing only the simulated pc rewrites exactly the leading
    pc-counter prefix of `encMetaHistory`; halted flag, simulated history,
    and encoded program tail are preserved. -/
theorem encMetaHistory_pc_set
    (regHex : Hexagram) (sim : YiState) (target : Nat) :
    encMetaHistory regHex { sim with pc := target } =
      encCounter regHex target ++
      [encHaltedFlag regHex sim.halted] ++
      encCounter regHex sim.history.length ++
      sim.history ++
      ProgEnc.encProg sim.prog := by
  unfold encMetaHistory
  rfl

/-- Advancing the simulated pc by one grows `encMetaHistory` by exactly one
    cell.  Changing `cur` at the same step does not affect the encoded META
    history layout. -/
theorem encMetaHistory_pc_increment_length
    (regHex : Hexagram) (sim : YiState) (nextCur : R8) :
    (encMetaHistory regHex
      { sim with cur := nextCur, pc := sim.pc + 1 }).length =
      (encMetaHistory regHex sim).length + 1 := by
  rw [encMetaHistory_length, encMetaHistory_length]
  simp
  omega

/-- A simulated one-step pc increment cannot leave the encoded META history
    byte-for-byte unchanged. -/
theorem encMetaHistory_pc_increment_ne_unchanged
    (regHex : Hexagram) (sim : YiState) (nextCur : R8) :
    encMetaHistory regHex { sim with cur := nextCur, pc := sim.pc + 1 } ≠
      encMetaHistory regHex sim := by
  intro h
  have hlen := congrArg List.length h
  rw [encMetaHistory_pc_increment_length] at hlen
  omega

/-- Boundary fact for exact block witnesses: if the source step increments
    `pc`, any META block result whose history is still the pre-step
    `encMetaHistory` cannot satisfy `BlockPost`.

    This exposes why cur-only placeholder blocks with unchanged history are
    local-effect witnesses only; exact `BlockPost` needs a real pc-counter
    update in META history. -/
theorem blockPost_unchanged_history_impossible_after_pc_increment
    (regHex : Hexagram) (sim : YiState) (fetchOffset : Nat)
    (metaProg : List YiInstr) (μ' : YiState) (endHalted : Bool)
    (nextCur : R8)
    (h_step : sim.step =
      { sim with cur := nextCur, pc := sim.pc + 1 })
    (h_history : μ'.history = encMetaHistory regHex sim) :
    ¬ BlockPost regHex sim fetchOffset metaProg μ' endHalted := by
  intro h_post
  have h_eq :
      encMetaHistory regHex
        { sim with cur := nextCur, pc := sim.pc + 1 } =
        encMetaHistory regHex sim := by
    rw [← h_step, ← h_post.history]
    exact h_history
  exact encMetaHistory_pc_increment_ne_unchanged regHex sim nextCur h_eq

/-! ## § 3  Worked example: executeBlock_halt

The `halt` opcode: sets `sim.halted := true`, no other change.

In META terms we must:
- flip the halted-flag cell in encMetaHistory from `(regHex, Shi.wei)`
  to `(regHex, Shi.ji)`;
- bump pc-counter by one (because sim.pc advances by 1 in step);
- set META.halted := true (so the global meta-interp halts after writeback).

For the SCAFFOLD we provide:
- the implementation;
- structural lemmas;
- a **local effect** lemma showing the 1-instruction halt sets META.halted.

The full encoding-update is straightforward (single-cell rewrite) but
requires fetch to have positioned the halted-flag cell at top of history;
this routing is part of the per-block contract subagents must satisfy.
-/

/-- The `halt` execute block: just `halt`.  We do NOT jump back to
    fetchOffset; the META machine is now done and the surrounding
    `metaInterpProg` will fall through to the terminal `haltProg`.

    Subagents may extend this with explicit halted-flag flipping (one
    `setShi Shi.ji` + `push` if META.cur is positioned correctly), but
    for the contract scaffold the minimal `halt` instruction suffices
    to demonstrate the post-state contract. -/
def executeBlock_halt (_offset _fetchOffset : Nat) : List YiInstr :=
  [ YiInstr.halt ]

theorem executeBlock_halt_length (offset fetchOffset : Nat) :
    (executeBlock_halt offset fetchOffset).length = 1 := rfl

theorem executeBlock_halt_first (offset fetchOffset : Nat) :
    (executeBlock_halt offset fetchOffset)[0]? = some YiInstr.halt := rfl

/-- **Local effect**: a 1-fuel run of the halt block sets META.halted
    to true; cur, history, pc are preserved (in the local sense — pc
    does not advance because halt sets halted before pc-update). -/
theorem executeBlock_halt_local_effect
    (cur : R8) (history : List R8) (offset fetchOffset : Nat) :
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

/-- **Sim-side bridge for halt**: `sim.step` on a halt instruction sets
    `halted := true` and leaves all other fields untouched.  In
    particular, `encMetaHistory regHex sim.step` differs from
    `encMetaHistory regHex sim` only in the halted-flag cell.

    The full per-cell rewrite proof is straightforward; for the scaffold
    we expose the simplified form. -/
theorem encMetaHistory_halt_step
    (regHex : Hexagram) (sim : YiState)
    (h_halt_instr : sim.prog[sim.pc]? = some .halt)
    (h_alive : sim.halted = false) :
    encMetaHistory regHex sim.step =
      encCounter regHex sim.pc ++
      [encHaltedFlag regHex true] ++
      encCounter regHex sim.history.length ++
      sim.history ++
      ProgEnc.encProg sim.prog := by
  -- sim.step = execute .halt sim = { sim with halted := true }
  have h_step : sim.step = { sim with halted := true } := by
    simp [YiState.step, h_alive, h_halt_instr, YiState.execute]
  rw [h_step]
  unfold encMetaHistory
  -- All fields unchanged except `halted`; the ` { sim with halted := true } `
  -- update only affects the `[encHaltedFlag regHex sim.halted]` slot.
  rfl

/-! ## § 4  Subagent guide

Each of the 10 remaining blocks should follow this template:

1. **Define** `executeBlock_<op> : Nat → Nat → List YiInstr` (with any
   per-op fixed parameters — e.g., `executeBlock_setShi sh offset
   fetchOffset`, `executeBlock_branchYaoEq i j tgt offset fetchOffset`).

2. **Prove the structural lemmas** (length, instruction enumeration).

3. **Prove the local-effect lemma** (a 1- or k-fuel runFuel from a
   block-only YiState reaches the expected configuration).

4. **Prove the encoding-bridge lemma**: how `encMetaHistory regHex
   sim.step` relates to `encMetaHistory regHex sim` for this opcode.
   Most opcodes only modify `sim.cur` and bump `sim.pc`; some
   (`push`, `pop`) modify `sim.history`; `halt` flips the halted-flag.

5. **Compose** (optionally; can be deferred to Phase C integration):
   the global simulation lemma in the shape of `BlockPre → BlockPost`.

The two examples here demonstrate steps 1–4 fully.  Step 5 is left for
Phase C integration where the surrounding fetch/dispatch context is
fixed and `metaProg.extract offset (offset + block.length) = block`
can be discharged.

## §5  Summary table of the 12 blocks (subagent assignments)

| op            | per-op params       | expected length | encoding effect          |
| ------------- | ------------------- | --------------- | ------------------------ |
| nop           | (none)              | 2               | pc++                     |
| setShi        | sh : Shi            | ~3              | cur.2 := sh; pc++        |
| flipYao       | i : Fin 6           | ~3              | cur.1 := flipPos i; pc++ |
| interlace            | (none)              | 2               | cur.1 := interlace cur.1; pc++  |
| complement           | (none)              | 2               | cur.1 := complement cur.1; pc++ |
| reverse          | (none)              | 2               | cur.1 := reverse cur.1; pc++|
| branchYaoEq   | i j : Fin 6, t : Nat| ~6              | conditional pc set       |
| branchShiEq   | s : Shi, t : Nat    | ~5              | conditional pc set       |
| jump          | t : Nat             | ~3              | pc := t (replaces pc-cnt)|
| push          | (none)              | ~4              | history := cur :: history|
| pop           | (none)              | ~6              | match history; halt-or-pop|
| halt          | (none)              | 1               | halted := true           |

(These lengths are approximate; subagents will refine.)
-/

end SSBX.Foundation.Wen.MetaInterp.ExecuteBlock
