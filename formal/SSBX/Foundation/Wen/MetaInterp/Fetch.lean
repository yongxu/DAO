/-
# Fetch — read prog[sim.pc] from META.history's encProg tail

## Architectural design

The fetch subroutine is the bridge between META's outer loop and per-opcode
`executeBlock_<op>` programs.  Conceptually it must:

  1. Inspect `sim.pc` (encoded as the top counter of META.history).
  2. Walk past the `halted-flag`, `simhist-len` counter, and `sim.history`
     regions, reaching the `encProg sim.prog` tail (bottom of META.history).
  3. Skip `sim.pc` encoded instructions in the program tail.
  4. Pop the next encoded instruction's tag cell into `META.cur`.
  5. Restore `META.history` to the original layout (so dispatch can route
     to a per-opcode block whose precondition assumes the canonical
     `encMetaHistory regHex sim` shape).
  6. Hand off to `dispatch` (separate Wave 3b component) which branches on
     the tag value in `META.cur`.

## Why a "destructive walk + restore" architecture is unavoidable

YiState's history is a single LIFO stack: `pop` reads the head, `push`
prepends.  There are no random-access primitives.  To reach the encProg
tail we MUST consume every cell sitting above it; to leave the layout
intact for the per-opcode blocks we must rebuild on the way out.

Two execution patterns are workable:

  (A) **Mirror-stack rebuild** — pop region cells one-by-one into a
      "scratch stack" (push-back via setShi+push), walk the encProg up
      to instruction `sim.pc`, read its tag, then unwind the scratch
      stack back onto history.  Cost: each region-cell incurs O(1)
      pop + O(1) push, plus the O(sim.pc) skip walk, plus the O(scratch)
      unwind.  The big upside: dispatch sees the canonical layout.

  (B) **Tag-extracted state** — leave META.history in a "denormalized"
      shape after fetch (tag in cur, payload cells exposed, region
      buffers held as a parallel scratch).  Each per-opcode block then
      operates against this denormalized shape.  Cost: every block's
      precondition becomes more complex; many post-conditions need to
      re-canonicalize.  Upside: zero rebuild cost on the fetch path.

We choose **(A)** here because the contract surface for the 12 blocks
(see `ExecuteBlock.BlockPre`) is already defined against the canonical
`encMetaHistory regHex sim` shape, and refactoring all 12 blocks to a
denormalized shape would invalidate the existing per-block lemmas.

## What is implemented in this file (Wave 3a, deliverable scope)

This file delivers the **design + scaffold** layer of the fetch protocol:

  * `FetchOutcome` — record describing post-fetch META state.
  * `fetchProtocol offset dispatchOffset haltOffset : List YiInstr` —
    a concrete YiInstr list whose first instruction is a `pop`
    consuming the topmost pc-counter cell (or its marker, in the
    sim.pc=0 case), and whose final instruction routes to either
    `dispatchOffset` (if more instructions remain) or `haltOffset`
    (if sim.pc has fallen off the end of sim.prog).
  * `fetchProtocol_length` — proven structural lemma.
  * `fetchProtocol_simulates_pc0_initialPop` — the sim.pc=0
    base-case simulation lemma showing the very first pop instruction
    consumes the pc-counter marker (`Shi.wei`) and lands at offset+1
    with `META.cur` holding the marker cell.

## What is deferred

The full `fetchProtocol_simulates_general` theorem requires:

  (D1) A counted-loop simulation lemma where the body actually does work
       (pop one region cell, push to scratch).  The current
       `countedLoop_empty_simulates_n_iterations` covers only the
       empty-body case; generalizing to "non-trivial body that preserves
       a fixed history-tail" is the major Phase B engineering item.

  (D2) An `encProg`-skip protocol that reads tag cells from the program
       tail and pops payload cells per opcode arity.  The arity table
       lives in `SkipInstr`; `skipOneInstr` currently handles only the
       7 zero-arity opcodes (its own simulation lemma is also
       zero-arity-only).

  (D3) An "unwind scratch back onto history" subroutine that, given a
       scratch-counter, pops cells from above the encProg and pushes
       them into a freshly-pushed region with markers re-emitted at the
       correct boundaries.  This is structurally similar to the inverse
       of (D1).

  (D4) A halt-detection branch in the encProg-skip walker: if we exhaust
       encProg without reaching instruction `sim.pc`, jump to
       `haltOffset` instead of `dispatchOffset`.

Each of (D1)–(D4) is a substantial sub-proof on its own; together they
constitute Wave 3b (dispatch) and Wave 3c (writeback) of the broader
plan.  The scaffold provided here is the structural anchor those waves
will compose against.
-/
import SSBX.Foundation.Wen.MetaInterp.SkipInstr
import SSBX.Foundation.Wen.MetaInterp.ExecuteBlock

namespace SSBX.Foundation.Wen.MetaInterp.Fetch

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.MetaInterp
open SSBX.Foundation.Wen.MetaInterp.SkipInstr

/-! ## § 1  Post-fetch outcome record -/

/-- `FetchOutcome regHex sim metaProg dispatchOffset` describes the META
    state that a *correct* fetch protocol must produce when `sim.pc` is
    in-bounds (i.e., `sim.pc < sim.prog.length`).

    The `cur` field carries the raw tag cell of `sim.prog[sim.pc]` (the
    cell whose Shi/Hex encode the opcode index — see
    `WenyanSelfInterp.YiInstrEnc`).  The `history` field is restored
    to the canonical `encMetaHistory regHex sim` shape so that the
    routed per-opcode block sees the same shape its `BlockPre`
    contract assumes. -/
structure FetchOutcome
    (regHex : Hexagram) (sim : YiState) (metaProg : List YiInstr)
    (dispatchOffset : Nat) (μ' : YiState) : Prop where
  /-- After fetch, META.cur holds the encoded tag cell of `prog[sim.pc]`. -/
  cur_is_tag :
    ∀ instr, sim.prog[sim.pc]? = some instr →
      μ'.cur ∈ (YiInstrEnc.encInstr instr).head?
  /-- META.history is restored to the canonical layout. -/
  history    : μ'.history = encMetaHistory regHex sim
  /-- Control transfers to the dispatch entry point. -/
  pc         : μ'.pc = dispatchOffset
  /-- The global program is unchanged. -/
  prog       : μ'.prog = metaProg
  /-- META is still alive. -/
  halted     : μ'.halted = false

/-- If a fetch routine has restored canonical history and placed the current
    instruction tag in `META.cur`, then it satisfies `FetchOutcome`.  This
    packages the target shape future concrete decode/restore proofs should
    aim to reach. -/
theorem fetchOutcome_restored_tag_state
    (regHex : Hexagram) (sim : YiState) (metaProg : List YiInstr)
    (dispatchOffset : Nat) (instr : YiInstr) (tag : R8)
    (h_get : sim.prog[sim.pc]? = some instr)
    (h_tag : (YiInstrEnc.encInstr instr).head? = some tag) :
    FetchOutcome regHex sim metaProg dispatchOffset
      { cur := tag
        history := encMetaHistory regHex sim
        pc := dispatchOffset
        prog := metaProg
        halted := false } := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  intro instr' h_instr'
  rw [h_get] at h_instr'
  cases h_instr'
  simp [h_tag]

/-- Zero-arity specialization of `fetchOutcome_restored_tag_state`, using the
    `SkipInstr.zeroArityTag` name for the exposed opcode tag. -/
theorem fetchOutcome_zeroArity_restored_tag_state
    (regHex : Hexagram) (sim : YiState) (metaProg : List YiInstr)
    (dispatchOffset : Nat) (instr : YiInstr)
    (h_get : sim.prog[sim.pc]? = some instr)
    (h_zero : IsZeroArity instr) :
    FetchOutcome regHex sim metaProg dispatchOffset
      { cur := zeroArityTag instr h_zero
        history := encMetaHistory regHex sim
        pc := dispatchOffset
        prog := metaProg
        halted := false } := by
  exact fetchOutcome_restored_tag_state regHex sim metaProg dispatchOffset instr
    (zeroArityTag instr h_zero) h_get
    (by rw [encInstr_zeroArity_eq instr h_zero]; rfl)

/-- `FetchHaltOutcome` describes the META state when fetch detects an
    out-of-bounds `sim.pc` (i.e., `sim.pc ≥ sim.prog.length`).  In this
    case sim halts and the meta-interpreter routes to a writeback
    segment at `haltOffset`. -/
structure FetchHaltOutcome
    (regHex : Hexagram) (sim : YiState) (metaProg : List YiInstr)
    (haltOffset : Nat) (μ' : YiState) : Prop where
  /-- META.history reflects the post-step (halted) sim. -/
  history    : μ'.history =
                 encMetaHistory regHex { sim with halted := true }
  /-- Control transfers to the halt/writeback entry. -/
  pc         : μ'.pc = haltOffset
  /-- The global program is unchanged. -/
  prog       : μ'.prog = metaProg
  /-- META is still alive (writeback runs after halt detection). -/
  halted     : μ'.halted = false

/-! ## § 2  Concrete `fetchProtocol` skeleton

  The protocol below is the *structural* implementation: a concrete
  `List YiInstr` whose first instruction is the pc-counter consumer.
  Subsequent instructions encode the (deferred) walk-and-restore
  machinery; each is annotated with the sub-proof it would discharge
  in the full simulation lemma.

  The protocol is parameterized by three absolute PC offsets:
    * `offset`         — where this protocol is placed in metaProg.
    * `dispatchOffset` — where to jump on success (sim.pc in-bounds).
    * `haltOffset`     — where to jump on out-of-bounds detection.

  The first instruction is `pop`: it consumes the topmost pc-counter
  cell into META.cur.  This is the only instruction whose simulation
  is proven below; subsequent instructions are placeholders for the
  deferred walk/restore work and are documented per-line.
-/

/-- Concrete fetch-protocol program.

    Layout (top-to-bottom = increasing pc inside this block):
    ```
    offset+0:  pop                    -- consume top pc-counter cell
    offset+1:  branchShiEq Shi.wei (offset+3)
                                       -- if marker, sim.pc = 0; else loop
    offset+2:  jump offset             -- (placeholder for skip-instr loop)
    offset+3:  jump dispatchOffset     -- (placeholder for restore + dispatch)
    ```

    The structure mirrors `countedLoop`, but each "tick" of the loop
    must (in the full implementation) drag along scratch state for
    eventual rebuild.  For Wave 3a we expose only the structural
    skeleton; the simulation lemma below proves the first instruction
    consumes the pc-marker cell when `sim.pc = 0`.

    `haltOffset` is currently unused at the YiInstr level (no
    out-of-bounds branch is emitted yet); it is reserved for (D4). -/
def fetchProtocol (offset : Nat) (dispatchOffset : Nat) (_haltOffset : Nat)
    : List YiInstr :=
  [ YiInstr.pop                                              -- offset+0
  , YiInstr.branchShiEq Shi.wei (offset + 3)                 -- offset+1
  , YiInstr.jump offset                                      -- offset+2
  , YiInstr.jump dispatchOffset                              -- offset+3
  ]

theorem fetchProtocol_length (offset dispatchOffset haltOffset : Nat) :
    (fetchProtocol offset dispatchOffset haltOffset).length = 4 := rfl

theorem fetchProtocol_first (offset dispatchOffset haltOffset : Nat) :
    (fetchProtocol offset dispatchOffset haltOffset)[0]? = some YiInstr.pop :=
  rfl

theorem fetchProtocol_second (offset dispatchOffset haltOffset : Nat) :
    (fetchProtocol offset dispatchOffset haltOffset)[1]? =
      some (YiInstr.branchShiEq Shi.wei (offset + 3)) := rfl

theorem fetchProtocol_third (offset dispatchOffset haltOffset : Nat) :
    (fetchProtocol offset dispatchOffset haltOffset)[2]? =
      some (YiInstr.jump offset) := rfl

theorem fetchProtocol_fourth (offset dispatchOffset haltOffset : Nat) :
    (fetchProtocol offset dispatchOffset haltOffset)[3]? =
      some (YiInstr.jump dispatchOffset) := rfl

/-! ## § 3  Simulation lemma — sim.pc = 0 initial-pop case

  We prove the simplest meaningful sub-step: when `sim.pc = 0` (so the
  top of META.history is the pc-counter marker cell, encoded as
  `(regHex, Shi.wei)`), the first `pop` instruction of `fetchProtocol`
  consumes it cleanly:

    * META.cur ← (regHex, Shi.wei)              (the marker cell)
    * META.history ← rest of `encMetaHistory`
    * META.pc ← offset + 1                       (next instruction)
    * META.halted unchanged (= false)

  This is the structural anchor for the full simulation: subsequent
  branches (offset+1) test `cur.2 = Shi.wei` and route accordingly.
  When `sim.pc = 0` (marker on top), the branch is *taken* and we land
  at `offset + 3` — the pre-dispatch hand-off point.

  ## What this lemma demonstrates structurally

  This step is the inverse of `prologueProg`'s third instruction (which
  prepended the pc-marker).  Together with the dispatcher-side reading
  of `META.cur`, it constitutes the minimal end-to-end fetch path for
  a freshly-initialized sim (sim.pc = 0).

  ## What is NOT yet proven

  * The general `sim.pc > 0` case requires a counted-loop iteration
    that drags scratch state — this is (D1).
  * The encProg-walk that finds the actual instruction tag is
    completely deferred — see (D2).
  * The restore step is deferred — see (D3).
-/

/-- Helper: META state at fetch-entry, parameterized by `sim` and the
    surrounding metaProg context. -/
def fetchEntryState
    (regHex : Hexagram) (sim : YiState) (metaProg : List YiInstr)
    (offset : Nat) : YiState :=
  { cur     := sim.cur
  , history := encMetaHistory regHex sim
  , pc      := offset
  , prog    := metaProg
  , halted  := false }

/-- Helper: the META state after the very first `pop` of `fetchProtocol`
    when `sim.pc = 0`.  At this point META.cur holds the pc-marker cell
    and META.history is the remainder. -/
def fetchAfterFirstPop_pc0
    (regHex : Hexagram) (sim : YiState) (metaProg : List YiInstr)
    (offset : Nat) : YiState :=
  { cur     := (regHex, Shi.wei)
  , history := [encHaltedFlag regHex sim.halted] ++
               encCounter regHex sim.history.length ++
               sim.history ++
               ProgEnc.encProg sim.prog
  , pc      := offset + 1
  , prog    := metaProg
  , halted  := false }

/-- The pc=0 reshuffle: when `sim.pc = 0`, `encMetaHistory regHex sim`
    starts with `[regMarkerCell regHex]` followed by the rest. -/
private theorem encMetaHistory_pc0_unfold
    (regHex : Hexagram) (sim : YiState) (h_pc : sim.pc = 0) :
    encMetaHistory regHex sim =
      regMarkerCell regHex ::
        ([encHaltedFlag regHex sim.halted] ++
          encCounter regHex sim.history.length ++
          sim.history ++
          ProgEnc.encProg sim.prog) := by
  unfold encMetaHistory
  rw [h_pc, encCounter_zero]
  rfl

/-- **Main simulation lemma (sim.pc = 0, initial pop only)**.

    Structural pre-conditions:
      * `metaProg[offset]? = some YiInstr.pop`  (fetchProtocol placed
        correctly; this discharges to `rfl` when fetchProtocol is
        spliced into metaProg starting at `offset`).
      * `sim.pc = 0`.

    Post-condition (after 1 fuel step):
      * META.cur = (regHex, Shi.wei)         — the consumed marker cell
      * META.history = `encHaltedFlag :: encCounter ... :: sim.history
                       ++ encProg sim.prog`  — the layout below the
                                                pc-counter region
      * META.pc = offset + 1                  — pointing at the
                                                branch-on-marker step
      * META.halted = false. -/
theorem fetchProtocol_simulates_pc0_initialPop
    (regHex : Hexagram) (sim : YiState) (metaProg : List YiInstr)
    (offset : Nat)
    (h_progAt : metaProg[offset]? = some YiInstr.pop)
    (h_pc0 : sim.pc = 0) :
    (fetchEntryState regHex sim metaProg offset).runFuel 1
      = fetchAfterFirstPop_pc0 regHex sim metaProg offset := by
  -- Step 1: compute the single step concretely.
  have h_step : (fetchEntryState regHex sim metaProg offset).step
              = fetchAfterFirstPop_pc0 regHex sim metaProg offset := by
    unfold YiState.step
    -- META is alive at entry.
    have h_halt : (fetchEntryState regHex sim metaProg offset).halted = false := rfl
    show (if (fetchEntryState regHex sim metaProg offset).halted = true
          then (fetchEntryState regHex sim metaProg offset)
          else match (fetchEntryState regHex sim metaProg offset).prog[(fetchEntryState regHex sim metaProg offset).pc]? with
               | none => { (fetchEntryState regHex sim metaProg offset) with halted := true }
               | some instr => YiState.execute instr (fetchEntryState regHex sim metaProg offset))
          = _
    rw [h_halt]
    simp only [Bool.false_eq_true, if_false]
    -- Lookup the pop instruction at offset.
    have h_prog_eq : (fetchEntryState regHex sim metaProg offset).prog = metaProg := rfl
    have h_pc_eq   : (fetchEntryState regHex sim metaProg offset).pc   = offset := rfl
    rw [h_prog_eq, h_pc_eq, h_progAt]
    -- Execute pop on the entry state.
    show YiState.execute YiInstr.pop (fetchEntryState regHex sim metaProg offset)
         = fetchAfterFirstPop_pc0 regHex sim metaProg offset
    unfold YiState.execute
    -- Need to show history's head is the marker cell.
    have h_hist :
        (fetchEntryState regHex sim metaProg offset).history
        = regMarkerCell regHex ::
            ([encHaltedFlag regHex sim.halted] ++
              encCounter regHex sim.history.length ++
              sim.history ++
              ProgEnc.encProg sim.prog) := by
      show encMetaHistory regHex sim = _
      exact encMetaHistory_pc0_unfold regHex sim h_pc0
    show (match (fetchEntryState regHex sim metaProg offset).history with
          | [] => { (fetchEntryState regHex sim metaProg offset) with halted := true }
          | h :: rest => { (fetchEntryState regHex sim metaProg offset) with
              cur := h, history := rest,
              pc := (fetchEntryState regHex sim metaProg offset).pc + 1 })
         = fetchAfterFirstPop_pc0 regHex sim metaProg offset
    rw [h_hist, h_pc_eq]
    -- regMarkerCell regHex = (regHex, Shi.wei)
    show ({ (fetchEntryState regHex sim metaProg offset) with
              cur     := regMarkerCell regHex
            , history := [encHaltedFlag regHex sim.halted] ++
                         encCounter regHex sim.history.length ++
                         sim.history ++
                         ProgEnc.encProg sim.prog
            , pc      := offset + 1 } : YiState)
          = fetchAfterFirstPop_pc0 regHex sim metaProg offset
    unfold fetchEntryState fetchAfterFirstPop_pc0 regMarkerCell
    rfl
  -- Step 2: turn h_step into a runFuel 1 statement.
  show (fetchEntryState regHex sim metaProg offset).runFuel 1
       = fetchAfterFirstPop_pc0 regHex sim metaProg offset
  unfold YiState.runFuel
  have h_halt' : (fetchEntryState regHex sim metaProg offset).halted = false := rfl
  rw [h_halt']
  simp only [Bool.false_eq_true, if_false]
  show YiState.runFuel 0 (fetchEntryState regHex sim metaProg offset).step
       = fetchAfterFirstPop_pc0 regHex sim metaProg offset
  -- runFuel 0 s = s
  show (fetchEntryState regHex sim metaProg offset).step
       = fetchAfterFirstPop_pc0 regHex sim metaProg offset
  exact h_step

/-! ## § 4  Standalone wrapper

  When `metaProg = fetchProtocol 0 dispatchOffset haltOffset` and
  `offset = 0`, the prog-lookup hypothesis discharges by `rfl`. -/

/-- Standalone simulation: `fetchProtocol 0 ...` run from offset 0 on a
    sim with `pc = 0` consumes the marker cell in 1 fuel step. -/
theorem fetchProtocol_simulates_pc0_initialPop_standalone
    (regHex : Hexagram) (sim : YiState)
    (dispatchOffset haltOffset : Nat)
    (h_pc0 : sim.pc = 0) :
    (fetchEntryState regHex sim
        (fetchProtocol 0 dispatchOffset haltOffset) 0).runFuel 1
    = fetchAfterFirstPop_pc0 regHex sim
        (fetchProtocol 0 dispatchOffset haltOffset) 0 := by
  exact fetchProtocol_simulates_pc0_initialPop regHex sim
    (fetchProtocol 0 dispatchOffset haltOffset) 0 (by rfl) h_pc0

/-! ## § 5  What composes on top of this

  The next sub-lemma in the natural progression is
  `fetchProtocol_branch_taken_at_pc0`: starting from
  `fetchAfterFirstPop_pc0`, run 1 more fuel step to evaluate the
  `branchShiEq Shi.wei (offset+3)` instruction.  Since
  `META.cur.2 = Shi.wei` (the marker we just consumed), the branch is
  taken and we land at `pc = offset + 3`, the pre-dispatch hand-off.

  We prove this composition step here as a brief exercise; it
  demonstrates that the `fetchProtocol` skeleton's branch logic is
  internally consistent.
-/

/-- After-branch state when sim.pc = 0 (marker observed in cur). -/
def fetchAfterMarkerBranch_pc0
    (regHex : Hexagram) (sim : YiState) (metaProg : List YiInstr)
    (offset : Nat) : YiState :=
  { cur     := (regHex, Shi.wei)
  , history := [encHaltedFlag regHex sim.halted] ++
               encCounter regHex sim.history.length ++
               sim.history ++
               ProgEnc.encProg sim.prog
  , pc      := offset + 3
  , prog    := metaProg
  , halted  := false }

/-- After consuming the marker, the branch at `offset + 1` is taken
    (because cur.2 = Shi.wei) and pc jumps to `offset + 3`. -/
theorem fetchProtocol_branchTaken_at_pc0
    (regHex : Hexagram) (sim : YiState) (metaProg : List YiInstr)
    (offset : Nat)
    (h_branchAt : metaProg[offset + 1]? =
      some (YiInstr.branchShiEq Shi.wei (offset + 3))) :
    (fetchAfterFirstPop_pc0 regHex sim metaProg offset).step
      = fetchAfterMarkerBranch_pc0 regHex sim metaProg offset := by
  unfold YiState.step
  have h_halt : (fetchAfterFirstPop_pc0 regHex sim metaProg offset).halted = false := rfl
  show (if (fetchAfterFirstPop_pc0 regHex sim metaProg offset).halted = true
        then (fetchAfterFirstPop_pc0 regHex sim metaProg offset)
        else match (fetchAfterFirstPop_pc0 regHex sim metaProg offset).prog[(fetchAfterFirstPop_pc0 regHex sim metaProg offset).pc]? with
             | none => { (fetchAfterFirstPop_pc0 regHex sim metaProg offset) with halted := true }
             | some instr => YiState.execute instr (fetchAfterFirstPop_pc0 regHex sim metaProg offset))
        = _
  rw [h_halt]
  simp only [Bool.false_eq_true, if_false]
  have h_prog_eq : (fetchAfterFirstPop_pc0 regHex sim metaProg offset).prog = metaProg := rfl
  have h_pc_eq   : (fetchAfterFirstPop_pc0 regHex sim metaProg offset).pc   = offset + 1 := rfl
  rw [h_prog_eq, h_pc_eq, h_branchAt]
  -- Execute the branch.  cur.2 = Shi.wei, so branch is taken.
  show YiState.execute (YiInstr.branchShiEq Shi.wei (offset + 3))
         (fetchAfterFirstPop_pc0 regHex sim metaProg offset)
       = fetchAfterMarkerBranch_pc0 regHex sim metaProg offset
  unfold YiState.execute
  -- cur.2 = (regHex, Shi.wei).2 = Shi.wei
  have h_cur2 :
      (fetchAfterFirstPop_pc0 regHex sim metaProg offset).cur.2 = Shi.wei := rfl
  show (if (fetchAfterFirstPop_pc0 regHex sim metaProg offset).cur.2 = Shi.wei
        then { (fetchAfterFirstPop_pc0 regHex sim metaProg offset) with pc := offset + 3 }
        else { (fetchAfterFirstPop_pc0 regHex sim metaProg offset) with
                pc := (fetchAfterFirstPop_pc0 regHex sim metaProg offset).pc + 1 })
       = fetchAfterMarkerBranch_pc0 regHex sim metaProg offset
  rw [h_cur2]
  simp only [if_true]
  unfold fetchAfterFirstPop_pc0 fetchAfterMarkerBranch_pc0
  rfl

/-- Composition: 2 fuel steps from fetch-entry (sim.pc = 0) reach the
    pre-dispatch hand-off point (`pc = offset + 3`).

    Premises:
      * `metaProg[offset]? = some YiInstr.pop`
      * `metaProg[offset + 1]? = some (branchShiEq Shi.wei (offset + 3))`
      * `sim.pc = 0`. -/
theorem fetchProtocol_simulates_pc0_to_handoff
    (regHex : Hexagram) (sim : YiState) (metaProg : List YiInstr)
    (offset : Nat)
    (h_progAt0 : metaProg[offset]? = some YiInstr.pop)
    (h_progAt1 : metaProg[offset + 1]? =
      some (YiInstr.branchShiEq Shi.wei (offset + 3)))
    (h_pc0 : sim.pc = 0) :
    (fetchEntryState regHex sim metaProg offset).runFuel 2
      = fetchAfterMarkerBranch_pc0 regHex sim metaProg offset := by
  -- runFuel 2 s = ((s.runFuel 0).step).step = s.step.step
  -- Use the right-expansion identity twice.
  have h2 :
      (fetchEntryState regHex sim metaProg offset).runFuel 2
      = ((fetchEntryState regHex sim metaProg offset).runFuel 1).step := by
    rw [show (2 : Nat) = 1 + 1 from rfl,
        SSBX.Foundation.Bagua.GodelLi.runFuel_succ_right]
  rw [h2]
  rw [fetchProtocol_simulates_pc0_initialPop regHex sim metaProg offset h_progAt0 h_pc0]
  exact fetchProtocol_branchTaken_at_pc0 regHex sim metaProg offset h_progAt1

/-- State after the pc=0 marker branch executes the hand-off jump to dispatch. -/
def fetchAfterDispatchJump_pc0
    (regHex : Hexagram) (sim : YiState) (metaProg : List YiInstr)
    (dispatchOffset : Nat) : YiState :=
  { cur     := (regHex, Shi.wei)
  , history := [encHaltedFlag regHex sim.halted] ++
               encCounter regHex sim.history.length ++
               sim.history ++
               ProgEnc.encProg sim.prog
  , pc      := dispatchOffset
  , prog    := metaProg
  , halted  := false }

/-- At the pc=0 hand-off point, the jump at `offset + 3` routes to the
    dispatch block.  This remains route-only: it does not yet prove that
    `META.cur` is the next opcode tag, because the real encProg walk/restore
    is still deferred. -/
theorem fetchProtocol_jumpDispatch_at_pc0
    (regHex : Hexagram) (sim : YiState) (metaProg : List YiInstr)
    (offset dispatchOffset : Nat)
    (h_jumpAt : metaProg[offset + 3]? =
      some (YiInstr.jump dispatchOffset)) :
    (fetchAfterMarkerBranch_pc0 regHex sim metaProg offset).step
      = fetchAfterDispatchJump_pc0 regHex sim metaProg dispatchOffset := by
  unfold YiState.step
  have h_halt :
      (fetchAfterMarkerBranch_pc0 regHex sim metaProg offset).halted = false := rfl
  show (if (fetchAfterMarkerBranch_pc0 regHex sim metaProg offset).halted = true
        then (fetchAfterMarkerBranch_pc0 regHex sim metaProg offset)
        else match
          (fetchAfterMarkerBranch_pc0 regHex sim metaProg offset).prog[
            (fetchAfterMarkerBranch_pc0 regHex sim metaProg offset).pc]? with
          | none => { (fetchAfterMarkerBranch_pc0 regHex sim metaProg offset) with
              halted := true }
          | some instr =>
              YiState.execute instr
                (fetchAfterMarkerBranch_pc0 regHex sim metaProg offset))
        = _
  rw [h_halt]
  simp only [Bool.false_eq_true, if_false]
  have h_prog_eq :
      (fetchAfterMarkerBranch_pc0 regHex sim metaProg offset).prog = metaProg := rfl
  have h_pc_eq :
      (fetchAfterMarkerBranch_pc0 regHex sim metaProg offset).pc = offset + 3 := rfl
  rw [h_prog_eq, h_pc_eq, h_jumpAt]
  show YiState.execute (YiInstr.jump dispatchOffset)
        (fetchAfterMarkerBranch_pc0 regHex sim metaProg offset)
      = fetchAfterDispatchJump_pc0 regHex sim metaProg dispatchOffset
  unfold YiState.execute
  unfold fetchAfterMarkerBranch_pc0 fetchAfterDispatchJump_pc0
  rfl

/-- Composition: 3 fuel steps from fetch-entry (sim.pc = 0) route to the
    dispatch block through the current fetch skeleton.

    This is an exact route theorem for the pc=0 scaffold.  It intentionally
    stays weaker than full fetch correctness: the tag extraction and canonical
    history restoration obligations remain open. -/
theorem fetchProtocol_simulates_pc0_to_dispatch
    (regHex : Hexagram) (sim : YiState) (metaProg : List YiInstr)
    (offset dispatchOffset : Nat)
    (h_progAt0 : metaProg[offset]? = some YiInstr.pop)
    (h_progAt1 : metaProg[offset + 1]? =
      some (YiInstr.branchShiEq Shi.wei (offset + 3)))
    (h_progAt3 : metaProg[offset + 3]? =
      some (YiInstr.jump dispatchOffset))
    (h_pc0 : sim.pc = 0) :
    (fetchEntryState regHex sim metaProg offset).runFuel 3
      = fetchAfterDispatchJump_pc0 regHex sim metaProg dispatchOffset := by
  have h3 :
      (fetchEntryState regHex sim metaProg offset).runFuel 3
      = ((fetchEntryState regHex sim metaProg offset).runFuel 2).step := by
    rw [show (3 : Nat) = 2 + 1 from rfl,
        SSBX.Foundation.Bagua.GodelLi.runFuel_succ_right]
  rw [h3]
  rw [fetchProtocol_simulates_pc0_to_handoff regHex sim metaProg offset
    h_progAt0 h_progAt1 h_pc0]
  exact fetchProtocol_jumpDispatch_at_pc0 regHex sim metaProg offset dispatchOffset h_progAt3

/-- Standalone pc=0 route theorem for `fetchProtocol 0 ...`: after 3 fuel
    ticks the skeleton reaches `dispatchOffset`. -/
theorem fetchProtocol_simulates_pc0_to_dispatch_standalone
    (regHex : Hexagram) (sim : YiState)
    (dispatchOffset haltOffset : Nat)
    (h_pc0 : sim.pc = 0) :
    (fetchEntryState regHex sim
      (fetchProtocol 0 dispatchOffset haltOffset) 0).runFuel 3
      = fetchAfterDispatchJump_pc0 regHex sim
        (fetchProtocol 0 dispatchOffset haltOffset) dispatchOffset := by
  exact fetchProtocol_simulates_pc0_to_dispatch regHex sim
    (fetchProtocol 0 dispatchOffset haltOffset) 0 dispatchOffset
    (by rfl) (by rfl) (by rfl) h_pc0

/-! ## § 5  Counter peel bridge

The full fetch program still needs tag decode and history restoration, but the
first real peel boundary can already be stated and proved: consuming the
pc-counter prefix of canonical `encMetaHistory` exposes the halted-flag cell.
The proof reuses the empty-body counted-loop theorem from `MetaInterp.lean`.
-/

/-- The canonical META-history tail immediately below the pc-counter prefix. -/
def pcCounterTailAfterPeel (regHex : Hexagram) (sim : YiState) : List R8 :=
  [encHaltedFlag regHex sim.halted] ++
  encCounter regHex sim.history.length ++
  sim.history ++
  ProgEnc.encProg sim.prog

theorem encMetaHistory_eq_pcCounter_append_tail
    (regHex : Hexagram) (sim : YiState) :
    encMetaHistory regHex sim =
      encCounter regHex sim.pc ++ pcCounterTailAfterPeel regHex sim := by
  unfold encMetaHistory pcCounterTailAfterPeel
  simp [List.append_assoc]

/-- Canonical META history with its encoded program tail split at the
    source-level simulated pc.  This is the list-level bridge a real fetch
    walker needs after it has traversed the register and simulated-history
    regions and skipped `sim.pc` encoded instructions. -/
theorem encMetaHistory_program_tail_splitAt_get?
    (regHex : Hexagram) (sim : YiState) (instr : YiInstr)
    (h_get : sim.prog[sim.pc]? = some instr) :
    encMetaHistory regHex sim =
      encCounter regHex sim.pc ++
      [encHaltedFlag regHex sim.halted] ++
      encCounter regHex sim.history.length ++
      sim.history ++
      ProgEnc.encProg (sim.prog.take sim.pc) ++
      YiInstrEnc.encInstr instr ++
      ProgEnc.encProg (sim.prog.drop (sim.pc + 1)) := by
  unfold encMetaHistory
  rw [ProgEnc.encProg_splitAt_get? sim.prog sim.pc instr h_get]
  simp [List.append_assoc]

/-- Zero-arity specialization of `encMetaHistory_program_tail_splitAt_get?`:
    after the prefix walk, the next encoded cell is exactly the opcode tag,
    and the rest of the encoded source program follows immediately. -/
theorem encMetaHistory_program_tail_zeroArity_splitAt_get?
    (regHex : Hexagram) (sim : YiState) (instr : YiInstr)
    (h_get : sim.prog[sim.pc]? = some instr)
    (h_zero : IsZeroArity instr) :
    encMetaHistory regHex sim =
      encCounter regHex sim.pc ++
      [encHaltedFlag regHex sim.halted] ++
      encCounter regHex sim.history.length ++
      sim.history ++
      ProgEnc.encProg (sim.prog.take sim.pc) ++
      zeroArityTag instr h_zero ::
      ProgEnc.encProg (sim.prog.drop (sim.pc + 1)) := by
  rw [encMetaHistory_program_tail_splitAt_get? regHex sim instr h_get]
  rw [encInstr_zeroArity_eq instr h_zero]
  simp [List.append_assoc]

/-- A real fetch-entry state is exactly the empty counted-loop entry state
    for the pc-counter peel, with `sim.cur` as the carried META cur and
    the canonical tail below the pc-counter. -/
theorem fetchEntryState_eq_countedLoopEmptyEntryState
    (regHex : Hexagram) (sim : YiState) (metaProg : List YiInstr)
    (offset : Nat) :
    fetchEntryState regHex sim metaProg offset =
      countedLoopEmptyEntryState offset metaProg sim.cur regHex sim.pc
        (pcCounterTailAfterPeel regHex sim) := by
  unfold fetchEntryState countedLoopEmptyEntryState
  rw [encMetaHistory_eq_pcCounter_append_tail]

/-- Peeling the pc-counter with the empty counted-loop lands exactly at the
    tail whose head is the halted-flag cell.  This is a route-independent
    bridge for constructing future `FetchProg` peel witnesses. -/
theorem pc_counter_peel_exposes_halted_flag
    (offset : Nat) (metaProg : List YiInstr)
    (h_loop : MetaProgHasEmptyCountedLoopAt offset metaProg)
    (cur : R8) (regHex : Hexagram) (sim : YiState) :
    (countedLoopEmptyEntryState offset metaProg cur regHex sim.pc
      (pcCounterTailAfterPeel regHex sim)).runFuel (3 * sim.pc + 2)
      = countedLoopEmptyExitState offset metaProg regHex
          (pcCounterTailAfterPeel regHex sim) := by
  exact countedLoop_empty_simulates_n_iterations offset metaProg h_loop cur regHex
    sim.pc (pcCounterTailAfterPeel regHex sim)

/-- Field-facing form specialized to the real fetch-entry state.  After
    the pc-counter peel, META is positioned at the counted-loop exit and
    the halted-flag cell is exposed at the head of history. -/
theorem fetchEntryState_pc_counter_peel_exposes_halted_flag
    (offset : Nat) (metaProg : List YiInstr)
    (h_loop : MetaProgHasEmptyCountedLoopAt offset metaProg)
    (regHex : Hexagram) (sim : YiState) :
    (fetchEntryState regHex sim metaProg offset).runFuel (3 * sim.pc + 2)
      = countedLoopEmptyExitState offset metaProg regHex
          (pcCounterTailAfterPeel regHex sim) := by
  rw [fetchEntryState_eq_countedLoopEmptyEntryState]
  exact pc_counter_peel_exposes_halted_flag offset metaProg h_loop sim.cur regHex sim

/-- Field-facing form: after the pc-counter peel, the next history cell is the
    encoded halted flag, pc is at the counted-loop exit, and META remains alive. -/
theorem pc_counter_peel_history_head_is_halted_flag
    (offset : Nat) (metaProg : List YiInstr)
    (h_loop : MetaProgHasEmptyCountedLoopAt offset metaProg)
    (cur : R8) (regHex : Hexagram) (sim : YiState) :
    let μ' :=
      (countedLoopEmptyEntryState offset metaProg cur regHex sim.pc
        (pcCounterTailAfterPeel regHex sim)).runFuel (3 * sim.pc + 2)
    μ'.history.head? = some (encHaltedFlag regHex sim.halted)
      ∧ μ'.pc = offset + 3
      ∧ μ'.halted = false := by
  rw [pc_counter_peel_exposes_halted_flag offset metaProg h_loop cur regHex sim]
  simp [countedLoopEmptyExitState, pcCounterTailAfterPeel]

/-! ## § 6  Roadmap to full fetch correctness

  The proven content above (sim.pc = 0 initial-pop + branch-taken
  composition) covers the *base case* of the full induction on
  `sim.pc`.  The successor case requires (D1) — a counted-loop
  simulation lemma where the body pops a region cell and pushes it
  to a scratch buffer.

  **Sub-lemma list for full correctness**:

  1. `fetchProtocol_pc_step` — generalize to arbitrary sim.pc by
     induction; consumes one data cell per iteration plus the marker.

  2. `walkPastHaltedFlag` — pop one halted-flag cell, preserve in
     scratch; re-emit as `[encHaltedFlag regHex sim.halted]`.

  3. `walkPastSimHistLen` — counted-loop over simhist-len-counter,
     same scratch protocol.

  4. `walkPastSimHistory` — counted-loop over `sim.history.length`
     iterations, popping `sim.history` cells.

  5. `skipEncProgInstr` — the encProg-walker that uses
     `SkipInstr.skipOneInstr` `sim.pc` times.  Currently
     `skipOneInstr` covers only zero-arity ops (proven via
     `skipOneInstr_simulates_zeroArity`); the parameterized arities
     (1..4 cells) need their own simulation lemmas.

  6. `readNextTagCell` — pop one cell from the encProg tail (the
     tag of `sim.prog[sim.pc]`); leave it in `META.cur`.

  7. `unwindScratch` — counted-loop in reverse: pop scratch cells
     and push back into history with the canonical layout.

  8. `fetchProtocol_simulates_general` — the top-level theorem
     composing (1)–(7) into a `FetchOutcome` proof.

  9. `fetchProtocol_simulates_outOfBounds` — the halt-path
     companion theorem yielding `FetchHaltOutcome`.

  Each sub-lemma is structurally similar to the proofs in
  `MetaInterp.countedLoop_empty_simulates_n_iterations` and
  `SkipInstr.skipOneInstr_simulates_zeroArity`.  The combined
  engineering effort is estimated at ~600–900 LOC of Lean proof.
-/

end SSBX.Foundation.Wen.MetaInterp.Fetch
