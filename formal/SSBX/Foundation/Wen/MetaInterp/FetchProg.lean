/-
# FetchProg — Phase 2.3 redux concrete fetch program (base-256)

Companion / redux of `MetaInterp.Fetch`.  Where `Fetch.lean` developed
the *protocol skeleton* (a 4-instruction structural anchor + the
sim.pc = 0 base-case simulation), this file commits to a **definite,
length-fixed** concrete instruction sequence for the full fetch
operation, parameterized by the two routing offsets the outer loop
needs to thread through:

  * `dispatchOffset` — where to hand off when sim has NOT halted.
                        At entry, META.cur holds the next instruction's
                        tag cell and parameters are accessible in
                        META.history.
  * `haltOffset`     — where to route when sim has halted.

## Top-level shape

```
def fetchProg (dispatchOffset haltOffset : Nat) : List YiInstr
```

The length is fixed at `fetchProg_totalLen` (concrete numeral)
regardless of offsets.  This is the contract Phase B.T4.A
(prologueProg) and B.T4.C (executeBlocks) compose against.

## Halt-detection convention (per OuterLoop §"Design choice")

`fetchProg` is the single point of truth for halt detection.  The
strategy implemented here is the **straight-line skeleton** form: a
linear sequence of pops + branches that, in the full simulation, will
peel the pc-counter region off the top of META.history, observe the
halted-flag cell, and either:

  * (halted = Shi.ji)  → `YiInstr.jump haltOffset`
  * (halted = Shi.wei) → continue into the encProg walker,
                          eventually `YiInstr.jump dispatchOffset`.

For this T4.B deliverable, the encProg-walker portion is committed as
a **placeholder block** (`nop` × N + `jump dispatchOffset`) so that
its length contributes deterministically to `fetchProg_totalLen`.
The structural anchors (length lemma, routing theorems on the two
boundary inputs) are proven.

## Tier status (per task spec)

- Tier A (must): ✓ — `fetchProg` defined with definite length
  `fetchProg_totalLen = 1 + walkerLen + 1` (concretely a numeral).
- Tier B (try): ✓ — `fetchProg_length` shape lemma.
- Tier C (try): partial — `fetchProg_routes_halted` proven for the
  *degenerate* shape where META.cur already carries the halted-flag
  cell at fetch entry.  The full version (which walks past pc-counter
  first) is left as a `sorry` with a TODO marker.
- Tier D (stretch): not attempted — both routing theorems with full
  simulation traces are out of scope for one agent's slot.

## Sorrys (≤ 4, all TODO(B.T4.B))

  1. `fetchProg_routes_halted_general` — the full walk-then-detect
     halted theorem.  Reduces to (D1) + (D2) from `Fetch.lean`.
  2. `fetchProg_routes_running_to_dispatch` — the full
     decode-and-route theorem.  Reduces to (D1)–(D7) from `Fetch.lean`.

The other two budget slots are reserved for arithmetic glue if the
shape lemmas need them; not used in this draft.

## Interface for composing agents

  * `fetchProg_totalLen` (Nat) — concrete numeral, callers may use
    it for offset arithmetic.
  * `fetchProg_first` / `fetchProg_last_dispatchJump` —
    structural lemmas for routing inside the outer loop.

-/
import SSBX.Foundation.Wen.MetaInterp.Fetch

namespace SSBX.Foundation.Wen.MetaInterp.FetchProg

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.R8
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.MetaInterp
open SSBX.Foundation.Wen.MetaInterp.Fetch

/-! ## § 1  Length budget

The fetchProg consists of three regions:

  * halted-detection prologue:  reads the halted-flag region.  Modelled
    here as 2 instructions (`pop` + `branchShiEq Shi.ji haltOffset`)
    placed *at the conceptual entry* (after pc-counter peel — which is
    represented inside the walker region for this draft).

  * encProg-walker placeholder:  `walkerLen` no-op slots that, in the
    full implementation, will perform the counted-loop walk over the
    encProg tail to extract `prog[sim.pc]`'s tag cell.  Concrete
    `walkerLen` chosen here = 8 (room for: pc-counter peel × 1,
    simhist-len peel × 1, simhist-walk × 1, encProg-skip × 1,
    tag-read × 1, scratch-unwind × 3).  Each slot is `YiInstr.nop`.

  * dispatch tail:  one `YiInstr.jump dispatchOffset` to hand off.
-/

/-- Number of instructions reserved for the encProg walker region. -/
def walkerLen : Nat := 8

/-- Total length of the fetchProg program (independent of offsets). -/
def fetchProg_totalLen : Nat := 2 + walkerLen + 1

theorem fetchProg_totalLen_eq : fetchProg_totalLen = 11 := rfl

/-! ## § 2  Concrete fetch program

The order is:
```
offset+0:                 pop                            -- consume halted-flag cell into cur
                                                            (in the full impl, this is preceded
                                                             by the pc-counter peel; for the
                                                             length-fixed draft we model the
                                                             halt-detect as a single pop+branch
                                                             at fetch entry on a state shape that
                                                             has halted-flag already at the top)
offset+1:                 branchShiEq Shi.ji haltOffset  -- if halted, route to halt
offset+2..offset+9:       nop × walkerLen                -- walker placeholder
offset+10:                jump dispatchOffset            -- hand off
```
Total = 1 + 1 + walkerLen + 1 = 11 = `fetchProg_totalLen`. -/
def fetchProg (dispatchOffset haltOffset : Nat) : List YiInstr :=
  [ YiInstr.pop
  , YiInstr.branchShiEq Shi.ji haltOffset
  ] ++ List.replicate walkerLen YiInstr.nop ++
  [ YiInstr.jump dispatchOffset ]

theorem fetchProg_length (dispatchOffset haltOffset : Nat) :
    (fetchProg dispatchOffset haltOffset).length = fetchProg_totalLen := by
  unfold fetchProg fetchProg_totalLen walkerLen
  simp [List.length_cons]

theorem fetchProg_length_concrete (dispatchOffset haltOffset : Nat) :
    (fetchProg dispatchOffset haltOffset).length = 11 := by
  rw [fetchProg_length]; rfl

/-! ## § 3  Structural lookup lemmas -/

theorem fetchProg_first (dispatchOffset haltOffset : Nat) :
    (fetchProg dispatchOffset haltOffset)[0]? = some YiInstr.pop := rfl

theorem fetchProg_second (dispatchOffset haltOffset : Nat) :
    (fetchProg dispatchOffset haltOffset)[1]? =
      some (YiInstr.branchShiEq Shi.ji haltOffset) := rfl

theorem fetchProg_last_dispatchJump (dispatchOffset haltOffset : Nat) :
    (fetchProg dispatchOffset haltOffset).getLast? =
      some (YiInstr.jump dispatchOffset) := by
  unfold fetchProg
  rfl

/-! ## § 4  Degenerate routing — halted-flag already in cur

These two theorems are the routing **anchors** the outer-loop
composition needs: from a META state whose `cur` carries the halted-
flag cell and whose `prog` points at `fetchProg`, after the first
branch instruction META is routed to either `haltOffset` (halted) or
falls through to the walker (running).

The "general" version (which walks the pc-counter region first) is
deferred.  See sorrys below. -/

/-- Entry state where META.cur already carries the halted-flag cell
    (post pc-counter peel).  This is the shape on which we prove the
    branch routing. -/
def fetchProgHaltDetectEntry
    (regHex : Hexagram) (sim : YiState) (metaProg : List YiInstr)
    (offset : Nat) (b : Bool) : YiState :=
  { cur     := encHaltedFlag regHex b
  , history := encCounter regHex sim.history.length ++
               sim.history ++
               ProgEnc.encProg sim.prog
  , pc      := offset + 1   -- already at the branch instruction
  , prog    := metaProg
  , halted  := false }

/-- When the halted flag = true, the `branchShiEq Shi.ji haltOffset`
    instruction routes pc to `haltOffset` in 1 fuel step. -/
theorem fetchProg_branch_halted_true
    (regHex : Hexagram) (sim : YiState) (metaProg : List YiInstr)
    (offset _dispatchOffset haltOffset : Nat)
    (h_branchAt : metaProg[offset + 1]? =
      some (YiInstr.branchShiEq Shi.ji haltOffset)) :
    ((fetchProgHaltDetectEntry regHex sim metaProg offset true).step).pc
      = haltOffset := by
  show (fetchProgHaltDetectEntry regHex sim metaProg offset true).step.pc = haltOffset
  unfold YiState.step
  have h_halt : (fetchProgHaltDetectEntry regHex sim metaProg offset true).halted = false := rfl
  rw [h_halt]
  simp only [Bool.false_eq_true, if_false]
  have h_prog : (fetchProgHaltDetectEntry regHex sim metaProg offset true).prog = metaProg := rfl
  have h_pc   : (fetchProgHaltDetectEntry regHex sim metaProg offset true).pc = offset + 1 := rfl
  rw [h_prog, h_pc, h_branchAt]
  show (YiState.execute (YiInstr.branchShiEq Shi.ji haltOffset)
          (fetchProgHaltDetectEntry regHex sim metaProg offset true)).pc = haltOffset
  -- branchShiEq executes as: if cur.2 = target then { with pc := tgt } else { with pc := pc+1 }
  -- Compute via direct change-of-goal since YiState.execute reduces by match.
  show (if (fetchProgHaltDetectEntry regHex sim metaProg offset true).cur.2 = Shi.ji
        then { (fetchProgHaltDetectEntry regHex sim metaProg offset true) with pc := haltOffset }
        else { (fetchProgHaltDetectEntry regHex sim metaProg offset true) with
                 pc := (fetchProgHaltDetectEntry regHex sim metaProg offset true).pc + 1 }).pc
       = haltOffset
  have hji : (fetchProgHaltDetectEntry regHex sim metaProg offset true).cur.2 = Shi.ji := rfl
  rw [if_pos hji]

/-- When the halted flag = false (running), the branch is NOT taken;
    pc advances to `offset + 2` (the start of the walker region). -/
theorem fetchProg_branch_halted_false
    (regHex : Hexagram) (sim : YiState) (metaProg : List YiInstr)
    (offset _dispatchOffset haltOffset : Nat)
    (h_branchAt : metaProg[offset + 1]? =
      some (YiInstr.branchShiEq Shi.ji haltOffset)) :
    ((fetchProgHaltDetectEntry regHex sim metaProg offset false).step).pc
      = offset + 2 := by
  show (fetchProgHaltDetectEntry regHex sim metaProg offset false).step.pc = offset + 2
  unfold YiState.step
  have h_halt : (fetchProgHaltDetectEntry regHex sim metaProg offset false).halted = false := rfl
  rw [h_halt]
  simp only [Bool.false_eq_true, if_false]
  have h_prog : (fetchProgHaltDetectEntry regHex sim metaProg offset false).prog = metaProg := rfl
  have h_pc   : (fetchProgHaltDetectEntry regHex sim metaProg offset false).pc = offset + 1 := rfl
  rw [h_prog, h_pc, h_branchAt]
  show (YiState.execute (YiInstr.branchShiEq Shi.ji haltOffset)
          (fetchProgHaltDetectEntry regHex sim metaProg offset false)).pc = offset + 2
  show (if (fetchProgHaltDetectEntry regHex sim metaProg offset false).cur.2 = Shi.ji
        then { (fetchProgHaltDetectEntry regHex sim metaProg offset false) with pc := haltOffset }
        else { (fetchProgHaltDetectEntry regHex sim metaProg offset false) with
                 pc := (fetchProgHaltDetectEntry regHex sim metaProg offset false).pc + 1 }).pc
       = offset + 2
  have hne : (fetchProgHaltDetectEntry regHex sim metaProg offset false).cur.2 ≠ Shi.ji := by
    show Shi.wei ≠ Shi.ji
    decide
  rw [if_neg hne]
  show (fetchProgHaltDetectEntry regHex sim metaProg offset false).pc + 1 = offset + 2
  rw [h_pc]

/-! ## § 5  General routing — composed from a peel hypothesis

These are the theorems Phase 2.3 truly needs.  The full walk
machinery (D1)–(D7) catalogued in `Fetch.lean §6` — the pc-counter
peel — is genuinely upstream-missing.  We discharge the routing
theorems modulo a **peel-witness hypothesis**: the caller supplies
an `M0` such that `runFuel M0` from the fetch-entry state reaches
`fetchProgHaltDetectEntry` (the state shape on which our branch
lemmas operate, with the halted-flag in `cur` and pc at offset+1).
This factors the routing proof at exactly the boundary upstream
agents will plug D1 into.

The post-peel routing — branch + walker placeholder traversal +
final dispatch jump — is fully proven below as helper lemmas, and
the existential witnesses are constructed concretely. -/

/-! ### § 5a  Walker placeholder traversal -/

/-- After the running-arm branch fall-through, META is at
    `pc = offset + 2` running through `walkerLen = 8` nops.
    Each nop advances pc by 1, so after `k` nops we are at
    `pc = offset + 2 + k`, provided the walker slots are nops. -/
private theorem walker_nops_advance
    (s : YiState) (offset : Nat) (k : Nat) (hk : k ≤ walkerLen)
    (h_pc : s.pc = offset + 2)
    (h_halted : s.halted = false)
    (h_walkerSlots : ∀ j (_ : j < walkerLen),
        s.prog[offset + 2 + j]? = some YiInstr.nop) :
    ∃ s', s.runFuel k = s'
        ∧ s'.pc = offset + 2 + k
        ∧ s'.halted = false
        ∧ s'.prog = s.prog := by
  induction k with
  | zero =>
      refine ⟨s, ?_, ?_, ?_, ?_⟩ <;> simp [YiState.runFuel, h_pc, h_halted]
  | succ k ih =>
      have hk' : k ≤ walkerLen := Nat.le_of_succ_le hk
      have hk_lt : k < walkerLen := hk
      obtain ⟨s', hrun, hpc', hhalt', hprog'⟩ := ih hk'
      -- runFuel (k+1) s = (runFuel k s).step = s'.step
      have hstep : s.runFuel (k + 1) = s'.step := by
        rw [SSBX.Foundation.Bagua.GodelLi.runFuel_succ_right, hrun]
      -- Compute s'.step: not halted, prog[s'.pc]? = some nop, execute nop
      have h_lookup : s'.prog[s'.pc]? = some YiInstr.nop := by
        rw [hpc', hprog']
        exact h_walkerSlots k hk_lt
      -- Compute s'.step.pc, .halted, .prog directly.
      have h_step_pc : s'.step.pc = s'.pc + 1 := by
        unfold YiState.step
        rw [hhalt']; simp only [Bool.false_eq_true, if_false]
        rw [h_lookup]; rfl
      have h_step_halted : s'.step.halted = false := by
        unfold YiState.step
        rw [hhalt']; simp only [Bool.false_eq_true, if_false]
        rw [h_lookup]; show (YiState.execute YiInstr.nop s').halted = false
        unfold YiState.execute; exact hhalt'
      have h_step_prog : s'.step.prog = s.prog := by
        unfold YiState.step
        rw [hhalt']; simp only [Bool.false_eq_true, if_false]
        rw [h_lookup]; show (YiState.execute YiInstr.nop s').prog = s.prog
        unfold YiState.execute; exact hprog'
      refine ⟨s'.step, ?_, ?_, ?_, ?_⟩
      · exact hstep
      · rw [h_step_pc, hpc']; omega
      · exact h_step_halted
      · exact h_step_prog

/-- After traversing all `walkerLen = 8` nops, the final `jump
    dispatchOffset` instruction routes pc to `dispatchOffset`. -/
private theorem walker_then_dispatch_jump
    (s : YiState) (offset dispatchOffset : Nat)
    (h_pc : s.pc = offset + 2)
    (h_halted : s.halted = false)
    (h_walkerSlots : ∀ j (_ : j < walkerLen),
        s.prog[offset + 2 + j]? = some YiInstr.nop)
    (h_jumpAt : s.prog[offset + 10]? = some (YiInstr.jump dispatchOffset)) :
    (s.runFuel (walkerLen + 1)).pc = dispatchOffset := by
  obtain ⟨s', hrun, hpc', hhalt', hprog'⟩ :=
    walker_nops_advance s offset walkerLen (Nat.le.refl) h_pc h_halted h_walkerSlots
  -- runFuel (walkerLen + 1) s = s'.step
  have hstep : s.runFuel (walkerLen + 1) = s'.step := by
    rw [SSBX.Foundation.Bagua.GodelLi.runFuel_succ_right, hrun]
  -- Now s'.pc = offset + 2 + walkerLen = offset + 10
  have h_pc_final : s'.pc = offset + 10 := by
    rw [hpc']; unfold walkerLen; omega
  have h_lookup : s'.prog[s'.pc]? = some (YiInstr.jump dispatchOffset) := by
    rw [h_pc_final, hprog']; exact h_jumpAt
  have h_step_pc : s'.step.pc = dispatchOffset := by
    unfold YiState.step
    rw [hhalt']; simp only [Bool.false_eq_true, if_false]
    rw [h_lookup]; rfl
  rw [hstep]; exact h_step_pc

/-! ### § 5b  Routing theorems (composed via peel hypothesis) -/

/-- The "fetch-when-halted" routing theorem.

    Composition: caller provides a peel-witness `M0` showing that
    `runFuel M0` from the fetch-entry state reaches the
    `fetchProgHaltDetectEntry … true` shape (post pc-counter peel,
    halted-flag exposed in cur).  We then take 1 more fuel step
    through `branchShiEq Shi.ji` which (by `fetchProg_branch_halted_true`)
    routes to `haltOffset`.  Total fuel: `M0 + 1`. -/
theorem fetchProg_routes_halted_general
    (regHex : Hexagram) (sim : YiState) (metaProg : List YiInstr)
    (offset dispatchOffset haltOffset : Nat)
    (h_progStart : ∀ i (hi : i < fetchProg_totalLen),
        metaProg[offset + i]? = (fetchProg dispatchOffset haltOffset)[i]?)
    (_h_halted : sim.halted = true)
    (h_peel : ∃ M0 : Nat,
        (fetchEntryState regHex sim metaProg offset).runFuel M0
        = fetchProgHaltDetectEntry regHex sim metaProg offset true) :
    ∃ M : Nat,
      ((fetchEntryState regHex sim metaProg offset).runFuel M).pc = haltOffset := by
  obtain ⟨M0, hM0⟩ := h_peel
  refine ⟨M0 + 1, ?_⟩
  -- runFuel (M0 + 1) = (runFuel M0).step
  rw [SSBX.Foundation.Bagua.GodelLi.runFuel_succ_right, hM0]
  -- Need branch-instruction lookup: metaProg[offset+1]? = some (branchShiEq Shi.ji haltOffset)
  have h_branchAt : metaProg[offset + 1]? =
      some (YiInstr.branchShiEq Shi.ji haltOffset) := by
    have h := h_progStart 1 (by unfold fetchProg_totalLen walkerLen; decide)
    -- (fetchProg _ _)[1]? = some (branchShiEq Shi.ji haltOffset) by rfl
    exact h.trans rfl
  exact fetchProg_branch_halted_true regHex sim metaProg offset
    dispatchOffset haltOffset h_branchAt

/-- The "fetch-when-not-halted" routing theorem.

    Composition: peel-witness `M0` reaches
    `fetchProgHaltDetectEntry … false`.  Then 1 step through the
    branch (not taken, advances to offset+2), then `walkerLen` nops,
    then 1 final `jump dispatchOffset`.  Total fuel:
    `M0 + 1 + walkerLen + 1 = M0 + 10`. -/
theorem fetchProg_routes_running_to_dispatch
    (regHex : Hexagram) (sim : YiState) (metaProg : List YiInstr)
    (offset dispatchOffset haltOffset : Nat)
    (h_progStart : ∀ i (hi : i < fetchProg_totalLen),
        metaProg[offset + i]? = (fetchProg dispatchOffset haltOffset)[i]?)
    (_h_running : sim.halted = false)
    (_h_pcInBounds : sim.pc < sim.prog.length)
    (h_peel : ∃ M0 : Nat,
        (fetchEntryState regHex sim metaProg offset).runFuel M0
        = fetchProgHaltDetectEntry regHex sim metaProg offset false) :
    ∃ N : Nat,
      ((fetchEntryState regHex sim metaProg offset).runFuel N).pc = dispatchOffset := by
  obtain ⟨M0, hM0⟩ := h_peel
  refine ⟨M0 + 1 + (walkerLen + 1), ?_⟩
  -- Step A: runFuel (M0 + 1) reaches the post-branch state at pc = offset+2.
  -- Step B: runFuel (walkerLen + 1) further reaches dispatchOffset.
  -- We'll use runFuel_succ_right for the +1, then walker_then_dispatch_jump for walkerLen+1.
  -- First, compute runFuel (M0 + 1) explicitly.
  have h_branchAt : metaProg[offset + 1]? =
      some (YiInstr.branchShiEq Shi.ji haltOffset) := by
    have h := h_progStart 1 (by unfold fetchProg_totalLen walkerLen; decide)
    exact h.trans rfl
  -- The post-branch state.
  let entry := fetchEntryState regHex sim metaProg offset
  let postPeel := fetchProgHaltDetectEntry regHex sim metaProg offset false
  show (entry.runFuel (M0 + 1 + (walkerLen + 1))).pc = dispatchOffset
  -- runFuel (M0 + 1) entry = postPeel.step
  have hrun_M0_1 : entry.runFuel (M0 + 1) = postPeel.step := by
    rw [SSBX.Foundation.Bagua.GodelLi.runFuel_succ_right, hM0]
  -- postPeel.step has pc = offset + 2 (by fetchProg_branch_halted_false)
  have h_postStep_pc : postPeel.step.pc = offset + 2 :=
    fetchProg_branch_halted_false regHex sim metaProg offset
      dispatchOffset haltOffset h_branchAt
  -- postPeel.step preserves halted=false and prog=metaProg.
  have h_postStep_halted : postPeel.step.halted = false := by
    -- Inspect step: not halted, branchShiEq with cur.2 = Shi.wei ≠ Shi.ji → falls through.
    unfold YiState.step
    have h_halt0 : postPeel.halted = false := rfl
    rw [h_halt0]
    simp only [Bool.false_eq_true, if_false]
    have h_prog0 : postPeel.prog = metaProg := rfl
    have h_pc0 : postPeel.pc = offset + 1 := rfl
    rw [h_prog0, h_pc0, h_branchAt]
    show (YiState.execute (YiInstr.branchShiEq Shi.ji haltOffset) postPeel).halted = false
    show (if postPeel.cur.2 = Shi.ji
          then { postPeel with pc := haltOffset }
          else { postPeel with pc := postPeel.pc + 1 }).halted = false
    have hne : postPeel.cur.2 ≠ Shi.ji := by show Shi.wei ≠ Shi.ji; decide
    rw [if_neg hne]; rfl
  have h_postStep_prog : postPeel.step.prog = metaProg := by
    unfold YiState.step
    have h_halt0 : postPeel.halted = false := rfl
    rw [h_halt0]
    simp only [Bool.false_eq_true, if_false]
    have h_prog0 : postPeel.prog = metaProg := rfl
    have h_pc0 : postPeel.pc = offset + 1 := rfl
    rw [h_prog0, h_pc0, h_branchAt]
    show (YiState.execute (YiInstr.branchShiEq Shi.ji haltOffset) postPeel).prog = metaProg
    show (if postPeel.cur.2 = Shi.ji
          then { postPeel with pc := haltOffset }
          else { postPeel with pc := postPeel.pc + 1 }).prog = metaProg
    have hne : postPeel.cur.2 ≠ Shi.ji := by show Shi.wei ≠ Shi.ji; decide
    rw [if_neg hne]; rfl
  -- Walker-slot lookups: positions offset+2..offset+9 are nops.
  have h_walkerSlots : ∀ j (_ : j < walkerLen),
      postPeel.step.prog[offset + 2 + j]? = some YiInstr.nop := by
    intro j hj
    rw [h_postStep_prog]
    have hi_lt : 2 + j < fetchProg_totalLen := by
      unfold fetchProg_totalLen walkerLen at hj ⊢; omega
    have h := h_progStart (2 + j) hi_lt
    -- offset + (2 + j) = offset + 2 + j
    have hoff : offset + (2 + j) = offset + 2 + j := by omega
    rw [hoff] at h
    rw [h]
    -- (fetchProg _ _)[2+j]? = some YiInstr.nop  for j < 8
    show (fetchProg dispatchOffset haltOffset)[2 + j]? = some YiInstr.nop
    unfold fetchProg walkerLen
    -- The list is [pop, branch] ++ replicate 8 nop ++ [jump]; index 2+j with j<8 is nop.
    have hj' : j < 8 := by unfold walkerLen at hj; exact hj
    -- Manual case-split on j ∈ [0,8).
    match j, hj' with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
    | 4, _ => rfl
    | 5, _ => rfl
    | 6, _ => rfl
    | 7, _ => rfl
  -- Final jump lookup.
  have h_jumpAt : postPeel.step.prog[offset + 10]? = some (YiInstr.jump dispatchOffset) := by
    rw [h_postStep_prog]
    have hi_lt : 10 < fetchProg_totalLen := by
      unfold fetchProg_totalLen walkerLen; decide
    have h := h_progStart 10 hi_lt
    rw [h]
    rfl
  -- Now compose: runFuel (M0 + 1 + (walkerLen + 1)) entry
  --   = (runFuel (M0+1) entry).runFuel (walkerLen+1)
  --   = postPeel.step.runFuel (walkerLen+1)
  --   = dispatchOffset (by walker_then_dispatch_jump).
  have h_add : ∀ k, entry.runFuel (M0 + 1 + k)
              = (entry.runFuel (M0 + 1)).runFuel k := by
    intro k
    induction k with
    | zero => simp [YiState.runFuel]
    | succ k ih =>
        rw [show M0 + 1 + (k + 1) = (M0 + 1 + k) + 1 from rfl,
            SSBX.Foundation.Bagua.GodelLi.runFuel_succ_right,
            SSBX.Foundation.Bagua.GodelLi.runFuel_succ_right, ih]
  have h_add' := h_add (walkerLen + 1)
  rw [h_add', hrun_M0_1]
  exact walker_then_dispatch_jump postPeel.step offset dispatchOffset
    h_postStep_pc h_postStep_halted h_walkerSlots h_jumpAt

end SSBX.Foundation.Wen.MetaInterp.FetchProg
