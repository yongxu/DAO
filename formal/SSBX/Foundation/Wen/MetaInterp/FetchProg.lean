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
open SSBX.Foundation.Bagua.Cell256
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

/-! ## § 5  General routing — deferred

These are the theorems Phase 2.3 truly needs.  Their proofs require
the full walk machinery (D1)–(D7) catalogued in `Fetch.lean §6`. -/

/-- The "fetch-when-halted" routing theorem.
    Starting from a fetch-pre-state on a sim with halted-flag = true
    (i.e., `sim.halted = true` so `encMetaHistory` carries a
    `haltedTrueCell`), fetch reaches `META.pc = haltOffset` in M
    fuel ticks, for some concrete M. -/
theorem fetchProg_routes_halted_general
    (regHex : Hexagram) (sim : YiState) (metaProg : List YiInstr)
    (offset dispatchOffset haltOffset : Nat)
    (_h_progStart : ∀ i (hi : i < fetchProg_totalLen),
        metaProg[offset + i]? = (fetchProg dispatchOffset haltOffset)[i]?)
    (_h_halted : sim.halted = true) :
    ∃ M : Nat,
      ((fetchEntryState regHex sim metaProg offset).runFuel M).pc = haltOffset := by
  -- TODO(B.T4.B): compose pc-counter peel (D1) + halted-flag read
  -- + branch-taken into the haltOffset arm.
  sorry

/-- The "fetch-when-not-halted" routing theorem.
    Starting from a fetch-pre-state on a running sim (with sim.pc
    in bounds), fetch advances META to a state with
    `META.pc = dispatchOffset` and `META.cur` carrying the tag cell
    of `sim.prog[sim.pc]`, in some concrete N fuel ticks. -/
theorem fetchProg_routes_running_to_dispatch
    (regHex : Hexagram) (sim : YiState) (metaProg : List YiInstr)
    (offset dispatchOffset haltOffset : Nat)
    (_h_progStart : ∀ i (hi : i < fetchProg_totalLen),
        metaProg[offset + i]? = (fetchProg dispatchOffset haltOffset)[i]?)
    (_h_running : sim.halted = false)
    (_h_pcInBounds : sim.pc < sim.prog.length) :
    ∃ N : Nat,
      ((fetchEntryState regHex sim metaProg offset).runFuel N).pc = dispatchOffset := by
  -- TODO(B.T4.B): compose pc-counter peel (D1) + halted-flag read
  -- + encProg-walker (D2)+(D5)+(D6) + scratch-unwind (D3)+(D7)
  -- into the dispatch arm.
  sorry

end SSBX.Foundation.Wen.MetaInterp.FetchProg
