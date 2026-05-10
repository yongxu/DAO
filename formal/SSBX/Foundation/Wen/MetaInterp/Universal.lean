/-
# Universal — universal-compose theorem for `metaInterpProg`

This file states the **universal-compose theorem** (B.T4.G.U0): that the
assembled `metaInterpProg : List YiInstr` of length 85 (see `Assembly.lean`)
simulates an arbitrary YiInstr program, in the sense that running it from a
META state encoding `(P, h)` for sufficient fuel produces a META state whose
history encodes the result of running `P` from initial hexagram `h`.

The full proof is multi-day work; this file's scope is a clean, readable
**theorem statement** plus a structured **decomposition into named
sub-obligations** (U.1–U.4), each marked with a `TODO(B.T4.G.U_)` tag so
downstream slots can target them individually.

## Strategy-B caveat

`metaInterpProg` uses fixed default arguments for the 5 parameterized opcodes
(setShi → dao, flipYao → 0, branchYaoEq → 0 0 0, branchShiEq → dao 0,
jump → 0).  Hence the theorem as stated below is true only when the simulated
program `P` consists of opcodes whose parameters happen to match those
defaults; **full universality** requires sub-dispatch trees per parameterized
arm (see `SubDispatch_BranchShiEq` / `SubDispatch_BranchYaoEq`).  This is
sub-obligation U.5 (documentation-only at this layer; promotion is the next
ticket).

## Roadmap for discharging the sorrys

| Tag                | Status | Cites                                                                |
|--------------------|--------|----------------------------------------------------------------------|
| `B.T4.G.U0`        | sorry  | composition of U.1–U.4                                               |
| `B.T4.G.U1`        | sorry  | `PrologueProg.postPrologueContract`,                                 |
|                    |        | `Assembly.metaInterpProg_routes_outerLoop_to_fetch`,                 |
|                    |        | `FetchProg.fetchProg_branch_*` (2 sorrys upstream),                  |
|                    |        | `DispatchProg.dispatchProg_routes_<op>` × 12,                        |
|                    |        | `ExecuteBlocks.Aggregate.executeBlock_<op>_local_effect`             |
| `B.T4.G.U2`        | sorry  | induction on iteration count `k`, applying U.1                       |
| `B.T4.G.U3`        | sorry  | halt-flag closure: once sim.halted, META loops in halt block         |
| `B.T4.G.U4`        | sorry  | fuel arithmetic — pure `omega`/`Nat.le_*` reasoning                  |
| `B.T4.G.U5`        | doc    | strategy-B limitations — sub-dispatch trees needed for full ∀-arm    |
-/
import SSBX.Foundation.Wen.MetaInterp.Assembly

namespace SSBX.Foundation.Wen.MetaInterp.Universal

open SSBX.Foundation.Yi.Yi
open SSBX.Foundation.Bagua.Cell256
open SSBX.Foundation.Bagua.BaguaTuring
open SSBX.Foundation.Bagua.KleeneInternal
open SSBX.Foundation.Wen.WenyanSelfInterp
open SSBX.Foundation.Wen.MetaInterp
open SSBX.Foundation.Wen.MetaInterp.Assembly

/-! ## § 1  Universal-compose theorem (U.0) -/

/-- A generous fuel bound: each simulated instruction takes at most
    `metaInterpProg.length` (= 85) fuel ticks of META execution; the
    additive `+ 5` accounts for the prologue.  This is the **bound used
    by U.0**; sub-obligation U.4 below is the proof-of-sufficiency. -/
def metaFuelBound (n : Nat) : Nat := metaInterpProg.length * (n + 5)

/-- The META starting state encoding the input pair `(P, h)`: cur = (h, jin),
    history = encProg P, pc = 0, prog = metaInterpProg, halted = false.

    This is exactly `RunWith h metaInterpProg (ProgEnc.encProg P)`. -/
def metaStart (h : Hexagram) (P : List YiInstr) : YiState :=
  RunWith h metaInterpProg (ProgEnc.encProg P)

/-- **U.0 — Universal compose.**

    Running `metaInterpProg` from the canonical META start state for
    `(P, h)`, with fuel `metaFuelBound n`, produces a META state whose
    history encodes the result of running `P` from `h` for `n` fuel
    ticks (under `encMetaHistory` with register-Hex = `h`), and whose
    `halted` flag agrees with the simulation's.

    **Caveats**:
    - Strategy B: parameterized opcodes use default args.  For full
      universality replace each parameterized arm with a sub-dispatch
      tree; see U.5 (documentation-only).
    - Fuel: `metaFuelBound n = 85 * (n + 5)` is generous; tightening is
      not required for correctness. -/
theorem metaInterpProg_simulates (h : Hexagram) (P : List YiInstr) (n : Nat) :
    let simResult := (YiState.init h P).runFuel n
    let metaResult := (metaStart h P).runFuel (metaFuelBound n)
    metaResult.history = encMetaHistory h simResult ∧
    metaResult.halted = simResult.halted := by
  -- TODO(B.T4.G.U0): main universal-compose theorem.  Strategy:
  --   1. Apply U.4 to expose `metaFuelBound n = 5 + (loopFuelPerIter * n + tail)`.
  --   2. Use PrologueProg.postPrologueContract to discharge the 5-fuel prologue,
  --      reducing to a META state at pc = outerLoopOffset with history =
  --      encMetaHistory h (YiState.init h P).
  --   3. Apply U.2 (k-iteration loop closure) with k = n.
  --   4. Apply U.3 to absorb any post-halt fuel.
  sorry

/-! ## § 2  Sub-obligations U.1 – U.4 -/

/-- **U.1 — Single iteration of the meta loop simulates one sim instruction.**

    Hypothesis: META state at `pc = outerLoopOffset`, history = encoding of
    a non-halted simulated state `sim`.  After one full loop iteration
    (fetch + dispatch + execute + writeback + jump-back-to-outerLoop),
    META state encodes `sim.step`.

    Discharge plan:
    - Apply `metaInterpProg_routes_outerLoop_to_fetch` (1 fuel) to land
      at `pc = fetchOffset`.
    - Apply `FetchProg.fetchProg_routes_running_to_dispatch` (currently
      sorry upstream) to decode the next sim opcode and route to dispatch.
    - Apply the appropriate `DispatchProg.dispatchProg_routes_<op>` to
      reach the matching `executeBlock_<op>` entry.
    - Apply `ExecuteBlocks.Aggregate.executeBlock_<op>_local_effect` to
      establish the per-opcode local effect on history/cur.
    - Conclude with `jump fetchOffset` (the trailing instr of every
      execute block) routing back to the outer loop. -/
theorem metaInterpProg_one_iteration_simulates
    (sim : YiState) (h : Hexagram)
    (h_running : sim.halted = false)
    : True := by
  -- TODO(B.T4.G.U1): per-iteration simulation.  Statement above is a
  -- placeholder; the real conclusion is "starting from the META state
  -- {cur = sim.cur, history = encMetaHistory h sim, pc = outerLoopOffset,
  -- prog = metaInterpProg, halted = false}, after K_iter fuel ticks the
  -- META state equals the same encoding of `sim.step`."  K_iter is
  -- bounded by `metaInterpProg.length` per the U.4 invariant.
  trivial

/-- **U.2 — Loop closure / k-iteration induction.**

    By induction on `k` using U.1: after `k` outer-loop iterations
    (= `K_iter * k` fuel ticks past the prologue), META state encodes
    `sim.runFuel k` (where `sim` is the post-prologue starting state). -/
theorem metaInterpProg_k_iterations
    (sim : YiState) (k : Nat) : True := by
  -- TODO(B.T4.G.U2): induction on k, base case = trivial (0 iters),
  -- step case = U.1 applied to the inductive state.
  trivial

/-- **U.3 — Halt propagation.**

    Once the simulated state halts (`sim.halted = true`), the next outer-
    loop iteration of META reads the halted-flag cell, routes to the
    `executeBlock_halt` arm (which is itself the halt instruction for
    META), and META halts.  Subsequent fuel ticks are no-ops. -/
theorem metaInterpProg_halts_when_sim_halts
    (sim : YiState) (h : Hexagram)
    (h_halted : sim.halted = true) : True := by
  -- TODO(B.T4.G.U3): halt-flag closure.  Cite
  -- `ExecuteBlocks.Aggregate.executeBlock_halt_local_effect` and the
  -- runFuel idempotence on halted states (`runFuel_halted_idem` if
  -- present, otherwise immediate from `YiState.step` on `halted = true`).
  trivial

/-- **U.4 — Fuel arithmetic / sufficient bound.**

    The chosen fuel `metaFuelBound n = metaInterpProg.length * (n + 5)`
    is sufficient: it covers the 5-fuel prologue plus `n` iterations of
    a loop body whose per-iteration cost is at most `metaInterpProg.length`.

    This is pure `Nat` arithmetic and should be discharged by `omega`
    once `K_iter ≤ metaInterpProg.length` is exposed. -/
theorem metaInterpProg_fuel_bound (n : Nat) :
    5 + metaInterpProg.length * n ≤ metaFuelBound n := by
  -- TODO(B.T4.G.U4): pure arithmetic.  metaInterpProg.length = 85;
  -- metaFuelBound n = 85 * (n + 5) = 85*n + 425 ≥ 85*n + 5.
  unfold metaFuelBound
  rw [metaInterpProg_length]
  -- 5 + 85 * n ≤ 85 * (n + 5) = 85*n + 425.
  have h1 : 85 * (n + 5) = 85 * n + 85 * 5 := Nat.mul_add 85 n 5
  omega

/-! ## § 3  U.5 — Strategy-B limitation (documentation-only) -/

/-- **U.5 — Strategy-B caveat (no proof obligation).**

    For *full* universality (∀ P : List YiInstr — including those whose
    parameterized opcodes have non-default arguments) the assembled
    program must be promoted: each of the 5 parameterized arms
    (setShi / flipYao / branchYaoEq / branchShiEq / jump) must read its
    parameter cell from META.history at dispatch-time and route to one
    of N specialized blocks.  See
    `SubDispatch_BranchShiEq` / `SubDispatch_BranchYaoEq` for the
    intended pattern.

    No theorem is proved here — this lemma exists to document the gap
    between Strategy-B and full universality at the file level. -/
theorem metaInterpProg_strategyB_limitations : True := trivial

end SSBX.Foundation.Wen.MetaInterp.Universal
